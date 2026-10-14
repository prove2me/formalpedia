-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1670
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:09:05.105988+00:00
-- url     : https://prove2.me/submissions/7b35a810-41b1-4f51-8bac-4d9f686ed499

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 300179856 ≤ n < 300359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 300181106 1250 300179856 300179909
    0x302071e030f0c050f0d020c0f1c060203090106170109050c01051c0b180903250f150b1309171207110f0d0c020f0d050706030b012106 59
    0x55903058031182d828180144045404000b40f00b016034180c85440c540c01903c50050040711180c40455020304040440d120501225101502c3e0550041a0700292400c0c4030110000f080308465110f000583d0307076141c0030213484c0904001d40020400301c05580200760099015072080362007912541c2500e042c8101d01006541c3c074004c80c80700c8014011038220f00300800409910460010301c005190311030031a9490014100400100c0d18010554000105103407003d000c19040d900313001c032504190034100f01994441032110922507005000d004102c05070f281d0070045070805c0740b1030701002d001540c5040e105110301c0042c040b100c034180c035581c83c07a01c0001102e844031000c490f2180c5502c0c88a030000e03107030104122034078014a900380f0644c2c0a9400344240d54101408203250749001030303594103c1c10007540100800384089243c0f49109802d4020100000350340070411401b01e907940c1c04c1c000740d22a07c15005070f0f010207038105800006081010401403400ea181d00200a0f02d014041486002c5482140d1140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 300182356 1250 300181106 300181163
    0x30501060b071505060906040b01110303070309050f010209030c0907030e06070504170106030206040e0603070f33091703130e070f0f080105060d020c0102070b0106020d050406170421030207 83
    0x400118000018046007400c0d00f00c027a0110041c50b0a04460101200301410b6804c103079143d10029031201c441d68140602007200c00150168980214038181c04400001d0b5910001120540160f420342c00182da120700a03803140050120400943c0c4035484d20b407200800700e44c02401181a80c61030038008011140c01480340f40142d0341d010f82082e10b02824440d40c0704203250003e0010740d040c45a280041510087d00c15400002c0c40c080c41e10581584085007200ca41d0240d80c0d030300c03031185180034514010340d07907000c1e8120044460443e120703020340010490441c11480b40c254500b254403070200c1300141480e0403a00c000e00c10002a501c6000c20a1038442c11101e2444200310f0100051340354005014a15003600100240703d0090703401483c2a00c0e44840e142a6040741c4016240002500010080e181c2c060005841d24091864070602d024108480a40341d52a4540e0a0704a4002c8500060130040a40e40314020740421046c241e18036a8940f400170b000c0d52041c802101c0d441c03038000344a00031405506040300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 300183606 1250 300182356 300182359
    0x60f010f060504180216030e0307050f1c05250806010b0c0d0509030712030804060b0f0a0b0906090d0b180313060807030f06060903030905090906041407030501060b07150506 76
    0xe14042c03500700c0d040c420300141315541000700d41c200103400783c407545415000309283c420703103800b411030380d00b0810942400f40b50b50041c0d002c0c4001e820600401c0c2c1d210341c2038610f11003401511640c141b92600f403641c41d001c3c9580e00030b0f0b08111103440f08901d841c044c401c00310456a048080350150303070301c44026401d42d014040f40760311980e201d40d05100300a030042015020700701e006400c48141a43d9569448501c10440c4420303170100705441c0522044c41018042c0c3c3e45264002c1e036101140d035541c0b50218040042510604280400c0403038055480e68179001140c40140006280074600c80d0a4104128001d40c140c5030040d40300300c4004461030b415070100540d05154907a40c0200c08241c1f0300403090300c0c15500180100101a40c443c04144d2400d00c41c841cac00091300035990780441c1c0a09500d0b0181103040150000303845039178800c0030800080760020780c0340e0b0703c59030080c80c002c150038000d00c050785408403d0300b00504135420308202003030038020400a0700d45680034881154120f09080d002000b00c0e081900c42a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 300184856 1250 300183606 300183617
    0x4060b0a0c0803090c0310020703080f1015030b04050907050a1401050702010c03020a021908070b043017091e030a021210020c010c0f090f030605060d050609060f010f06 74
    0x207400700300603402855002c402c84060f01c100c0c215420000b4103040c01c031001c9982d41c0d03a000c5251000d141e88004e8480e400003034040303142e180d402d04d000001c41f540018401c03c20346840c1e60109806143c1700b60000404504080e1041c0018208081c444c0c1d00d52043c1d0080034000d58000c9000204c10300d01c0c0600f24035207001a103819181001c1c1d60011641030161100039410b61040850540050700c40c00129521248101c10042685c2d0a10200500b0004940d2040c00000c1041c001400100001d0101d206052481340039002c4100300809000c0d180140a90081e061412600c0b007540d40c002000000d016400c0d0443d25800a45a522054031010420340c1d010b80d0942d02c85e00c010001410803031003141070b8402c00400c4600411540d000201a03a01c04090801c06035190081c0248098200b15071032001241824001d680600700000d0b174805984512018000d1505c1d04040b0751283c88006010200e1900141500c0062400002c0f55a80e14400e44450007000248000003030070603070b0310f01c0003002d844003540d80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 300186106 1250 300184856 300184877
    0x415080c010f080a0507050919060f09030b1501030605130203070f050c030909060303091c11040908030a0506010512070e120d0c060e151008070e0f04140f060c070204060b0a 76
    0x1018001d1000030300306807d10204000414a61b03a0ba83c41c0301d010b04227014071585c2c0050034080001c1651780b0304e000180c00e01585020900c0094030040600d41c0c042d00e0000700085041e11200104d010f02080e51241303802c203034a80c102c042c18010380d80080d0f2081200340c403541144804804111201c0c03080c408083d04603003003440000d031b452400030b0044d90003c8000302120b0400f9140800a5565144500b034121701019078a045010070880340405464000d00312410054107103e501c406402c0e200044c001d070203036940e500004415a0091083d1443e131003501e1a00081464003040c040c104c1c0000c91651441001c10201c40d52441d1000650300da42864140c0c1c807101c102126503a010080e214000c46007855009030861001d1500180b01000e11801c980102c00c0c01c1546440d000d5130a185681c4c100c040d101841500700300004040e000100d8103c3e0780b240c075441c80c2c45a207000040c01e0000100010300980154424400d600c2c00350809040c980740211740800115a50341006c04091064410007004504070a44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 300187356 1250 300186106 300186121
    0xb1609150f0c0615050306150117180303010605282106050d1110090509070503062d031902031914070b0a110a23010b0415080c010f08 59
    0x200001d03411041c140341407010207580d104000e48201940d08800c880b2491020440c42c0ba040040ca9003101d49050403283e0a20703450002405a12000181d400c1890508041100340454001000420030f000042c4c9450f56140c86006200d540000b40496141c25020ba9400e030810700356280409086150b110784164040c0354402584060a8103400c100d005d960703881c0051141c5501d0404141c40c2d1240c51842e08403211402040068074440243d1020040103100520060b1100b01045404c00841c1c1007541d120364821000455581142c1a000c2461240000441c0b401140c20710803040c40c5003c81c02d4444e444000305000c3c050484001010303605600c0380344021484c41c035070100510114001e010380d41180d0440c0380601d18059240c0d11150080c100058040e1506520520300e20158001c00c0c00307070000700b81c2920346004004003902c40b8505c4a035140303080840001c00b540f00d001418070103130041c0450b890030091401504d4451082e05814020320301061001d40c840c6841010401031921441070359241c00c50f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 300188606 1250 300187356 300187367
    0xb0f060111060a050c09030102160b01061b0330050f0601020307050c060a0203222102010e010305060a15080109050a0204060c060b01050403060501030b151e06070c050901030b160915 80
    0x9091060017a401c0040d800c003924280001c1032680c900c48015941e204d00c901d000c0c4e2400030f0582c0203200b0058036001d10f0344070b08060f1003442e00d1241c05141c080100174902c4240302d20012001d10046201100e41e13000c580000082d0050f0740306001c06440050f0903940c002c0160703100c0c0b0520100030007580201c0c210107210326004010300f000d100c2c1e034030480b410b2000d500c02000840da00d00506040c3c2c41c4124000300101140fa1100b8081000ca100fa561102c10181d030000e0401c0e4940c21089040c10785035400031700f4984644490800520004480c035a0101410788080e210b10001e000b00c080301401c20000490b40170b414001c550031618942ea80c204082e4940c0c48100083c001e1240c85410040c08106c0000402c5503401100d020b180103c0d00c444103030500200056101900340300c45405031100120018030a0b005c2c5000110108003071f070350191340b4007080c84c03c075000d003a150300040c0e88058403030004000c0c404044c9080c1d1252203501c4850700b05e41008a401e548007100c43c800c90b5100c04418036507102c05403050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 300189856 1250 300188606 300188611
    0xf120903070603051005150309010b01020102040311040207022b0605061807050a02010f02030106031a01090302011b02040902120a0c0e090709110d09060c0e01170103080705190b0f060111060a05 85
    0x1944000c2005440b06e00080181083c0208480c0c504000700510113170950a10690000c140300340000c62030f103440c542c0d6441d1414400e1400d248242e9003c5506d074150349800084030305c0e001c018101508000a100e46190a03116508020b40c0d50324600703000143d1906102140340e40c0705441128050980ea12800c0032030301da50000d4180c0e0219500c5d580c0714192083c039800030394040e007042c0e100030588100d00040400141c03d0030b00c41c0790400c0003a031010400741c0d03000060740c010004603807042c00c0c103003d081c001704010f0f02d001c3c2c00c000c0d084070f2040400d103109400072a00042482c400d01c0b005440aa8900414001c000103861120854120b03940420094149610616980b8208410181071642070941b1604552140800380c60a0361540c41e850109640321072a529a18002d0074000d40c00c03511401810f070307117190500004150f043c000a50006007c020000e02c20b4624484c491805540040d20b000c40121005a9543c0c040060042c04101d0b55800f4801014008100e00001c05030380d55982e03042005040003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 300191106 1250 300189856 300189871
    0x10513020f0d020a09140402121603020c12041d1603050a060905150a1502070306021e1b071a070210110304170705190312030f0e0f12090307060305 65
    0x80140b00c840102c2c0d0700180408001e44c0c0c882401c298a041075400100c80b503082c1c402c1c8150710411070b40c0018200d1300e41c0315130408145c400d00c1201c500c510742c090303000f442104541402031054034004081c1c040e4a80041041c0d039a0010210401c90b054000300007044001c0e2070b40351100f540c102c00740b44075900c258850355004500344000b10346e0b10b5032070800d50f086a20580301700c1480003003203a43d81000c1c18600c00d01c3e00140320303c000d1b55182450858009407105180c2c04010412500080e0b0601014107031292940240251801266117008203040c0d00c0040d1061101800e05001c0d080001038404554942201c2c841c0c2005141454000740f507003009840f000501812040c010300643d2a014000c00300060409083d55a1101c100e81c001c0b0179509103041007239800f091180081d080000b99030140b41241c0e8084070b03480340c12202d021000110542c0034180701c15903a0103251500d4030400313070001c00051041089000d103050b10401244440742400e180300e00746019800d070340301040802880c0e10903444580c1c001d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 300192356 1250 300191106 300191137
    0x21b0721110a060e01030c05031509060d0b070804110a030312021c02030a0f1b0c0b04031403100306140708160203090d08033112201c030501051302 65
    0x8079500080032401c441d04030000182420110700c01c10b503010300c80c0301850b0f8100d040c01e60643c90281d5058030900041900d2902442940380454140d0b114083c03100c00740d0390f1003d64543c0a1038001c1c1d00a050b40c204840a68200d1f251800c82c450390f0415020841c00c0d40d405070b5940ea0080b03c001d1104000c0d5021004084032400d071600035400940c07840c0b01850045440c0b1202140c12418020400190380d6405e80603c404000d9061100700940c008640e03413540c9038045400f415656890805071803c195510f00307903451010000802c8103c000c0c0068140917648640401c1003071340c40d40301d0568004a821504000840d500001244070246040304100000c076840c81101c2c90040030b8000300ba245149002d04840c1e100b008070503c104061010300054641e5040290040715900300041682d00310b0340c0c2c1d4005018154008000da9480e4030980754a61520703008045041003101c4035039040d036641061440f0b000340c071340003540329031003030703100780246030480d480103001d43e5031168003400b41c10080d804003841c441a0799 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 300193606 1250 300192356 300192383
    0x70b0306011709010f0f020315040e03040e13030f110a06020c0102070c09090209070507110d0623010303110c030c10031404110103050601050309030a0f0e0301020409021b0721 77
    0x219003940c5039114001d07150011070022950b171103800554800f5588116103500600c10804070100d1180351250a0b28102c40c00b040e40060359001904511403900301c00654000d02c000c10028200155003103440f203101c2d5840b0100060328000444160300d009852944030b8100024800120712180c002d400f894501000040c40c18000b40d480c90407104450303002e500119202e40800055207000881c96910035a2420058540f83c0d447d0b8487c5820300c08070341c10743e1041031225001014084550320008000c00000300c45038005d04104680001c460003484101c00003880700038010703048400480c500301e24680240060454198442c100300f008400c40e00e90300c1c00c1654903e044401031410b82d880310300071405540044c048920000004003035800080486050200800900451110000858940300c0c42071600c0000000c00c13403c1145c09000b040019589503002290100d80243d02e607000746140051558040d00456000c1c1c41c0644a00d00f03441003040882004501d411214410002119003504c20300c0d00d0611350 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 300194856 1250 300193606 300193637
    0x80f0411130f06080c0103060f060c050c0603072c063103080a11011a041a102f15070c0606381801020a140105040510020c070b030601 59
    0x12403212003000e4910f0b845280400040303038188500355441d00c003841c0502185003016505840c40f12070384900010480d0310070341102441828052000008001803030a5179a05140790000c00040c02e082d01c2d00c0300303c22144a00300b5800411580321101403030282a00d81000340c070141c034405200e050b6000034a421f15040003000f140d039500511201440c82519100d8a510102c03900800e40d0380c803068402030b01d0380351000d4429807070700207881014441002c45011036214103c1c11008a002c85290440da0411501050304c4081a08024004c208080f44440d10004410004008601600481700c0241e281c101801d020b00c0c103402e801c16540e1041903400e1044042e246591038030111900c640c4180c0d0002212803684882e00302104448000c51103024812007c0c200482940c80588030301511001049003d040719041d0764020701c40d00f200b2a40000c4000002c0d0501200c0034003916088600721094000c078500f00920120034400d0710034090a5800a0038002e013890242507150303001401c07550500c8101040c85e20310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 300196106 1250 300194856 300194861
    0x30609120c100e03121005010c12031b0e0f0402070b060103090c0e040303090311030304030f0509040b0d0506090106080d020c01200604030e0301060b04030b0609040c080304170607080f041113 84
    0x19880c00400441c1e4400d0100b20216144e0809016102c0ea06010306040010349e1b88001141040c54200d440741b0000c1e20803030801d0b001401c002000e620681c01d03491100c814070303400900d0010008e4091b61000305c1502c1d1031040108038410348100600ca209006c0210340294440d90144901e82d01c01c60200c8aa00c0d00c0301c040030704000c1c003101d0072070001e51960905000c0503030100055170100100070003542142007964015020561000b2514104040031549504650752600030031004c4502510000380502242019038603850102c8003001c0039030800e1340c001402c1d07800040c18900840b40c0d9028001c00d0520000440c4c045014a4142d0203421302c07191800c00701701080c40150b004612a464040308048000103240c2940ca16500c01c845847c1c5c207100810100342513003903055002c0c104031441c82d00e603912880c1860f0740e00580d0f0410b4103a8400418041100c00310340c1000e16005000d072040303c1d000d5482440c11103410008445440c1040d40c7e082c00700300001d80b41503280358601001800340b01c1840f030007c00f0204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 300197356 1250 300196106 300196121
    0x3101a07020307060305011422090f0c0f030201080f09100e030703180602300c07030308010519030204021e03070314010e070203031f050411030106030b030609120c10 73
    0x1860400040020451404200c244010070f070900342030150350b00d410b0a0440b40ca003107500e100d000c0c180351401417070030171888458040341146210042180584d1420a00140302c90384204a41d0304113103910210340e0125202c2c48508680c5e0584d1480c00d02d588002d0310b0150f0a80c0079081d04132034800c40c0444210241a80560042156130f8070040d41c84102c0d0f414018110840b00088600001303180c0d1061004ca68041010f11030080c08a1003441c0c5101060700419548078441e03408003264001254100d011180445c11004603802990780c44c01d1030f6224402c00058000750b00b160304540c41031620401c01420300d40c007e4002d074000000a900c500300d080b1140c400d264421121100065510b001c4c030842c07084150142405041069100061480e05000c082d54034400a040c1c10380440300c0d01380160800e001954030002412003d0b206121001c0750150114a5801c01c2c050301c1c0200703082ca000700303060b070800040702482442d03035000400490402182c50a01980405e00001c91070140031071380c6c0a401c095009400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 300198606 1250 300197356 300197399
    0xd091203090501181515031e031403060f04110d0501170706050702030304030b100807031b21060507090e09030705010b010c120e06040e07030c090902040605030c0310 73
    0x50410380c41c542103003162035850031500d45075030702c0000b10b01143d680007641d1480c0340f030036200181b01d6001d02c1c800520702000d6400203068581050722945a5080d28030900301c01446a219010503a061700d0380c450244c04105c07a00e6801084880401d0324600d09500210090080c030f055076403500e0b020040c06c0c82a030300244c20040480303025003601060028100035000c01003101d45409030030034807940c1c0000c1e160720031488003901c00c0300f00e071010a0318045000d42c680001c03d0a0421580003c1d600d02d4504e25014407149000b20380712141c84005090075460085000c00125a801c1e4040c10005a440c80010030010304480104580400085030f901400c00525000b500c585c3c004640b90480343c03074a1429118000c8c481410005249841400a48002580b14000080781000b40388880d80c0008075005000f41d40c0b0800031013030070700e0038003035082c0d01544541d8007030302c0175699400e41c191504240d4083e4401c82c841e000000d10208000303950048004003031364120707468106490761907565544070b42c01c2a00820504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 300199856 1250 300198606 300198611
    0x132041205150604110409020c01020405030607030e010b011b0b07020c12010501050a05040b060a0302030421170a020a12050c040824011e090203070e0307181a0a0302060d091203 78
    0x1402d100d5441a105030340080c044a0502c40c8486000d5030f50b6085c01103114070090942c000c240d180c803180c001e4043d034001e4900901244c5851030035640040c06072050b1010514194641319000025510070860900303492a80282202c0d0310320785540d03001c610b160050010045014450140c41155940020003032100046800407845505286c00c203c0700b0380307880d071250b4400c80c078000030440c540e20f401c0c090328000e03009810016140d03a15401d203032503402c580100303a02208040c0d806031041300760406410b503c180d08212042c0f480d50340b0004c040381284100e000003004141e62400695030090143c03c102d0f40a016a0985828a561070800790300d0720000304208641050f070703650070150201c11840400c0c01094076a48203ea840d00102d036540c5825024014020780c240c0000018241600a5640100484004c0c00711081d10759203e84100380e925607508402c4200307007000021540d000c0704105450000f24010700c103080040c61070f0300f04003141d4010307020305403580e032501022004a049036411180d80805500d01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 300201106 1250 300199856 300199873
    0x51e0316080106060912050718150905040b07020f06060d0f02060a020607110a020f1c021e01021603020f0108070c1703041703040b040314070606091a0132041205 71
    0x38207054000c0c0c0051b9280c00031380007544041071000803900c04503040c0090061400000721450000345c050f0404000380b03100420400255240c055000790b100d80d01035441c2403602e468000d0304a031201c459801d41e611a03440340b00400c400303143c0036917202c030b0302407080c1e1020808480340d50203d122034100d2480e40c80942c22220030840c0c000e40200041c02044103687c06801d09103040e0380014510765078041d500e07001703111482d006800c4c2c040c4940032a00d0326800400e61042c041d03800e0887d06455040c802c0041c014080c0785079542e00e400000e0042d000b40ea070700070700180c41c5906100046811002c000c0c030540030402e030824640042103ca00b45201d860394500381103030360303480d040c1041038400925850081c5c01280800804c000f0801506400d6005035161030f0140803103c4486c44001c0c140640503001c0e18191030f01c0710004891800c0e0307220a4040308000b0081003020440c0006440040c10220801c04400340d202500b21250802901c919100c0c51044040d4101600c8062819042c0c03e410070448095000862 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 300202356 1250 300201106 300201119
    0x602010b03030721050c100f0f09080306060a17040b06030d050a0807300b09010b0f1c061703090109080601050a17030403020d1b060306051e0316080106 67
    0x590111904207030300031840c2000c0d0741d80b100c00400a410310340300d070314039243c920094161245044035a03509041c3e08448140079810129002029890701414515140c107003880d240d5911406500f2801e0303000340320142596655001c1c0304866011a1900341001071800030742030b031843c601e00864011800360b400c40d5140d00c2c1c61020316280c240c0701035000050000a014000100d035020407515407045851525000c0102c0070080802d02d03c09855584800c1c08164061314100b003480d61003103e41d0b05085401e40ea00b80d03602d108a1a00d84903100101c004400b08201c0580c140245070780d1240c08031480d01c00003400c10360320210401400c0f0031045804c406c0d080001d1901c0c0325a40f00820801500c0701c8000345c0502c1d45440300003100403c2510800d86000d5000c4203540d4192001d2060f14015a005011110f480c80c0900e031013011602442490070641e80c46020100342c582c4030348580e009580000d08140310001000004403041f40c10942d41641c10302c41d0020580954130b40c065882c004080000001c6140360908a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 300203606 1250 300202356 300202361
    0x12030a080f0408030402010c03020c0603150310060b03060d15090f03020c011e0c03140a021c050306060d0207240b041d0a060905031e0405151204080a020307061104060201 75
    0x100300c0e070407184000041c000419449011241c00660900709030740c90500a01d0281e041000c0820900da00280120400082160403418008001c00403420348401040201030801151070364090710746508020700004085007801945255014001c0410b0505614041c00341c4003926803000c01102c2c221000c040402c00c0540400219a61140074203000c60000581040108440f0f00300c000c0a042090720041041030501550a543c100204800100d580e110f8281019542c0d40100010701a04c5044030b0703200c008a403060080e00d020300d10041c12503240c8100101c840019411030081600c207440900c0444116240102d40503401c0c2d0143d8501143c644c4c3c60104010450300c06244a51240d0701d00e002000090b9008a011140154000c000050200070390910f02d155000300c1c00307103081d1503001c00c19040101e1034142c01b910850314211401804070090100401c11030042e05403003040d12403540089000110010041d2066090340e00c1100d041041c981c031260305841c000300700d901003000002028032046a0a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 300204856 1250 300203606 300203611
    0x30711090f0601050a050c0601080f0d08160e0406080312060103050a2003040c030c24030c0e01120f020403030804150507020a08130b03010306051609060f0c020a0512030a08 76
    0x4403550982450310001d59036030000014449410000d00081810f6400c3c0520141d5500c000401c0450745150303140e4120340e41d0744004e00780302032051103849a840c502a11a50b44180305950140b020303040d41080c441d00f581c1c00442018043e0303000340c85100210340d606081001c0c0010074028140c4502c0c90510000140c1140c0c0082e003a54040d82c1020105201c881c1318490007440841a507600d1552991a410001c0c1d44e180c40d81c2000340039100100d000a052a9200b1443d034a83c504850021000c00ca602c0c0c0c01d0301203072041b5a81c800861150078030001c8560040c40004403030703003c490380801d040b202c000948080b03a015800490100b080c260900043c0007041360b00c17483c50440309200704007500345190007950302e8480780402001000006102d5104210032201c042c01441c004c03031455200d5841e460000040c040c1129911000100b805564405078030401c0d200007101c03815203848440c0460814221074002d00ca0005a82081c501d840000305074030341c08a8a10f50078030b504091915814110710040503000003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 300206106 1250 300204856 300204859
    0xc09040b18190f06020f030c070506100509010501050306010909020d2c1905030c010501030609120305010302060901120b0907030c08010f0501050d020903010e010504050304150c0b0a0518030705030711 88
    0x566110000141c2c0003003040d42d941040c40424280380e01e02d0080003900c65061112151078003c01482105408480039214092140041e0b0b80343d075a91005c9034005032000c0c4200e070761151100c0d00400555010f42c00130754000c1010714115441c0d50315a01c1030010381c4d2099581e110305540d00c40b400c49000c3c5046000c40b804d14800030000300700c0308808a505940d00303c1f80d00b600b506451026285820080100110f861440824009001640c1d41c0c0c20012300802901405503881e0980c9c0540e074034294401d2040305e068980c014403050403d084d802c0112004560050310480d45a40d43ca80300006541d1210600c0c81000140c0d0040380f1108081d03070080c5070147c10707071000485400a100600c196170b00074044d251420703095000140c135034a5000001c0c0c05495003c00380c0500d5440c000900052080c044028030a41d82070051581744147e001c03d0445403000400e101801d512003010100c6c0344160f040c0c0140390862003c20003008003200f805504d60071640031880c1110301350b0001802c0000c0008504120700c003000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 300207356 1250 300206106 300206113
    0x31103090d052d060610090305011e060e060d1e061a04060b030108060105040f020d021b0c03030c15040c0503031b191208071202070b180109020d03110c09040b18 71
    0x400c980a03035500d0301030711700f900c1070302070f42c040324101842002402c00941d0408000c0c044070200d03c1d18000442e070000d0600803070310304046001ca0310024140c3d400c5d0254501910200300344455403100f5030701070010491030504079a414440340104401c1e00880080014a00c42502c1800c14030040008507000c1f503002c05070100303045c401003112690200c0c1c0380b8111030f07007903c02080c00001a54054000e1065180c110f860501c04030318286401100340b4050003c44e4000c00305c44102949004155803030248040903d003603070021080c00102d14040007200e4000f80308098921006d41c407000003c2c11600030042075000e42d48a10000000402c00b04003510591003200c21040802e501629602c8079050000415014040801c0c007181e0204e10401c6056800400c3c41001c40d1542c030746142a02c2e030a0020f4500d83d081ca040506881602d19041c0304248000b41d00400000038000740f56401d941c80c002217421003895000707814829106444a000b62485180b1400740d00542d8503040c200a000049103a1040000d0350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 300208606 1250 300207356 300207433
    0x5070b1b0711100c0f0308060102120a08060a05040605030307060f0f02030403170a05010614031f170c0402030705091c0203030a0305061c03050406110109020301140f01060516031103090d05 83
    0x45c05039000710803060701850310780c040380e942c0c100503850180d94400f100b00b424400100103403401d81c41464640117850484200c0f2520707070f40e00b08200942d1454080c0d69411340081248500048507607124400e40340304410081144030b07040c408881241c01c01c590130340c0403550901d03c607418450311560703490b4000e0a80004018035410701000601c0892003403010140400004041070b19543c0500500b007440e003a80c015843d05035183c80d00610030000c0a030601859202e0003400c00c030716103051300039240300b0b64280d42c506e401e0036481010003c2c000c480c07480030320b00c4283e40c001910143c2c60500040c9509840c0d0b4402003031900300902408100350310205084d0040400401110009074041c2c200d5046a201d0b20f0001500000821b14900501102400030b42c10b61030803440c00e11007100500400c0c4104640180282c450f07907110800e0b103180c030840d40031100d502441107113140002e0140c250450000c11000c11241407202800c041041c0d00e607185400d0302c0d994844032901a6040012444040c111010f081c03114030349 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 300209856 1250 300208606 300208613
    0x2090c040303020307230109230c130b012c09011401120f060810060602070608010f0303141b0709050c0c15041a04201005070b1b0711100c 61
    0x280180385005041180406c0b01070000c1d084200044503e0030050000c0100072900e1405541c058220307100c18000e03881545007a1031000c80450070111940025009a031040d10f000204c000a1020701c040368144504111034001d070541c20441118107800c1030141d50030302903c5c1d50810844860582c0103c08881000f41c0041d5581d900000651910032080301c0440c800810790054006003100e5000031700d0a100300c04090031a070a5030f4001c50101e804079000e80e900ca80c2c03684000c8410310803d004142007035030212001c000182c40340c1e21084003540c4118042d818003100c0c0780c50041d882101c440e041e44076802120184402a407030300c5141d405c40e00b6a031701d81c3c1c40c1018102c5082c4d1120140309590340c41e0004100000c05100680070540402803160900b409945050f01d0a00c14000105c01405510111001b01c0c501c9414500170811902600b501c502d400c01c0b18995070707000c0c95030700280b140da401054001c0d0b1002d241c401c4001303064a01d01c02d64140300d20343d91010a020b01003c02c160880100451045501d011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 300211106 1250 300209856 300209863
    0x302010b0f060a35040c080105040b010b0a140f0a0e0118120f02030a03080a060b0418021605031308060604060e0103030f0e1c0209060411030a090f0204060303030902090c04030302 79
    0x10816814200c000c500c4020043c81c802903050798451520031480010742651444d84801032045209882d1008415102c1c00801d08941c01201c0040c1604003a40041c07180d0208540a011190f99a15044850004440d2140e01c6a04031711b042c000030080c007040000c00d071070b00b00c4c100d58181c03071081c81c24020015001c100302c104a00c0324440d43c0c0d1411185ea0000080c052451108001b13180c001d000c0710146106890010101141210950f154514208011401c103000004070340c1102c40f4031070401e00d810f6a00d48454000d41c4a0020303080c9000040210710700151051026004c0755400c041801040c526140d401818100e0092255220b00e203098010300c045540c10b407030141969003500e0a00880d81e8220000d541c2c0d81c0ca00180664020310390280d0062100b1108041c000152007900d210780940c4800d820300081c1d07495150307c014030381d01c14030000382a1b0003181d00008032a4011942d48096180607000724088034400c3c1c00c280c00080c4c07038601110950600f2214242c11020980300145480d2950328020744 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 300212356 1250 300211106 300211117
    0x1e030303071803080f0c0d030e060c211008010f0213030605061503010906260705190512010203090c0a060509040f060302030615100525050109050f0a0302010b0f06 72
    0x1400a44040400d001a4101810b00510f07444000d80e80c3e2000000c84500340c42e0801c0440c412148039607108503084a02c207000d03c000c400354400003410703141ca941c0b18142c4260840301c0003040710884680d400d1a00c0c1071908500c1d0141d41a07410b864807040c01c0691071070943e4a0301d140361140600400c0495488603d00c3c91503011240c0002001501d51103c2d400118035a18078140c000400b10301000100d500307480c80d0311003030840b0309107091a018440341da9100d081d1049050450001030b00300400811581c02c044d00d4503402c500300303a48080c1003261903400046030074414071555040c0ea940172003040703d902c000f0488287c0b2100b045030041140c510341040200075200301c40d65180113a403614002c1032808125005100690340c0141550700900d42040039055060440c0d5501348030b041000c00c0740840c240500b0840e14078940d900710f140c048005414a03400c441c881c0340c0084072290b50340c1200e81c01103901442240b0003aa50403024001e02643c0b410003e0a642414440300c0c030076026182e081e1203655984003202c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 300213606 1250 300212356 300212371
    0x51005240304141b03010b15070f1104020a0c050d05130303230403120306050910091a06160c050108070503072d030903200607110304050a0605091e030303 68
    0xc0d5296120310f80303003800c0c2c01d007107503004264482c4c2c0b00c50f5070301081d400c0b0082e51000d4043c1c2c020002020010b041000400d0a580540c1040408109030700100c0c56241c42046807901500d05400301c80c440e40080b408030b07488003101200186c210100002080414070100307081c610039282c075905000e21400315540c0000603100003014045040125080304011074404410f40c4000b0b00c085032110b0b43c4c2d04001c5110344000c0e80c6000024500000801c80e403034030740290760080400007110b101d16814030340d20078014401e04c003024000e855030007030000341d643e101e10080c00c2000621442c50407100c1d803450030040c10340c1e06400c0f080c1807281e004100201d0b0750b80542642d80c01402480c1c10324542944d60392569103200c2d44101c030354000000c4210501d602c0d0f0960400b55205109507206401c0d07103500e6041e040b0422020001141a0300302c41c0208040503c42d00015069005241c240c034541a0388800055040302300c1da0088010800102d414480c0f89040c549030000444125150440d403101e80c00000e03100d1200410300c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 300214856 1250 300213606 300213679
    0x30b0c090f0d1109071b03090e060d031202070206090405151302070f170c010e28120c150e010603021008100302190e1008010e030a050304290a051005 66
    0x5c1c940e01e20030851411000f0442820342c00c081d845090051002e000d9024411248982c103001c5112801c014803011860390309652281c1d100c0601070343c550040e5000310343c00e0b03a00c96414807800329903540d544030741e50041003603024084500303003d0000e00c2000d5048d40e48105649106000c06408a000c818207001990341c0803000502c4151147d2100026000742c00c1a49510340c6883e19002114000203201c00b120f4450850030042940b4208403050079040d100780080c1100480300021030400c0c080c401012015120b2403201c3c0800061840703150480d16030b005854040da44800080044d0b0814502c6054016500e00e072902403072a009180703142e20442071000034000d404030811020b0611001030a54041c003152a403940c00b81c01c080d200800c06030124050383c9410f51908030040340009000040b135041c0f4156071602411076480751210150205480c00800404408031016084011001901c40c0301b0240a00005103508142100d0030212200c0d0b000300d0701411440b91a072000c442c101007030002750340b0407a411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 300216106 1250 300214856 300214861
    0x80408090a090e06010905060a0302060d0e030c190b0a09120806031f141006140706060504020409050a0608010e0307140717030a0f171609030b0c090f0d1109 69
    0x1207803800166034445000b042c07078224080c4800c040411880e04a03a1501402d001e02d860b22010441d00c1310701072000a5108030200300d0020302e03003201e03000010b5410000040e64104042c82c4402e500303102c6041700b003400740c1140c0c00014042000d1508078940007040c582042040c400180d41c0d114180640c8a00401171140a800050440d0340401a03030850401803031803003c101d058020400090003410f400c0a454114002c0040d460f804043c000c0e008482c0c4550b0b5060701844803810701c0c1c0050380924810380b03126440d8400402e460b22540000c0c002001714020001c0c00c2d16141080c401195459048a072182c1d04080c40301c24051000802e0b40c070065003100103143d00c0c610000c9030a141010685c0607004000c04015480c010640c0031026210382c00450300e44041c8003022250485001e0a4400314800f0000c45c100400c0c03110300b012030660b17806006814100f00c07543e143c0d02e40041032941200c1610981d540011100050308040c0d4511400800a8888000c2c1c41780d00d0303442615031034400c040c40c2d0094070032400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 300217356 1250 300216106 300216109
    0x30f2b0912020f060c070807090c020601060c1a1006020f010c0509010e01050c0105010f0515030105032d06010b0414040203010b0306120307080c061617160e15070b060d0308040809 79
    0x6452001440284034556440c00c0c1d1650a0701c402e1140311f508410300441000107190364590055440140c1c03580d001d403409a0800b101580c040700074007401d0b640720f90b548100d0071500c40720542040c040c48038100d42c050640c5c54030300c00074601308409011400070f03418500d007200c100340c004060b514440c07000d0a0442c003503407403000100c03820f0150402040d840c5d070800c0c00000d2048000303883c0f4000e03940141c030f94405811051445031001c1c8820710030150140d01040b00b00014001c0c021030358006034400b100540f08041016082450031000703800881000e40005020000c08a0b0140c900310901d070203840660031503150600c0000c00d03000c02800d00c0e000d203203035070706032410894107000b11035000303500c0707800c41d612106001c214503a01c00303045034007540030f201140040c1c095600030103000704102c1f5032081186496841205003001c00c03018200130414000c0c000365840303140d138030751341035401b0403842c1c3e00340e035031a40107609100e2148400604002c2c0102450702c0b9100203c2c0e402000b1740d40c095001000c0300da0b101402c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 300218606 1250 300217356 300217369
    0x70e03070911070c030c0303020c06210438011211060901020f0703050a0c090209030606040f0605041107120f020a110a05041d0c030c03030d050402040b030f2b091202 73
    0x4001000c0760b0341420048100311010586d0800c0c2ca0180d400c8502d14000441803140501c92102e07507441c0041ca11003940114103070794400540c000e100b11540240504020f14121110307003800b4400440445401c54610103119800c4818010703d1038103038280007000c1c1c94070b9082900e840005807a0240d040050b51152990003007000805200b011000c0362a041da403400c000e07483c0c0f0b1018038126180b45001d0750010b419000d034001d6402074a0000d0260209440c0c00041000515420350304541058490800040e00c3da11841143c3c4401c0c1c807000350550f901b5403882c2840790f20120645a01c28840b100d42d00c1d913403003640056a903a40582c014100140485a5000a808101d4680c011a0b0141c202070300c40501451112040080c02d1301d91003101e503100005000c064544c1d09100009405501c14045200c4402c0c80b500910341060000c2c0002406454170408217051810109480701146d0000303030038142d2140c40e1100c68507025681e08600070419454800144001064491161540c5042003410309542d20380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 300219856 1250 300218606 300218617
    0x90e03090d0b070e041a0d0c05150a1407030206010e07090b18010e01030b03030307052109060f0106030b03150403020114040c05030d05070f0f050a05011112070e03070911 75
    0x9182403030307032040d0745002086903200312441400509040306400560610340648194110617290314109140b006040c4045030580d4141554404068013000070396480e40f40b81659101c5550010558400110368090f140041c100b180e240c403104204101004280e01180c16410340708481004001915885000c0340c9c803d20541241112a1000a40740c0c02c0e42c08090000e410a4420f80b242a420801800103404407800c00c013480d0340503001000000e080d40c2c03191004041036010160062101a402d00c3d0801d6005011180c0410316400041803020710011804200d004050300d190a000c55003a42020949551240103080c003032440301c801040800d4000c1d0005005005203100003062271030a4200040c0d024a50700c01e450280c050085c00303100862041c000c41e0920780c0c00c83c00e004500a40c9030341d44545240c1a540684041c0610f40f16540016400e018210380001483e008a440c0c4200420350034004202410a000b4800203800b142825100414000203c440200b000640c401c6a07005510351071042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 300221106 1250 300219856 300219859
    0xd080f01062712030e09090616050f030a0501031403030717070309051501050108150a1511100e010c0c02030604121808100501050405010b040e13020d1a1f090e0309 72
    0xb0b000200d02c05060403078480c00280290f49440e05145104103121160308183c4c0c451540b03421a10002d4000b100c1c20381c02d8040481a80703842842e041c11540341c0910ba80003640c0b02c0140c1d03600d480040061004581c020120303000369034042c51541c03c003070700c000e450b220b580d80e14003100c0d10101000600f824040e5018150305904101940c0741c9088021865072010024055a804107492801180c190341824084000410300030741442c1085050440c1d419000b50301000b10350410030407c0f0b1283c8076034001e0105c00f01c0c03102060404595420000300c15400e4034540c1c0660070410214503d2100980c5e0b0000700b050b00306810038940b028a2811180445002c00c011a8004003004044800501440c1c002101100d0190003c810041c40c0d07202e074200002c1d40c400307100d14801080700340710038482e2500303599107660421800c800581030b00340a540403592801031500c0035504d2072440c0da04100c00b2454a082180d001440c5008040c4611858a00d485444280c1c02103843c0e0030f598510f0403181c0c82080040b20007e040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 300222356 1250 300221106 300221177
    0x806010e0a03050105060102060a0501080a0807150c0816030203070e0d0606030507080c010801081914150411040f090803011412010f0504050d05040e0a0c21020301080d080f0106 78
    0x710b9091081c080d08055a8050040c4035500015031074041c94499a4165207a00002c0c084101003600c0c1d242c040e0308024403d80b9903014040c43d00e0035244252164038a19145600ea42c0e40a00e0881e020b1104c1000c0b040031842410300400402c0342c0590700c001105480f60046400840c0c001090511400805c02c903013005195100300040070450301000151080c0c084400d0740d070b655460382c0768803011fa100c0c0100d18082d480303404a2090344002809071303191401141301582c112004009404441070b403052050720103a900138040020004103040c9070080032440c0c8a0800c0900403d11250380c0c0754240d200c1407190340c10701106100c0758811550340c0c102c031600c0903800c60300a2000c1001100031340018041603604444a00c100d800d4144214060420348080f43c802081c45041ca81c0d80c90413000207007030600c400c0c00030000708000303070306000000e00090b0407101450751006840b5810502c2c0b00b460050134400da001404943d0040081c40104024018103480761864034460300703075034440941582800304046007440b44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 300223606 1250 300222356 300222359
    0x60f120305160605181f0e100c20011b1b2a051507030e0a03080a020703050c0f030a11030c15190c0201080a0e0c0d03051902010c02030301060806010e0a 67
    0x5010381089004420a031403103c00121400c8549030303943c03034064200074402e00b0140380301c2d00c4c40c0f02a400203440c000c05030150b441000541080350122803510080b040800c41541e08400c0cac042203a1407842c1c0024240b0002c00500e800702e410501e00c0041401c200c810803000c080303150391088401d000100402c2d13000040c09441c0406e4040c0030360500500c2038088800c0221480010145060100c80c4003020b007900d81d591605809440803200c14444015168228070b50b05000400242c8460050031510710641c003402e046400c500d00281024440030025204400b02d050f80c00341d544d804101c801c5090760007425402940003140110341802079407818142c3c0880441100b440200d0140014005600c3c1a504001c125070800d07001d60701c0200c1560040d0000d0003d500003448400141d02c12140207080d82c0c1283c842590000000f00c050100f507a01300d0004501040180c0c0d01d42c030101c201c0d400384040740000d02c6102000e001c001e541c2c1c0014400c3c101004102004101c0c1640507d2040340c1c40c54000d000d409116 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 300224856 1250 300223606 300223613
    0x1c1509032604261218150118060f060e0f01020f030d02071407270c05030402090406140c0405010908030f0a0f03020409090c030203160513020903030c03030703091401060f12030516 79
    0x980d0110789441c020541c1288000172a000801c110000305185104120300745d00f410800103004003060441191250758101c0441c01203c0590001c00802040d503c1301c042004490610880f0342504040b0360541d401242c4004013400080b065522420003484010380b982d1041c01c12440c1000ca2084e442c1d0207020b0003902086d0040000009103509094800411003081145026403c454451009400003641440820018a0410300003034209004040120702e414003401104d8000405841801591300000742c10405941c10064490003004440003660405128000d82e00c182d00c588410340b4100505081e00451260203641642e002d41001d4100300f21000491602c255080e2181c081a8881c2c4610210314040184001d41c4a094550242c40040240600c408143c0030b134101c001e016504d4001031080c65403c0800f040914800d40583c1c1d000315030b855103410101c0700d0071100400042141d051070030900144400306a81021904078126000702420141811144c500800c1044c022402c0d56100c00c000b070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 300226106 1250 300224856 300224887
    0x909030301060206090606010207030807030c02150912010605030a0602130e0c0a030b060a140a1214070306241b08030a140a0b0901051c150903260426 66
    0x10b840032502112003a4541480e610b0307803030701c003215203500503440394005000040400e005855a988a801d007040310030034903070001d680c511403802c200144a0b0042201240d42c5458002c883e030800d04080200111824600071035161116454068041600080c41100094043c4a030000804c80200d41605605100d2074094a41d4494010b900000303007003150b15201417903c8811074900603540d0b111205d60b5040807a07590156085035403840d007403041410502e8841201c0d80905200341d00d00d20724000b41e601d4031071805400ca420326000728407445e10514800790311201d010000c40c0b5034112400e11682c80b44822450140800b0b0600d0000c203610004002e000580c4026044400360807403030b07a11000c0c107039944040601260403880317085500c10302c1d440c0104181e0510850030501229407030101c0448801984030348044d491800c2d451740e5407580c0c07000c03403a06240e846884115001a0700c0b442e00116050742425101c005005000580310803e003000b00804440d1104e041d038120095010459282c0c0401301e410741031b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 300227356 1250 300226106 300226109
    0x60409051905010213091a01080403030b031902090c040b03040b06061b300d0b030a02060a090f0f0e040204020d090510060e090601060203030c16050a111c020a05060a0e0909030301 79
    0x17018410034401090a81309405114840c0052507044440e0380410b03001150f80d0000603205070103155642500b0351864400b1711000c00d003960880c008409007121407042c000c004400515507400344900340f100b07000c03450416003141c2c0c101c0d80005422189840b4007000038814490302e00f690b1000110080407280a850101d80e038030920070002d01640c000d540b4a901c070001c0c442d2104088895500402200783c60040c5079200d0603001c0300103411128045c100341d010485950001ca861004607010741804c00c0710900f410420030182c80b803401810b840d2450079a0411207040041c0c0b00900c107a030041013028403049280c1c030045c65030341c1103012100b124810780c00e50340007441140101500c0d030361210002010fa007400515107040300c41950082d0724680d11203c2d82c0c0c5a90700a010b0010380e501d8556aa58007040c8204a1078a005004030700c486030b105030042c01c001c1c000c11072025040f03134004409035000150342e41d000c0f0f50701100c0003030b07603807a0b070707644440500325250310030500c42540c4003200707a0502c40c0303246000000d5030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 300228606 1250 300227356 300227377
    0x1306150914040504050309120a1208010e09010902030309060705030d050a061404151202060708040905060a050d030e1507080301120528110604081906060501170604090519050102 78
    0x8074a1040d110030700069850803a40500303c2d03801040b1407039030b900345032894000d00d8200d13409031010403c066803208580329915152800007001000180134000749031001c2030304005240001c11040c02c1c2075010949034004c04803010310035500418010180a010b104840040011040400051a02102680007009203000d503030007020552184480c2800d040c0f2035601d00100801e1551400c51500c950304c1048551944203d800c9036051100000040720200900098a5101c5007c2060b14080b410703c90721101c10340c0402c0c810380301030703080a0220b80c220101483c41ca005552001c80d561040e51085400c1c41140c0700105040c40010001440310014040404414402c9003139943c0a40206043c0b83c07000242c0607417004005a03400c0403800920b16030340c0301d030404c840500f4041c1000d40d02d00c100b03810405511000460842e41404090800c0300500c11400a0503090078040c01400155000326038006008003e54015550f031409801800000c0000248803071a00e40140840c04541c50550302075041605c0030b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 300229856 1250 300228606 300228629
    0x16050307052b2403062706050105010311121801150311090a02030103020603150414070c02030c03210f0f0a09060806040c0804030c1b080a03081e040213061509 70
    0x949202a9440d00c1d20b00320700f078a810004015007941c44110050405101004014910406c80d04420780c48030b00c584006405885d00160541c5042c0026040c0c851040100b4a28241046103800e0070002e00340e00c5030889410180398406100751041c103130040021612013034200d00c082030000b00704101078000c154007800c19200c4142c1900d60b1001c2400360300007808020f44c4600103000080004405a40c4e00d508444010008103650140742c18004031494162076540c0021284601030042d400c0c10481c1080c06141035001301010002c00d0342c0c0301c0c9603500c51a290100304500140300b40200c01c08006942030b105546032159074031007a54074040c2042c1c195100314008200e03030000048007450280f0030403114451940300d8a68684d01c40d0303002c4900035040c06c0300311516820711244104014402d0f1300c41024007130500091008441c50304003d4541c2c4002000030b404103030020344c000c00c500d0381d9040d103941150741603403143c003012074040030100a850300d03802004149480e442d020f8401640144508125003452426 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 300231106 1250 300229856 300229871
    0x40b0f030727091a0102070302060f25020306092d07090c0e09011706010603090201180611120301051c08040b0307050721020c010e21011b0816050307052b 68
    0x10104c0800c201c000340580c01100d010030260070404001c02807080d900111307900d0310b150b4025003a00340614040051890030000310345000c5050800c00c09801c00f54400c01420107084442450359821018032200300d00b000c0e251031260802a0412040300a401e0b10b0ba024001e100c000c14009200344c5031600c4092188812500004a226590383c15642090004015040680c01c100301940604841c99041b4100407041c00300407100c8542c3c05804001c0c0041c1c0d61004488000da02c51140b9109140d921280c440708100010402561441013003c0641c4904088020345020340c00e10201d40d01565100140c40480001002800c1c0d600c0f8001300015842403241540d120300280380503490000c100042c00150307012126070015503000e140c2a84214070000c01500d11800c0364901000444040074100720113a4560b81c04001e0a00380040c40c088051491808040f40e103482d142000c10300c050590300c3d10602c00000045081070788914200c03803544103100004d160142c0001e50903510891000c60702c3c40340510b030091 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 300232356 1250 300231106 300231131
    0x103060608070c031d12060714040f0e06120303040317070908030d0e0c030d0903060e010b031b06090d1b0e1303050f0403020409030810050105040b0f03072709 70
    0x6403180100065911480000204e95080d50284040f50000c0d001310440380648610399207400e0410020882c2d075001c0c0c40141400580030b0180007114140c00200c030400c1c4424010a0b01213441300c1c01f11a20003441207929200d100104010110300d44103080d40e8080001000306260700a04d10300c40d0404000b540100540d220f050883d904a01c6005044094000304001c964095013a084644660002405d89004154100c00685041d6200c24000c001c01c030740550410522036a441840340d01940e4400030302081c900b07000080c2d15103030000841180f030344000b010540c0c01e403070f1032080c0c072203040c000341070080421428180b610030b218020203000c6000c0c0c619074010500c02c0e10002d0881c090305505a0051024160355002e40e00780c0c00090140c0b90781d100611000015070740b0f502130030314804d000b500e803140a410480001d52000c0c800c3d0300901d0510104100820203000700a00b110304078001d43c0aa2038482c0c45051086030841652700d0100c03e14401c8004a065603018002520112401604100f0000051030b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 300233606 1250 300232356 300232367
    0xc0312060102010b060d0506131d010f02090117180a06020301051e010f05160507091d03070305090405040f022e03050c03060105031f030c060912171b1005040201030606 74
    0x4c0340d039401450602501001d050300f90030aa400444c001d1103001034a2910030031404071660f090184482250440001850324000e20a07880211081e94095117410440d00010302844070300342d508000681d07800c0c00215645800601141159855415500350050604008001c1d400a006240c8695910b09440e800c0807102d1013014032100c81a1562550840320b41000d6405804c0903000c10111841d10440d000000c0e014130480e0050200400009038480100c00c141c0d030007201c201c1c07800c0400c0d40200228000710345c10106540c02104116000f10320f5554520700308800382c0e80c0641c000d4004000003600401400d141241c41e21811f000c000341002036140301030071802d0f20700950300c4000303405003000407820f554802c000a650080414502c6007100311403941103d10703900c45a0041d1070500800c1c1080c0f00303d56100d041440100070395200d51b482104551901000702083d0003e80f54a0305c0002842d064020b0105141d00d0401c4424082d034075194108030306100640010bc40803400071745000b4001c5895030150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 300234856 1250 300233606 300233621
    0x32229060f0f01030e0304030c0617040b0a020901030f0207060501030215070213090206041a0d050a1b03150f0b0415050f0307030504170301080d0f0906020d030f110c031206010201 79
    0x14451408005001d062003040e12803424050b040649901c10300b64150410001040103510416050041d2860020010481c01d1442c055070768804a90701800b011402c8031130340a401943c8103400595170103c0368010b030010003581403041c031028008987c040500c5a242c3c403650480e8025034a2403200b03929081092400e00c00d1580081d0310510003c0c40111400346640003940305440901042e103004d8480100500071200c65181c0b1149120001d0002c0500030719024040d0090b0307220f00d041c020181e41004100700f00c2410040b480c01c0607902d003146061100b00300c12050082c0080c414140303400b81c54082103410342e4024061aa1540c0500382c0c80b000c0d842c8514101c0305503080c0c0c01101070450700d07466006c40240c82d002d002a2540d0100c4a9800c43c0007154800550081c02ca1000030326240d030304980003030040c000c0380f401507081c0113004200700070b0980c01081c0e0341c0311090240750009803210360070303070410043c00075001d141d12828020814600f91000000202001941004130441c03554404c001207082e540c09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 300236106 1250 300234856 300234859
    0x30f1e0f0c020d0204060825030c03020f0a030b0a060617070206061c02060f07051b0a050103090c080a0609031103160f0203010e060406050a0c0e0306040803222906 72
    0x40020301940910800e10511942c1c801464081044800e800181c2980c030a5000007082d40c11001195407248548010041d18508540030143c20700c0c590f858081446001e48400ba01600c3c80000b40d094a5131422504c0020b181e00c10440040da04041c40c43c8001401c19015040c0482c2039100139424042e80b5030591442040c2c1c0798002c0c482c5035100001e0115248504520440489036424014010303a030f24001b400351040390741034135a00c0d0005810001c3ca040200085600c040c5510864108a0b0b11403814041c10f5810a090105081049103171462801c0b040713500c0714596004260b1250708200007500b1140c100d50081c0e40300300c5d401016025481d100e1050b120031106030540c81c4210400540c0d8103180c01851800100002008034440101e6400c0c804110780484645a0b81d00c01c0104040803031003049145001071a09904a00c185008207a4034003028002609424022000441000031951903000c05910380c8110024844285007403c650300c41c00d40d280c0081c1ca00f884c0c103000da02c00c80c1d050651107400f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 300237356 1250 300236106 300236117
    0x30106180213080d080402011b0308010b13031707061112040303110d0203041a15090f090705100507031403090319180b2a100e03090d030f1e 62
    0x300351854030000d500c101502a490850a440011001018051442000480d440b0366590b41303014400144401c521040c2c803e108030303845141c0d601095000c9001415900d001030b41c41d42d40d8120f224607500c400034a5100070100720084410300381c00a5001d015040d0b00e0320520f014040580c0c034040404242c082d82d021124018550000100403134402e801c8100001c0c00c81d0300051400c3d51000d00031059074000c80d4265050560300b0450000207540c02c4005a011041c0542d0060024082c03002400c42800941250061005900800c002d40d000340a10002814010a600419028040b018040b500040c00c2030700813a801082c40b00b280700c09031080b03071700c15110708002d11b20b08500d0444080ca00c41280b0004001c0140c1204546040d807100408080540494070001b42c4490429002041c50300c64801842c42071108110040f850741c20010b101c00349208250340106401c105500824a180a10500d0680c4801c83c605000c00b41504440c008050b4030056a1345411034a0001c0154110700f5101e81c46000140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 300238606 1250 300237356 300237389
    0x70b070e010c1a0411060f0d05040c08060f090705030d09090f1104060210060b093d0e011707080703020a020304030606090605091302091506070f030305090c030106 72
    0x184903209004528405041c02c80540b09107864024522101c290b000000003100e9040c0014003184510070b06040e641114258904115031b0b86207144d5005020380b8519150702d401c04a400c01c011480740c54080c1c09030340c08075805072030804c2414070303540026105000c480c0504a00407509003000705004030741121584400509500d0040c10800410405815503038407951601f0107a54254040001d01c0108103a50086c00c3c0345240c12044402c0303d0302948040c0124404001020f007503112151001001d4400c0d100780c5942081c20404c075440c1e101d1140820040c1a81da04038002d41c0c941148282003004001c0c1c1c4d45140742c42d2541c2c0003d543c01800e6551501007550780001440700c4e4800d03001080640c11070b10559040c03680d6540c1c0c0c0c10640750550000e40240d0740350407090082d420110000b0b603100c0066401a054040305401007200c0d01005086e410a00010014a910684a150031110714030f50050010000c2201c1b424001d0042c00140d454421600070420355503110b1805014080036a88070162151456 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 300239856 1250 300238606 300238621
    0x130e0a0203041a0606040e0942010e060d02011101090b0411030a0b0a0c030e0715020c0109060f081b0309060f0a020f04090c0c080309030c010c030e0307061d030406020c090a02070b 79
    0x216801030008200c0e219401910308427400c0254000341c888000610f0401e60404040c8082d44101000c0405000c030805400420415a403202d41c25004807040d550740d440401d0702e000403a901c1195006100284d8204103010041006082115105501403007244081c1e038010810543c446442070b2000e880c1c10310030000301c1c10400c001d0384011600c42ca203080019072001642e80c05c0d41051100e034043c1080c074034082001404540c05000d2010006424a1b19418003410400d029013003403807048440042010810000311045507215504500c1a08041043c2e2641f40050100d60b540d1421212041d001c2c640e140820705000d034038000d556012104500c5a410300341003440e10801080364110040800085d0928500814880002103000c5ca1140d0701031070780c414000c260385080d180c8014032a420189001c08010310400701109076080194880c0780407640002403014400441503451401500e404001800904180c00040309454400152013142055407a981448124020903c01500d0707440c00c0300c0080c0ca072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 300241106 1250 300239856 300239879
    0x2150a08041506050a0816050a03020303030414010f02040306091401200d060506070302070320310606030e06010e0c070b1b18090f0403050f130e0a0203041a060604 72
    0x60070071030000504a84c0ea00002505440c2d1a444102d40e50000700440a034620150702d005c1c090300041e2082c4500520390340c0840e540f8840100060065070703581c00c3c40c5003030300400c0d0040041041c5182c4195103a50312810314000405000380215800700819084403401c22040c016440c4440000100c160b01c1051030b10358401c50703480120220000f84d5206c030b011400341d852001801d1250b00a5001b4900b030780c03d40c03402d8156201ca182d04a070700e04280040c0e105490751810023002940c400014201030036488565803405407025203c0c105c4042d03080071004030b003155069000c0c1c40940d640700b080b034407541d90700c100810413003c0a8541c464840e1003000018041040000b00c5608a9038a411103159188000d44d180e40341d41102000d4084440d139815000881c2c5403980780c0b182c1001c00e0f88041d0405040940d0040e10301c1c0300c8c4284446504101003920703d0400503d9110305e000382a4404074200307074a40140c943c4d009600840d8101e82000364065100901010380c801d45105250140c4200c0c50300e810107602121 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 300242356 1250 300241106 300241133
    0x9010507020d180506030f06031e190201022e0b010305190903210504061b08010302010305090f0105090c04050c0f03072f0a03020c10091202010504030b011202150a0804 74
    0x41800782d010000896441740002103200d6880050361148906091080504101c594411a41d1080c0142124181e400d80440c00070201500d003060711818000d2880140d051460a58a4618400600e10422a0452210144207103003002000030804010444015001c4400c103a582c4480740c3c856001100410000d07234003031000380d030003400c1c9011a40c1000c1002c40803202e4505207608440c3d100d9061008101240c000c2c08680e2607240041d02c0d400c292110020504801484042e04254880f07011446100050001000101e40d500c000e10144c509690b01c0360361141c3c00340001c2e006901c1c0c85c0000d60300450110541d0140402c001c0814510745030510204c0b11041040b0000075000c1040c04a0500445020840e84184480f0350250411003000d05000c4d0400310728000a902454007010301100440d03000306800103560682c1e00c00e02140c442400101c80c00d004680004000c902c246c400814420114030055595501c21210741010520000c0050200d0182003c9480402c1071440400c0c000b0341007000010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 300243606 1250 300242356 300242387
    0x5070e030706140a0e06030a0c0f050913270809030c030706140309072409051f031e0606020f06102103140f13050303041229010303050c0609010507020d 67
    0xd4590f04643d00086d810360040d125004403075039490200e00203681000030f03041a000c1074244541056840701c08692046885d1864070036940d0380351000707209585078801d5441000100700700420305407a02c1c034002ca0a980842e00e0a0322921561401280b50724000400e4019600c00340e03116014102c900c1200300c85038001400316021405800c4000c22050480c1000141d8810301c40d400c2182c110b01c00c0e002a01000b81600403030f00511080c0144080c050303064001005841103440c0010746c0585c00c4120b41c0d030340c1c000c15042e0641c5a09041c00007030f11a60024102103400d280032700355041502c8403881050146131034442c3c02181c404c00301c0c1407080b01180c900388841030f50003401c1540d120796500d00c1c6040c00707500031104404000760105040e078480d40400010301c0501740680082d403400d42400c12006002014910042800e00b0500d96a4071050180c00a921143d03215090301d29296141d28018005802076481000203100b0100016185041401814055030030b13a00a000c01c0d940c00c0900710341c0300c151008a103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 300244856 1250 300243606 300243617
    0x203100612031d030a29010b04050d050307020d0f03020601090b0d29480715050103030201050a0c081b210c19090807140f10020105070e030706140a 65
    0xc003441d0702d0501001c43d0607441b840b41c101403400d41944900080382d10b2508030180841c180014045100500125019a2411959056950901c0c40c0251462042c010001c3d000000102d80000b000701036100b017816503202c1c5d0299003c60703032203092150840701100b02c5264000d00419000e800700e03415175040b07010030329005a4038032540c00c1da0280e1140544150740703c0004061220070449102e84d00707034960b00c400080c0002c1c4036140c12032700d55a04901100705c402d01c01c1e00707400192817010030131140d003403030f4100f20403100600040d0380d03a08019009040840e00460541e09024107684e1540c8500242d40c41541c91500a100110b04088642c14607041000c601003080301c0d940f03030500d20341d00282289215040d070320340542d80c4107020312014030f035800d095041005010201c1030030b2005400104040c4151a103c80d500c4c040c003150500092405003007405e40981000d10091440c45590b41900194454880303030712100340504a020506035244a144907642c0011449204d19440410b00c3c0b00510104140d890030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 300246106 1250 300244856 300244907
    0x1050d0606090518010501080f0703080d0e071d0f0603031207050f04030b180102190809070e04081206030c18061801060c0b010e070903080702030703060f0207020310061203 76
    0x11401102d1041e50b03407400011164440d4110f1940134006c1c3ca016108904c00b400040035030b02e005542e6880c0b6800014000000407400340004502a4461049540075004450310680d84000c0450f032071000701c0002c0410036111001803403c12082c0080f6000d07103c0500214034140c2003040c044c102c2032001c1c10740d1013000070802208200604580240014602840c08441b96003401c0c02c12907002808d000312481d1690050101e000c10851103003502403280c1081c1080809980d4903680c0e20709041c0260003210305001c2000500050054040c060985000c14441c040702586039a020955150203001001c0d501c94a4458080e4001c00c0c031b2082c440d00b1000107804950401e649911131881103000360030240002d0b074840c502d2405e00104812032401010f06000859140c01d0164004201700d0890002030b0124400160a604540b820070095000b941c03c80410807036607003a665811301035841407009901c0b074480d000340c003000e500702849210300312002c410400400c4c888559066400e002b032014040c0084a85103407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 300247356 1250 300246106 300246119
    0x52502011205270c090115090504140702100b0a05010c140d05071509030e0907052701120b03100b06040801113406050903091207030201081e01050d0606 67
    0x1409000e0100c21406076084062914046003e10a0420340b10300ca500409841005840e0300b030050f41500c03901030340341100e205008000d554200701ca503c001c1e0054a4048003000e401c039605007040c0106465429a01e184031202c140c0c00689040342c3c01260301a051240c1088158010405440c082e8400d0300400940110781d03910300e06001301ca940303c80c0450340010b196010400d07034214134904400c407e0410000405a5240244075945810b41d00c2d000c4c0c500040468211341c01081660b00300081c0420001c40c0c5140600c0d0301241072072040d046800700741c81d28007000704d00c0d0f03841c040e00840c120080c004210050324020098080e0001141d0b642d04600c1c10440401d10308820301807411411040c10f800d9545880b40c0b076078502003404001801520700250401c2d0400005061000c5d04802e40140d40440e254403113106103421441454111980080c00c00780c440e00e0361101040c0c44003102e000740c98898082e42c0b88038445651010305c80c0c602c05212440304c01440f941c6451800e0b540c403130740259000134a2540b40c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 300248606 1250 300247356 300247361
    0x140d060305101b08010b0a05030606120901060608060a0815041b0303030213150804030f050408070e0f0106141c060b03070c02130b0310020d110301030b010807060525020112 76
    0x9a4058562203140c03490f05003c9410314000c15030028603200800758034101c0301c2402c074050705036044200034000000c00c50f950f0380e031815036004a031000d16034460340c140181414001d004601c1010042a45040081d80fa80f52802070101120b42600140a580d401c22000314080c24000b442103c0401c581e014001400c0000d194200c00b42d0f2082c1c400507a1030088125800000c0190340c4040054844c191030300000350b6001c21900d81265050800c840303801e110140650307580c05142c00c64140c1c0d00c140f43c00000c00014000116015514405020a851340c80d034408950280c00c0c13a02c510417600f41000302100b440301b040c0200d460546120000a05291036000d442000d600903141d4400043d081c803003600940c85c00003905103040160070020003440a00741c3c0401c1e02d907407100702d2081c0c81d40e40c0030885550b950001d0700b11001c9155440a6030303a8135038680c134101180704800c0c01101c049118140c4081542c41c09031040340e00301c070010590000120f46c40c0403ca500c1820701d403c22410094524581003854640f070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 300249856 1250 300248606 300248623
    0x1a1812030712030609110703182301120204151215091e200d06080a03270f090f150b0c0c010804020906042a030504021c03140d060305 59
    0x400c801c2d1000c907200c5400400760745a5030040341610b494610038100c01c070020411104a00da060030010020203143c00c41001d4070302180c0c040d40e060825100e004210324203e140351010340100b40c0729240510701000c2d01008070300071401000c05240f468840c0d000c225016510b1002202d00104000c02c89503400150740c0040f03080c50313001c05401a00c4000040d000324522850f88418400306004000c12090046200382e1030400d50603c40d101600028400c0644640d43c21900c00307005600b044130351140280c90000c100d0010b01305202c154501c120b03010440550b0494100c000c0f40e420000c0c0242c4c05050880310300041c00c1001084911981c0e4583c101407541c82c0d860524000c209404006845038049481d80f8204a868441c2c40c0c10000c00c4010800182e65003054107030051000d6800080840800340401e100e624001900c001c0e181d004010701864a81c1a0003440c462807003035405a0351903150700c40036180c0e100f507840c2c0140880c51802521414400e02c03400740140003045080414016503a86840d030411850 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 300251106 1250 300249856 300249863
    0x503090606010804050a05370c050111101b0809070806010e060406152102040501140d06050604030b0a110a020d03090302070f091a030a020d1101030626071a18120307 73
    0x400c00c506628040d0701c23001d041050030b4840003a04842150341d8034800d0201c2d13009040c180205030038880440b03501008001078512a078501009210203111504088035800c02003c00021900000079508010100b980812070301d554004010036400d2424149058900411003030b00150b540400050f511010108001d0024446d140e02c1c41e000d00e544071030005006a90004128180100320410040e42d1001d505100d41c80400d0170300340c580a01d911003d000e070001d6403209a0101020401006118221700c8550140c5950242003068210513110b48500d4004c121111025030401c44042d001a40a600180d0206100c0e1040d503001589511207880307078201c01e8102c0484159109007c0c0d051600000809181c14400c5005144111840c1c0c0003a0b15101e403103000403c89009000130310300e10b90082d04100050654010701403031400480c96090240b06140b0a054410f105606000420103075400c9813070000454070f80414503006011210483d03c21081280305e42180d010404001d104070300b4001350131410712 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 300252356 1250 300251106 300251143
    0x1202010e041b02060a0506010c080304020d17040f0f0308040605070c1a0c010b030f120d2a02011a09010b0a0c0605040f05060907120308060105070c0b13060503090606010804050a05 79
    0x140c00600031300e0311000038100103041745803005204940c0c2e00a8003400d01994400300361a562368803440814000104040001c22003406036050503d00c0c8c9425000c0c00690b4200d170040b050b442d650ba00084a1000c45c2d220180a0340300811050213134501c100300611129000e00d2825802d5940c5c0e85108122800d104410701c60b00304081203000d1144420302910384100412002801d00c007a8140d4a291a05800044149818800184a0400304c0e142d00321504104401c0040c01d100b090240c00358030015030303100d2500010b51800600d100320490f029001e00507880d020b0410031181c0c0c00d0040d80c04180d4043c200314010b100b0f400c0d06040005016002d080d205034400c1e4000c2c2148a010314040c0c0c9040000b0b05100c0e400e40081009203ca0303484500d51454058240c41d201504e40c44e49001600c80b8031400e480503182d91140e0101140e8100303160001c182c4121010f1700c050a0707c0c0c1d9a00101c41e40c1c0026900000603400a40c0071410542c420001035800c80c0c040e0040e95045070346075803003610780081c0c191340c81107014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 300253606 1250 300252356 300252401
    0x40b150a0306091b0309020a12050307020a08011a0f04020d05010f030b100e0c1605031b0709020f090906010512010e06040b010804020105090d030e030d0305060405090a0506011202010e04 82
    0x603810b005900081c80300300c0090140003181d40001c3c010b00c092400e1071040582c2c800e10b807401e55442040ba403000744259182002c1160550601c1926540014010ba00941d0140c01c0040c1107601407040d009400c0200860044c80b0307141d441001211070f00079400507070107034003807240052a0299214440c002c20a15003036654140c9903251503100301000400d1404013061025040041d0115141400d80c040c0c40186900d655a000e040e174a616040103000140c000d2101181c25810a8400c002d0000300158080840c0c611503a6804a00240d2141c48881d10b1150780500c0111400c0c2441c203072150b04103c05050850602c4032403c0400f800c3c210903840b485d40e40701e5903010301007d41400e1150141c03010081c42c0c1450300e4501600064190720840c08464041c4019400c0c050525205203030302c00100c0740c0141910212a149500100907010680e000c80c865454000071808950001944142c0780354403202410040c0c1c6000144414900d02c0d0100f40c2c1440920b00c4400c1590703a50344182e5044542024a120703410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 300254856 1250 300253606 300253627
    0xc010b0109030c0314030d091202060f1302090912161202010207020a0b130504020c0304061e0206070f05041a0d0f09020f1315080601032604060509040b15 68
    0x58415100403410300805440078804118511080c0c015aa00001c8112001c4200c804151039807103620240650f0a103000c22880c01c0080340c01207000301540f560700f110340b10740394a145c10018079010744050400e554020055001802e100c400d0550086901007a6014080c41000004031503102240700080768070b250b20310f002003142e03603440f50003060400d01c000c40c140380030f0740d0102d03a111a090069031400702c004619032182010141002014100241040d5200d2032500a100ea49800900483c0080ba450a0b41012505031904154044e140303e5801405162138075442030f10600c1c00f07035100c1c50420004000c08203484d0100d42d0066500064950041c0d6a801000d031224204c480c40800b514141d81010115400b6030350b181841e03500b05000301d44c6158075240e8040c0c450010001c0e0300703034920680c0c601c91001480500228810b4101d80c001c18034000d420348091081c550501c00d071120f0798506601400240000b5104030080c0600340c2c40508001100c00f904000100b145003e41c0c1d07541000e82c0002a8803000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 300256106 1250 300254856 300254861
    0x604090c0801050102240601050c0a0203100f0b091605031b0c060f09031c0213030c0e18030708030a05130803040516061b111c0602040302010f080610080601180b0c01 73
    0x11804141250783e5040c06e52078003028030013000e412a81007240104c0c08103030841e42400501c0f030890380142210b00d14500800590082d120051030000c106180c020116241e040401c441e81c0f154900c3d99108400c2c50f1000019074268101916010800c4454115103007a00d482c20024529281120014038143c5001c100d401ca807400c0040c00d900040c3c000f07100030b5400314611126000c040142d0b44003d82c5401c40a003c11050700c81a900c0989441480c00000400c4400400580e0040c66550520098000800003055403403081c0d28005141c42000c0001511501b40d0354003043d00309240300401100c010b210348401d181c070703027084c0e0b803d40b2143c1102e154114603071a07000500000707004c00e040c9150030a100c1c0b04118404004041c000d400312801c210607603080d0b03641d00e80d40554052184030004030040c06003480320094005000807400b2036070014000401c140100c2c82c0c64030525000f03100b141070400c13480301140c144070040d0115040c407050000300c03840c2e140d00c114002e001d040c2d84c030760306030b11203007210440c03800d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 300257356 1250 300256106 300256123
    0x30c0b0d0c0903030c0f050c030d11060a050105061209030706020a05090108101203030506240a0e0402090a06120b03030a0e0a090207170a020c04020301090606030e010507020316020604090c0801050102 88
    0x707002c20b1080400001c1d402a030181611508000840640e10b100d0074007504004a0202a65240c014540348044807a0801c0088044040b00000c42d00e040d5551801c01c0e088490030700555900200c213002d100041c81a0a501c80c1e03001c08520b094034207040141c2e50b480c05a8201550f010701182d000708400b104d86d60301280380c9500c41511115034403102e18100d40d46240641c0c001029007015144c200048607034440d1b0701282c08031804035590341100c148810f80405143c1002c00c42800084a040031001784e0702c1c081c000c0d01c0154000500b000720407450030005440c07103500200e015001ca1303100c65003496070741d509001800d0000307400c1d01c070300c0300c0c82442100b000368900180d00401d102620502001000c6048079082205100da090100c0e9560720325030780264640035800516581c0680000f00200f01c0c00030075000541211410f480034420002880045400e0303d504480f000d006070b0040c0010208948078080c030031380003800642150328080d11000c840b02551030041c2d1610114480320010441564100608070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 300258606 1250 300257356 300257381
    0x315021210031e03020106120605091504030f0c02031f050105150309071205070b0706020a03060501030207020102060402091b0708070201200613170313050705011103120c04030c0b0d 80
    0x80618215541d0b412880c440090001c6103075910141e02e400c04d8000d5101e2006803506080503e407da52600c0d04030050882190f6002c458080e402e0020b91060802c400b45014079415214003501030700300c100844040302e000100b6641846207400ea00714450090920005035060404081805c0d8104030511502004100848415136000c00c108818480c009c03558100391060f50401004008040c00c0092034507240b6008940c25010020f24581005002d43c02010041c0442c0c90038000d5603901c1e4015000c901485101902517040321000030010f00d8000700c15a8031661030041c1c005030301814481c003800ca40080c141160310807400250702c410340d0381100b503501c0b480c12440c047c2c04030407840d45410707038440340c4c050808000c005040c0e513580304120311000c0a45800108104080d01c0b032800710001f4680420150301034956000b07000300407400d940b00310250744400c0b4411000318131702840c0326942d00201c54010329840d5400014403002c00001c0c40c1104550080030000c041c3d03522503801d00359031801c039074600440c0d6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 300259856 1250 300258606 300258631
    0x30605010f03020f0405180303070807020111070b0403200f070306051f0e19020703080610030510050105160210080a1415010318060606020703050609030c0606120703150212 76
    0x810050342c0c1c40620a40c5480140e03804101501c511024450700480c907d0100c4240c000401000300c11030340304c40807504c40c804980c024480702010280c590494401c01c04040d094520400000300401d0141d2000255261540303840c502074140d4612550400c16160a13280c00340c0c0000d5410801d000450140c581c12007420442e10120100e0002c144408515601c10004200fa403c40010565034088403003c078102c00d0898295591505880c2c0100591411140284184085120b07203090350320034411188121043c10a0902143c01e140055505401c040c0104010484c0c4a0808006860383c02141c0d41125068a69003401c1c10718071040342c2500c900d00500d1901012810070000d0049819807c0c00c207100080c01c0004422196400e4913a00c00b440c0c180c007170f010a0500c034000400990029120080b60f000e42c06940c91911810b5106480b4420340c40d424046920410109840340382803011020102501320450715141da49540d003c00400300c0b0781044500b2a400328403014401e00110300c050744010007003800c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 300261106 1250 300259856 300259859
    0x10b0a0806060f092202071a07080c04050d080f0d290a050112090212030a020c060c150603160f0f0806070804080915042309130f0804050613030605010f 67
    0x1200c2560080d07210480c405e1202a180300d46140400d00002c2400c00c9080307003035544617503504014a0341030081c0c070040f101111040005c1d82440c46034840500800b64054890701d454174000802204601088043e242c0060030404241e015101d44000e000d01208240089804060b1032143d4140840305e09541905070341c1781c0c00d10389150745c8030750b4000300703035002402c0c12020408104000b0000b0480320750002c1d0041050720150f11500000405004064131581c201d0304200b0018040c00f40d6400391554181c616405881e28264140380f481c0c08a40c00140641110500442101c04101d821610380c880644803016503003d0003550030b0804000050014903001b0300c81420000e000400d100802400079240580114001082c0e5450920100301042c0038082142c80e00d44628040300c0c0c0040c5001d450b001c10407411072507002400c0840307040c0d114140c4c810002c04014210384a44000d171415840885103c60204800308550b40c4030009440c0c0207402400c4440103e04520b008811039406070000d05001c1e105100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 300262356 1250 300261106 300261127
    0x10021201050102302b05060f0a0f0306020a02120304030305090d050304050303070c11060d060504050a090206041203121103040b0106030e0316060209040c08191109010302071a010b0a080606 83
    0x80a414160a100b0b526030383d9201515805c8081c0703402103000d404a040b004112240c2e02e555003000c0e0140c0d108658441d152a010020000b407003c061084901e001c800c00e0040001c2802c41d4080d09140e6298010355001c03261002c8034103440d500c02c03182140402d6440090060305081081207110101c02c5040c8a0315600b081c1e11101d83c3ca010040c4580d00b00302d00f003002e01003040791440d84004d4031040544426250802c001701d0380041c15150042e41d00580c035100020300c2589a500036142641d4028040300e2074542884040c1d1000e0150700001d03400e010300120500114165441500030305460158519103c2c02c0601d0050340c0716006902040406040c2407040c04000004811103d00710500d0b1a98540f8504e1854010060b000342401954461f2401000742d685540110030340c4d2044448200301c04e20f2880b1142da210848400d003056481c1c580050011004550103a40104912405003400781011454006074100d4000309801c4a50765807008100c2003002034100c0c80580d0006802c40c0c9460504440c0311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 300263606 1250 300262356 300262423
    0x1a030606040e04050703060f1d2b140f071101020721150c0201020a090909030804020f060d1a0102010606020a050c041e1b110114040602030910021201050102 69
    0x500c0259801d0300c0c010070f041090412414000350340c40031043c826528000c0000000380f41e0703170184d0924400c0f120361300110300e040403a0905400701181051040045c2c0c07403100e40c4e2030007040a805010702c0310114010140c84e50070405041100c003051030b081d59030302807481c000c1480c840e142c141c03070b055500c40c010602240a1368403814607401d8119003080c0b080411030030060354a02c0780d103100b5012540b82001800b0b900e903044d0020103803e4050344031240d0090f07a545d0101e0444508c0c03134001d00096422000310b070051030251280086140e00401d000d0a000380095001d040313400d204a41411655651003642c0e183d40c080c000c4400620550014148600d0a070702c40e0b40c0c4424030480d245101341d03942d019507201d00c2c0c01070203c0c8444a80b00346003001140c0303030308050500e040415840100451031002441a801d1014019100b81c0c0e80c406010030001e4a899032540081c0d017014001a04d140985483c10100000781e00c0074040204070071041c0a801d514080000e810007000c032494000c0445038455800c9000c1810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 300264856 1250 300263606 300263609
    0x30b040e06070f0e06030405070614030403083d060e040911040207081e040303030f0605130e03090411040f050303070b0c0903010902060714010606020303190b0f090f011a03060604 79
    0x504003010b400c0c0c1c00303840480c1c00000308504d151740410302101748010301c18002106004e9540540382c41140a00054a120f0b40d40403c03100180025019000516400c0450044001c510301401c1c0d14480004894248601e40003429121340303141d89605410804150f1001800c4e12890041e9001c00034441203849a11200030340c606a140542d4000410300100032005044995004080f034540141e030001c0a6220b040ea8082d00c01580045e080c60700c2e5000310700c068419402280c200400070f000f00d11000c080e03a4040c11008100c1001c81c00306020085941d01c1d64003c1210803050080340c107589074100354504011120b540c0219000740d000b1b108040010306140a02a0415440210282ca4001c1440040d025003540c0304000c0d0072500118104040000141c019245000e41c107000b8010203896610807a56030204464031980c5050b040d100d5072142c0081c4d44a9400d140c000b408e080d090301d2900e00072414854066805507400040c020042050803160f640181c0c2540e45500d0061450501d44002212409075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 300266106 1250 300264856 300264871
    0xb0405100f060e0a050a1206050c120f060a03380f0612010f1a0f1210020a050408010e0c01080a02030417032d070f0503040b04082a01020a030b040e06 66
    0x5202d0031104130340d90701c074016000700703002040281d031547c88041c1a600c020303030204121004d60130103001c00c0e888001d5a041da000c0b600c550f070008906680301c1d00500101680640429041070401401202052084051100044000262203a00c5105c2042c031032211a91070f040504044034002401050100d80032882d4000f07030101c1f0340081c2d002040c0c084a00401105403000e140d24a85041051300d0441c83c80003a030491400c50303c07885640901424840e004017000448042078203c480c003c10707401615030260516205d90f1a100d820140c0b070351012401c55035135808018290b4014503401c0c01c5c0c1d6902c51741440e40000755400541c21400c00e56184041d50724550181c40f152803020000480310510020601da805192110381c03a803080664410000710a07060780e201001900140302c02c2016801102100e000c0c41d88400c0300788695489840d807034107503042512180c2004070169496020450720080615081142000040c0e40d50f2035444060304440c00c0400c1c003801a401d1048022080b00302058156003d0345 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 300267356 1250 300266106 300266117
    0x916020f12030f0718030606050111030306010801060513031a010510050c07031101050f12010306060f05030c040902040b030708060a0f06060f14040b04030605010305150408180d02090a0b0405100f06 87
    0x22005820ba179418038080710740b507907140080000024408603400403003c40d54280c0f181c16000d007043c8a0729413a4072044520303038045460305004100380392041c0c1c0140008040000d591441e0360303ca9440c41c0e030b41c00304620107083c6c2e00c200300300511071840c0030030111040700100d05200f8030780881030345611303241d81082c80090240030fa0296032800b185d00490484100088419450350303103110829201044030070a01058a80030310708080800c50480c800c0008060341e0b001001000107450b450f04110103441001412a0020b40750407042d503294404220400103005008041c1060746840302c0d03264101c42054031805da2040c1801d80400205401414029524810745092a0043c594840da03503a60311940d880104a00000100001405601d9000701c0c1a64030420680c0c4040d580c2880041003280140c0d00038100000822900c0044054280c01501c1b591016180588519440c0c0005541c90300403a60949100d07250f4280309501e150902c1503942c401c0005a03001c48150900e90620040501c40c0988014480c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 300268606 1250 300267356 300267361
    0x20102120f19031506080907170c0418050c03060c03040204021e031306060803071110030f0c0306030b0714370c200603040b040f020916020f12030f 65
    0xc01c240300726490071004545003070142e4030300300c0018002d2600101e034800d106981c69012941500c103100d000c3c0a43d40010040907c44c1c1028819810602c60b0ba88001003841802c0181c58182c480d40504011020852117099800d00e160410500b8240c88039004c511a802c110104104078020000b56904580c065034016212031420b4440c0081c01030701d0b40302140088010042210005d180c00c108140303e0312a901c10f0180a90300d40d582d507a070340a1004010403682603003044200a0400009001c0800294a4085a40d8001008a801302c4070381d01c001c007002a898020620921110b0101c01350048054030702090310500c0d1410701003843c05019100c1d13014015152400e141c80304c078103168407003204103502c00141c081e407410000741600c051401d0449030950058508002110f00004a46080501404443c074603951a60342d44010040144101c0b2001c003021001009601e800112610a49140c45e5280032202e600c40003038944103040c2c0010041e0780c00098400c40c0d5080b044143e0f900680d44041d1061140c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 300269856 1250 300268606 300268627
    0x1b1a04030c0c080309010f09050d03050c030d110304020406081c0f020708060c2104030903020409020127180207050a02270405010f050114060306010e01031d0109020411030402010212 80
    0xa500c220005007030700b40d16100109107a00040020103680c030f0241c81d248900c0c2115441580c0c08001c038424541e00ca0826841000440d0003000103080e40301440d0b003940e15002c8503000c8042243d007074118413a0014400300402085041c984540b6010303110302d000501801c1c10a01c250010002d4410354541002514540340c11100d0080000801401c0d15000b901c0c00c5140040b464546608204c0051039150004090310022202041d21240290b80503620b414400e130842d000d00c000b43c01200c0b012410003504403004c840b00a2101801d0094841e0700341d51120301c41c5055407a500d281c584004142100c2e1040140c2d60014070300080400041d80d05451400e00f140100202041410804010003100d654001c100810402c040d23124440941c011070040000f41d0b2640004200d540c1100100c681003941003022411039801118003111803401450003055441040b102c00e0400c2001c1703d5500b140d40c0d15a8018002c500d4507004411681d10386440756821403529800003581c4010842040304401400505110342 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 300271106 1250 300269856 300269867
    0x20444010b0418050d0906080a0504080f0301140a06030218090405030702030a0b16020604240b040216020117040f0803220b060117010308091e030d03020a1b1a0403 72
    0x1164001003042002c02e9110f4007603101d8a0010f101201c0600a0183c04c1000e103018140c0d40701981d069a0318003009030f0380c41c20480014480644142c5003040240940b07580355200c0704c010b60190690341010020020b020080c010408225000041458018050b046402c4403040358075442000c222401980e079215810f01600710721484e080030b034043c011940140c0070301002c104401d0051030703001c0a03144050ba0200d012611454150340040106502640c00d510705503900000b1101d164040d0000140d40c268840020101e07031080c815022640c00350305000c41950f03044072103085100c00551104c0070b00e02d040d0303860f92142e800c4028000d000180c0400464501030030f00d280740078161025441c90396441c903913082486151300d08030b50450000e016411049442040b100c0920304036503024010038200350f034140400ca0718980b400e020604040c841c80a21045a0b020001c3d500c90410300c0d200161348045e10741000307110044d40c40c03c04174100441c81c00703d000102c24040407600a45407190400980e1a1440c040b2030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 300272356 1250 300271106 300271121
    0x20c150706112b0501122d0309090b0402030c0a08040c0308070503091203091e01050c0102130603050702070f031b08061006020d0903020a12020604170102044401 71
    0xa180c0700800c1c1021050090f6005821107501040680c3d0a07007a58407a0b0b00c15a1400d0041928810380c008200b400503c03176400c4c6504902e19001c20300d500f014a4010f4031a54500010107800003503071003004011201a91064505013102610305600d94901040c1c01203181c81400f1000d000c01c041c10340003600740065032601102669001101543e1203485042441c1d803900080152031181c0344102c84101800d0340042101c280d00c0018001d041045a11000992010348411189052050800c448050180284010000d801c212102d40d074030513040c4400101190801403080055501548040c41808101c000e00c104580c1c4c0304200715041a4400401c2d4030464803a44550350500c00c0905000c900c0410b42811400e07210564200c3d004103414010858002100d0301c03000c0d410000101c001d10940344141800e52490380041e082d146419030319140508061001d2154010726540030405110005040080400e12180009042c0030310340c010301c0340035090710f40a00300720388294140c41c02c08040400b07400104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 300273606 1250 300272356 300272381
    0xc0103181112030f0423040207030813020604090e01140603030307092702400918080a020a0b07080c090108060f030d1706150909070201021204110907020c150706 71
    0x15110340d07503000c0c22411b0880710002888801c0c05c40500a0240c1401e00c06d41d10302640503a114480b07500c0b1400c521000d800000002e98114208100104080d240703401040340405104d000010300e00d0001055421081015080d148250030800501404d103a000550a0554032850b40c1100e18088a00b072095000c031901c00140402c0d400851401411010b54103000d0f8821806985203004011481c0d001058000000426250264000c0d0500c00030066522141600c50341003c69443c59003952240e01441c1c100c10803107401a8080d081135001c0241264001f50804058109181e040c14596403410582c024020b60604200c079840000b4a180c3d60826403d030220070107815502c4500d000c0701d00a00d42c05501d0b0300400032501e6a4003280c41f9082060004440d652100c10680c10941d95204001502001410000031513400b801003000d0007000c4c6080d1405184600f00c0040c007200d50105010417000000c201c00d081d034005a6031108a5260340d4212007442d000720100c260b42e003140346001e2005107081c0040e007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 300274856 1250 300273606 300273637
    0x1051207030e150103061d07140604050607060c1223060f09040b0108070602120301090b0d0501020a0c11102003041701060603060e1009051509090c010318111203 71
    0x3d24041281a0403030689008401c1070010943c041468038000c1c1500c4043e212561050f1000c22407800e14a07003105160300c00428040c039040ea214000b03681ca4001ea4000e541080d03941101d41d80007031b007000c00d40744c000c4142e100138080d103540c80d044440903003034050001854950b244002452940c1e080c50f02a444240205091a9030405040088000e4003d026000c010f100341d08000c200c00d800000c1c44102c002d82c5107400c0e49903a003080b2540004d03041c40000c090308001442044070000d64280094003290030035940d40f034020142030034a044114030308403c860141c1c004a0f441c034071983d404040540700c0303140c0e8003029605c1c00890040d01d26510a6511000d00302d8120800c000102c00c041d00141c00303c441c965402d104950715040c400305001419101382d4075984056404101096090700400d5010860100645411041201180301c2e04422500403440b03812400d045405580c141c811090290315144120110320660b60361400400000b10b2028402da0300e000e01070407000c40c1041200c204881070f8a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 300276106 1250 300274856 300274873
    0x204050d0614010602030403200d0c0801020306040513050a060b01051309050103140d02152a1b0705060901050304110319140619020c07320f01051207030e 68
    0x740e001000182d840d40b80001d0080000903149100006940030b03a5005080c43c56031844511500b05003920200c4405d400030100d05100d0045005894943c004141c454005603032864100104021523000400d0240c460f101240d000c1c003c1000000d010482d40ea0040380015607445038001a0350b64024517140b080001d0004c10007056088040d00554100d912500f2445007500c00390b0b0207944c9680e400702407035006910400d8101c1078841e40102c4a6002054007540b202601140b60494060030200d206961082c0800609403000c0050302c9050084260b605000e0106e843c2000001040c91080151070f904105000c40031605101c000b0204414a0100404495166280302e821143c80ca01d003050580720751a141142c2c6560b01800308401744500c205007400131488448840f00e000a401041c1900000c0c81040c001042442c2502200b540001ca07200d5100f18582426042101407480400302d280903181010020140c0d90b084419580e084009aa000c091070366103070803c40c01011003200c80703402889402034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 300277356 1250 300276106 300276113
    0x14031501080d08150609090c2a06090f0d0507140616020d0228060f05090616030b0904081b07121509051203070306090203010b0c060f04240204050d 65
    0x2003444a5102d561101c200369500d9404540c00f03500c0d0340311216009034007013001008074581004040da22500c038503132503401d0034070405600d14100c4810021121143c000c007902205940100310071613000140000520500103652803080e1549801c0418109014000c40c1b62410000840f044500b40c513181c008958080c5001c0d0072980d41010f60444540242c0100100c080c611440401d8004850050090b82201800d04818843c58038030300b450306460341e90766400100b400d00c00c24082d05005180c40001802c41741070608801501001d0004101c00b450719203014896151181703603d040d40301c1c1e04880410785a515500c000d111030594412928081d00844a0110b15142040480c1c401c0c81c0c015440e9043c08102005940b040381c41c850805031265201420101003042000011a4418400d2502003100e0f603444585005903002a002900b0200d40030850b0640007c0400855501c41c182a0700c410715420141c46403030711116040c0094013011041e15100340f20720890b8048038002c01d000340012690324007906 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 300278606 1250 300277356 300277363
    0xc030319031d060609040f0f0b010e1315051302060304060f050604060834180c03050615090607020d030302031b0301180b030f03030103080307271403150108 69
    0x203410200c0d180540c9151a031101070700000c14500c0d03400c000c0400303445081c104010040010001c4444013050002800015a01000f0740d060340e100e03812004482d41850748158003280010204076034901c501c103105010401e81d509060400015500000c0c06e521201d2800c44404c030000b8012390007450020a000410181d94810380c0f030021841d60403c82c54460000300001d6170700382d06c69902c01d544964071000030003031440c01c00716248110140111800c580303800008001c282c1c03640410300070400801881030100c0c460080ba1880802450104802d140100001e540323100031010485040c1c00109003402c0c070392644411546028cc000b000c0081000c010301d80140a907100700c0300618410b12032403503445080190425213060701c0c44200410a4248000c080342e00910304d0f120340b503500d44110078040c1c0100c82d062008601a5024480d01c950b2450440005002c040c44510341e00c036800c0802d40c000d401a00700800e110107a0f295901c45144e010010700019150848107588010382084036000040d5005000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 300279856 1250 300278606 300278647
    0x151c0c0b0c16050a050f040e010c02370b1902190f0206090705040b0f0a0b03040203070f050105030612011d03041503050f0c09120609030315030307020102120901020c0303 75
    0x800440314030786408014890400710b584580c90700581d00c0c0f04203001c6403400014844040a018100049900501d02d20b0384c2510100081080560005080354003c1900030166400c8a0141c8440c0e050b820841440c80900714242600070b00b20584400c0800d01884104641d90b540d120311440942d02c80c1142105048000100c2c040380e0040b0381280b1024210302e00108404d44aa041a0f000e491058540340901005d0000c40070780c03030350200040c81c50808696030341c00032a014000007803c41d5180d20701441810f1030311419410800d4071481540e0100032581c3e00c00122980407005480100314010810085409084007905038003000c05400010b1980c040b000014004503075410091100350f00c1c100720f080e01207034401d440c440c0b0014070203030000320a202c2030402030a070003001030310b800d040c48049448182015026101001207400c004240080a04800700068039848102c010b10301c0d2040c5540080c1d902c10140300d20900340400455101e00d1607000303000e11a840003026041d2503565000c05104091003002c0e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 300281106 1250 300279856 300279877
    0x2101e020106050a2304021b030408010b0108060603010b030a0911030a0b06150c06221203020408160803030403030e07051002010603050f0d02031b121b1005151c0c0b 73
    0x55400007910b17141c0005400c001880b6000b0340c2c0384007083c4403d10010b0f60010004011800c40c031440d06007440c004000410081001000000e180100d00d0001050008080d0800e071190381c080c030040c40302402200490b90010450800003404500d185401007201e03504100c21035250103200354010900c03180423201442024100c40e050300101c105190550180129120f60845510650008044680001da0802e18914061035000030034040d1340c0d1103401410172140200040e030041030401c403145040040d201800b0136021500c11450410500c0e0f41c1d01d01000744050201a00c030401e807410f0a006012000262074060700c002c030314070041179010f406040b882c42708450a20440e049480d24020200d0001528001a80518545403048001510394129200713012a14022030b1201d03520144100c00614844c041c2400b10090503698001c06410305442c01e40c0b20f1801e50604007001741d103014454802d40c101c50200d400166180c08403200c0280e0b10815080109044c415100104080901c03802401c1261031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 300282356 1250 300281106 300281119
    0xe0402010f0f140714120406030605030a150902040f0e010926030601080a0e0a0c030203162d0b0c060105030601140a090b030a0c090209030c150702101e02010605 71
    0x1e0504200e40240e030010000c030020b0607410840480c01c0c40b0b90010000075010b5141126001030f50103240342812455a84a40c540000107070400185805005410090804501425090745951180107100e8030348000940e0b16559500c0d52811503855a01050b050218140b08021160f0030200d5a4000e1950705c84c1558201706d050700031012240b410341500b83c580101801d40f400c50b22504019610f26401038200c4812175250a940485607004212000480d409100213900320340c80c41c018903007032000c100009280520848400c4c082c111044a00c01c03006000e0080041390140700266030000c003c0d8039004200e1480000a288002c01e80014603181668400c80c00c0c3e407040d9a130356402c0c0448043c0e444880760403441d0044104040070159000d81c81958024013a5074904203103545280c400315864100090095000c1019181420b00b0030043c42c5000c1c05490640348240000c0180045018443d0000e01c2402000b100300c0405104003c00001c201c0c903c001290700e0240004007a000c0c2800d03014441c001e20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 300283606 1250 300282356 300282377
    0x5060318070e011d090a030c0212060f0412050a020a0210090e041b0806150f0d1e050706030b0102030d1107140f0c061c050c04050d050303060301050a02041d040317010e040201 77
    0xb200c0c0700141c0030ba010307417004200f0f002d415a030940f451401c3d804c0aa0b4803803508401004904414401e880c4152620024400030345804c0c0b030000c030f606400220f8034003003040501c00f648403581c0000d040c1d46010b404540401003455491012070751250a50004090041000c080c0820080f9940d4803000d00c8601c1c05007800700c1340d2140c503001d40e01d40c2d040340c07255142c001840c400c04041c2003040c0202c66914000d03000c0e1408040ca91690070703800500707c01c20411940840d00d000c00384003043c84410040c0c040f51030b087c8007018120300000e50300c1c01084030340b0380700715640c0aa00d0001c032045d030b0443e10b686911140e541d51140c1400785160316000d401038540703820f018210500d00546006400c642c400714210201c00781440060403110018a00100103098180b42040086501e030b54460b0380f0190f041c840c50040d942d07490300b101858255500900140b804a0050006002032001100c048410050051381c107217080e0b40d00d040442d01254020b09141c9021944400401c5003002641103a103c1c600030b0b00d85802d42d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 300284856 1250 300283606 300283649
    0x1e020d11090a090f110408030316020f0c0105030a15120311070f030803060a0302060d1a090106081602210405011b050c0d020409020a0906030507060f0905060318070e01 74
    0x2032003480703000341d40403024210a100ea280903601c04500341280100001d00c80c11800101c00392035100b0340002034950720100800c00c1882c5c0c400b42c1c0d10300072111071015150750340c120900a03036910301040101c1c0c14071502200240c100380455001e0f0129403514036080426a41c1c0b130002403070340032130000c065002aa00703240c0e002c45801e0009070b0400f21280f28501c10b00807407464407034080d282c0020780103990204440400201503661600036000c22420060001503034804480c50b41001440e0548050060079000d00411025800450280d404400140d8003807220400e14401c0b4200f0311100c2200c6c0d12101c040030f01c0020080680c000c1c0c0180c840c2070702d409072800d0314040001161310002d44000e041e83e20441c0b45080130b003480038681c15528030113080411600702c19070000e136203a035950700314094130b596a441c2007061100c10015038000301124140800b40c0207820350018400304142c040d580c05103200102140c80c16407c8104000000741c5a0f06540000e07841c0c56040a0401e001c2c40b031203424540208680713810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 300286106 1250 300284856 300284891
    0x15030f0c030606010f0210050103061b21090f0510092f010e03010b040203090102130b361e100e0d1b080d0c1208070807121e020d 57
    0x10680040003410a9a83c03a0b00441d80ea070030300754214003140614021542111218000c0c00d001c0c2d88a0100403944541c8903945000c541c903d03811040c10052607440c881c1c0bd18402d005018207054003644040b80c103004900b0f0083c801d18000302d009007a44502020004d50506a91040004c00d1080030488140480000d6808101c0d103e03034030100d0b0745a01c04e00740012070b600504881e096804050004244c0f44805000101240c0003180c00118594000680e034540c4016402d6480140c0355001c0d40c1c43c01c203c0800c0540c20ba51804801d5451075050300c480304031079030885141b00155100001c1a08240001285000e0b0f403902c1c0c0740b10701e203009600c04206401d00b1401104020002c1201500303500c140380080d02c0ea08040d91408003504407024002c5004181c20b07a062040d00c0b03041c0d1440e15803c070028800e140103001c00940c2d00941d810401c01c81c0038007402c580c0c0869500d40001d07807032074081240036481c142c00000b006504207135003a20120503100c502c1c040e100d402500714219810700c100a11030305440480030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 300287356 1250 300286106 300286123
    0x19030c090e070809010612033501030b07030605090703230610050f070f1b12170a030b03011a1c031b031707030518011103011a1215030f 60
    0x4000700d6000081e0005200301085644503642e00e002103a1b80340d42d0f10320058081c101d800280d00082001381d00711107040740441c24005207500e000d001c010b449481a1a00606c14040c00700070030448605000c200e5081c032982050001e01401804180c0034104a00301400030070040c2c40c1540000e6402c4051550328202e09801481148098050034110b12400c00071103181e0711207011003180c4031082c8898004100c4004204402d07a1007404140c0150303800d402440d4034083c142e880040e52000020300400000c10f04c0d030800c1c038005001601a41c503500301503400c1c2e0241c03441c030410507059803a2007112100401c52200511003100240c415903003c4c1400c0165541600c10401d02802040301541c05601d0909501c00350a800e902901d40303404d09100341e049000e4810f80545075040000d45a03404d0100c1040c096407905440e0342e800000f00032450841c0700c00380c21400148540551211298011851040030f102107a0b02010580044952450514000f80c0300403810103040f4043d104400c10704c3c080b11000070340c405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 300288606 1250 300287356 300287369
    0x180105120f12070311030403030512090c06040603020c011d0606010912020d03080714120f0603030a0e01120b060d050a050702030c0c06090607060c2003070c09021e19030c09 76
    0x101400c2c0031000c440742039004100032410003400b00e000454601e400d002420285101c1d95440307690300b184100c20b00c1e00e9000176000481607008052442ca4030340c3d07418201d4045414905000d070b190000c0e03084030350050082042d00f048051030f902e01d1390b0ba2400046029441888262207a00c03030b080c0c54039002d00200d01200300081d0041c1040a42001290081d150990700c201d040c41c0c000904011010300418581180900500e254007440520803101705c0c1c0314910358412801d6000754200114614010885d0b03022000c0907042c4000c10201120440150b00321210004000e480b8130703580c1b440084540000c02c4102c505400c800d02d42004101d05510100403164050700200090541d405c0c80800c0180c660b000031003d030b6000f0f400300020800507881d802003512401282c0c0b20180d074481d40c039103485002a43c240c2c800745540c10402c4028009a5407108440955110700d00060b02c410043c203284041a0a03140303020380300c00020a402841100c28289420301c07c0080c0d80038402200c1401d000d4840642600843c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 300289856 1250 300288606 300288613
    0x10f050915131703070203070e070203030708100902072103061a0d1d011e060617040203030403021815090609040204051003021002030901110c1f02010b180105120f 72
    0x40e00100c044080c00702c80e0500155030002540d1200d00c0c203026154004644010b400100d03415042d8039080c05803e00900c0d80071420a020b241c2840003c0d16440020401004d00904034042003518642400560240048070001c43d82c60321181411640b1a07890102e510700c0c01e00d8031110342c424038800e004401c100c414032540301500c0346204c01c000c0c2c0540c02c07884540c9000759941c43c1440d50b5100300c049411088103081c00000e0005d081071407070102d0b144400d15000155060440030071203958060001100302d464034500d0f480315280c51001034118441d45e44040d40c4844030382c51244107140e000900a02a5848024411401c1c6004080c010106070403500144d10450480004001d070800d9000568843c40001c08820101e0300d030342c0051140c180d40004980141c2c0081403204440d40c00460059050499100a114400c0040d000442d0480415608801c900303207500021a2103000b500405d580c44401004189079100d02c20320070300c80d01400d101d05d80c420303060400361340522039001c500c0d07110489068024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 300291106 1250 300289856 300289879
    0x1609290f010c06090b10030201030b0d0c090b06130f0e01060207030506040b0601110f1018051e100203150a060309020306180a060f0f0506090c1606020c0d0e010f0509 73
    0x103440b240c40d01d000995070251102154000542414107603813050080c1c51416210a00358000107045070306280803903006140d601000c501082449038080c0c100c504100010882400e1040828030500402d89500d25a900700c48001c83d9424032010702a054070030101d040c007002e0780c0c0c0e8035080703945152074407000d030030b036000400407901042d0964201c6d940036406041c21024030b004040355901d400480e250007003946d001810300c0030040c001c6000e10304000d55060181c0d9058030b2251180c58031034281c1000c816010800b60303e46580b88400348401c80034248107207811500c030300d09507901e840c40d40340d0103d0f114400c40c022240400c0701c3e806072040f5101950040c00400991f96050488511508056480042445984074a01c00a10140102043c0e001c680c0c4c40421134080740400348007500c202824070340c41852000100010304a01c60291340c1c80c038030601c0c11404000800e05000c0000e21501c0c4e0b450100c1d00903902211a0306410500c3c0301c008060a80e034a0341c812200c00f108071000d0264200c0c85078000035601a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 300292356 1250 300291106 300291109
    0x5010b01140403110103091401050403080a200d09081b0607030603050309190f031505090327041d1f0c050414130603031205060105070b0c0703021609290f 68
    0x2200c0d0031034130041c10001240c641a4481403d04c8544503a5225140e465000f00f00030158000b12094001c8a4240284110550342100007031076001114500c60005002c105410061100c1d08401c1c505078110300c066035100d050564004100d0304110b80001d4520a880c041810f0ba1310910621040f00d42142c0a1070400b0903160802100c07411050710a4000359103020082800031008040c1002540b1400e8000220b1100d58004015114000d02901d0250028002001368104600404040080c50605101c40804200000e001007844a02c1581c440c0c1e00424508072000c00000c02d0894440f90800711000800c600e048841039400c80406000011414042013281d06411100e229420500500802c100a50050034100710ba14582c0240e00261460070140101292485241d0f003000d030a107402c516006458580484015003d4103401e032280000a030813060500c00e216080001d80740a1081c0d4040d0382d038101403000b0f04101039804c40300805104d000400c0440c190750074400002c020300b00c0965000c4110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 300293606 1250 300292356 300292373
    0x31060605031e071101051603061a030705032203051809061c08120a1508030304020102030a050f07050706120e1902010c14030f070c06020303270703021c05010b01140403 74
    0x910403414030110b5003400c091580c0038000d045c412102c041f075000941c1c44020000341600d0b640c0c0e11482d00c00b041c1c2420140310103916000c4035449512401c16590340d4554410001900d8455040020441500c01151040581c0075008010555407010500349840c0034604010313070701d0030607182c075030f03000c1300449521283e68031144008080318041c030b00460800c008110038000c800c104440c80c1806650703c840028020140d5900c0f5030150a512000b18190314081c1e0000c1c1d80c034071071224184140200894015070071110f500c2112080d80d401410303a000c8503900e00020340301e07882d81d00040c007055081241d032098244001803032800104410b204a9000c4526400540e2642d00c44081a521000300c402c05106121081004010b0b0524145085030b6660b604c0c109031107060b085400070303000c54004100380005510050244601040d80b0340c803500705504154225032a103900340e0f0000707401561445031a85000c0808400e800780d00c1c0071300000e02c4110344402c0111900307049005402e950003414007062000c2003114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 300294856 1250 300293606 300293611
    0x1090510051005071b030203120f03010b0904240e0105030d120b120d091508010e0a0b01110a06020301030b1501020604031d06030c032502070302010e31060605031e 72
    0x6043c07280c0f60500c00d40b00c40c1c1c1a00381d4002400c401d41102c1e80104110700f410007402d100c0600103520141414660b1410b44510704c410711651240100210f481c004940c0c803948103401e41a810002c01621a03d003024241d41c1c4411446401c141e02c0000e8000581e50401140103039a1900990317400c04059180701c200f40007050a103212a401c0000480e000284100800141241301020b4441c21806403601510a43d40000c4030002e900300510480100a4900060343c05500504564800b2880740e0f40c2900480b002e106615a6143c0fa1050032026014401164000c0d07058038000c50904801769142c0040c003401a410216090040c0e02000010700400d20892268184000840d803440d90340410723600060b0141c00944445c00050000400e00000e60705610b194011381d82c40941518085010700f9019407614030510002c2c1c14454204401d0140340e50310b040d110030b00c030004240804c850800a201d01c10803410441c00c481c5c00761a10b03a010a0305030298007070702d100d01c204002202d55050700c4158034840342d901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 300296106 1250 300294856 300294889
    0xd08060312070602070f1410050606120f07020a05030412022407080309070308030f0a1b050a050a1101090c0e0f06130902010e0904060213140d060c090306020a02010903080109051005 80
    0xc264200000b1f00c810528600c1403801c40010b00e06130401080c040b04881c4c0c05441d541c403894003042040340d040e95180b000c5e5442245601d500d0500ea45110050f4180034513507100030b00c140000500450f82d01100358080e08082d0081d5501042d07680e00300180d00501e0f0728502c03481151030051000500058a001c0210382c404145400d032841242c1c0c99840100c183c006641040e6000f1224040000e0140d0318804d4a01c04015094200d5489264507005080d9105c0c225802007040400500004200c3c06141140c075074851003002040740c0006810400c180f480780c0d003c0d00e00030340081c0000c1000c5081c89503816010341e50040460301c180c0104110400240700441d001c9041c081c0d025440a1070390b40d200782107032080d030050030f002d6644e248528088200c0525500035085d5660300d0340c4001402c0d25240c611814140e800344000034411800c1c1c00c150b883c802c450740010b011b24000950307101110f03419004180d41030720a464a0f00240d803104801025540c0881d0700d05c00812040d9000c02c507074a407034411441101c61 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 300297356 1250 300296106 300296123
    0x32a07120b011502160305030304290402101716111b0409170a09050307060309230a0510140601030506030d1409060d020c0705091012030509040e0d0806031207060207 73
    0x201085d40b1307550140c158016286508048200300c14010089401c0714241c1002410500868400064400e0710f5800b0300040c0c000c0010f201e078901c0703c0d8004c0704807034004070558089071024580540d0f03901200103014880c50009100c00b51020241304000f030031070704403000807480e19174001401083c80000c1c098003e0170340700c9211030181107012480d0040204030300c0d051903503101704850804080c5407900c103941c1d200c40101840c20000401103146010b4000310400000c0c00202c02e024480400c610304400cd1a01820034094041862841c0d0b100742d0118000e144e42e40706011341c940c1c40c07800541c00c0310710442d20990503400408044080d144075050382c2d11982425681c0034100b504010200ba180c0c1c100c440720a0700c0b1540000d9008c0c1030f03c0d0801035080100400c403075010251824a802c804030f071800c0d104070418014190b0440c0d08140c081d6042c1d800c0d190f00540100010030b802e0b14030030780c0c03070190111010205040d5404103016050200380c0034a40c070f002c41181403901215969030f50081d80205800c1c0d0b410710 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 300298606 1250 300297356 300297373
    0x30106150810151d030703240c091511120301080f0c310608030d0c0e010f050a0e040906020a0503090d23030405032a07120b011502 58
    0x865210011101248a603500007151910148401c1c000703269803c1400c080f40c50314010b41c0c00603070080c0340600c04003240b140d00141c01e0a40d00030a14060b0346420003481d1200440645403200f032800c1c00c41202c66104031040c003800c400c21005940c9000e9501800c0b0428074203078124090740d4002d2141043c800510000c40b2115207004005030501c0c0c00a0300440007507000b11a0912040c00108880303203210b002140d400c40981d15a0550302c0340349462074060006100200082c0303400e80501c1e8401002000080152613640c104a4103180c002d01c03541e00160041030300c0c5410b05501c4d5104003c003080010950722628600700c00090152440b20303140800550054039895100000b40d02400900710700c1c240740d10351079164240910100d050408807030908007000040c90303001105805c0405807a1190b001c501c0c115940f40c40e00d0a0550451042d0300b40d147c0c004490b10007103424004041c3c400440d01c0c18030300c2521002c3e619807901c1c90144010110240c50543c44000600c014401c03008414524401070041b0345055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 300299856 1250 300298606 300298619
    0x109020412030f20030405120115030201200105010f0302091e370e01050112030e0d0213140402030c0f06070b10080d11010b010509031005040312020c030405031002130311030106 78
    0x400c513041071100307507040441e080203907040c051500ca541400c0c480080c085140e109103440140405848040e04000103c01e4440c0c0f90411502d103400412040c2c0c0c004d000c10340e1a0b00e104403110019201c00ca002e00a840300080c00e1403100f41810040e031600c03c40004070303a25001010071200b090740b00900d00c4d614580b543e078041c1c00784003030303484000d84101000402c81211098295085030016848100d07203010f590564000640d00800803425008200c48110b41c4160a0000c25803429444141c007a10502e01030140788281144100030b81301e548201d0845035000419401e000d01e00d59401081c40d040882801034900207121205075641c020f101d401d0140010381d84410403480d1078070340c084001c080750368915120707072509081c058a111641d0a08045262075000c402290b502c0c2003108800005e10b07035403004103042500c0340030031302101c46401e10b0642d02d80024078101a101c0d405841624420300c645042a20020300314001e58490850003030050b01000c1c615103403800044261040a5490b5503261008140c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 300301106 1250 300299856 300299897
    0x1801021b0f060a060302220b040f020c0609010b0d0611160f03140405062d0a02070905180606120a02042307110309060a0e040e0102120109020412030f 66
    0x148080c4000c1c2440c11094070410b00b002c101600b4280540c0c103101c010310268031215440000c0c10340c01051a00000720030303001200140609070295501c20300789a90a042c856140e00901000b080c28002e4582948a840015089495440310305412840d06804800490420340c0110611a12021054540418140051940d201c0c001040302c2100c100d40b46030091640c084014202c0759019200d642c0b501e82000001885400f80729030003003540300c440786120715002460b10034509480b80c02c0806038403502c26002c0a5210070f914014220061b240500150b61610b6090120750b2a801c200003401c41501d602080c030100442c6007144000d0341c407403003440a005072034038410690104018603c0000d030300d442034a08050041d02030205010028120f1100e415400c010040f9000701d0400c40d12566100160101611654400c600da42e0703015107000c2c240105608190000c0c100018070206040080e0388a0050720102d000b10b0051443d0262540290300c0000d006039111581001c40741052101d200d00e01161240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 300302356 1250 300301106 300301147
    0xf0409020301030b0a090f060923030307020c0d0c05121501031a15031005060a0506070c09063c080a06060302030c01020106081b1807030509070504090308180102 71
    0x4000303900000420134422802c000540240800405002003031040d2584660400740704000351400c1c0c1e803181010104078090303003011000c2c0b4010404541500e00d0010480c1c030707900100c072001c015000b40040c0c40c45070300d00a2091011213a05c0b100e2450a6030422040c8501169404444482031140c42e9401071200c201c413050900862081c415282d103d018210768008481c1c0c09020b0428509500014460b41d03034012a8502007001c24010005543d5070351303000110345640ca5885582c00900c0010f0b00020300c2010880441038940e8010284000b581e0b8604c00c500401c0e001c0c074180140301c1c42024121001010680741da0f40392800240b45001c035500c0c0e1029a08204121900301c401c1940d444040046003800d20036007464a10900003044510326261819454421039113501d0948280c0d00222201039a502400d0042c01074114060051480d060a000d001800142c80c5860741d0b200d80c10000406141030b0043d545196419582d0290715100d4441d10a1140707980742d9030700000d5400380b29100035852600c0c000c29 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 300303606 1250 300302356 300302369
    0x90b1b07170c101709010609090302030409050912030118200a031104080d03091a040308010305061f0e060d0b10140a060215041b0605030601030e07050102060703020903030f04 77
    0x40d809400c200c641d4a0012020b030024041d0312228501c0c00e00540001e029411401101542c6415941e0b0860081c0140855006202d0380703442e02a0110605500101801c00c1e1101440c0c100b1458480c0d4650300c2c2d071400b0241d02080d6180003040180501000d10030300409054140c40c1c0401d42900b81800c42501d10107813032148a803005c0109484032003c1c5c1c14040c03141404d4440d00c3c0d45103810f042840c160384074210320700440181a2100d1400e01008034401040c6024600c00710f4600c4070382070600e00102001030070302c01035840e44a8880820b14088030813282c5e03100303500820300100c036840c544083e16100342d400a04860f8400e0008000f440400d6403e2440744c4940e0302a012440c03c6802c00391410007203a00e0038a800d0107158078003010f0024507000220b00c0c00c039008814220f605940c85103012000940c03800d44072800c039070140c28002103c9800002540c002e842c241c0b03062109c0304004840c04c1e030301e0045200303450041c3e101902080c059402540204034110001e01542d1070601c0521207034009070302c99071118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 300304856 1250 300303606 300303629
    0xf1e080a14010e030a03290f0f010c0c08010516020606100c0f1401020a20061f090f0614010c030e010f03021b0f010b011d1314040b15010c03090b1b07 66
    0x7e0072101e01c1c02e03074142c11440700340c02550170b00c3c015800841c102424141009000346802c0c1c802d6030311a801000c0115942e40d0103459000907d0311200064082d18090b10310105060140d480b50260078004994a8415280a4820103038004100b508403101300914000b507440a0108816402003600e0b0300710220b200405c0c10002da43c8640400c1e005085900104003920040d0401110442801c000f0940c1500303c13482051170403851003083e00c000c480e50750b65800488030a10304a1040e14812898000398121084454407443c0840c5410054800b010403500080000e0b036a403128404a40c0604c1119400010a00c1d00504003120310301e00512031050850302c0750039684000c9501e90843c0c024020b19248010030b01c2c00100c2c103c20f0910485c4034240601070351f8425504204002d40c1004160702040c03a895102100d4405414070b0304015403800740c141d911542480e14403182c09455401030309050001645542d504141c0303482c20044000c141c00020b00388485c40842c0c0c445199420023042400041c04105211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 300306106 1250 300304856 300304871
    0x301020a09030b0c041a0d0e030c01090501050c0711010c0314040303091e03030512060102031e0702130c0905130b09013f032105010f1e080a14010e030a03 68
    0x30485803030b0003090110612001c20060110303030014040039034840c020b2500c203038640e00800c1d18074000c1c001c0f501510016100118070002b01500542210900314080d1001b0881d58584460b14244e07440f07801406015a0040c1c0030305172040d4818104091102d001e40b81c1305192040c100074103011903020358070550003e40400390501042c0c01d0362400c090856500300315a035140e8175541e800b0300580158142080c0c454200000140c0590090040b03e003400005031001040c80d055641408003a0000d00341a4024a28010382045400d0541308004024115499402c105403500040040c02c0c0c041c1c070a04043c0d00d403030750040165921840401c60103000c4110745100a2400003869100c191440c08803400011040f400d07030703001c1d40c0740c1c0d001d1a0042c1790540740000000101e800d00078011040d015400c1041c500c0c0c04000a00c120a040802c019514110040c081e20307075038070008041e00c02c80ca000c4d5401c150000743c60300e40000c44410780b100340308103004004906850101300603811070b00000d5111010945a121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 300307356 1250 300306106 300306113
    0x1206010c17130e060102070302010c0503280e180a1505030a0501050403170f010e0a1b0504050a05191202120706020114090610030b070908060415050610140a05090301020a0903 77
    0x841402400f1250a001c3c20f5150850000f0740d580400c0c03001034140050144030205000c0f050040702e200c84130710456108040102500c03181301040c00003000f800240e8003a0007a1070f07403900c40456041c035011448010701948410400ba001030440040126804480d03550000d850f850034454446030743d01420000455184c40d09029080f0003441c100c21030090707180c02c208024803011481c02410348041050300503e076641d007200c1d1401890040701103400c1050002a00c0c0750f0580c0170f001881075800a944071020295980248400e69130040c0703612001c04180c081c1404a200010b031314408072030004181c1183c3c84034074400c947c242215030308a980140d440d189a07030080e85110140980080d0b444000f00240c3c600961254961810341c08010000c409010100e03140c3c0b80f040134440c0103044854250341d02d030708062400940b4455806800c904440c02e0600003a1649030001d85a10200c2c25174540c81301c550000e0000c00c1d03440c0e0040d504a42400024080d1803501d413801d1001d01000401620b482134090305504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 300308606 1250 300307356 300307387
    0x5011811090c04090c200a021309110d06020403120509012015040c050a1d100b1e070b0a0504061406031e0c09101401020109081206010c17 61
    0x10a19004118110500c003190a015044804641c0b005000085000740143c08903103054800381012288400b1506d03280181c0404034003900c0d114400c541041c0840710b0494a80b0980d06541400707040c2010f07121019105052140591103003c0c4a12001458151242d1380e09146500f0784011000054000c200002103580211010084540800660715450603410b0380564900303500b003a015068444070007060411038428404806003400410000130143c44480c01001410702030b544045146088003c603240043c40c1e40803006035980c13081507038688055808886e10102d0380100503003000d601040b03d1404a40c0074150340340240381442011896040c0750030040155946552043d103041011b405100c400c0d40c0019809890482ca40110203a10002c0c604a80c100201c9448094208080c0c408100384007031604100000c0d5000014825006103d10b0012402c8a00c02000102203880c200b020b155101a43e0240540c802c20501d895030300403107259155141e4103418001003581400c0450112910100c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 300309856 1250 300308606 300308633
    0x9031608010f0b13150f09020705120301050306010308030408071e030e03121c090204060306140a0504171b100b0111010b0f1c0b091614030d03050c07050118 69
    0x5818032403d9000750004440c003103114114013035256210140c0c1c2c2c5402c1940100780040900a00c0880480c0e51030300f0078006540201c0003201d45002c2c0c2d00f0100d41e600c202d0000d60303059610180c014800c1da800c5075180c900704e61020380151038401e001d0048000040c14049140d440074084112509a0041d074580074051441442543d03100e90091002e5420502c0720708250b42c1d9403102e50304030366060b203c4501004010144108040c1d00300341480c03000320901000782c00510a2800c07100d084441542c543c103058040340d03402d8400801504001303505900b1409000050085510f074a9a40500d00c009541d2a91510b40882010a03060f61140f03004a40c070340c0c01c4004040041445802800b844c2000c100181412031800f0040b80705902c05030402c0103000404030020407865102c0e109090341c0c1004a107040d42c035806440d6900c0c00c42020140440c0d02c00500746103410300c5034050010400c6413946101503008e800001c00a029490081c0b0030366011560034000d40080c1c8540030b1202d2030041041c1070220456419 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 300311106 1250 300309856 300309881
    0x1f150c050a120e0f10080f070e030a0807021f090618080114180309030303061e131a040605030c01121803050d0b040b0a0902070203150a14010503011b030905030903160801 75
    0x10303445c0841d507581104140d640710f07003003001c0707804035a480c18026121905c07c0b01c0659014844c2c4042c25017000064401844101e00072110001506904800303100c40c0c03181c0d01003000020700810030800025005048060302207203941d00450400791200348080c05c4420f18400b0b250060404c4051100f00031840082125036400726024514042c2c2e02c90119030f40c2d10000e05020701480d00c104440384040008130b0703210300d401001403d0385c0940d200f82003410080e000c6455490b0310850155600452071034140b040c2000c880014010b8065000c641006640c1100b134030300311030480d0391582c1e81040e041203006003e05075240310340c540c41c2d110904c0c0c0d601582110032244d00240500e00d030a880c0c040c55952141c0150071206000f0300541c1d40e00c441c3c40800d051505021030706108884d01800d201d40a01c05800070615600b1a0000d2882d50b80d0360810142a940390140000200a4003800044060f00c44e80051013228001c01c100c038030300400100840d01d4040848082e0500b810100300901c034801c03007800b40b480741100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 300312356 1250 300311106 300311119
    0xb1203090a030201051e0307020304080f0a03080601120f06080a060f0c02070e0a020d060303030204090c02062403070302100806010816120203130203010e03031f150c050a120e0f 78
    0xa0080c0420a0202070707000280c180080420034401c240701c071070341d500c0d05144004031468403400d0011000e5900c0c0c2180c06501502c0c000d00b608002e41640c0040c0b40b0240c250169182005611044019586043c02c24401c2059980700c202e03020403008640981d60041500c2d1000300781c400c00905041007140d00d0440500d007070504007518811160f80c0050820155507840182208a844140524001348929842e000380d03541054000014560158041c000325500b084051094540c002300486e00c0785000c039000000100e0b2450003180c0035210010907051140c000e42221a91510b0350009909003031380450700b80018140303408000c81543d100064640200c2c6807600281e0000b4051310140000801e41952414290b020001400081c1c80c187c0c0b0642403174015000700180740d50045556107030f62046035050758980110382d8221382205901c040e00c04039080c0c9400b0100361303110441e084400c4152000700381e86602c02d1604120209941900d58030400b03282d92a9000b6840c0c51b207050244000401c101c5510589 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 300313606 1250 300312356 300312367
    0xe011e0f030e030702032d0703080d0507052b140a02090316120b0a0908030406090c080307030903080c0115080703020906120a140f0d031a040e1002130e0a0b1203 71
    0x80700081e07001c1340c54103100150300a10f1070780c05000c2101f003019480188584140300700007050100003402071889584992090015541d640029101ca00c20318080005829846411814916400e0403880105209030790120314251202c2e046d101c000b00076280d40407180e42c00105140507203820030015080369018000c0d030020f81d14000c01020b11b4070008001400d015900c10000b0050001d59100e01040c2d0b612014094903410a81000401481880c0e07041710b00e14582240854240710002c02c0da4280b41e8141c1d200500d42c1e0840ea948103454000700c0d032f845000d64070303504081541c2c415807842101400c0d05030000c050561440c010000d200c0340251410380103203440900741e1000d040c0440c010309a81d0f082450401c018400300c41d01441d00c5500240c2c1c0f0300502401d0080700200d83c1c9a04a141514001d8a401c04040c000c1c80030082110040203607160b440e03000f070941d1200d03039000e6009440d80c1c2c0c520007242480c2943d0350f1422445a0011110141041c1e85d441324002e0610344070401c0c1ca5203000c03010046040c071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 300314856 1250 300313606 300313609
    0x20606130b1809030706020301080c01030c0206010b0f070602042c01150e0d050a0210050717133308091006050f040f0b060c16090507020d0e011e0f030e030702 70
    0x200701c0381a8501034042c0d5103001403000f220800c1101c5007290300080466072581d50f96942c6454034658015540001e081000200300c6510006016060340c0e00c42c1c90b0b4a142502d40341c1a481940d002200856919400b03010001d0305071405030f1030315541103055149811740b240d0100c01609842058101c1ea903610704043d003195160340d2040752080709140950740488028001e007070180c50240200002540311303d003a10301c111425440405010f003244a2525841800c1c4070301c011003294000c4000c6022040c0ca900410880388240340b070190b40c0c0300744d2051410707918010381d509150740007020400e09010820a80502c50744a4041141102e1580c0f1040c0420489041200041120000608051180b40c0f00c2980ca032913052107038080c41625100810807542c808900046a840b0b505122450203809000b2100041c001494000c003032043c080ca80c0a04200380e00e004040e10b90542c000100e6041084919010038400b070655500b5030305c000c160711280e1021502003030007401e0721072603442c4200f01d810601124006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 300316106 1250 300314856 300314869
    0xf09080c010e280512151f0305150411100c1b0b07050f060c2d07051518070614071403030403080a0c090e34020606130b 53
    0x414024070344002e1940340400090710180e00030080b01d2101e90302c45031240c1840d072128003400c100c403400d80b0481258003000455a0b294200742401207401c65101000641c5001c072400900425101118111485522629554031300003900d0880400c0c2c68094050105120080d030406039260303400c0714868a422a103d0300284100ba14040c028032404001900004281c000030f8140c014240990803a41c850125040032503851840102c00d121a024860100e4031000881c8111045840544181c0141c81c214032240c0b80c0440c0842c400102da08018442c21000540030b004040780007050402c00034050500d0b0161310070710f03a072901404045501034007041020503040602c00407a035840d0b218180d00d400d000d00b0001c8004030841741e201d01c10300001040004058000781d00601501d04450200701d800001c01040da407001250154031154424240010350b5803605141d0741800b8554840d01006401014040c0942058822403400242c0c225808108190400111004004c00b10100034424219910b0200b0070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 300317356 1250 300316106 300316123
    0xa120f0b15180c04050d03031a0118032409080705070b0a0f031d0a051b010503040c12050a060203101703130b13031505070806040e0d0e0109090509030a0f0908 70
    0x102d10070007800007031000c1d02440a031401001c1c054102c0282c003d41e841c0080003080a4600098504c0c02442d1210407940700760038031504082c4040a45041500f1a2201407031500340d200f564082400e094a403025000b01c0b80074400f003091042e09585d80720703007161030024103003080d541055452220a00a90241d40e51020900304001814140000c5a50000c3d080e0070590821062249940c03103882d14400400c50005414030840c0d0522200001000c102c500448091005503409030040380074080520581e440500b29911491086086946101559548805030381040f079810042440341001007003030b41a41c8000ca0028240200a107260440080c01c000910116002d007409070700300860941d81c03000c02c5400c1d62002d160099640e1801c41c07808110340001e8281100c0d01d10000f030300d400c045121414640280c1c03036115070480251544040310b0345d00311418a2030724003903410401c01a00005180320340c1d110361801307400030b80e01940d525000298060721000fa4400c0d60000c0002ca4042000455408120b01e01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 300318606 1250 300317356 300317389
    0x6090b061e030c10030b060705030a181406160606030b09010b1206070f11070801020310090207021f180f0e090a0b0f0601030e010c02071802090906040504020a120f0b15 74
    0x30b81d040205e004220201e40b158000b44009001001e10200001410300000c01c2d41ea20445501c1002c035541c0342c0c0102d889030000290741103118400b00d10f41a0050000381e400b49818000040d41c98490206840e00355000b41c5d00903901c0320078011505c40a02520003295400d80360303403411312101e841d01c580d1007000508c0041008800004000d481d8801c10200c000b40312440201c0700c1003070b01c5100c8907000754401c3e0742d540d803c100c3d40300d0b00142030f118500990760501d80081c402102c5070850b20070706040190440b8801302b040342c00c80122480703001c4024440041c280030700800d00b585040c42c0c4040d26008000d0710f0144298400403a400010f01070700806035205608009600b51500c0b8003005034003400101d1078485031542000580c40c681680012800111040700500c1e0081d4003042111404a1041101d590307001000342d00007c1fa03904081c1c0203260894409000803800e036070344400a8038660511030b4202c50707001c840511002400030041419420450555014052603205000202d04440340040d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 300319856 1250 300318606 300318619
    0x702070e060f06210609060a0305030703140d0204030c080d0309080d0c122301150f0c050a0b010f1e0e130c0e090c03060c090a1e0306090b061e030c 65
    0x2000c64540c40291407001030750300c242045a420782071300305141c8602140c40b140540b03480e10018240340303008030404003201d8004001e18584a500c0d1070803102062050310300c4200d01d004202110101020f4070081c001103002d214004142ca05020100c6d0500c070306000310344100b50030107100b00d0114405004884c4541521100042d41448404d000da03852407070f220007071a040c0d14003200c81540151458012079005a2001400f5060fa01c4803500c9201c0c511040d80c00c4001a10721085c0109240912803c40600380600201c0b00f4080391541c803c48210400d811000d04001c102d0f6003004422030700803507075040d00c0d0240c0c08000e0746411304140c140c0380b10006112840c04a0310f40e805c00180198038101e20050444200c0c003021628001a401c0c0c0d131080c005420764041c0c801c1c6000101c0c04100c002c151981048001c118504092030030703005004400040c201007003c2108090004002030540c0310b40b0f0300080c400c000501c180d20300b06003004a1451207a5210030341c0307500d11170980348981d00850040796140d4110380c2c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 300321106 1250 300319856 300319879
    0xb090105031f03060b011e02100b030304050303130602120c0c09070e0a060f1b0203121e0a0905010f0c15020d0b061204050105060d030c17190f080702070e06 69
    0xc240d26422024014a0710180c201d07408401d04c4a5034004030401003017a01d91b0340c031041d804501c001480c4143e03001d81c801030b0040454034007115030b00e400c2003c0001008085905254407100040e0542c0d005941c02141a9004d4800304282d03078050001c0c034600c0c5410103d083c101f10600c031407592996a1104194469040c0d00300043c0c981c0c1c0280819a40280c01070044540683c4400b03020b0200e0807a100f240700418800c25200700855940d240d0305402e1980940584103100b0a07410780030903900011882d08000508400400040b44c54002a00803d000c1c3c0c0d46900c41246484000f501d0022128039080800c4107034100c11000c01c007400000204030400d1640180e462900f6003604bc001e048a00300e06611460000f0002504608102014001c6015400810194569804104a00082143c014082070001d00c01c040450083e2403e004081e040e961750340d10f001c5440445800582e1100440000b00f1005505943c038268020707401e96000c074060008084090806211540c070380c0c0e0080840d44241c1a4504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 300322356 1250 300321106 300321121
    0x605090109080d030911061e0915071b0506072f030d0c0c0b070512070609290705031b0705030d050f01030605160e0f0301090213090501150b09010503 66
    0x94001800c142d01a41c848401c1402d0080c083e04c0410000d403540b0340300c0c107014240e601c0c1ca0350460380c082c2840310941100c9444400f440c10241c00814009a02c0310364a004004040c2a0a000382052840348600c180d00080c80c810340b640c600c040340c2106010310001c0c02440300007245020310f41d0602c1d212202c00c08005410b855884060108120066014021080d007030214903040012000303114490825550150740781d080b40321142c0910900600594003091012101011800003040e28a00800010032800c9194a4684171603005640011403401d580d60b2030601c1e100c07030707420b07040d0001c005241a03403840c203240c1104807205450b0303411a4102e10001031254100f100401c11100e1640c3d071a42d0500140c0b500030034034494a41c007484182c03a41401e0074001030700d0081901103912402e6417516020b200c01c5542c018054808021411240c041d90703070b040c44201598642000c070380028007400d4046500d101e549040da084d6201c5034040a00140c54100a0080104500684601d08820700c2e006440340d94011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 300323606 1250 300322356 300322367
    0xa0f18020415240e180f0705090a030803071b0c0b0c011d010501150302120403032c010c1d060307050c031b030d05011e210203030f030702010c02150106050901 70
    0xf0300c05102e400e4002c41c00d00c4101a184001003d420903a1280805002c41409001608440e1810924107000c2c2c6800500c250700d400c000b6613001400c80c50700500b40110300010800310384042d0425180c00740c003c41001a415441404600503c0d481440024114040c0d9a8013005001034020521080c001241c4417802d1078003584115224001103900190705030341a242540200000c0c015000300710b03003003000d80e4505806070003110340c078103403044075800c80d80c1d51a2070440081030310341d1840340b050f090460600c00b40a6410103580d4010b00071000014801c0b24420050544541c5030951000040d05600800350751360392070160b0ba8020307214109156103c03c09032a0f141548100b00d0038138410880c2d80c1c0343e54003120002002e040c0c80107106500308400d980394084c0b201081040d2013070f840e26000d2041d003401400c5030076003281468000741c1e005a059020035400241181c101b4040030041b42c00220811030542c0c0d0900618201d84147d0004c3d05000b00c000405120f2810140142d07018014000740310b03280750b4400c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 300324856 1250 300323606 300323609
    0x12110f03010e0a1b051824030102071a1b03040b09030c06011206050708160e03030910030905060703060315020306031606031406010914010e040b0a0e0a0f18020415 72
    0x2e0080d507803281082d103401c100c0c40703001e00c0d05804410134080e00440d250800f0459100070240d00039101540d580c0d2080c0000001d2018000702500c10780da450044c0301500d090016200ea50711852407066007411507101024031000042000941c41e00d4145001c401047c200112508150030040c04540341d6510714140d460742c45000c040440740d104400002484807100f48107044101d00c66413086c411911040d404460f03840041d5a40c06a680c04071003516603072406003042254414000d01640d052810100005526141d04920030020079207d0614070100142440440d50166032403d0411100f0300350313250300c804282d5100040c4090740c0d002000c0b40d41681c0c2002209580c00c00c8000c22580c05455010040107000076001031806000440003141c120360080201c1d0041d12104071010301000e0901c40110380c0201030756891500266074124030051612401c025101401d402941e0b5800b0b803c184444e42c0072070f83d03210310244c2000d10342104052803113441c43d00401e1150701180e0100303008244251720300d00c6d007449 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 300326106 1250 300324856 300324881
    0x50a110a05210709090e0c0f01050a1103030c07020307050d08090607060902060301030303090212010605310501030807021002070b0f0307050904140612060c030412120c170112110f0301 81
    0x150003c00c101d450784207080c3c00503a0f001c20380c144017400b00c1e0208a1ba48400e01ea007000d900050444120105510482c05421004044c1c43d04141070fa031011031150440d0b1050702d00b4040800001010070030340c1010000c903401400103981510300000d50380c5494070349004640ea503034442e040c0040d001092044d031303030401c0001d00c1d00105210768a584d00e16001d0001e10f10490128010040c4000e901014681840740c1c208540015080f00c515200c6401c8100c400b00460603240201c203012013081c1980704207842001c2c06103204040f12995a0a140104030180c180050307094115801b10340c1c2405418214400d40c3c4480303900d6030346151a0f4071240f40c02d0b1000e0007460b4629800c103280c1b0045044036200c840c000c60180500765503100030b03803013450042615001d080b10211000030342000881c00280840c51418020111442e043c034440d0303982d003400c10685082c142550002a40d40300800c118007001000d0a00420307030b50251013005003481d52401030441c03501a000b80315602004960485031801c2d005900200003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 300327356 1250 300326106 300326167
    0x712020309060a050f04150b010221031f060c110d1a0103120302040605090d0c030f0c060e01030905100e100207050313090c020a0b0c070c0e0901050a110a05 69
    0x200205160381c2d807001200c00002e95410300d00400c40f400c0c0c0c202c1d0442e000355040480c40c031901c8510850007000c0c040c0d00022034111300c02d00d5100040100101c032600a41d015070282c80b50740c3c2c20460088490214207840001008112100c00c0016642000d460101d40d40d00c00503504240e110706000400020700260040c050720700001c0644503071051a26a107040c2d920030f1240c01002c01d2206811400c81c09580a07000110b50100025144e034a00031090b420001e05c10a41d212085843ea41c0f144511034644400322400c14109405100050300030340c054003a03690a01e0708003c04200c588666a0ba03140002403000360b65a0758144072107400c0b003485404d040000821096640d4401c1d494965542d81c400c401e001d03401d100d6580c01168900b240d0080c5220148147d00170204030025071114288a0800342c115000c5c050100101000030707601c1d0500500074007510f02d420515150140045094841c001c0c41c04102a117000f00301c200e040e90701801e0f03035a0450203181a54503111000400000701c1d500c4d510703448a088 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 300328606 1250 300327356 300327361
    0x110307030c120203010803040306050a0626010b0316120c050603090a020406050f090c160f060e0d0c0c172103011d06030307020112020d05240a081507120203 69
    0x150507400c1955501800c1e03840581c04480031440808078002809926815001084100042012a041181c008214020014070719680d0751003421120011880f0b14a00c400703200d23942e00c0c003207420720650035910b10540c003900702c521400d103e102c18008240282e103040304507555481c0034091074408030405030402400f459502c0c10180c40440d5109400c1401301d115a08004010480e4240040308514079800074100c540300c2c0e00d071714040703040700d070402e800d40d4442d130056075503d00101e40d20520100015002c0c100020b0b2035290324800c1410028a14030402c24840744d0886800010190200081110f0f941d040c043d90b01d4101070405070402c1030f0352018942d00080300903100ca050004000550403201600689103000b010b855a407540728004442d52070b0b16400c00c0c4102da01550060034140b9030661121401407074424800c1d500c10855506540b942c0c105414654600e1141c0c0340384d00409014a004c883c0310705c8251030f02d07800b03076550444071319104c1c103600d80c00300030440c600c0c015441c0e0403680310350b60070541d00da1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 300329856 1250 300328606 300328621
    0x4030509040c03140a09030c08071a0a0b0d1b0e0c12100b04120f1a04030f021615020a0f1101090506040b0304020f0a09060b040e0601020102190c061103 67
    0x140c02040382107114a00e03003840410201d01074440e20102c500c084114108a03681c0244000c01030486450990501080ca5000b4000031548002001a2441003804540420307900700f01c80403000004044c0d00ea01850071010460f00c3d0744900c51409190707403005230340014034a00102c40018030442d50080b240c408001050041105100303018001c40820341d0f13075400742e99681c0c40c0c072070401c8001c520400448034000c000a001c02d1007212522040c00d030058656009212a580ea105444a40e00920458801010081c80101544011403098045991009010a8244203100c2d03907000454840c1c1071410b02c254101040c0c40e030090100690b40b580000050003130009504101030040d144840b0180000c010181c081090703d0b02c0800d480580784440e411508503981c1e5402d00c0050425404d215a0000e0061000030743d0f05614081c00002d882e5284099031558941945207104581c09400703241564014820300c515038400d07054256130ae408510304041040c00702d0409500424004890000d80c170800000c01060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 300331106 1250 300329856 300329867
    0x3080304020328060903140f0d0f050c2d0a08070906230901020705121506040501080607050d020702040501060908060601090609150210022116080406020c0c090403 72
    0xd94000e81c150707441d071040c0b09415100d012412103810901d9410a4040022840a90207010458400e081881c045800005d407201c0030b4010b110075103c0500700184da87e0b120603e40c0140c0c05000440e60091015007401403882a450003007100300306000e24484400703900105046111003010b2000200d007641d40d220071400a08150046030000007003001c107280018100d104101040c0c02e0120400050a500a0b03000749000c141d1044081504501c52075102207090740e54880f0601c00130300b0550003810301e17041c1145a0301001e103005195600c0780d49410010172021602041d13050f400000351802c1030b60380d030f9a5107600c802400b420310007a401c149000300224241e50401011819617005c0011074420340e03103c1d0011641c640f0740327004100000f101900c1c20821012040c100d201038100500590341c1212040c01039030f0481e04503000700c1d842041d600841504000144071116085446008124034002005c04041c0981a02a01c0100802c0d80054844a01207051203451245207004200e0301440c1000c0c10000c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 300332356 1250 300331106 300331111
    0x50a08040b19080f0a0b01110d0305010f0602010605030a17070b0901090b010e2a0405030a20120706080c0405060307030501140303090f09060612131b030f1b0906030803 74
    0x5111891965120885008003070491040c8a000e40c00803896485411240203840b11146c0c1e1414044a451003d0391070b001031201490969882e9000900c40d031401d200c10003a40034a90103081564505001807140741c601107080a11540c00041d41e07910548602ca082d6201d11400c0b43c0038000c40101800d100c5081c1d81034001079042409582203240e90390302c4110342080c00206450212203130162903e018214220721518103121503840f180d190400341d0364000b090901c18080421100368a1541845440200c12030324a07040c0c41d800e44500085c01104503d0703543e154441e004400500c5040400075101c0302641c8120b401a280c00b9226581703a04003514040d0140c0000e0180c0c1c58866000b0300b000a850600205803200d400340100201c5503215031f02c0c10310160391405081c540e0484030421251484e4440c041100d03004100c141201901903c0c030307091080c0c0e00b4006086c002155041c10034204080b95030b0304004006550400f56940c0201003030b000c44541d07070201c2ea10030810300d8107220b0000248802072020f1361 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 300333606 1250 300332356 300332377
    0xa0c0807030b130504061d030306100903030221160501051b0f0f1b0319081018020d06150201020901091202010801060f03021611010f031e09050a08040b 67
    0x48a0300c0e20346080d000da400e000750003604940b200002690300b0043d030304210340181c064540026002030700c07060100084d004120440380d47c0d00000620010741098442c503c54212145415448242103030745c02911409013052103545103cdc14040003c00d0b5007400300b1107107108405014110f0040a42c541240030703010869204402c2119800e4401c003c2424600b151611326029040501d0016404c03401c004540001c0310950100105454908042c00c00300014000314510ba600700c542c40001c80001815100700805041d203c25a10504000c29032070071004902c9454103030342c05610b5109054a50005001a501c00c10851800b00c0c0d50081103034044d0300410400c542030b43c0345a0b6150b180c11380c1d40d100c807030f10300d4009001600d07500041028a00c01e009603900030440c0c0c900585010159014042000030b080c1c81524403602021550310a076802c0125000a8115410b0511089200703206441d03049a02d0054bda100c0c94690b215a400c005080c4a004401d0f80c2c040302c01622a03441d03801242068000d500344d032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 300334856 1250 300333606 300333617
    0x303060b121e0402030d050723070e0919020405070c020a03140f071208030402220c030b0405041a0603030d060b070614010b0304060209041103160305011401080402060307090b030a0c 80
    0x2407100105401200d0f105903000740007007a80c400000c1c400c54060b44207080598203850000711004d004145010340b58000381d104801090010b007800381130070b108040544403034560f0384041d01d0703640c000c0c507092442c0b00c1103501214001481d5860340419a08a901e0a0740254048280003000c000c11011198490a004041c012209001d038103c0c001c5035a50140d000d102c00542074014040000350f486401107501c184040c0800d070b828003400e0b200e0080c034620038080a10094450344c0d0700900a50607c50b00f0500e0030200c500340454205901e131600b01488400000410280074000075644c2d4130204100c400e842c00c00369041007580e658140309406a0000309044924a04110035511049280d01c0b03054160354a8a502520315201c565a500080d4004c42c0011303003040d16809028400002000135511803031440b9062a0b0b1150f504000404581c0c050300901220310b01d99004400036684039424980c09603060701c0f420b41e2a00c032600d05035444d40c0d0550008401420010400034041c00941200180c40c0203510741 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 300336106 1250 300334856 300334891
    0xf071e18080a05060a05070504120c0e0f4f05070504060315150b18090f090316050109050604050a030f140a030f0605060a030b13110f070303060b12 65
    0x9840b8121100050503030784c0320302c020440c0d44615500080d0000c0685c10060720703003955412030801c1c0201d01001512241c040e8641040301201d000c500d01d5105220034a40001881c0c40d1645558842d03004000c59140480e01c3d8001401842481d0003421090085015410507800d40028100354103005808845c02d02071504001a02d090034000d0f807050b00c0c0d102030b072a000404c044680304010401401c2c000c8400c6604c1c0c00c0010b141244a0080c16010b41003426048207156100500c1020900030345882c030030300000400c000e200301d8003105542000284000002020046003045800340c81c2c4030310054000e002e000c0600c01000310008030b00000c24440e49603003400d100c4ae00300503038030701210100207110348004001c4002c07903505c87e510403801024900e800050660310383c000b007442c0e500107003c100c000c01d5491454290528204542c0050000003210601c28915260420815406110400c400300180465004101800b0380c0011000d4104020004d4803000c0381200c030036200406a4800e800806c2a03042c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 300337356 1250 300336106 300336119
    0x50916120213061413150f0f09090908040305010c080f15010e060306130e0304260307030c170304050c0406080a05070e0a14011701060602070e0f071e18 67
    0xa941c2e030007a04000c1c034a10586002820761308a9440c1203002501d050410192941c5645010310801500c145c3c0ca4001461046a1014001d4402200ea8500b8040c000034104001548548450203a49081d000410740700403502d4082218003071a00000c025509200c61074050542c0440350a1041c622450311000c1030311481c2840c00c07060f011804860020300043e1410b041c1e410004002d40d080740016060300c400d001410780404c1144e54041c015003080d00001010064181c0b4614407051000510035034186c0c07400b0307c07100c550340c03841001c00c02803d004182e00c05206216105550b908407429500080e9987d140600e00151a403011040c801d120300e2802c00040b442c80f00c0000e0700075606a100009000ca1802c040740281c4ea104002c5c505141c1c42d448030003444c8403109041400d4001c10200440602001150950f1402c3d24615001041198000b841c02c002d001019468290050521003086180c1e849008085402c902084c050825100f0b2008106809580c0705a9030042002d02102002c41d0684501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 300338606 1250 300337356 300337361
    0x9010e040c0311010507061d0c0a18050703241d06012c0a03031709060601050a050c010b040612050106060201050c0703031508060108031b07120b060a05091612 70
    0x640140c60494441e4041c000210800442c4443d1101410010705101541d9504401d507000d504203c180200a0424a100d80c0d508000a4240540464a8208050605100d081c2103904880f81030b0300d854464010440841c000e0740b028400e071030040122000d4001e1b449002e000000e803031043d0346400318821120320140034004c0e103c5000e00e2050b5100c0b200008195801c1e40030118000a207800c0b2427001044e04959528480200000c6210351240951b920045405c1c0002c0c140041c1200700c1500030b6030400c6a9a82d1084c11600750001901742181c40340c0444c82c040d07004005a4040580017840d10401103100602100c8405913284158000d008103034542008a09941d0706840f0049999410720807500002d000c4d030003140c0e25051000702c20142030355404000d03241c03003c01e9001c40c031360f42c0000803207070700042c0b00c481c054004616a400424559203800c44090a0f101d410304050003880c003010100c0d14070341e10003080100a20008103442000d08000058105901281c8804004102d01584605401c40d690 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 300339856 1250 300338606 300338611
    0x15220903091a0a0e1e031905010b040603050a080c03040801020d0504060f0c05090111010e030a0c0c0e090303041401020d09050d090e0606030621010c020307030e06030f150a03050304031109010e 85
    0x3d42d0740c0c4180711200d1041c8076155000040182822005e49503040d1aa1003c11070500300f8411200e280c010203203141422800c454003008102d00680c203104040c80402c0c0d001030f505003a1980088810750310405062a541180545d40140e50b5550002401e40003064840d0401c80c0900d0207030710200580020f0403480021100b011400001080701848041c29660003440a460340548580000ca6080ca01102c803501f184d208026607000700710407880d104c0503c00800031460280c208002000f81c241020b100721581c0e40070051000702541e50032000052104029016110020b459010510044119140007600d55003980300e02800200e03200703c005a00b2070080c410502801000c0c26440ca941c8070700060003000c0ca07030740d400010300c81c114100c07032000c01c2d10074811541c1008040d0b0107140c6035041403400400403141c03010164444d041c1402880b2451004055081d04840c0079071100848075100d4000c82c0201c842c2e80d10107800d501000c140042403114241014428410842d03000d00d15030b803100e544c1070022405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 300341106 1250 300339856 300339877
    0x9030e040203042d080c1e07120213020d050403020d021612110301020906040603020909070306080c100e0d052508120c0c041107050c010815220903091a 67
    0x20880692800240c400402240410242c0744c860700c03c0f0307603c1d0301055a00c51040d0800562152400180c07510540802084d080e440a000c1c02480345803078482d040107060400b000c1e111380d011b00441d210740510360f0b0480d060005094020310a610703140c02c0281d02e131044403203c0005800b038244001001e00c0750b003d003002a5000c0c0028100c0b035030080d854005000281c1c0c0c0031650159403c200210a603655500a80001c0905682c0035036242d00301d00600c480b804003d1701500c245804d003081444184c5000c902c070050000b0544050160f0070308c845040700c03103480c10902650032100c20312424082c041c000c00d02d26508841c84007200085020500001840c0d0070b588103010b6150001540100b843d04007400905038140034030704464103001c460b4002030444003121000c1040c40b030000b80b90820030000384031080c2d5404090910103040d161520800a40340080c0c8044d51040c1c91501c1200c07440c2c1c1c8480007241c0c54100129040002c5c803245e2502030005072850052501c2000002c54a0308021a18821601107042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 300342356 1250 300341106 300341123
    0xf1b020c030d0c050a0b010f03030e060316050c0a150c0305060a080706050a090f0b0403021c02090a02070f050a0b1f060906140702031c12140705030408120a09030e04020304 76
    0x400d0401c40b584031803084101c07114010101d45d03402080110b0350681c0031788058a01c0f0303296203103186409059030304000781c0c1d40c0c001d0000b0300800c0501441c441d01d260008840e414020303640d00752154039604107141c03110020108034004001c44d031600016840381c81c004940b03071001c10468450504220191085100b80c0d0419400800240813051040000c0c2402c0050303400c00c22581c030744921403040310083d980c01c040134440022508005601d0000c80002255941254a0614a01c541c01264200c0401003900e680c42d500021b510080160100445005a8015050b41c0008079980b8050704442006d64003000103000c6180b00c480e800302c2c103c126034225149520760013900e51030000c01f41d81c0700078855005403810f071060003100c015072401e0249600b070390400f000c102c0c2103450030500038003a951041c131440388e03061914042480741c0808440d4150000b44c030b800c019880341c0e10f03031626111510405808000c070001e60824441c1160658208410492090325210521502e003001d000c03c038001124090324026 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 300343606 1250 300342356 300342373
    0x5100c030b15032505070c030b0403120203060102060a020a0e03120c0c01050301080607030c0e190911090a0302060d0b060d060602060606091003050613020a120e070b03150d02040f1b020c03 83
    0x445850350131a00c885820610b0404101361658043c40310305900a562044880081004142e4410414070a003441c00c10118154144400000e59030f0380014804d4031025400107212171640c1c020f0032000032070000181106c0d40c1c0110301301003001a4200e8840b105240c45044031a902ea9030007241038a0603544010001e02480d03548002c00c80c003400320806880b060000441d0029103544465001600c50328000036031210a07450001450101e40e1010380000c00180b003070100d40d0031503480040c3c03101100d404035a040d80707400390400e0303040040c4540705039994803440002d0184100c4885030050003caa4041d000c0d103103255524402d0140c148a0314800f554029210000001d40d41e00a03840030750018006420010b03020000c100c00012a48040d4050022540c2e03d500c2c154980d00034002c0d0000d840304040a414014500051000d4601014020840003044140d003c0a9138a0b90140c0e06516a0000e10900907a040000000300034a4051325010003c0c40030702d407100209000050b06000a04050014020035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 300344856 1250 300343606 300343651
    0x40810050f280501060e010206100807050915040501030c0303080a0605060d0203181015050d08030403050d0209040212090d0c0809040b010e060a0f11060405071205100c030b1503 78
    0x2540d800040354000c9800e45000d804103d01c034060203803c0945510401e021648006850b00307000500d0700380e944000c10000e02c140080030074200200c60054581d036499450750700c001482000306011458000d80781c400004140075081002030200da00a840d4800305032201c3c0304480640c0e1460250b10b41001c17041011082c400543c7c1d0046a019004e140785407240d143c0032102605140c01c7e11841c4030300c5900c0c2c1040c2c4a41921a41e441002080101c60505960441e43d60b40105c07804018800340900401042000310108550100c2d0002d8900510441d9190000c03404114032610556900300c46102d0070141500140c0034103001c01301e442d04112542c0c28440c4c07030420070001d8210a0f003994100454a4104c072030310b445e010090401000030f074a44503140c82803000c0081c5003c2d0307603101c4070f0803d0340010b051001141d0003080001c1968100010342c40384d81114180540360a1441c03003920207840c50a01d560108990581c00703482144822590340840c1c40c03175081c08074100d0105613111202000f0203d40031242 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 300346106 1250 300344856 300344881
    0xc020108070905090423010c120b0301020301120609023c061e0a03021c0204060305281116060b040b061e0702042007050c0d0b1326040810050f 63
    0x2880b80c20044050480d01b519200c0c29a405010401d020038040e400d583e8002c9021b0107030b600e01003801d5008608640c0b40c01c0c0590f6240c02c02000140c00c813650b1b2000201551100003801c841c101381040416494040170602a00011201001100304204454104000c0c07074a00129461101c105400704490620013907554a15413100c844042495030800c240c503140000305d404140280c4c901e14005031038a03d062406025074400030484402108520040418101c85d552409480f1510400015450840f0860750ba010300c503012135080d4001c8030486846c10480c080d00846048141a40d05001c0440e141c0d082c080b050092210000e9004880d00c40030362102c0041c00a08107060000f403020800440d1101c1000c094400100c6409041c0400141c517404d1020812000360004c1c001d4940d00c08070300d895282c02c0300c8100064100d03903407d0388020061302800f821440d5080c0c08c00307462102d1640c044003090305c2c0156900905c1200418000e400036140015141e100c1c09201d0707060031a05507002e079180c0600409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 300347356 1250 300346106 300346133
    0x70f080a0e0d0c060b030606010c150204051804050c0118090509010b040903180f180903030f05090a0308010f030302030f0a12020a0503011706010501021c1e0c0201080709050904 78
    0x5036624001c0d064608001c020844051000b910380c00450091410500251104070b01c000f40a54405001c1c4581642c0c443d8011141c103405c501444c10f04c3c020880920064852540700715407103055400c00c1900c0c9100c0e0500c0034041c0d40328908079001c00d805407005480181d40c0c4200221a544c016404020b0307990583c01c106d5100c990307070700001104034400307000074101c41d8a00c400740c4c0064420103c50f8903505440c041203011340110f22410741d16628050f54400702000070b07150119181c0c1c54003092400c150107608580d540d5031004d04140243c0c5400403a031540c61803041002d6001030a00d5000085055052841301c2c00d4a400d0740c007a52074594416600d55242e4004140e442c200b010022060156010034809022003000c1ca03a11140d42e07500d000303e0010720114184241c01d0765003040c1c004010036070700040d408450301084000009482d00040d0b041c2c0b080744414049115070b00e401000900d43c2076007c0c042481d0607100340c0b20010b8503183c07204200c0780121207008140d00304032100046400309621241219 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 300348606 1250 300347356 300347371
    0x301050c190201111201031208040c06030908070c080d030c08060f041112010902030601120b010806190e0f0402030609061608040f120306080c0d022d060705100f05070f08 75
    0x380c1000b10304020788840c4e2000080d000003174502d500500c10440100341c424000703201da01d0110b4031410244c41c5d0403402c20070740c420002410781d117000d0001001b10761400d651403243c0015568130a40d944401180e20f070f41907441707c10002860000000942c84c0100d90460081002814201409403c841800001e102210034800b41c120300f4482c6600310100b81d4003280c041e090074003005d602e904044001404610f04407040310016414500340c0307a540d036403244140d503104908480c01450302c4a070100405500c0c4103a004004d043d0f00300c0c400c01101c044105100c03400b8520030f80403680c10740c0c0c4600035681c03240810707210102040c499a43c46001a8414907a950b005030040b600b10300b40840c56a079108030503c0d0848a100400d0311100100030204081c0800a03480109580c1100010007a5000950b07189004007085029900003950180050401d06004000e80000e0702c00f958500c3d4034202240c0c1c81e42c8414142d52003e04103c2e8006060195015141c01084662500110905412002d80e0300c44001803000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 300349856 1250 300348606 300348611
    0x3118120201020f07110a0e0613110c0106030f0b0c0f07150b06070b0405060c0c1504080d141012030504150e0301060b070c08030901080723030403120b0301050c190201 73
    0x22440c00032104020802e05102d6460050b10180e008103200c0e0320031b52507200c9811054600e081208580310b40c0d84803801e240303040384009209500400c0103201400b8041201c640c4d9860410003008002010740f1004082d4000e182c680c0b03141c0d60b182032510191141c45c01401c1288014044200011040c5080c031482d07003802d042c003240306c2c824000407078402c0c0c10210341030b14a001100140414080103001898210801100451030800351b41c1a483d0740303090000c0702802c0c05142100207401d004a86e82a202c40403c1d444050024800d1010190b8076900e0581c5d42544414805c0000907032000002c0350130068a0349500d80c0c0341070614003c0310720126448a40c080c1c1c2070005150015039103139801e110300310241c50200d5641d034943e00182000041c20303026801020240d80200411b01c62603812116096100e6070305c2c41d001a0001e110107500c00c840340a5200041e9040b0302005110801d90000c00380340b4061b000240c1040048240f004150981d10143d540464020081100300c0d041754540c0068048070041c0d0001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 300351106 1250 300349856 300349867
    0x8161703151909020f0a031a030309010c03020a050f010b010f030b310518120301050306010b2d0301140102060f071202040f330f030c0e311812020102 66
    0x18032050741d015104105c4074000000e0803220b000e8040c46078090340303da441150b00b0300d10b52500100c1d41e240700d071600943c18001e040001c1d000f01071003040307203020301640202a180b140040b0304685020305503c0c41e81c140414210101e480009102c2d104018000030300070720442001009401c0c40190140000600315040b40750342e040c84003803181d4010300703014994040c03800c00300c0610820300b141454840400d5100103c0c0820042120781d400003000350642c1c95040c1210f60381ca046843c142ca5402c0f100104d640400c801110200c100c400361001795041300d0b40000170b140800300c21001280c85a001326409880c2d0054880803c00351845914880c1020303540c41d13001841e01c3c0c1c0300c440e03000403807680d588560007150300e072901000c040b05c107111b09503554074081f410311005a40640700581030507000c040e40f6007019629043e80031842d1180002c422002c0d0090820400804545000c515480324440590600b02d40d0242448001e81c40d03118404103c10546079150071400d15644038403009580151240441d17409008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 300352356 1250 300351106 300351119
    0x510021218030d09030606051519030905073305030a050613060306022a07031707060501060513061805130219080f07020a0807021903081617031519 65
    0x546041d0324001c4c1c40d04100c403807461034240d040d40e00c150840c1380500032043c85000b880003170400381c2e0007050501030f038241400e0716070400314010025480d01400511440000103840c0c1b40c0210707940583d0320040104105c54005a90841e18a06104100b40c000364003040001c0d1900f990354015a0000344c01000508200d0701106c2d460b06450040e04203440f134641c0000c2c8410b02d03110a051100c0c092024000c1460020701240103030383c450710a480054a017488082c0d0010f201d0703c1190813a480d46034054010841561510300003440c07500103411030002c02200b14404500c803400748040001140c800c1e4011841c082c1410f0902c81c800703207880c090405141d02408140b80310600c00314104070303000023651420b07a1071900d4000812070b450042c2c5020b081d908080815804a00780d00d084070304454040d1a00600c041510480802c80412940301600c07905011030300c62451052a2013042c009409403406c1c0f1384801080840784010312050320124901c0794010b00c0b80d481403c1083c541c07120382c8892b070510800c81b40c1d02e00c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 300353606 1250 300352356 300352363
    0x4030c0311010f0c090f05030c01121107060e101419060f060e15040f0303031a0306070206070f171f08120a0f02010b18090102090402160309051002121803 68
    0x40300703240741e40342e132007400d06164488903000050a5010640c403045d0f1600380806d898201c000512030420901c0b0314211258005d98000c10707206910601002d9541c800703410800003c210003905a0700e1801040b03030384014800e1b9400742040c0c1110404107409030741c6034008190900d03200d040c240010f091f02c0e0744c4c0001d0300036001c501105c000c1003a0303102d4100d00c5002c0420040764100428194003000030501040c05100c1a01003882c0540c1d0b450b05000503142464801e191000200c0300d5415414030600081203c810b5002c075100707008040685554044600003807065442170309a00e01e00040c1c0064800080141022202504100d41401100e828135070329001c40da81042048150161405c0000036a045001c0d481107514007510000d20080000103680000126540d501c0150420550686e0000c526246c5080d41210300038040144119901c50f43c001d036141c00e107407540c0c805034081a45040002201d0a101c1c01014441507560702070300310303030300025080e0516800c2020480c400000c00d100c1e9100985040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 300354856 1250 300353606 300353621
    0x51e0a0608281406060f03010603090305072103060b07020105030609070c140f15130f021f030b0f01020307020108220816060b030111070303090203150f010f06140304030c031101 78
    0x14000850000d03540c903c0918030190260601c0d0182c8002c0013200c46109006040d00c2c191945494003040e2000c0700d007021a514040d028001c0c0203042803144a04900e00c44244400800505450a0007500e560302c0014440303000700040070380800c100300300240051804016082e80b020460070a4000c503242ca840e18418109c0030028000940d00c808010032900e05d082003e40025020030403510781d1442d0444603017046041340786008040700449260b0604668a17100904044442c54540b0342c003c02048000030701401c2c40f80015401a0758507980c07035100c0e500c048202c400440e010303110b554064a5248030b170342c1811040d403154a40d8614021207a00040c0e510b000400003041d088654081030403841c02c1c08000c480544038218880d80c5450240d0100301d8083c4140c48006070582800500345541c1e00200f820300f0f00c4059646c81e1050b240c810001030485641c1d000f416507400900e0880c0c803a480b01410b5403412031145950380000d2090000600203885090b038040300074400c0c50216802d400261005082d02c01c2b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 300356106 1250 300354856 300354931
    0x309011824030e0604020f010806010c200f0a21050a0203150406051312050c0312010303020d02060901021e030c1b0102040603150b04030605130804030c051e0a0608 72
    0x40601015103036414007408040348000c0001d0256810182d001900d403082e0031fa29a41889507103000104260700900c3d039640c440b0380040180c1420300316200c4514000d500165128420308038410403a080f41803000b950720560f1030300042400c2c1001141e0341c003121110015011100c5119608104005071001d020907806610201c0c4110700904061400e0411740b00c1c01070203003d85901c403084500202e001203400c0070040c6412700700326650715030032100142140302e00e01c10000f084002400000c201135000468801c0606281d095130300300e8407112901e074281c1c803420f824490040b0400c58103a8070954228000d5800c070101c284850f00e040941840900381d03016680c840003446c0d40c00709007040855094094008149010103101c04d649061074140c0b0301600a030300016104954650000d20100043c440300c0c11020b401602e5551511b039649082d08100e0f0f00e501034103002e4820040c00c060107803161606001a4180148129081800c200c0101c6166400401441980c00c010303640d030340780100c1603910b525800b00c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 300357356 1250 300356106 300356159
    0x150d0222020d0b031c0f090f0e2505040302040c1b030320070b040f06181b05121e0309060d050103060b0303070206030f1005130b03060a06050303090118 67
    0x3000b003916040740c8410190300c0c082d07000000c405640000502c001165643d81e03003042d6007a0510001c0865104e0b2854000b104d0b60302d100180401e01d00d1300f25402c58401c6008602c2c00d40c80e1030600400a241007100b80c40800496028041400149000d03089003040304c0c01d5281c0410507040720000080307003141100040d4003290f500c036404480d9001100704101052400a4100c0c68291156142a0400030091000d020110180b000c0c0d4200070464001c499400800d6140c0b0303511041ca8140818160070b001d032501c503142811000003070103003451000c4c00754408005014280f41c0c0341040c5203800c0e69a02410a41c1c42d40420013581001c0c1d6204006066000002a000a44c0303604600c0c00408684041004500c01c2c0d00c203001c0d42c0011390b100d2089070b5020862150200c0e50351980c090441071601c0039048103030300442030540003a503048580e0010f68210011011201d8984850840c1c0301150f2050040541540042051180380d5003c1c7c100c041c1e90f00380c9041d0030b403001036560b07862449607913440c01c1032210303200d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 300358606 1250 300357356 300357367
    0x120309170c07060801050609041d0307080d05012106050718090605031002030c070f03110303040f051e031e0904090305030402210606040c05161217150d022202 70
    0x2000b0100c060f10840c14186120b5041c480054001e01030894181e1083e510780c011180c500c201d10140c2c031340110050084a4450040b4a480f43e1a9000561051116032402c070000030300d907240d02c03040401c29264442110391b07134109817101005040000e05800074400f0f42c40d240540280d5610401c401070242e54000070303032103040004140c206800d0358600f8299074014030601440082010031120455840000a54000c000e4501034540c150310a6003003465010110400040c031415400a41d1154400c0d4240c0b180070080b0641030b08444e0001906080641c014001600d54156811003005201d514130700c6941480d200000050641d0800442240020004000c1c0000c60408170f07090f5081098001d5400324040c62400d82581e0341600074003480c881c0762100c00c4054010300a8048441401c2c0301c01c00c0c109000d0103070621002c0c0da010019800f0014a81c0a03134902e190042c051a5030069014041058040000d801080b0700390f001c0c0c42c4c0581e800440c60800c240c40980740c54203000251040d1401681380d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 300359712 1106 300358606 300358627
    0x30f0c07090504080711060a0f030b0d080301120303050c07030e010507020a050d1208010501050c06060405090304050d0b1906180f060504020d0e0d05070c0312030917 73
    0x4600c2e00c4140410b00c01d00e68000d15080d40034984001852080780107000c0f592061050000c0007035800d501013014148240c1054180c0764006000c00242d0202c1c1c1c941d55469070ac01c1e408220a24071441d1003104141e014000c0f140d1256000e14032500304100b50324082e146c603160b160014100072000500608543d10381c04d503003000d040b02030300103190031000745001c0400c6040342c0f032600e000c9105000000b840750300c14070859031a04004405000f0700d450304001d001c0a4a00981250640d010901c40402c158642c0c0c0ca1541e00d10b401407052110754200403070700341c640344001403105070090b042000a0042480c88440240050b114280019010b82ca00304650020555a0880d0f94040d000084d880800b0351a9080030502d400c4038415a0816040700e1002d449620910308001c2c6a40c0400000b000414800c1e95014851031141c00c010405120f01c1e6140304c3d100302c20083c903120b000400b05070501407 = true := by decide +kernel

theorem cover : BRFrame.Cov 300179856 300359712 := by
  have h0 := BRFrame.cov_init 300179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 300179856 ≤ n) (h2 : n < 300359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
