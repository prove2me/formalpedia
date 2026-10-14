-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2466
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:46.191695+00:00
-- url     : https://prove2.me/submissions/f4628ac3-caf9-46ef-8c4a-6b22db05f4d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 443345323 ≤ n < 443525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 443346573 1250 443345323 443345327
    0x2030601080705010e040e06010b07020303120124030216120c0501050c0304060e1b040216020d030c03020c03010b0d060b190e0a1d06060f01020c210f03072a0f0303 72
    0x200f4060b01340401e05508054a062400c0e01a4a03500c00210010b40081c0e4030704484034405422800d41260304d4002448004c00c81c1103a2070b00d0324001c082680d0380036400d01d46062013103559600a2550405c15004100d000d0040c001d0001031031540f035101413852116080b0800807503c00311514401840f950800050054000310000035600442c01070394108000048001d4840e40d8007050050b0390140e00207122440a00c1c5031550290203000100110202c000b005030740000c00e41c00403264101c01042c04100003a05140e41080a100351001c107400030414030b0303c0e840c0062002c00c981324000745038a03240c10710500c0c0c0344c50f01d1103092100f281c51038044140540311070544008200498868907007500e0180e503400c0c1004903104191102d90202d01070012600d40c00180b0642244400c43c00d070640c8600310a4420b01c1d194030071600c00b683c1c0c01d2a64080d45403007060a20382407002059844445078001e01c1000040384a07030030f0082c4040e60101600c2009480c070002904558001c4e0700c4a40001c21080740001419 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 443347823 1250 443346573 443346583
    0x30204051002010e07030b06030309090118051f090911030f0d021b09040b0a11030a0b01020601080d09300602031603060e060103020d020d05090c031c0e0105030c070203060108 77
    0x620100c07151800e080c0c00010032400c0f10302664490032554002d4600b00040f400080a1541280b0302a00741c07441d00320b210000c10403400c001e1744448101c001200d940a120045032140b0b41e080320700c205429888240781c03207003882084030f18054001c0d03599a0391b01d0300c800c100c0c00390800c5c0308104014060b11006401c0903003240d114200086103070050700902c0d00c0c1151805c02140701c01c03060480100042c1d0140c4071900d682e0400d040042c808101c0036078408100c00c0a590300d49c0614031400c5504c00200c1d8102803000020b05000060f804071049030f020b0240040007640100020b82500c0c60310b40c0c0d000c0e01965003c500d100540346100e40c0006400f042e4a8201841081c1c0c001b1841800c40c810510aa4082c0007011001c9500b40e2280c1810b060f94100400e59039031103600140100d0034903140150900409560303480440f8030aa41980c00f61703100f4540324102d402c080c44160f0824103200e50381d08050140c244054075405030400c10700e0400c50000300081004900d081a200300700d40103001c0b20019178544c400143d4030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 443349073 1250 443347823 443347829
    0x51f020d05010f18060501050a030c052a0111041a0c190f061103150613031a060307061103040e07090e090c0f060a05090613050d0303050f0601030e1f0f0c030204 71
    0xc40d0140011011103444c40c000d40084860603900c0034600a007400c1d084004100d0b40f030f0360034200b040422180d5802c18140894210f40d5402800400750079415050302d40c00c4800d5076604030720445060000304107800c0da404402c20074124000d40c040d17450103482085030034841203000d40a003082400c0c80840034007100024561100344616400c000c1d01910758a40c25850104980010407661304c403444550606040020303007440380d00080c01d208503a4480c1d650820200d080c12400714504481810014146401c0020340700510050030955181c1d051185a1a12481540940300c5e030440b00300c01040c03281d44100301040040c0146103018081d420034000494680d1070300000148560001040f4050515025040780d96204030350311214900700f140c4040c40403e40109000b49401c4260040c009403584502503000f80300f510036500010186400c17807038084220005420181014036254020304039800c00142c1000042c80d41111114001011098074040c0204c00c440740ea115041640c00c800c41605030300070b0816 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 443350323 1250 443349073 443349089
    0x20702090c0d0f09080d09031b0510050c040f0b130b0309060708150604090509280b2a031b040f0602060603060f072303040b010e0f04051f020d05010f 66
    0x1801280c440040f040d034070005000740009804005500541c02d96a115824003880307801c02500755880d00c3c0444015003601340082d2100d401002d00903800d00998810640e001c0060b001090802d800d101c01c02050128500440550000006400031305050a500703400007400c0c0302004555a2501803542501d84405881d541c010030b116001141e404881d4034008550404041d1005040901e0441040d000e000c0c0602110440d006042c5e01c00e1060b80c1d03800c6808803040600301d50016040351441c0101c0e000038001c00450b06007403134850059603003205d0518150541602a0701e543c681d16850a03070a940c0c0101c0010405440001a001500030321a00b816011952541c09455071541c0d60018152100000c072204184041c00000250455004500c45c100d420b070124200f400000d61076020502c1e0750710684040c0c4004c460040108118200381210b554048022a1401c3d02400d05540d002c6c3d076034007100e00c41e503a007500307001d904c000c284c21580c16201d40b941c2440301030045503918039070096050024003403800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 443351573 1250 443350323 443350331
    0x180a03030306030b10082508060705040f0603050907060e010513030b0105030d05190c05070b0d050a05070f1d0d1a0402040b0303180d081c1a010212030c0c01020702090c0d 75
    0x109441d411170061080b5409440501001032400001c0101c11740000340305070320040c0d03c00000c11912400c1041300d2103401c454959959683c209040040e144030198400b10826051104001008202140c100129061401d102c0725500054005a48600442c022044a07d006007400010b00c5180d0644504072601075007039038801c0c6201c9030100d800348504070310000c908201d02c440140c10b92149685501690058058814260311040d0f19150380e4001c1705400c4030300da10b4509100805100d4400e51b50041c11505102c1c2e00c0c0c3e808544050152210004008210301c42c0c90b8900c0e8254a80d0045d100c845688991440100d00644181050039141030790264000c62810190016a0400104580000d0900c403c0040b0b5400b0103020043e00400c1604210f030504828400c0c00c02e42c41c904030400c90b06079140a00070401001c20040c86107052005044141154000100d051040100c0d800b01c80e0407809a5207038aa4801c0c0007030040d03029104026000f5040455841000400340710f40b4090132400c1c0c48540144 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 443352823 1250 443351573 443351581
    0x50d2d0c0f0212031609080a030306090c091d09070b0d05041205070b040825030c151e020306030703140607080105061908060109030b130b1614180a03030306030b 71
    0x9a5a07030f0750000103060040f0800226050146013407400d00c2c001d881e80341a560306504c88107000d0400301902030407400b0903100d0400f03004255072030040c402c80701d1880c0361070841140b030000100c403e10601103035014044201402318444860900c4104013030003110250342c4d0340341d94105162000701001c407001da407070110094190348464414001ca5060b1a00419440501d03100d540300e0400070b9001342604034503010280104c2256095800300400014003a4491807002c0c0001e04168030617508485905c40510b1a01781c41e042010220400c2541582c0040d20042e120390719a8007007464200b580c1c0000c2c06242c2e102100c030410140c00203c0c144540c1841d0741b00016a681c80d4244600e60082544002060038649410049144207180c039036032040f014503002d055150782c1d0f25038400c0e00e881524100000000003002c1020321500e0300b40650021041003003c00481e54089000b0701d2010789042007100c111001540081c41c56601c0100c0a440500030810074905541c4d2801800500d4184030448220114500103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 443354073 1250 443352823 443352827
    0x906090501080c09070203040324142208071704290f07081207050c12070c030f0201050d110304020a0902070f0b06151801110d050d2d0c0f 61
    0x30314101c071003200c01010705218031003c0001d00480180110b08510040c000000840c3c00c0c0599400c451003841c800d4071001101005010550b10748008045040d1914424802c4901941000c60060805500380340c5c1d4007001840c092210b440303114000740072941595460b1030381000544c02801241c2c40800303813080340045005000b5002c021000e0351510f130301c0144540481620010010200e9511030315409261190404012502c0c3c030303054031080c1c0051008207180082000822910780c01e02e1820f94000d050183c80d0361100f188003400e000040c40840d050784124110390040080d60b1483d00381c404140088a90302001d40c0c4150030031501a885074104140000e8080782902c21142d000c2e401c0140f80c413001c145900d5a00c0c0803200600340340d420040303042015208a024201400d2030502000c1c0310000009420001400105034400112070350700a40341d0803602d2038100c03046550320046198003050f8601d68801e20040901c1200b4010601ca041d04e0003e2030745a000d5114103404a51038589041d050121001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 443355323 1250 443354073 443354081
    0x906060108160801030b1012050a0510060509060402090303070804090c181503111303110405010504022106010e120d02060106020601080a020d141e0c01020a020112050703091209090609 81
    0x14001083d121401030003c02c042008040d807000901103010003c81c1e80e8100b100404180c2c80c0b00307a5098101d000094200802441142d0313040e45d01290078070586080c0400500c2556015044074850b0741d00089032606900c0c180203483c5485d8201200c81d032201d03610664400a402d2611000000401d82c44911003071031a078890380008c5d60982800240040405c0f101580245098685869041810301c4002c0e6040c138000c030684007842c4140f000b140c00b489540d00f80801d403a010b802080c401c50040c8031210501510311603090402c95245803000e25900c1d500d0068580480e881da9507a0411940007a80700b0450b4001170865074007185d503080398000c0c0e0b130f0b03414105e803105e07000e0040105640080f2108800740c80c11585010a881c002c0c0700703001196005c5d060b0b00d842e06140d0400a0b0a110724a80c2242d65054207020960b00721a081c0058106844c2c0350307000820b0440304c8900d060040d941c40b000b00300c459201e80c0c420b1601c0da03800802002d100d0310503000a007401c1071601c030700650b81d070520201081000c00381c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 443356573 1250 443355323 443355361
    0x6030f1106030c0301062303070e040f021914070b040f05060a05090c060c01020c0f0f1606080708150301090318080c09042301020403060b040e01050f0a1505090906060108 75
    0x3c0d2581180d092620458183e00c030079019807450001e507d400c00b0074283c100005c60240d0216101c0c41f00084041c000d0105441002525081d010301c140440118a80b80b02e8203c40c000d101c5161480740c5045121114429028200300a80a504003000300710801884810388134480e170040c0200c1f0b0309961808502c030280c80c422580f103c0b850308152000304203810110090900310722000700140c103104110100c140f500c10711400c5148241d0003145070044498042c0904101c607600005200551401c001000d481d44038058204410031200000041242d908101603542c1c240000340248181c0506040c02410700c640d20490714092a42071000180d590000180c0e101c060b01c019000e145260b650351221001c51195100f0a00000592200c001d828082032004101441c4601030020700c0c500c0c848180012034a1519400d14140c5c580000e00c5640201351035910380c40020040e02007903400700c00e14092110745456000c02c2d00702c050300d001c0c040e21141c045403440c41001c080e43d50031526588d0200348180071420007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 443357823 1250 443356573 443356591
    0x504020414040f080a0e060d1a010c05030909100b0705060406060506041211010314010f091b020307150b131a040b011706010309020603040b07030c050c15061306030f110603 76
    0x41c0850000841c0540170b01500c0b030560900711422030301c0c040807a5441d8041540154100d682d0204014030740c404250240b540802032901d089012219596150f40e8031914070128442c83c42100010107285a220001d400340003040f0145445240a28180303544110030b441c2203d1503408c1010200b802d003014001da4088407018520f90084d1000742d19000c4484048100c01410942c0340c0240013504aa22107100b40280f840528100310b443c0307005444400c07240c00c500c085900340c440345800b135003069000040c1c0700602e0300200803010403c00b0003098001046440405c64004150303480e03074207126149600c040702000094242000042030300c0c0810044440720b0268a0105500c10200c14032210118503503603001006040000d5650740031f0b000214a5001200c00b00c5000503400c1c10400c034103038940652411100a03080403401c0010403d8015100d10242d803032070310024070074000075010703980300300c0400e0b80503a91601c2045929101e04240d03515401c1c0c17a9040e034800100188a049504000c01143d01c511508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 443359073 1250 443357823 443357843
    0x120f16050d09020604030f0b010632090a03140a14010c0f050c01020403061a120f0601061206090606090312050901090909020d050d120c0203090d2d0501050402041404 73
    0x7901d004801400070401c181d030001402c1c0401300c0001d00000400441030300a0800425a43c5400c00040640040b4460070300c203545003000819107400700508c0b1046c02c0c0c543c0204a0780710003141c00415408011a48017408089091071102d41c03c0002040c020722050080d2a034680e02706d2840d54050a0351100700c0d0580010321824003852000780304202a0060a5482c0b0000d4a0213940340c840005455650195200c00f80c2050700c3c107159460b18040d04411803280c4000f07031209041400700540c071088148195418045c40e150a0025000c07150b01440103403a03512010801e05403560750042802100b408200d0701400c40c0040d420b0001d000744292810854141c1d43d80031103505250b440c1024001c000e00407138218480c440e4403000120180000c8100201c40d58400b030080380080b40d40416900700c848640b0541d00108640c45098036108112604031f0b4105c015001e0714094031600107404030400e81210064103000014900300003040d04101d0040b03000301c40902c440c88200c83d1301d00d045181a14000c08113845 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 443360323 1250 443359073 443359087
    0xb0105010e010203070503040303170136020c071d010602060907090f020c0a0318050103060605161a070503010303021b01020d12020f0408010501030c09020703081308070206120f1605 80
    0x4944042400590103105803810304174155103440c61600190400c50100710b101c0e800307032100000d80011078010b01c180c043c584c02c030b65034aa490320500d600c007180c2002c091050681e800b82d8002d9a80454801c100038030101e480081d980d03040d041c0e4403641d002980326004039000c00040c10600c0064000d00502161000d0030409140c05200b04c0200149401403052680038071181960300300602418109078003a4903000c081130710000800c1d400550742e821079418145014418416580e221040c1c8003804050100d040c4c0060840c00c06a01305403043c851003951003820030401003070f01c0d8440d0155040724030a0b001c87d145040c8541c1004a2802d1801e40c09005a11415102000b2480b403120318a60b044005d80c01440c1c0b81e41c44407070f44400e40c01600482116174581c0c0040042128084080005000b0550308609202e00c95400505a40b00644500d01c2004051400380a00403c28100c0d584168014455543d80c240020022214542140d414440303680480026005e81420782c0760101303056090b07a6984c46c00308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 443361573 1250 443360323 443360327
    0x4080f0f0d0f0909240603020406020304050d0c0e01230a03080906030717090c0915090f090f0105130b06030a0203061f09060906080d03060503030a0e030f100e070609030b010501 78
    0x5009802c4400c0040200001890241c64414542c114041a480307140e08010f60102810030407543d806441050710400040040c03d5000c0203480039604125802100710f01681800d0210345441c1e044200084c00c41c10000a4480c2e2441c00c1d44402c40d4462103009050b01030404102d10514103100141500344204007000716490b0140085601204ea418452020720b82614030000842d421207003540140d1007403040d4010740c54582c1d84261312427042c1d010350303243c074004a0104001c2140a00741c0c103d08800c19010800100b418094010040c0c0480001c00841c90203000c45002c9491501054990682d400f0100d030791030074042000504946c01130010106074a0380003040d150b4030340600344030fa016041c4220115440030709000d10710091101e04004a40c0340d00f082d180c0c9041c6034141004809040c5015020003441d1400300035900c000d1500c0c1442d64611741d01a0200b81040c60510744a040740c02001900c00f070b010b01036800030382580880b0088800e02c0d6250001030741e004141c1d00016103240720910041000c0d41c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 443362823 1250 443361573 443361587
    0x7021f080a090825050a240519020a020307120c1502030f151810060801170c0405060402072a060e01050301091122090b15030406050a020903030c0304080f0f0d 70
    0x4040da29138018264040d1310f0302410708103000d108403220088850045182c102d01c0d580c540003521002d1042002d81070080d107039400004030100003c2d101d0b4000caa62083c40b07000344140e030803880e0850411281140b03000c0c0000c00c0794006020499282c007085002103202182882903078814051501c002c01039449a1414100201c07151140c60703444403a450744a003448a0303042d10b103402140d10b829140308203818004040c081c1c00c0140c000200a00e005104012103610000d10700c523000344142c50000315501c03507001140c064410282c000d46040221030b80d007000e0410700380005455409150300c1140e015203038030045132010055000380c0d001034018801800710804660025010700388089400d440c240160003840f401d500a050018031404d413984041000000ea0700410388009402ca8001000074140a03480320b2a01001d40083c141035901c03000100901c40301d40c121000d000008049a17280c480215189540307030700030b024060a600440302d6100400030001070903d50603008030050300c001c000c0e052044802d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 443364073 1250 443362823 443362867
    0x306040b03030409140604050105040b0901031b2303070602010b0a03111807091a03060d08180303040f030521120a020f0a0825090603020a030207021f080a0908 70
    0x5800b04020006204030f25202c0d1200e0100344088001403071a20008110464005a0005004600703240483ea01640e9410034076042d40d5010400d0706d46c020071482041d03d0b03030440342c0005907100500d030a400c602921185210034441e0084080700c0003240c50b03210803420781d40020412908101090340c148002482c0c003520b10a40d0300083c0c125006034035043c01098900c5825a030000c041214030f04144031078003200c04601c2401400100c014078500382080801e81c0d03542d200c400540141004606105501a4442d602c0003c03000201180d45030707501e03144940140645403004031407074130400d00c2454200c06094003000361003030230b600a42d0a0000b4800316110005d4010408409142d003001118a68400c07400540010309507036840a18514124039000c1220051140e140440c1c40c60410090754943c0c040501c000f0b0310803a00d03026071920380c400380a40c00390041800c000e43c00104840703030811054030745880006100755a030380c2560b00d8460901d2107080718800080a01490000c10800c0c11420b4104103800c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 443365323 1250 443364073 443364079
    0x6062d04033516020a0f0806010905070f12140a0509010e0604020d020603040c0b03042009160f1404171e10151e0311040b01021f0e0609060919080306040b 68
    0x1600d83c107900042c003094060300108001510380704140f251580401c00b06000d4460082e00b001903003055103024103000c050185080811a01540340c0b15540340a4100d40e4040781d206180002c181081c0642c01c0240c581207424010942c07901e184100e2440c00080c0290003290050543c0052502e560288440c1d136000800a0322124a400e800041c030080d420300035485a401625203c0c3d0004002c5201c0050a07403c2d10a07a2182d03200d8030501030342c800541c400c20380602c101d0030184542e896184050f601c04605003140090b1000c04500001c03a2aa4090241c1c9100b01007020b803041d80b06400d4440b09041060b0f00800d80ca5846940b0804e064842c44c2d102611529454a541484550b605c00c0b50541d822103642c0740380050804441001000030842c00c440340d00c10100ea080c0580340c24000006c0d80da411581004c11080c0e4409801c00c440e844552104030f40d0b14955050702d200f40340c1031305641d0781e0f0082958400b03d81c3c0f280c01143c83c2820311074104203916a502c112410300e56101c2904101c080c25001c003103c1c1c4c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 443366573 1250 443365323 443365357
    0x806031903120914060c0705061608060d0204110d0e01060803070302060a0509030d290105090d0803150904050a11030a0b01050103021c1505011d0906062d040335 71
    0xd281004140d104a1b00010290380e035181d18501541440b40103000c00c00075501905008900f25040301106901c95016609c4030021041400042c0207810101c043d5034070b05a00140b1400e031160310350844801010703010005e208159480d07402568a1140050240041e0403c801044451486400a607041690042107a080200000603e02261a100c10b140500c030401c69603902c40c1e10716280c220040c90b03000d0074018108107002020403604000c41100170b081200c008001010044071b0443e4668455000d41080b0491902e4600160341d903000f4581912107580b456000000c9203000a0070402640d484104050117900c2e10700190b003e03410100d26100816081007040711a02d07450310403a4040b020b004030500f407461030203001401700f21400ba08207486402c5c0b099603030000c1c1c4546240c03d422403001c1c1c40c0203545409174003d09000082070015a80150f0480740741034011164400544250f90007180b2030481b020500284144024107100d10608182d00099000c40c10300c00400940101310004010f02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 443367823 1250 443366573 443366603
    0x20106030b13060506040506100e030703080f03091b0a060309020f090a0c0914061e070816030f0206040308010b0a09090609020a091208340308060319031209 69
    0xa200c0e030212060749000903210080341c00e00030300d800b41303070742114007540c0070402400d0910128000141034107441c003c3c803840c0924010503841c20028a401103410400785034894030a04401909a401a02c485219205003160290300c04821400b09218039001400b40104500d04030301034028000c010030603607020550061001c916240c0e50300d454840c41c4e4a179000074200410880181c802c80c4107030400d00d0360203080c07040308049840e10011180d000c0755018442c0c8000703a4414241c1c0142c401d500e0010f140004c00315021a401900d4010305600d00d1180d03c2d130403200b0801c4001265100d8040350003030006400140100304591940c0000c007200031061400300c14450701d480c1c14505580d5a5484074a800d9030018000c2e10856200c0c5000000e4800e9100b075080404080d21b800d40c0900400e004411000050842961010303c4070794650880c410f000c01744010302d152414050181c100450700300313000e80506a01410120301c102021000d4a5064a07015108441840c0560040000c0d4004880a4246a2020f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 443369073 1250 443367823 443367833
    0x1b020405070318050604060c0903033f0510120b060d0219030f12021f020d06030b0f190506030717010f11280c26040b12010b07051c02010603 62
    0x395941c1d40200300a01203406d003440e00c881203070b030580310103010844641d07424800207074080d03007201c0214100c0400e00d084488000780c1d03000100c0c60151f0f10303600740203e0160400344c2c4031ba40c10203449294120143d0082c05e13500c2000c00030760030619070018400390071100001c0652420303031403029450b80050a2080306507004261510891210713041962121207010b0307002e00308120300c81300c55090340882c400740c00c41204004680c00e071000c0c005110003030541c01040c850540d8429510400086400c4200ba4000e4141305412419a180c10303a508005c90070303450808042035009004250003154042d00400303800d0b240c04542003542c0707101e8002d41d10700d54980e440302c1e024600034040c0d01c0704030314480000c40d40c1c0c04240c500c0710300820386500300361a020402045e44464070741180c194820340d604420303d0603440c000640210342070401c11448142c248800f00f4049110704008000d04045808850041c0240c0d803680c400c513583d40100c45005010303a201c00c00d1114041c0c5681c10942e10342c6110300010601940300e98032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 443370323 1250 443369073 443369111
    0x605101805090a0e0c100c0b040302150a020d0e0d090627030303060602190b010b030601050c010c021b120606041104030b0106020a061811190803180307061b0204050703 74
    0xd4168136007404c800c1c0700e08140911400500e08540100260809100292510f1403078a40034000d0f071028030004060500034000254104c903462a000d2980c40d007400400005e40045805d50203407840d1000b4512003102c00201514401610340700c407000300c0d180100440c1d000b03040d000d0407d8007513140c0040d0142203100c00300c600080c503c01d440c0840c68604100d0001d00e02140000704004038084440c1c4040815500a6041d040d58030000780a55256140707001690588600e4030300386001d40c40c000c0d101c4400c69012038040100244003c3c010980100b010800014915000c1c00d1344241d0042c2020460f03d10f040d5001080400e01b090310319013800d42d242c0320a82c0f91082644514050b07008008050200519885418242c41020031311400e001d8068803510f00d18044501114001d4012506214441102103c094024003081088039929850b018051180300302c6041414041d100304a000b007500c5001d0003c400541101000a511190003a02040007800003e4220401d0540e1250845940702107640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 443371573 1250 443370323 443370331
    0x111e030612030d0f110f030106030b01030b06130e0702010c080f07200d1205090a0f02040e010e0f0f030406050a050702010e0901030311100516120b0a061d04060510180509 75
    0x2a00140384003500c13035a40c042d5150070b16000c2200108010f80f00703003115a81d05030790540701c10380303000600c03030b02c51702d00503002080c2d602d100e40d41c0035001181e80300e07080200010b02003d8403c500c1081011b41c88004d01030707082c2c42c6e100321060042190100003808142e00500520341c050800d2801c92288a00301c0000c0c00c0b101400e4030450b013984c00030b44111064a410000c0f400042c4a4000b041150b0316002181c04c1d103541d00b510006003042d0f02d2000c44029540d4035080407804851589c02080001591880c44c0d03540c81d00d8600f004650b001c0c4a0440034241c02c048295130440301c041c1c44003403a08010341c0301207a40380d0017580102d050107075201d02101ca0b41c80f1010f1450182d44a901e84030200000b10404c00c0c91b000900101520503404c0600f040801c144168080784041250b051103603c42c4a0104c840003d04805920703281c2140c1c51800006080d1380c082d950b00070028000da0002c0160040c502400160390041c003d882d08800f0810900c24101d2083c601d0702520080406500c00e00ba8171800092a601c2081e5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 443372823 1250 443371573 443371597
    0x619080607110c01050706020a03090209090a02031e060c0a021203070e18070917070305010c08060108100501050403081c1b0905031b0d030c0501150603111e03061203 73
    0x4011100c1d030003158410203840b0b6000203280100c03050000924510404400814003900411125100750181e00403c2410368002c10b091010710704030004660b50f03900c100040e44a84960070424050740c403130350801124800600090403165680804070012580541c98180861240000082280101d400903500440c066503d480e510450340d810481d00c034003010000031340740100f00705004004d90003403009001c5481c00710003030b450401d10b120410304044007544054420750815079092f1400340e01828280c030030002602c40361100e0f11107045129060b820707400781c1350100700c007000140003040048000c0c05c0251076018402403040c4140c1c0c20f550603240d0071841c4803841d00c195010807104681102031603001c2c02c001d50040902444507490300d248203041054842c000c154442100d800e140c420103440d045943c01c51300a022000c0080710140d210030041c8180e1002900c0c10076000e0120701201c044403100c401c036400c0c0b85094600b001c002d8050358406810194040303020120500900c1c0c0a1000c0d10f0107641807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 443374073 1250 443372823 443372833
    0xa150903090501050a0f030507090f18051e0604050c190908011a090a0c030b180906060402040b070210020c0d06061a0c150a02160605090c03010b0a03020108061908 72
    0x2914000e801490550003190621006114840d1203a07480800161150001d241c0810300341c58030f2005032421043e503048060f44c001e01c1c16000c100c00319041c40744240450941400c03c020340e5104a0203503a0a000404055124111004600c151400c1d4001d20b030090010780c0003500d00b05c501512a02c040d00b400c4501c0021410f40c20082000710028401d40604200e00081981c1c80690140020a03c910081030381111550350604880d05501c60303440f43c174540303402501c82e510203d60340100c0c0d109100304550448031351140f07070009062402c003802034070201c900c581192402c10842d90f00b00310b070182c0f15401d000114810140000c4841e5907c9003411607041c0140340024001d42040e601b130351240003840950852000030040c040019900243c142a1140d0f5010880700301c1c0ca900484001902c01e1032601d406030007503c10b0b10828840e0580c0f0060080501d4070440301c51482d40c0c000e043c20384000440495201304034120400255008482ca0f82e4855401001c41003013986907207036182d040700309030403d00c069404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 443375323 1250 443374073 443374091
    0xf0d050f04120311010c30020705030c0307120302090603011205010b06270a0305030a080c0c2a09062101020702060a020c15090306041401150311030106050d05061302030a15 76
    0x1c0c800c94034186c0b07203843d16003408941681d405083c10440e003800c00c5080c0840c10516100003099054404255014080e41e0340d03800300d8019a5034170303004000d00b0b071120120400302541c0b0500030720031511448809403030b881c1142e207458144010303000e8100301594039540b5020001c45503035a500c001c1500c01c0c1c1212a14100a10580c0e210006001c4031000c2070061100303183c03c3c004254004246d400303582c81464105413607601c054003184180030341c203100580e621444005100c1504100303598110102c06140c0d682d1140e20f25030410503150390940d40c042c0c0010443c0c048410700c0e440d24400c031103401451400076141082c107a02140565000b0704003100103030030a2806015074a8070b01035174001c1030111003070301d401c04184000181d11814040c20082ca40740001104c3e00e240b1000703410010075400c4a105040307040366282005a401c0c03401c4224103210b54078101004c40c03180b4003419a50380c03440d00803000b40140c1e40c540304500032480341c1e454280d80c10301c2000900c01c0068800074a0350b01050f410040031551000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 443376573 1250 443375323 443375357
    0xc030503041a090603060405071b050c10031404060b240d05240f0d0f0c0918110904030c080d020a03050a05090a0b220302010605120f0d050f041203 65
    0x300b0440c01c05581400c000e042020780d01c2e50140c2e60000c0b0111400216502d0718101030b03500f4020104141c410404890741c450038028040340007a00c00c50140c2c0c000c404030198080480484009d01a6400d40341724450115001c43e80c1035101464096003d40301c21580600114030300810005a440c158103410b00003050829000c07240105504230b0b60401e64000c10790524081110703040c1c0c0c03d8050500802030408041991307030301e070705001c88501c0c4c00106330401d0016a081c4030200c2043c0d0301800008038140741c00c20302c07181641038404509907000400103404500750f900f00118068060015003c2000380b01a11000c1080c0714020b20740c0400040f801641d80c00c24000c00790940307200608a003101131a0a00301312500c0000f00f68146409d600010840301540d42000089102041140101c5081049079240d410944c0542c042c0041e64811511042d4402d404103032aa564851803411429a0f049111240c07030243c0180c0280c08148074103100e1604140e00c4810340342108180c20307c2680000c40355024001100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 443377823 1250 443376573 443376599
    0x1b23010b0310051009091a010e07030e07050d030513090c020f0105090303010f050d030314070201020c010b0a0b0703140405030115062003090d2907140c070b160c03050304 75
    0x1102c0582c091201d450804a81030411a052041515503a281d00c002c4040101d841d5150341c607481110414003007135031282c2c01c9400000c8112005004280380040d848d01196001400404440d0012706044071102e03259000c4440760048101402020034404000c00c40003102d0250100803181580104001d800c1c20000a0a4a83c050984044d0340c1003000180103816100a00c042502c405903842003043c0043d21302100105101c450380920541a030050044855042d0020409040484000d2140081d880f0800c00e8003455407003a42d2010710100300c0f010000303018181c00e8510202903010345080079510804682592007180030284e2004511400f44806030b0442c407400001c030300f001c110340112080c94044c40c0d96071082d0341c03d080c807818070618284c0070451120303811566002c525a0b500400302820380c148800042c10780f07000c0d011400d8410000c405600180c04c4e144003038000001050710750702c0c0201100c0300d5440310319080540380e61001d0107000b08540c80303900001188654002d6035030b1807030040c2c004040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 443379073 1250 443377823 443377843
    0x1140403090605030f07030903020a020301090b090c0609300a0b0a05010837060e0303250c0209060a170c0405010503070e0a0506061909060e0f011b23010b03 69
    0x40f000c2030084c0700f60f004090b07902079030099080c2070000d502841410143e1500c259050f000b5803640c20903081c5010030160342102c60240341240101d0320001000740130000c660052414064101040c0c2c0848002010b004c03214110300030501c0700c1a01c01e11015050300d81441c0c0c0501065a81274a00f105004210105204450041136451702401201c60740d103881c0982e02c401d443c0c03424000b1200306c025802c4103d1070301e6071502c150ba102d40304218020440941d00d03103d40040f940b4154031100300104000c3c2060541c125848070140e40d0720312a030815558200804410701912180e040b11420f00041104564110500c0110b200b010042010f80851810030094a005811950090300182d40400c1a02c00e800e20140d0098920a008285644ca0707001048043c051075403041c1c01d446400f040c1000068001981030256029552400410940c0f1002d101c15036a201e015280084c040d0f40c15021952250300707601c2c0c501440f95149070f2200f0109445a140405d0b4044003502503552501080079a1900b00060303604 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 443380323 1250 443379073 443379077
    0x30d1d0d021806240702090417070507090506040c08010905130f030305090717120306130c1e05070f03031d0d020114160f0507050c03031602120f19020a0503011404030906 75
    0x25a640044d240700035010380840203001c0e4035002e012504120382601880f0280e81200b1046e621410b0070700740745076100e80d05d220302658140303860046aa181458010584401c04945990380c83e6403034849100020300703005100d92019031070000c61000040054842c0c5800310b002ea03a01240302d0034003862090030002d240e03000c0c014490001d40f1001c2c10403004035500ca030f84101020741681303941d296404107030b9800640600004183c94007503100f014980000a107082d40e50040d0781d14404074410070080c1d07098450214060840d41d1940440c800191003074204190648415581d201c59020740e8013801d29000c600403001c800b50751074066603010600c1c4055515400444070045840030107413448003504c0591010599010400009925400d2050400c590081c84a014040b40e0344d03814004d410180d83c0034510412072003100e030000302081c14000042c0031001c08000e04041d0401a0346020780c0c800c10801d440301241c11010000001869540a1080c000d02c0107032601c503030720340b403a00e0b180040c401c00e443d81100e41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 443381573 1250 443380323 443380369
    0x21090a140f03010605030d0c021906030501080d0c0f0f060915061502120405041104180f05062e0c0206030108030304031b0b01031209030516060905030d1d0d021806 72
    0x80f5a40007e11f01a0005580c1040c03034407211507002160000c40002c0d400c28525a5030300f00090401da240c0c0c42075040b55046410740d4150b04915100700c0f0307144010301c4098100d406006c0c1e0303000807500900c2900541441510006100d03c0c0c180e403101484805030b40b140000d41c0d6984002c018485080040c5411030106202501824402e5800105140a103019460040d5661840b100204e5007420465025142e415140c3e0f05440d41c1d140c3c0c610182c0682c00311140c0441c00c0401041c210304010a05800a400d44440e200340d2003480759082c1c400d00100045101000720855840015880725030085001e05241c50185540703144c1801c01901400840303090398040380c4008900d00204005d03680250540e40d100304000100307105035100301c031001015000509580a207201c900380c2d0391030042c1110121044c0c1d49840d80125a11020146c556407502c800c0c0001c91200380f000c07413203082c0e444a10052900c00401d920b00e81c2030542c003c0358040c541803400c004010100414862149031402805001685844000c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 443382823 1250 443381573 443381579
    0x1b030606020a0c090c09030b180111040b120709090e250308030403032c0a0c051f11160f0e09011e0c02070305060907051206010821090a140f030106 65
    0x3d020f4407690720030007001c1a039440302000500d1051001e0001143c02640052545c00e01485100d0250001409140b080d1300c0d20b400b01c6000200340040d5400c0b1440f550b0740905124180b0312112000e6001400e55080101d0054003240240791303442a0300c0c0c41c030051002401c2030021000c0500644071042e1440c45c40b03072106030041001840720390484c1e5005a25207000700b0703062071049039026504101c00d410300902d601c1083c140d00340c0e500003031100602409035110b8141da03941c4500303001806403903038403901d49040346c10214040c00c0d0144803c80c000042e40c80c00c0b904e02d100c1500003150090901c0c0c100050310034001c03008010a001c0300c4100c0d40c08c916000001c101644075010b00319150540c41d9000d00c0c0c0d45484069000c031940c028801d540c000c5401605950152034100280c0d6107824440c040c15100d0000042616801040000d50905aa124600509145414030b19100c80342901c1c0c00b407421154420000140c42e42c5908145400a00380e40070030203000412001000310301c4003a080494000e030b14000d810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 443384073 1250 443382823 443382833
    0x612070308070c030614060301050a090c140f060d060f0b040602100b18010f210f0809060d020a050d0b0402070506040213020d020301081005011203050720041b030606020a 75
    0x508599111070080c1d51800381e441d004104035070a500281002c0d00c2c003110451141c0804820501c1602c048000f04640d0b9600c00060044541442010707000340b4401d139051250544091504414800003802e808141d2900b0b40003403441c0d03101c0001d1003025a01d030b041c1000400d130800d8013800500001c00c02c441c20103060040007555070f2005440708403000d803142d800008646408003070b000e07480340c403648043c620742e1558201c0030600140e04c0340c48840171000724680041313124100c2904c0e6059101074410703407290240d03e81101c6a00b1003c1a0b48e803040f01008030100078000c0b4801480c880420751540d50710f4500080704030045501003030549001c1c500410180d000560045000b41e800366040703805c83c012400c201e00403c003d00502100f11081440080040303200d690000b0030901001c0300020a21491fa02c408071040c0039111020001d0209105020385000602c41c3c11490107426112140c14041604a10000781550f101601a06c1c0740d210004602480c15414050480a0700181c00140403401c440e945d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 443385323 1250 443384073 443384083
    0x1202070f0312080c09040e010b0a090e1e0c060a020f0c010309120f02010b040606051b030901050706020304060b04061e0f08070501120f05070512010e0609060f04090c06090602060612 80
    0x10300304008080040c80030030038130301076983d9020f010304100002c0b00d0b00200c42e80207040a400c0584036140e10040010401640d0140382c50400b501c2e00602001c0c944024440651940104400207d00992304640d909840b240080c107602c1c41b25900801500c0c82c000281810405000c02260405d424216004085210651440403041c902c0c501243e041d410110224010044500c141d60300a003807031400031b20103038494003a01200b000c1095919651440c040655030364859441c40d5804680c091010001040c821b5029540c018003d190110383e420207200000e080f01c8054104600d01c0300003402c11115220320b20f0000c0080c2ca505071075180080d003080e03041c55640407135104084c10007041074400742040115030805096a005000d0a210a0403d180090000d41000850b0000240490000522614002c41d003502402003e00500d0310740c2c503006c0c184602d406492844030340042e00d400d0700c1000188240c85080040429a40b4800942d080600090401c2c02c01303001d15100f1122079401440819001c29 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 443386573 1250 443385323 443385353
    0x15031b090a120201020a12050a0212130e040c0312032403020102061b0705010c1e05030f180c150d060501030501050a060c051204080a0317040f0b0903040902071202070f03 75
    0xc8140c80e40d00b507880100e1800703800316001800c510000d414807a190307070000040c00505200b82c0903224014001c000c480f56602640440003180441a94108250000c14444541090244402801c0e0a40b40d031100a04540d10340940b50009985805040c4510705206040b01842d40704060300d1340d15495600000e41c0d89038003801401e581e006151028880300803050840e0005075102009001130ba81c0428060a001c0e950a004051071000c00c05100100e0301c1746040360701c108034200d040e0200f1b48070303111720592681604811820a2040502e4014265140e1040c0c40000300400b1038680c1d80c10300700c0c20080c00e98070260f0249043c07608200050106030303501840c007420344081d8070300305ca421806410141e2400c00688000c1c1c5c20500300050200317400c800802c4a410240c029150828a000441c07000a88a201100d0107022142c00320740c500001030000422036000990320080724102900c90145004a074401041107500100c120940365070b40da014404440182003070620524400e02c0c5855030000c00e101c4213 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 443387823 1250 443386573 443386589
    0xc0117061311090d0b06180705041202010c02040905010b01030f0605030601030f05010204230a240e061309020c1509060f04020301090c120c05150d02070f0215031b090a 74
    0x385003482d42c2c0e00d01c01c280d80d251000280400030204080c204030900800695440b0701545600c0e0706080680f55200515000c0c4817140d840354030300341c0f50441c02400003480d400300300c1c104a013090304140940c2c1d8900484c00b03401d0140e000000c0021089001500326141e1103600100103040c080d003040b50380d40c0421602d0440e50040d0748441c0301c0c01685010703802481141c0200c502102c60320000c148800107420010f950722025070b070f0030b5000c54449014000c001c41c007044500103405000002905c061161824110103080548074904003c141200c1d504800c5e0182c0084404690100380344119850400c682e11151195400c101d156081c20340c0c06caa01c4200003054824445d9000d800b00702191800d622040b1502d80141004003032545074000250032070b040400664100e0f801c6400440c440c5800701d171600d134500d50541010314140d104031080000c3e41210768240c4944c409041c1400241c0c41d09001004034801041c2c000d5500e29180303155401c0b01900015420a441060001040d42e40381ca0500c4419900c1e24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 443389073 1250 443387823 443387831
    0xf0c020c012d080a0b030c1c031205130501110a02033403080601030f0b010e01110c040c05120114060f0c1c08061e0307090209011b03020c01170613 65
    0x20882c1c1201c800c0d40c9010101070000101c50400307545922211490148070700b444280700441d062010941d4400c484ea950ba54456600341030307004140c7e0010f4903105680c0c842d062602000f18040c01110848030201d500c03211340222480004d04001c3d0070311403010212190f0380c0c3c1c1414041d2030319000b5900e0080a80104d00241e050388607044803404100c1a821080c44c074107002c41036031301c64503000784582815914030b40441d08000a589a2548038050380d50041c5040c0e4903100c018001900441c0c0b00c900101060701c8034001c030799000602d41c03038030301600315034021503102c95560300c0d83c41d0814604108146d002900461311210383c89059078918040324080c07402d05c4191910350795080d01641c285007162520300105200c03441c02c040c58581003181903205d140d013118103204141a4240d08450040002812541134000303820510026040e41e000c0c0811110600d01064180400708240481c4801003a0903000750380f00c83c07005075403583e10003d000c1107038042401c40c102600b051000706031032800c24142000b0260716 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 443390323 1250 443389073 443389097
    0x9010e07092327070f12050a1e0c03050a0308101406210a0b04150305101a060f0c0106050f010c02100302160615050d0c150207031202100f0c020c01 65
    0x48a00501610a5074204412111940c0c01c600e61340c400c0c0c1842502454440c0440c00105a07409025030040b20760000003503c00c840807550b41c407943c4082884002400d0902c00704810100310360b017540202961013100100f1401a0030300300549103c0380100580e14681040c2c00500c1601004020341d802198156481a11060110240b0840020390140754181801c01401c0100c900019006954444816a8200040000003200316090f14003404081c0540d03001c0c43e51405040f1959000c07040c00041d40c2c6050110180c2000000d00c0e1380d01201100c0c2441c82e0120301c40300345032400c1c41010010641140d0390812410b1702ca0002c0d005040101011b4451080c01d070015540c1400398046401c00c1541001c10312408103140341440040c594900148030000440f03802040a040081c001030205401c01001c94419150851015086000610030350842c00307132500000014824030454001e1503281d4002d4190320400341c00f034030112000840b80c0650b40703061001c50b2500540103d50054034050a00c0c021800040e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 443391573 1250 443390323 443390341
    0x100c080304150e0606011103040515071b0b07030e0103050709031b05041d060906040206040302091005040212010303020d022a1215090d0903120507031709010e070923 73
    0x85024400e41400d800d140c0290009400404d00034402c070000d8072091440510741303248035907a000d40d019a5401400c1400b00b200c03510400e01c00340140c0340c482d2040e00b40e05999417036491031144d03580e0b200b20051140070400e0020550002100c07801c241d42841c3c1000b00e460404001840c100003840003400654503a08401090000307a000705e006003202900a10806c0140103a000030403012801c0d2209500640b000310350000c40110f43c140c05540c00810711800d1038110303020071602a001801c0c48400d56035090340083d80da103843c00680310100380d0b24800002503245050103814800004541e03c21500450240b5075031841e9409a80c40038200103c01452029403e800706901311210403115406e4840c1c0c03080790548a03032495000b4821099007003510260400702c2c106964482c000d020040000740c00215144038a032065001d4818203000c0d15008004131071440038400700220540b01061165120800700d80300701c41c1000140010041110100001d0300300b11880312100346034a507106240b504003800300703e58003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 443392823 1250 443391573 443391593
    0x90501020c01140106090e090705100525020f060c0a030503130816050111040605040603150b0c0a050708032502010c05030d05011401030c0c020409030504080109140606100c080304 79
    0x41c504001c002c0c11441d1641115542d900b48180000501403003804030b030700d0a14040050140340c115000303050b01030503c020446909a002e48113804c105003404500d0029503405920074105058082032603400100b4010312440984442d0040d0151400700400515030a00003900010a038062404a840341ca40e1100b010003400e0159014111000101c1c0c00c0c0c6200007400407240c0310520800080055259075804001d0b1401144110404600180420000c0b540203401c00e105002c2d85800d0340364000d465889608007a0804050551a988542008000c00404002c42000b920900c8015070915229a201a0640d80304400441a1049408082c011640503840c18001c640e8408140c80d00c0340b0405800c0001000240325180503120040c90410300755010348100d845280da107a1700e4007013403203c58003800041d140d035940403402c020042200217000d900a202d0041c900c0d1280005200c0340c052000311503c0c040c6c000d00303440c0c49000640c0b0321003c0e071398001e0700841500794065000d50300d030b54403420041058 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 443394073 1250 443392823 443392837
    0x31804020c0706030b090105010816050c011e0f0e0102093d08041b0501080c2a0304090f110a08040f060c080105240a050903010b06040e012907020409050102 69
    0xa4418210702003800c1340c0503001545295001d40d09410103030323a14401154a2481900c2c0b030f01115061075009804184580020300442000700000b0070600b000701c96100300c8103101010801c2c03090340c6041800d408041400b0350000404410000e609010740800020440d078150051100400c1c44046510f9410305804240344884044d595942b01841c3c0604020305490012513084401d40100c075140713020b43d0f40707044029040c0c96040e916052283d032840e4a10318642e00001c03130782d040141031261302940b0900038400481081d944001944d01c940c0b91121490555002c01c5001012070b040c42e00d00032940607000b045d22080c61407440c00301d140ba10b070342c24101203003084510041c2c541070810311814000354001861034100c41040c1c800d80d072082e2503280c111407a41c0101c0d501940a020070400d4000780c500c80e9000d40908900180001303400c04804000405a500c65070045412030395000c010080308140308001811140060b442441f6103500080400580c030820341d00034421a507a10030481401000d43c1983d03e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 443395323 1250 443394073 443394097
    0x304090902130617120a14091c2604050607080a1202040332060105040507020f010f0b040b0319170417010b15130b030603030c0d030c17010803180402 66
    0x9540d01c82135440c1c6405a1071105050a1041d07405c50f20701031202d501110180c4a44e5502c0303801e0110b01c0b10780f02c0a20350045000d180e200f4200304107210100000880d0710601407142c02e80d03642c2c02200c107004948078000700c071124088483c10700082182c0d4590b0000c9171003042e4804a0030360b64401c8590141c515102c049031030b00c2800e02c0458040100051a03002c108072900c4184030001c01d02c00d00c4100d18203502c8943e450001034004000401c01810700303820490f0800341c5801501e59040a03026640e086444100b10040b1140d00c0c0c10321040d6070308051161611001c000d402a01c00602e103d0554400c035031070114010418071f9610380201d500f01c9100d059801601c1c6400e0020600710b20f40110700c2c00ba03c07602c40220b00c182c036501e01105501103403400b2140c82c8030095416008190cd01901c02a841c1c2001740b1440d00360200701704801203600b09000c04c04080e12552000a0312012a240090801549070921034020890710014000303000d00006807194951412080c40d443e80c81c14010801034041d1000c4051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 443396573 1250 443395323 443395331
    0x20d14010f060315051c23010204090b0105040303050a110118030e090609091902060c07031a0c0301180c021c0e18040b160c020d0807050f0609030409090213 69
    0x1001500240700804840d11aa42400041ca80040180ca506040c0c42000d07840110355400c640e04403031400032801c4d441d010300d40340d1188054042540c141c00e0303021400c00206940c002414025100a13100e01050b180c001c5c0f130040e0925096990140051007030702c9455041c00600314103000c0224003508041d0090400d000c10282004462502500f110300764080302e4401d84004001500d81d05282ca2070600c81c0e650800100b108000c0c0c00300d6090840350380007051b60040007c1210f41c20340101086241c004511411455440c0340c00d04005d41d000d00005448000c0092003000100000049401008034012000d000000e81c0782a640c0241d03c0c120030402c58002800312040c000c0407052304014501484c00d425208401c040507025001880860104d0340148002c0c2040d010030660201906411a036014504049008440c581c0002c5e03d00c26820904850f00070780021988200007007840b4240a00c1c50000080c505da0030b00c1c01466440b4050380c0900421242d64116a0040d503442070604040c1e1854084104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 443397823 1250 443396573 443396579
    0x402120a0807080408061f05060906041d010f09111215090103082a0a0308071b080d0b010201020324010309150b1206090d080c0405030f06180f0c04020d1401 69
    0xc0f01c580040c0b086140c03e0140700c2c000b4084692801e070b4411034015407050280c0c910309003001c022854100c4816645c00c142d0500c4040380c034525042c8402c5000300d80581800c02980344c06d8030b07500119034a4010b030020303c1c10180c189000d0200b0b0401e4507801004c1c2c2400340ca296071108100c90340c22100320310480c0d00c03284d050000001d101041c0300800b5200200f5100b01e00d510b125018500705403008030001603140d1b12442c0700c44d000c01d200310980307034000050740350051100384a00c0084080c00000c207800c1d1451000091801d480030010721900c0c040704020f000940c11440c10f0480506461170600e818002000d00c00c1d004016030b03100781e01c2040f64a500400040d56000308014900c01019107c0c0542d008140c000200d41060a0005a03207100d24181401001c041d014180111882000078018114000e03013031201140c0345c0d605108107031551805100903c070038038002d03800c862044281503c030403881e0070049a001c03954601290351800400d09480161b5100003071b228031030040a903048168101000b8038004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 443399073 1250 443397823 443397833
    0x20d140103020306010b1c0c090503030403060b271302010315060c05120301180902030a140d090e010b2b090302030a020d09120f0f0803070903150b03060402120a0807 73
    0x124107980c003c0d412502181c0c0c807190340589a101e50f8012030081c800010014100300303040d400c10a808041440d01c042290383cae9070b001c02c0c42c60b001508200d0300652034040710545030a01d1040810142c01d01507000c13100d10442d0324803038085500589482c0044001c2142ca00559009411070110810422003a5055940d118002050f10101520441f021b010315a840c81c09441600290380c10785050392500c02c800880c0005c41001444d000b401260180100810f602c0810207001d020068034606601030104007a100c840102141e50580084009000b980c00620611031250f06075407104a00001080340786202c5a003e54a04030001c0d43c1c04001030904203c10201940880607041d081c510303800f2100340c0e9218040c266500d801a0140c0b1807100d21203409078001c200090070300303c03081d80680c1c840400d12016440f68802940101c0701c10700402d01903c010400c00907015540300c1010300d240302c10045a00104002600c5150281019104100300e03140305022140c00e004114046502190a6a6a072a180b1340303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 443400323 1250 443399073 443399111
    0x603090c0b1801091a09190e010e060906041415041104090e190201170604020c010f0c09050108040b0f060307080607120608010b03060a0f0204050303040f0e01051012050604020d 78
    0x890360016840d00b400040c01da4030303200c070104450145c0301e8060a2040310001d0102071108469100004803642d000040d11160050546000e4200140036010300d140170304c14098241c01c041c002c00d018601e07007031804030f40e14218090150054003105110b084c0d40c92000005000e07004201110722803c03000100014041d04a5000300100034101c0150344008040882040e02814208400703804600c981840801d50b4110000c000d50010005100604104001041c50708554581e003030b0817807039075440030920201604400520000c00092030f143c6140c0c030380380c0e4034440c600e007020303000440144005010403210f58050001c01d0140000c1402c1f50294a0310110050110700001c26a00605141090224512006018400c1500c001400a190640303400600000820000c984501626420710001c61540e1302480207000608040712003444050030311005c40030f54403042c1c2c80940b044c00340c0f409440c1000c2d0403042c1e9078dc16180c00b4500003403c1c0d0390f01e008103003e44192000541100c0c580200d054020b40c0760342d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 443401573 1250 443400323 443400367
    0x3010f0213031b081c0507080703030b0a090903140a03020906030403030501050405060d0f170d0903020f010c18030f050a02100c0501270f021809071703090a0603090c0b 74
    0x1030b154098943e150314190b481d285800f80b19896084800d1044010012040b681202a0980f90144c07904e200754850680035000010304070000303034442000035254507190500034080d1011010810100e69695005003107c4915540c82d003c081000c101d81d101c5c18081e80c11307910400c0c0c0141106981e442d01e0b2130002c0040600b4000c00e44a42c0c40e10022035034900b407884d6801541c039484400d03400461010b40700c581c01802205e0085145002c1000084c0c041000340c001c21000c07030700c07d03002022000e84d00c0710742509680418004c0030812151044001303580e00b03009120000c980e00480c507040c400700d4a0804604103078206602941024000046024090380076207007110960199000b04280d4102507000c940042010040084d040e10600c0e41b0004191450940615644020720001c0190b040001d100590002110301140a80100d0000c1289083d01d01d41c41c89002098400365292500d4400001c00088550207102c0070565103e032000c0030070500620030070261050100190725800500700380c0d040006944 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 443402823 1250 443401573 443401583
    0x40f02280603021e071104060902090312030403090b07060212011520101d060406020705070e06010503010e0403230409362414150307090b03010f021303 67
    0x2903001800d02c1c0700e8800e9070502d0912165480a91401070b030040100d0700320150640b030030409000c1c0d02c00603075a00e01c140c000404000202584070454030003007500304100c1c10400c0e07600ca0020410040081d502c88a10026180913200311515030201c2d044c604028042c180030140400350200010a1480702c0041d0b6092480c01c6641340c003031509112484100708612036500c0f50156101c450001c880008a8224000501102554030750f0700104e1007070246003900079941500e200e80c1c0020410140724090210402810180840425a01740305c0002006440305116054a801d4608042030416208a003030302c00035400c8100ca0030208001101c801e1090344140700d140c240310b107004a850000100443c3e1a40b010014683e034045004082035141c002c6201036000700c40d4403240c1c900741c0c141c010fa0103401d0001904121070000701c40c00301a01000c1c41d0b10b40541140d0704060a000e000001d598005080f06c1a1011660080b98440580000c603016020304e0550034965030000c01d181900922803a040c4088030301032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 443404073 1250 443402823 443402899
    0x90f05030a0c022805280b130e010315020d0b04090c230114090102030405090f0a050a0501050904151803030203100e0c07081e0409020a020607050f12040f02 69
    0x2c0d505803c220100300000f03050201c1c030f00e00204407030b1800c6000c4088072a1449031101580c60703451610301b2061895003040b1100c06000c100760f1401e2a004201001420400c50181200c1d415a2101f501c000e0850080026443c0c000540411019142c0c110103030165029106001c0c4810b5171420100c00191401001f0102080d51100f950003912001058504d000603122000e200b0204800320071907034030091003141584020800060716071170303100000b031041124048105003401c000c4011801c0c2c810282268042c0d5003405e006000660300d8910030398015034031004028100100e045048041c040b00c108106048040d804940c0038940c054005511401188440e6040c1e0340e1180303555058400c0540342030f14004010701200c1d0000340060000c3c01601512014400c0c01403100400c1030740c0b0303400740c0c1240a5598000c6500c11180c0d8040040580110003030401a0603c09403a03c402d103640a42009100844404070108090004031303460040540d0f0098001c812015900260514000800102d540000b0003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 443405323 1250 443404073 443404099
    0x305010b01020d1e0c06060f0b04230a060e031002030106021f2703020c0a060c0b130b060d020409080304050303070215090d050c0c120c0f0a050f04090f05030a0c02 72
    0x2003602241030306101309200550003038900204545403403a81004030b501c1e0fa940e041c04a1000a400400d400404894000e59035650401070011607141c21114800d460040000f007070665980c41c101c1d24400d0310300e10724000038020032060000e440c200303088100a02241c4000004156550301083c100040807658040090b9045c81c1120300382100c140306c0f840d0045000701000540c55925048402e40064002c0c81128440100c0c0c0000804103107441d80000013040b0401508070400018003896580701c01c90a000704c0380709100391180d0707101c110010002ca00ca112a1444481150380d154844148190000c20f0300741c880c075240c0307030550792940247c41e0000544521641900044440d080592103180f58201800060b410454140e07507642104a40c96030138090110071042d00d490310030b9051450f1246038010700c001d44034841880301c50704010580501901e42c0c4042400141c032a16103c80121800f5140024400454201007403880c0c84110001c00030b0000040d03598a80c3c1d44807900c1984240225058403c20b11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 443406573 1250 443405323 443405327
    0x1e070f0212030a0e0906090f091c0f09090c0207170a05011d011128110a0c30080706150b04030302061e060f121f0608120706051009060305010b01020d 66
    0x181c1240e0056020f2880300c0000c000d0054100d00270b410841e00e0b0111008065039010b6002100d641428140010ba0104509a202c0303034080541c000406020134100300924025000035250f6280340100541c0111505800d10403580c2000f4400c4015080300c000c0001c21000c4030f115416040328074580103031358284200b0011a602d030b4030840304115043c0520500b02c88041052285040203541d0840030300c0101c0299190550b4144104440d580c0700742000950b0b1802c02d101120410200c1d110313581400c0e0004080088010b911907210388142e00003900c15180c160501e8903502420441c5803101c00b05c3e2400000080030301e1040051f10650b40b107038084d10751039030380d82c803c40c020b00c6c10b42046021084072100200d0300b1418600c00c0c404082d007000d4001c006080250880034035181441c01c1140c040d0003507400729000502903224483c003031b21030140505184110a8031240c04c41c006c044021b00301d0b40d990303408103c02a80b00c900440040410380c4007803010b40d9480c10031900804600542c0c45c054000d240804407824 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 443407823 1250 443406573 443406589
    0x3190206090601030b0408040b0304030305100807050a060c05030d021909090b010c020d110411070201140306100f2106080105151f020307200a09021e070f0212030a0e 73
    0x3008880082c80325038a1a11381d07140905010380300340c850060411000c5075084840c0c0055204601a84002c1103500b004c44200007444e40d1030340800300d950010802444651740d10005072003107890703034902a49070303851a0816a042d480360803003500040d403000418950300d05111880b404052706a403914481c0b07507551144d200995496410150021b0b0480b1015030062418000250000f80200c41d4200e820607000b002c5422540c05640200079554040790f48002c560380b01c105039008004040000d4110305040c0081410602c04103000414091400e82c000c0c0320ba4072556083c089011458680070004600d1703a64100148101e01604000c0d5081000003400c1a050506140d106000503000d50500c8643d200c1070100b00704421b40c110304500007045900701090603403540104490030500c50510a404090401c106000300b5409504240c0c014482d00b10f8840050842106200f002c520f540d503120036516000700e6000c410a00258040328408561069801c00805080305030b0068481c0c480349175503041041078070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 443409073 1250 443407823 443407831
    0x1e0504091a0108031303200a0608062e03020313081201090608030a0f05032208090a060206070827060f100b040b0904090201051b0c031204081b12070803190206 70
    0x3940720070170700300002180e802d400b40e261004040b4207580110b01c040000c0c80300c08a40d00880000d401c54052240900d400c25800005018130050307018024841c0701801c6e42c400306030074003400b4507034040009486e8880c1040903802003030303212040030303a50300c200040d17201d080f030081c020003040f00e161880101e203100c800821a0b00400c605c4d250380314171f45808030088500f81e100411981d924140c070310420700165401c0f050082c081c4d100b00012a103c0f5600b6045c07200351040d5502010441d401501800a41e50704202c1081c0c009921f130700038000159010301e007000c03602d49900325907600d48241030401a48005500f0304c00d02507820b85100c200744958640304031103076001d02e004449000e40e007040802054030f041c0d886401340c0303441818143e00b40101000c06486503411460300d032001e03800c5003056000342d00e414840c40300942c081249407030038a820030f000680d640041110b40c0c2c880540b41602c2220940e1a503202d105d10150000488003003036180d58420743c40f82c1000c0c40c4110340425100c1c00c40c10341d900201e201481 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 443410323 1250 443409073 443409097
    0x70509060303030f1b0414090717130204020f0705010c171902031f0e010f0902041d0405010e0709090201090e04030f12110a030915060303091e0504091a010803 70
    0x543d103610710200c01003040071340301e07131300c0386010711710174041c80207040080c000400c008013a0f40341c1c103a60b034410b102541d60024020010000070350004041502c0000c0b17140c0e04480040d044102e508581e01c0420028421a21024442c5001081c9141080015001818002503c1e514a007c244240a10181c664030643e00d00f5040c0507403900680c00310184d81d020b10b038403800349224040c1c0c0c0010b0019541420550790085603900d007404d070061101e0300c103d5814100030249820704516152600d01011851105c141012500e006080c000c101070000c01d40184002c001904161001140c0d030b5060b100c006d215142c400c9000c100752180018401c200552904d10841c1c06445605a890184804541c1040c02200040c54140d0ba6600076104e100b1880c0940495a940d480c00100e0010750b0905030342c21040049604c074180d0070958203000081d845025541103441c0340766403030100000070503072500b00c14958000382d0b000352800c03410074140404c9906901a1007000c1007004490b0362036501481c1c07207102e1342c441815 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 443411573 1250 443410323 443410327
    0x11410080c030c0c0c060c01090b09030702012c040e0c0418050316080f07030207050a090c0e06030c16050c040c17060d0201210c0201060807120213060302060c0609070509060303 78
    0x14180c3d9108000700350301d400708400d584001c603880000502075046011180d10580d501e0340103404010301100d81d0741d041003501d0011401c1c90700a60000304003403120310820300f8440c1d8940d007040c91407505008408030808000e00610035a0418041182e0301c1001c1c0309401e129504010100c00e595a0a980d40b8020300d410101943c030300340301c0502c241e50074843c0d401c041316000790400469148410351006048441c0c440d0f405849054609820021201c0341e68010301c406a1030044038100041c0c00c201c1200e40c012043d52a207440e5070fa29800c0360b10a00448078410340c9103400c803803000d0811201045040c6401400c0b00c0420803040f18010485210301d201c1d2081c41c42480c030b000071a000b45010b140082150b0320500d0041036540080c071803150b218400d00d42406046031146d00c0d1100740e40d020700480b406882d0b0240206940c0e45800715800d21001e6105000e40110031280c0120042c0055801c440c02a6402410480d07840384907020041d9107402c00c54001d2902d00401201045a140160f4803a00070b40700100198 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 443412823 1250 443411573 443411581
    0x801030b060a0b070c030308161d01020304050a091e02030112060e0a061b02060c0c0304090e0106030b130b090a03120203070c0c06020c0301050f0f040312060806011410080c03 77
    0xc2402030140c00150311148104001650301c040c00010b044451003106814174503855841d0141c10703408054410b000c880744074040c1121046e8042103500600200f611113031455111800182d0035442076410480d0088840c5001080024944d0014202c00e44090200560070f03e07005036041c00ca0000780a0300034152617a042c40d50209046402440310b40040c078090701d000082540e02c5004a500003800c44140141040074a6075041d010b00900ba4070078281e030703000741c07900e11003064581c0c6074852801518440c035911001481905001d40c4541d01565111b0020b415609205502901c5000100d004840e000d04c002c0011340f10440209071320701c0065040d215070944140d802895406900028844020089566290300c0840c1d9000916001410381e90040c00780d07004150705050030745400a140450310001c480500603070707a81d00c40245500035098a00b844801203c5c64044024200c258080352641c85030f07100200c0e45c40344a02042c0b03001c1c0e03021107020a1b2400f404800750307200e4500701d40e084e9414600740005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 443414073 1250 443412823 443412833
    0x102040e0901060521390d080a1107080a2111120a03090c0e0a0b0d1a10030b0a021812071a0903060408071a100b0d0209030604060921080103 62
    0x817607418071410994041816451542001100030902c0c40c0c03c0c08001600701100c480c100c0020402c0c040c00341c5825041ea6095207581c400c51040c1e10000d001c20a07072200842002105101640103408150f00f078416000036401c2c0340d10901050710045801d030360401c00c408001c6001c0c0e02d0700141380c070707070316001c0d0101032000540b02040390000d042030401e054070380c441040005e00000ca4880034081d0b642c1020003a04104a9a004035030500c02e80d00d019000120840700400d0741c401c140040b004141c4480b54644c1e5034032281300e480012580c0010300000c112400d00803408800d8000d010f400c599040d09012010183d402c208411030003814802d80c5400c248000d2100d40300c20280107401114050031680b42c040e5082c0482d14103101150140c1c4c0e00c440c00306101741000980390300040541042c0d9820300240c20700100c00851402c81c0d01c1000c00d201000202c074030403181281c040d20340c0a60f00405071161327071405042800180540a0085030081c01c08000100c4101004a030000740d00300c0307941e40b09416821540c40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 443415323 1250 443414073 443414119
    0x5120604080a031e0509011118060304020d050a03020c09070504032f0a080a0c0b0901051207030906060b0c1c120b030a05060c04031202010b0f040902041b020102040e09010605 77
    0x260341c04044d1038030b2102d0302141c180a01c051079030480640c00100d516000f100d103401c580350300541c0c2e6901c400c1044000c40301700c000e09042120f601c080340c0081c2d60703440c4c602c00201c038250860401002c500a000a0806268005c117134403249041c161440c03101c5540300c4108496500c40d80c0002440750786201010702d0200884808030300c99001d46203010703020460b90800a861501c0d00d83c00404a40e0201444074100080b502c0e80000030240c1641441c2403140f845c0029141780540c11601c59198418800500d000b0710982241c1c203c1c80d00000c00b04255502c450000c42036a00c5800c44030010700c00c100b0710a451810192031206000074695800500c0302c00090340c10b018060148004d5418400c0310100e40c04074000748405409010000c03552030740c5515514045503e02017221240c810b5924206211005131a1400701c400180411900001c41f5445480007a0003444a1140e100d8214261003110b024150158000d20650302d201e2451041903581803103160a03640c0f28001e4607002801082110032580d402c01d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 443416573 1250 443415323 443415337
    0x201180201200a05120a030b040b0607033b0102061303020d0c080d05070801080d080709140607060e1006090b03100507050d091b0e04021806030705030102070606050a0512060408 78
    0x1039880f180400c1e1201440c0284520301d01c50320220004089039400d40610401c00481416203052210004000c00034030030b8000e95002809101d440c1c05007041c500c0c3c10341220301d0340600307484680940103034414801d9910001003500a0143c03152102107011649010342c20000550300d5030051183c10340c00f45080350030702801c0404403003444050000107402c1c0306900445105113031594840341e0540c501200300349820b0b078604002080c4a51701c0144085281d0141102e0142d4031a820380c00011104680803640501c102039024110342d00d01b01818400c0c400100348003601e1a491107060101c21344510b038244c11110780d9684580d043c0c1c0305401d010000765943c0c028031303807009a9007031042c280900d128480042c1c800d5088100c070020000500c5078803806102402c03201906020302c3c06182032920303a01040f030781e1161150b1070001100500018801382e03030400404c409404080c00a40d206c0607a440d1090180c03481c0c0c0640781c0701d603030300c2d82000c101c3e810f0098182c200030382c071070000b40b4154131552243c0d034070f540c0619 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 443417823 1250 443416573 443416637
    0x2106010f3b0310051017060f060a0312020109260909130f080d230411030115030b060a080c01121a0a061d060f04030809041503050a030201180201 64
    0x2065049035554184543c01d0300d030725404404240707032405062481c5100c440e80c00c1007600610110403d910f003007001510641c091071070480c0d0300e4140c458600184031607002e40e2004003c0b2a02d8500641e450380d06400c501100c07445a00e0840302c207403410061036524484004d01e034040d040240041d880c913140c03e0f11025001040007640029405850b05c03560119424603c050b2544880084c075203444032800c0c82821281c0c981004202c4a000004c00f048541c2c08000e00054001c1ca1070007280d0070306540c00e51100e600512100c803411196541c900d0190103c0030112403040c8221314500c800244890007081c240b80c2d40341c059549440f07008010700480018041d5000a18001700c10070601c0c09261205000036002d03050903110b14190410061002e11301d66030240000d03008890500040c40d15003412001c0d40d080d654000b030b009840e8440000820000c04032040d28440c01c4440150002c2440f0b00400e2201d0118040d07802807000010114541c952000211f200034005800c0004402000c07090324521000c406e82c074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 443419073 1250 443417823 443417927
    0xc0103050c07060c0507051006030c03020105091504141c02030d050705150a0209040c0f230f0a200c1809030c1f15030206120c2106010f 60
    0x64541504540312541184045100010051b040c00b0003000550306488110005000e550304681d10900303118103511009060020200d0000a641c3e2000e41c0d252445050018540d104c6503102e01c00300701c00000201d060301442e907038040c0d0400340e030034081308480154010b40200314241d00c01004507000d41c03061100b606d040c002c2e40c44030b419008256281c54024101c52201503180c22840c0c0410040390800001e00e0280840441d00b041e0075500040100700c1550b44d845043d2000c00c4c0111840d2540c820409005a03812000a001841503004a0340700c00b1074603007050071004409240c021b0f0f50344050301c040c800e0f409054045140b000c0440b61080c16802a00030090324103080700c0a11003031404a1003001141c0070b000030008113400c4543c0c1e108603c15001520310100c005469500450130314800c80340c0d946d103281d40e60300004100255000842e00030401200d40502280d0070340341d550f44540d4040e203109001032104079140f1070030381c458803010f84485c00210764014403114084200079052280c19100320401701c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 443420323 1250 443419073 443419087
    0x150105030907050d210e040506090609010b0c0a06090b07090b13030f030e061215100c1202070302090f010e100302010f08060f040f0f06080a0b01032a26010b030c0103050c 75
    0x30f080500c0c44407483d6601c0d00d2400115086c03c04c010344100801181c0590403110400000e59982e24105045801480740726903213160b80c00650b400c0c0904040054406420603114104101ca0b1046d0280301f580503550b100d500c1610755240c00c50900c503001d62000003001c03d59052020802181e46031252070b120781480800341803c0720108983e80c000c0540e209a0003112401c120030154880c0e168005d1a00403202c00405031882c0030050981250340b2409800c141201c041e00c07110714003c1182c000a035070018080079080c41c00c12040000420240a00c4091614260119141c2d07088a840b480c180c0750b050311040307030480d05d94200b1a00e80c400100030f550b20554580208050340c03900d10400718405800d18007c036000481300c40700310554116a101c41c0e6039034070541c06d000115002d48032040c1500c1d40a203820b001070040c1d142e041c2c02500815100001407051000008140d82d60a00081020400034540c0c0e8006004c60081400c9401b000562905504146100841580303e540300541c48091100030781c0c145070f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 443421573 1250 443420323 443420363
    0x30c030d21060e070905010e061615022206080403320a020a05010b03030f0405190302130f140702060c09040207050d020a17090a05090601111005150105030907050d 72
    0x324603405050710075441c90a100750740743e200c04200007506c800e090101001c28a580070130a50701c207550608584501e4a03088808021240920700d042c03018426040d0b440d4580c0e00280b8004036140ca641240340c0c044c2500c00200740340548110351040da050348455203244500308140b20904c100c076888075055448200e2541080001101030000c0e00c9441d1300500e03c0c0e00841c80d005c3d003160303200d1008520a40c000e00003203a004524000310f9050b1002601d1404105016007129511405031b07030030003944140003411070102ca5580e60b00009803e182084140300301140c690705002c110030141c44550041e00b00d07000007080b006081004115003500a8001454540d25860390347c1400e50790a41f6a0060f0404d014060501900000b0b8110018103212410700c0c0c00060300005031280754038494140520000400906103a020329204c14603a2003500c00d03030700f0792100c0944000061904840c06048228241180001544103101b500e00c01d500040c01880428107150030490b4210380da4504a503c0c0e800b401c450341b1429 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 443422823 1250 443421573 443421581
    0x2091309080a020d140a0311070605040305120c0a080621150f0117070509060d081801080106020102090a05041d03121603230705040b180f030c030d21 66
    0x6401002000e0711040c0e4800024245113540c05481c0030801c80e28803d05801c0c0205080390400075090400184107922114010f91901a00030094142844c142c03c100030705400c01e0041c041000008089031240d56041c0c071002c4a0f0152443c00c00004802c400004c05c181821039503490b403641c000d1134029294101150b0280b03410040801030303078191f09000034000c000c0c0c81d80d52080d024080070b2202d5464420720a01c3c85640b2051403140c0c03403203015600c011444c9500c90340e030703021092900b080580c2c0d510740c101c902000440c50a4030701c040c0040c4a103400042c0d02c038411300c01d49240040081c03a0008661078082081f02800a1324588012000b1508048642c480308200411020501540c5140300c0d00d4a04000c41401d204890a80d0501d400e14450402440e4071440b1960703ea5907200300e84a083d2100700341141ca600498002100c50040041c21315800c07030245161400c44074088405640e912898000c2c941c48060200445416034810f24a20107150301403142c584622a00110000c500100c00c01d070031040e6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 443424073 1250 443422823 443422841
    0x40e0106030f050c01080c3c1801050301120809060906030f07021203070f2d02010b0a30050f060106030e06060108071d210322050a0603020913 63
    0x84058442e11808001081c41500750044003403c011440e07241400003d01a07204840c102d01d141c50100518080d01001e494100e446903d6035045000a0b0f090701000340419408015061400d6041d00e40443d010344c401e80440e0f058501c0400e84c440104890b50b07618006812822002e03510903414022020503440340c00180d84900015940f0500504085030040d0401003d0805504510400c00030040100e4001c1c1c600c10310320340345203480110480d034280d005a013007032240749020241c0c21592a06840d25415040401d1403002240c611107541c1e0740300b0412500c200904400482c01d108412040100410010425500384c00b070010744850642244000d4203200c4260000000b184d40c034010140d0700350b000c00240740d2100f000e003084003103070400c0d00025040c030794212980d8031604441094540c1e1a101e813101d0792210030100d500405100d08800619850750000c080115110b620300c50404c0e00c6140c3c00340c0d00400c80300003418402003d41000c170210065800001c081d500030341c8001d030310072144c02c43e44166282 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 443425323 1250 443424073 443424083
    0x906030403050403020a060c050a0206070f0c2301020c0f0105091306121106131710021b010522080313080304060902011d1f02070806070305010801140702030d0b040e010603 76
    0x3d9913083d84100002016a501f210040169143d05200002c40000704500666011586241c84e00c04614020b0f60b841d01c0f50270020122440400c0c001030010100e4888030054051a21138403100b50000f0049942e40801c0400d503600c407050b0308221a195001d0302c002c00c44941e0140c6032400016401c600d00050324030517445010109032054a18061044c40e8101202c882802c036038143ca04412100720307c0c2d00d20824068071310b04400c806245c4c0da142608024103d140e210616040d5210944007103000040903426802890350750034580044c52500c5968202c102c02d1810b01c245604425250b101c0340056000100340f05081c00704182d540c0c02042a4030040e600c514407401021400444a02c0010b0038070801000d8140280000d0041481e15519441d101d01501031900301e00c018a0740b9104200d2512080fa40103d06074041e10080c81020740e490b4220301d0598128100034880144a111891003039582114014016003003440683e01046a40d04110328146004002060b00300313008800130308491255208460f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 443426573 1250 443425323 443425327
    0x90105042a02150a090f150617030c0f0c0d0308090c06072108010f030b1302100207170706050301051003091e0b090102030915070c0b070f02010e0625020102090603040305 75
    0x2a000f400c121885a02c500a607505111321a49581d42580007a407890009040718812071040201c02da01d644100024444025420207061200e910385440e540b0441c04100b040c06000f04008031500001043c021000001d040c10943c0840c980b01160090400342250036940a0580240c140342c2d260030240860380e018500300384009480c0c02010109040204403101131200400040000e009108079540440c1d4003d013135840c00d07940f803c9c800c003060b02d24103000079800a900704600304840e9000941c14191034280040c0b1000003034100d01695160441e00c00e81001510810041c46181000c1805180d035001302c2c1400b244914499442a080342c0c055000301e022241404c0c6500140f12460012503040704240008503c1d43c248034100030344400503420707888010243d07400400c00700352245000c000c482e90003420503a543d04005038020010f11080c40f60b140150708203000c40425510124460b4000c1440400107400340c8090080360800344c0409541500b555400d201031003d036200c01c001540315910079500c50b0f03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 443427823 1250 443426573 443426593
    0x6040f0c151214042f0613050a0b4303020f070f03020a09021b030f030f0a021822020d0b0102070b0c06010303080c1c0903030b030c090105042a02 64
    0x904030707403200b65003d42c968201400e02011039039220400014000841e1001c40e9103c05e1400304001c0d990f0302ca40240c1112000500081007241c290404080c1c90040721410911750b40c807441d042c0d40e401140c0424a88070000201000c0c1c40740c3e00c01d580d03004c0c12034445c0114180000e0304101241c003003240b5804e4015030003180408503042014000380016116450307c4041c030fa0b08580105010380d002d0700411000c0e541c0012201c400003409124201c070142c2d0030048075070300c90f90400c07000070301e0f0020744024540303620b0740000c91680402e6000f514031594550300000920074080701000541401400500750298400c01d03444032407601e034001007a10040700172010030251001340c002031518405030310040e1961803d03c40080780c144086949030443c0e07010700c1e10b0821074070307040c2c0030076007510802e4000c000491180f150110b024685400402645019071003c010f42002481456160203005c20f0079603000b2241001480306142030303030110751000000300b80143c020220b2a400c12400150200843c0981d1001c0891 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443429073 1250 443427823 443427857
    0xd02030a030e21030f0a020c0a031208060a0509061e121e06160c060605040219030b0303090a03060e01140403021501210f06091b17010506010206040f0c15 68
    0x512000c4002d89111640580f5a0448540320300410541074140500042c0c40004d46108105608055800500151003240d8a01e8441001c40c1d9012811000c190840001000742c50100d00c0702045907070103040203580e0740e40d19040042610040b803a41d901c00c03031740108103e030341d4a59801d52205c5607001070080c003e000080d020381e8061850012048c0c00383c1c3c003050801564880c6d00708441e180150a046c0100002c0c582d00d846000f51406170803050708607101090300c060760f10340407114007004d0500340c030300f0001c28607904c0a0681320700c0b40950807038000e8040481040014820b82c480c0f440e00e080203000003074124000a1103010721105840a0300164056100300d000c0102c2130744441c0c010701e60054a10b100f4a0b090303403c2d160000d02c1c1c01c0040d0484100b156000180f00468010a01255005020340b140c020b040203d40c14201250180327006c19003c00010f80d0203181d051040314040c103016001028070760780d0b5585a8038031000b004000c0751602009040082c0030844041c1c030800a12654549801083da15111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 443430323 1250 443429073 443429089
    0x8030702180907030b0c12041505091b0f19031a09060609040305031e01080610060504081e0a0b09100c0305151905060301141f080c07020d02030a030e 66
    0x45612071012000902600140c001200c00c1100d601481580250380e030032000d09a540600d81c003480e0a01c91082c20032042000c001102e05500441a10821590b01c848503070944c2d808424801d018450007c0d04005c4182c901403078500b40c1c400c0000d00a14000000d954140795002580d0b0040f500c914410380c0c01d0031100e0b01401440d5102c0703c5c1c000181080d203040760003c0c6541d035010303201400340200000464034482d02c0554080340c09040c0c007104109940d5808a05586040c00c540d00e0b5180707485594046090741c850b804603011920380f90700400036807613100a650484210149400043d100740d81075400003448107183d240c411051072000d45a0755030350b00029020f50f4810741c070000400d45801c0402500f501c03041d071520810071003900c00340c0000b20701c61502d0312001001e820440d8001408000040d84030000340c402e001441040d50417681243c010300f102081c841c411500c0c200410100d00010b04003003007e201604020340010441080e801498000c40e06090f1b0728601640090380004680d1514208060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 443431573 1250 443430323 443430349
    0x4030303050619061d1807080109090b010b2b20071a04060204081f0e03160609021914030c100e0402030a1d0d0e0102010501060509010305040f06050108030702 70
    0x341034004203110b003c103c15800d66900480042c00800c51200d8810aa40300100d000014003400f2180f84401115240202100417107401000443c0c4d03a0001c6203007001c901650007040d5001c07002110690a10044006c82e0b001400e0b200c546282d1440050403010290704006000c01200c08000748516000c61040f144612080c1d80400683c4100f12420001d02003030258000e20180c0030564a440c3c54616004029108a5014590b5841a4400c0520a16000106203a500400300d0f00704401410181d101e601c034092800c142c00f480440007070400109002d07401c03802d1403900c010f00c40c0500311812842a011030804e500306d1800c4c7c4030061042e1a250030300304003c0c101c0c201c00720303244074900a0800e4002c0240c2c030f2801400380030341d07000f002094414a0b29086801712032000b110035030150512206113580ca61400c9013207030004440e954680081d5006105450580f8165900c5514040c84c0c4401500500b00150040f40c119441e4411000820514480e003406484003130091076a520141c0100118181420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 443432823 1250 443431573 443431579
    0x180c03010b01170a0b220b0d05060105010c030c08030708010626130204110f0307080106080106090b07080c0f0d03150f0306051015030c08010806060a18061a040303030506 75
    0x8254a80c2d0380c00803030341800c8001d1410800074a50b590700c0140c0c0038014030060141c204006000c0104500780c40d5a042c0b0440e0704004040240c41d030350404004156161040182460300401c006203ca0b52040840500140c0641046045d129050307480320b0644d80202c40d24070008040200522086600042c1c0c503140e4140001070440c3d10003c20300c142d218a401411540075a04913060540c21510780341c002c0d031078001e0b6000c40c1545401c0c2003440550746601c200d403070600050251001007040c1d03020390f0040741aa00d50b95a01c40d10282001911407403640806000d68002d00203107c0360301045000c000071055281c400019050229000d0000f5060b112040e020300007a164000040c440a900c55a20004030384e008103001c106519001c4a403101071500f074016007212008a10a0121250141c00210380709003140d98081203a030b41d410359291a180181c500c5640484000010400e06175440c5818850080e589d0000a410340d4807056100103a01d41940501c010b1400315080041c15050703c2440e500c40d4003a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 443434073 1250 443432823 443432831
    0x191113020a080601080601021609091a010b0906072d0204110f03040204021e030703090c0e0103050604060905011116050c0105130e040f0b090115080c06070201110a0b180c0301 77
    0x2421028220b454010000d50400c442e280000d00aa8401c104812441d40541c211460380c41e1100034280180100c040c4c24ac2d00c50341d2110011510350f00c801c4419041ba007002c4141e6041051041c02c009441c0d004100030740f804070030510100701c5408003c031107220f005590283d20300001e2440c030520055503420840010403401c00e0040541228402007203d9005a04840c016a01c3c60400301c10300d9030024940c50308810010110400980c650507074041d14446000b8502c0c0a00c0581d203201c1000c13444802d000090154015402050000c1c000307811118030740e8400c20010861803e44040000f00d9080740150140c42103d28a208040c44024042000d15074028681b403480d1121110305009807803401c0c89000700e251031031000181401001c841000850380c0c40042003c2030704005c1c4e41c540c041c05d10b45208c0c180c01c115841c40050b03d0400040c1d000c40764400a0030860410795242c0055a4052303288d600895039000749480f0000049100307015038031568a441c00e080d070480c51004030602d004040c0c00010300982c90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 443435323 1250 443434073 443434087
    0x102011d0d0c050f010e0703061a10050d0b1002011401090b0102030301150203040b04030c23132309030705190c03061107020a06091a07020612060319111302 69
    0x40400c03079040601c800e0410744941410b52415510f00180342e1400b0031154a007030783c80c64441c1030101c0c445040b03a000e280140607000c544084011240754600f03c2a83c4190211130b0781c0d0304035010b403002d000320704d503210701c0040c8040022010500c401c50f40b80700c91005075960080003403865941c07869a40906041d80e41004102105030010b55684410b005980c1031695000c02c02d24902e2003002141c014045c08010103454580e246406001d85500380074410030401c01d43ca01c01c0800d450303802414061180203004207003810001c03840b00000c0c0400c002c8040c1c080c132554600c1c032a00340d42803d4035001e41d1464006555905c03031802c1140c180000c0c0040e1542c0c624180c00c0100104400d08000b1040c0c0e41c10204c0020f40aa01e40c080204a10903094000e4014440a01c00a5156084541d0608072440000d0041040441c00c454580c18469180002d5100780706100d445118035140349013541c0300002904451941c0c07480101c03264008001c070070440d4610b40f000052011424114000905040c60441c25800c1181c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 443436573 1250 443435323 443435381
    0xf0f02030106030e0c101b060603080306101d040c09050d080304020a050d0b060103021b0a05060703110703020a0b0901020f0f030106030c0f020613020a05191410020303280515010201 80
    0x102000c004030401c4407d08580b03641d00304a00c001032046a01c0345081100f0741d03580c03410012580003102c0c040d105240f410369070b8035101d009590641c883d01229040314130f003c1e61501040003e00d011030401d02008150741000c03415031182d00024800301d02071071361561640ba042c8100b0800d0912500b01b90b01941e2594600400140e07032a03552030b0005402d00340503888103c0c10300b00240074002c0340c401c1c05043c1b04594402d41403100200e0382c140941400c0c1d03003c0c171244900a8500380f051149880042c0183e102080920204984900c0d480c1c20080350000903241c8205115562034a4102c0003502c0440c15002004110481d0140b00f410080009800d004182591802d8080e4852100801c86a95420400d19000843d5039902401c0c024140c02444051800340d09199944144401c1c000c0001181070000d100800f490100501c10402d178280d8011031544e03039030980c4071400c00c560080c0c03081140150302c4500d0003c01140602c070b10404900380760684c2240000002429940302c070041101c176890441399142900703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 443437823 1250 443436573 443436589
    0x70603051009020910050f090a060519090f0605070809090709080f06010b0313170a020c1908031b03070503040927200f04051e0f010602150a0f0f02030106030e0c 71
    0x1782d5050994a42130301e04110f084a1040040c03c03a8000340301000030901540280190400c8465003049042509901500380c0d2038407020302030350700d403200a00e01c100136180c4210b005003000e81c401d40b8468108400c0001007502c102c0c00f81d44803008620401000e010107001004030f01c201c080e00100a02040d403510031400d0b014440640b10b140032007943c000004c1849a0781008082800c1a041c129a40c0c0500d81c4000f500c602410072007034400c0901d03484100d034005580b00301c3d000340d802d2400618640401011900b44914644001d201c4a000074001503010460500241004090994001c00d8500340b402110301c9a19a502d00d40c03200e048681c0b000404114034510980c03100400c854500711441c000400240240d2120140540c014146410420300c0400341d036040440c0d40e40100440402c0d160f92000003a159070034054900164042003c1990030304152403229040070010328006141c0c4051180354068841e0390000c0100c040c2c0000042000036850b00c5201480f05520b8050709903501010005a40d031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 443439073 1250 443437823 443437849
    0xb0a0b0d12030912051e0909060f0a030c1206050a0c140d06030c080a05010501050306040b07080622150503030f040e18160303030b01090303020a0308090f0706030510090209 76
    0x800c0d00d81c84000d4095000e07030b01c6044510b400c26036403201030b480444000c105a02c8511018401454403040780c900100030029103c030882c006000603456555441480802024015065406a560040080405e8000c680000508010081501001c2590078400140c82c0050038009030b00703140c01d01c841c910319070000d640341c0c40c02d0039509180d07901e80c104102140074201070b13007014069203a00000000c440d0b2000a2b0b0021040c0318a000303101c81d0f0390315010161202811100500340102c0c00780056106442007011075801100240060b801d01c00c20b21509120f01da50030700c05d640d8a503550060002803c81076103e00010841103005600c0d00407050007a0f03e0078021446001c00600d8103d001ca10009801d02d806d100020b240c3d02120b4000043c040d8981d1a01601c0c0f106601281c50107030348408651003080d010081d207815400410030400030781c2c1c00300e0700100014540c0840e40582c40408507051070034883d80006007078955001c1040e0802201440c0e07803984a52042ea401c40c4100050b038481d40350801c2190403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 443440323 1250 443439073 443439083
    0xc02030d1d1210150504050a0c090b031902180306010803030714090d0516090c230c0f16050a0806090d0c1502030a0f0e150610020304051c0b0a0b0d 65
    0x218440d80d46002d840d0900c80c002c00c0c80707400d0908580020303801c800481c044c1101d8003180c06100700c1e25250b4050041348c40f8011450009000d9000c1800b07840d480350001e5420518076020f680806051303106000480e00b121560000d642a8007281d41c4503441e042004a015241d0540035601e07500701140003070603c01c1001d207265290000850115016550621400352554215003540d280d10000080745500c1c8801b80180d0b0080c41c5459007452450b4807441c0044034248a0b00700f1582100c82c440c514108980042142c8441481004002c0340e080342c050046500e0710400921422446081c41c0c2040742e00501c0c0c0c1c04c9104142c1c003100c01c11007400c10015172100c00020504060194404500388500101041408a1000780c00007090044d680065031040300c0313042d51000100030b240c0030100080d0b21031110030b665020940f0008081102403420203c0003220104500449107800d0350750000c40c5158030103800d80040200841c0c2b00c0d100b0701c024004801c2d84040404800c0045540f518001511030500c0346020f40b03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 443441573 1250 443440323 443440339
    0x60f0d0302250303090905011208030604090f05330402010804020a030b0702100c0c020a050405100905010f0e090304030317060103090812010f05100206060418020a060c02030d1d 78
    0x8141402400b4204410481d070807000310584200022070354840151000701d00043c055007000803072060074441c01d4140d40000581105400290700c03040841e401c080d10307855102e99a80b00620004207240070f005002403180c03002d0401c83c81e2071198108080c607442e12110b851000c0a049091051139204a15401642420080420b0302c46001280000c0c400e504000d0840c81010140710f41e03240c00050098001800c21000d20568088200840d9111606a0001d400000e001000c0c0141d1801d504040d6003c0781c1c00010700d51300f80c0d5410452054580a034031010a281200c0c0c0c0502c03001c9480c0140e1640610120000d51030f15165a0b0700505501c01d50100316060020040860300981c400e80000b442c3d0342d008040385441f91588607408809040070b100310362004c4160b007030000ba9404c2000a0001e002460b80180c81c02d035070307a01e082c88007a0442c0d41012074006056402d140c0180e892505000107080913540b1054805220710605261103000d215550910210012148402c1c0f0220000000e094040c0d80180b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 443442823 1250 443441573 443441599
    0x1214040609150c0506100f0510020318031f09021309170d1e0b090907060912020d080a09140405061c0501150b0703080a0e030406200a2108060f 63
    0x540940399028020024042d16041c81042e101401e1180d00761105507105c07d104990340c404010380361000002d010301682040c01508003055034500c54002d03269001e800e5410514030007080140703800005404080702c554409000082d410021000703441002c0041041164291030346542c1501400d040310b07040d00f2040018540c08020503600807a03132100348140300403480c50710400c920000e8105901aa03000b0030111002600031500000d0040498410780c0742c03031714880d08221410340c1c0d40c035105005a8206440400f605c000940343c10090810301000d0361042102800d0201035101e01c40c1c011443ea00c99420501445060b90f100c050b6030759412025800a08507018a20b003c0f8054005184000f0703a9030000480042c00305168001084201d100e03690782e13030440d0b03110451081103418141240c140d0390300511080c0034990003240301d01d0300c10070f00d45010303c0010b01200344180340c8045048200d620400f414001c200802c414443c071080c130b0740b8030300b40030b6881d02e8510082a0001e000450091007008211401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 443444073 1250 443442823 443442827
    0x3110411041802070812040b0a1a0d020102070506130e070e150a0e10050306030c0109030519020a0e1303090503030a0f050d020d0603084b0412121404060915 69
    0x11070130558000007913a01e030050803040d15428041207e0a450400800340060320800765882404070341c0710700c020341c0a001c04240060041403e03e89a0803819440b803e900405d8598403034000e040700c569265028096142015aa8004214040c091809010f0b99000340056076448502c2403500c04070032401c0c2e586412003400c0449140d0010074155802905040b01c9501041d800300042d4403400081c0d003100d003010750b9000111444d0030f40f40b102501e00d0b002001007036042c003d10201c1c0c0d050a40020600749040e130321503500b072501c80403d50f00c14505140c841c1c1d020f010903030403484031001000f040f40034508140020102802e040501944401000000141980f082000381e056584101441c0000c00c502a1280740200702e44e40003e2440429810000400752904141c44000304110248917103841d642d048502c0a12000e52070304c01c130603042101071002095000c8602d5400c00c0680c043c034100b00100d0700c40e0b0700150181c2202d0303260400e280420041131082d00c0d0000000002c41d5503960342c04413010244842 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 443445323 1250 443444073 443444077
    0x706050a0209040f050108010513051506030102190201060e0c03040809210a03030b04051015080402010905120d031b0c030c06020409090323090117091f020403110411041802 76
    0x165a003e8645248511182100c0c0d005505a0300440001c102680b00c9a6038500d05e021440320050082d0312110b800300007001d07514001500f114020f0000f5003041c0c0d1242e4071f180c50343c181d10890b4005031740d616400c200c103a281114240d00a829496201d1842c10640c4031440b40348105202280a01040b0303440ba82404401d8401105029000c02640c10100359841c0040142403c0301600e8800c1d803d10b40030072110303000342c0786460884403510317200d2800f07802d08a8281c0e44940e00620603070502508203c00600c5807618030060030100c8819001c0d09042401c01e001800b00e849010901c000b03a10039140c80300443c0c0c1c01045a07840300e501810705414510061034894080d1169801c0701e98414140380c0040b040640000700481180e40440d66035440c1c90882103902154042d48030414005980d0301060240c1c905198030b1641c202c840729040d1041c6551010291418030034801c2c0d0003919035400141002030003642d203540d08003114201c0701031000e00080440c1c0303050b60085001d0032440400d40c0940380840c40590341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 443446573 1250 443445323 443445337
    0x60d020a0302040f0b0f03031201051903060612050f060105010e130f0c020705030d0206041208040f020301060305160608010803040e07092117030f010b0903030903011109240706050a02 81
    0x109200400007102e000d000703810084105d0b4042c0d51030a80d00b106c03d00c0d020007614040100c0e0011130b2031680c030389410040c501910b65074060b003151240102002189480c0181405089640d18500d0380c034041d45000c0746480c0c0e001103400000e400401c01071109a911085440a400044980c0c14424200e03601400040180c91078160b20146004a40b0000ea6004286402143e4040703090f22042d051400041e40c841e00100d80c01000c141000b04402000c6018218158100740034511091180d80d143c6d010a0071194660030a8030294084125400305659103515140600200d24210445503d0001c0c0d8956a010310b0007071440d654103650019040521401c0c019004180842e10100040044400c90711014a0403034141c940d0050890070741c98582e81241168000c0c50b080d40b0740300d0340e0782c40c204490240782c12540d28564540420401d60030700e50740c01d004000728200103403600d503560b540f03010411185072064a004203440314050320080c0082c1040e0709176004650009800f24041d641c00d444080284a411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 443447823 1250 443446573 443446579
    0xc1703190e0c090f04050c040903090b071104110a0912050309030d080702010f050121052113050d030507060c0e0d14010c140f1303060905030307030501050117060d020a0302 76
    0x31404034808140000c0b0380410740030035a418035640d111801000c403204d400721009080c0d680001112109400e141d48408800340c000d18140c00e8540c0c0300c20760749001da4844402030351400c643d5400c1d0340ca207142c184281d1020300507681d85145001e440c0640640706d1903a034030510007005900d000210500c80240102c0b5101c2c8402400e581c621203020740040c202d20780070303124000150b20b0080240000b640510485060740e081040f014050400a54012179544801204440c43d0103028100002d41e034043c0f448491028021000588942c088003007101c91514640c0143c0c420b0345403d42e4640400c0c1c104013203c040b50340041000c242808290800d658000c2000310780d0723801c000034441c0c1e42c050045510801e5030303e010400083c481c41501000445e00801c0d0250200381c0500c080140c42117003c148401840c910581c0d48140d07100c20360320303141c1c9402c41b0b0503403d003940c0c0b540000040001440d41441807034050300342424038980e0080c22150245400c82c1c0206484c0c05804200c81c0c2c241995181c0c420b55008550007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 443449073 1250 443447823 443447831
    0xe0a0b09070e010e06040b04020a1d0a09180b090d140306130c0306140612010b0c010e031204060516141c021612021506040506120604060b011d150313060603030504060f0c170319 78
    0x100c3c4041c02c40c4ec0c00890103880341051a0042003071000085116055143d407640c1e8170a40f080f0407110104142d2014210300e602c0201d041f95024001868014140811141d480c00a03945181c046078100031100c921640d84515420484000c11040100a45054078480d0005035164107a0b021514010f040700c00c08060a44004691030900c40901079205c0d1040b40700304424826602c40111090700042e00c1504840811821007030040d04c0d00d480da003d001e0300786003600c030040f008810303002000490303022480b13070b400500e40c40025205016030395000c2d9802c0711091008140d44050310058031401c0c10050295441980c40707001242c000e036546112404042c90700020b40d4840e00709071624500400b150440c080c0810700c2c0540e02d4616002c9014100c05851000d410070800348100d200d001d81e2544010f24840342c0100c81c00d00d85000c10032034401c0300055071090b11001c1da0395040a03000b404980c3c0b03180e6500c08100c619400c2800259010516030100f1202c03034003442e1070381c86c2c2ca008118020600c00c030318043d880ca4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 443450323 1250 443449073 443449091
    0x1008030c0313050306070e040222080a02150c030315010c02130f0501050a0b070b070c14060108060105040501080309040c050405042901030e0a0b09070e010e06040b04020a1d0a09 78
    0xc080002c054000780b840c10020030395a28801d2584441e0204c1d8404040384010340a10f0003400d058000f031200c807000d00004006801d0500031f060782041c030f5401002c0b080e070060704044214100141003100c890f00700f114a03400e00d041816629581d1000030600c070301800c40317140544404d0f4010707440340c0f42141d8000d004140d039480303a51201e002400c007075160441c01d900f000c00024460600d80202d03815074810080091401100d0f4850340021a4040c100e201000080740383c10300401c00040b5081e0b6441541c0380680a07551514134168901a41030b004584107519100040050348400003c944458100780c5000c41e1070b914024040d151070081e03034002600107060600700c2c040e82c01e42041d050040301e050080601084020340044003100c501117505a00340d40070614400111b0a48400c1ea40d121220074100c400140e110300c406448050280d0110b804c2c900c60a042c03010f40d00d0140200c0f40901d03820707101141010252131009140070a8410303100c545d24403a81e042101511520140c401602d214403041c854158 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 443451573 1250 443450323 443450347
    0x41104090905010c031808030c07050303130506060906010503040f0311010509070f1508010513090f060c030c08100b0a090803120714090307150e03011407090803040f0905100803 78
    0x1c00c4540840b125481c000e14144114000d104e02c00c1c01403003503c0500c00c0d5982981c1d03050415030019104102d0040c060000c00000380041000398030500b155100300c10303402c0072807a210b450414054112882828100704000c3c080c0d030b200041d00d500541010720700c28120421308007038a488448000343c11055080004001041c540066044100c6401086d8411410781ea0b201132190120500d01440c0010500d1004100602c1e0020720300320b80460200d030000d25101a596400c20a03e0f10325400c88491362900c10a201c80b640511452080c0d1555041124062a280400e13140c0c801c554021428406408116140e02602c038070445d002800114003200c3c3e8403941c0141203120414110b030300030002400c9514421480c1a000250340b6542c02c00740c010f19502c2e0621800c481d0040f000ca0744c43c000c1010807411000555003d01a41040c8424480c0b20901c6051240000300382c0b5440d070708409110340c42040108401404e01c002c6908565085d20f0000d0241c490100c4044400007692060700e02c0d00c40070a400c8840c0d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 443452823 1250 443451573 443451581
    0x1203070516030917010b0a06110f060f0f0f04030c0b1b1303061d0d300603200a03020f0a08030414040605010f05270d030512060a05031b04110409 64
    0x521020304845410b0001c1c00c0c69800c0c4c482a101c6d00e0740140e1881802c10070b80d03015003c400800c03e070304019244480440b5810514091044403440a00b42200080c44006045080c0b4183c00c4100110120b25a181988000e00380d40880ba90040004500f180002c000c003400303241d6082c040c0c0b04076485560301c085106548000000d10301060380c400340350400d00581c114521813070025600c02c6001821032400580c1c000c2c0ca007000394a90207218054603440c000183d050b03c40c03007120744181501f00006c1d5541141003521112013940c200c0005a0344550039611213940700002882100d50403506500da514400c4040f684509032680100560310000c034000c5070501c90342000044445007550b040081594a40044841d08042401030307010035400c00c4038118640e040003100c0f1184038000b4013954441c0030400800c032240c100f0f0405070000380c8003003146211000500b40d010703000142100c1d045851820500000e84840780b800c4196007031840740340c1c0c099285e19180c120035542d1079090343d10703902c0da6036405a45001d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 443454073 1250 443452823 443452829
    0x3060922051c030902031905010b090903070c060813080c01090206070507060813020d06020a0309020a0b0d051b0313050111071a07030908040b130806011e0b0c12030705160309 77
    0x4801c20002d040d00c0714440d11980807025001402040300c1007421160034108014400701780c070155240d590b8903002d030700d4211286005d86d076004011079403121681820300c40c00e407ea070001420094a0000c0c000c0d050050803580e484290004903c5982c1c0002e400c034540100700304a0025001000460200c1c1800800310301c42c000c40324a0789808600b07540e1070401c94844603210a0007540a10902c4505002c01c3c03650380a000c05c1d000700e00780003841c0b80160300000d6400c94075034090649003800294401d60711a15000c2d090b080710104c0da10300110b21a9050703c3c0032030f000040c1501d01d03420702c03482e514062001c250840700300101314100c015910703901400c0901d085050010400d00b0480031902290005220f0303c41ca84402d82c2008000703003094102a01d120340e5038003400f81d501901040c0d81011502c56024481076000340b409929400302d80703903414a00c103102040f0f64480300300c2e080306220744451a5070120f8090804520040d44968a60343c0c01ca066610340185c240b007002c0940140e61840c101504907200f0803e03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 443455323 1250 443454073 443454103
    0x304090c0819050106120902030c150a02010b01030b030c22020d0204231e03120f19050705030a030f020c0d030507020631020406080d0309150605060306092205 70
    0xc2080b00303448042030352001c0c850300001a001807a44420701c4015400310340b042d8402000d42e00b10020840029240d425501c94032048200001140c15410382c0912400741c03d01000e0070148122a00040066207841d8580891341c066149034000300c0862404085800000c504200304548507040107141034001c0d0040c3c0680c020350004925900c500d41800302c08030f072420100030052078010103007000141545007092003541d014070614071b2180d03915101001800354070b030a260b012a100d05d81840200708200700340c020350702800410040c101c0030400100480d40903000b641400300700c0d8117400742c402c0001c0c4600301e8058101e00940302c107448115416080207010380301c1a402c64035203444001000e545270424008071900603d207000c00745840c50f5104601c585440c0011b100042c2c2540e2400e5003400c02d000c898404002940d940c10300800c20440710840b9585640280040003824107140205549100140c281c0340316101131800255100822010940c2c0001c10401916900e041031812030390301c0000014580e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 443456573 1250 443455323 443455351
    0x60b0c0f011a0d2607030201050402041406030d0e0a0306020a120b1207050112020f03040327031104021806040807050109050d0201200307060c0f030f060602100209030304090c08 78
    0x41450703a000c8503844201c0003e166050146607940c800000e00d41140300a40d00202e0409032003007100c035000140012900a400219035440d051040004961005103181650200170041c0320050720b00040e03420a180c580e04201c1c8010100100007141d0106c140d0004060500003c0c0e05036040e41e212851442480c903031001440fc04820364200f10520b003110400b041c03660300840c0104004e61064004056240074454014500300c0d01580800095204a801750080b4429010b090060020100900c1c0305542e04600004100d080d965998049960f030a0858400d5030042507907516000c22107140c4e100d41600070303c100ea80d682d44415294a07a41240316080c0841c4440e5000a040e0a00702e460040040d4140d40b01c19003c1002410310032270050000003007195200a0200200041c0385220307030040e0350200e8456090006120400034203450050740103000701801c0c00820000240c00160405c2604004c1c080540c0b181084400700c1e203140a0340e40444003d504000c400c01c506034104200300e01400b042c1603205c0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 443457823 1250 443456573 443456591
    0x31509020d0c0c15090822031712130317070f02011a0f09070c0606140907030e0703030e0301021210080715051e04030203030a03140907030206070605040501060b0c0f01 74
    0x10b02c9124100d0f202400c0150302410010038500039038000428240301d6242c05080011090081c4482c403201d8110300e600000e044024028400e240414100d041410000f451500b10044400b50703690f0710160848541c0c1c00e2244200003014021000400c000800562804c200d20304440c00410040080f400c0da005546000d000c1400c544207004800b00340d5402811101000310002d05010901c0f800815a00c01c000000511900044583c0548401020300d07241d08505920750750f04012548001800300824585000c0c034500341901c000c60303180c0440390035007020550305481c4008240a4410041c2c88800701d03900310208400684090b0700802603600c40f50440d485140c0394a00c003054a494880c1901c0031520600c03201c0003210a12864151480080311030a0400342c1e41c3c0d01081c40c5403c0b42c41660b000c45c0d140c1e0a0b030017000c204101d402d54800c0a44e0005c1103098030b181c0104900b4440d0400161040b03803520b00060a00009411500080805500c03003507130303070b032041d002c0584610032030305505800d50904840e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 443459073 1250 443457823 443457827
    0x31b010801050d0305073201230103050c04090503090a030f0506090102040f0915090603121806050f07061d030c0d0518040e01151d0f04050319031509020d0c 69
    0x4001340c0c15110310b4900005a2070300040c510503003802a942c3c54011a109504a40301c4446c60940c1c1000c00001ca03101c400c001c2000c4c0314403440ea074481c804405050041020440000301d04c54580350541d0000b88040544c2010ac0c194420851410742084800307800008007d000102c00d03607498081c0d4182d403041c3d05c0d10554a4240e124521130110442c40d40703481801808040c1e4452881a2403801c2c0c801016551460340100782d652a0744141c2c0c51071255003e0880d00350700034901a10110401064a4280d0701f0007074049d02502a646045d111301a0106041c82000803503403140303454190b82d54003640c410b14141e46e91640e940c4038856070081c034025034501c08400e40c00341c426502d800c003503c10310044081c6044c050100804807441c81d015a903403109000d524079601c84000401403d03112136055108400704510241c0d003035020340400c1c142e009034004c2201203200842510b04c8025112440050441c1012049000d0f041178850401e000501c48400501410540d00501451f440d10b0b0003032190003200d1600b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 443460323 1250 443459073 443459089
    0x90a0201030614030304270c031a01031104060548030a020714031c0e0111030711010323011509050108060d06020c0f0703051b15040311010e031b01080105 68
    0x10310b134155000b44010b011050746260f40d4070294990b0302045c2210078841110324140c6d40201c15440100e80d9942860f42a4080d004107100440320a080031310019410051004683c4210b11800c1c04001000c546100c00e0081c5241512004004400402d42c59004900e030000881c0200000c0300d0700b14419020803990040401900e50032121b94020348150b80c5403072034040304c0805c4034000d1a41405141c5982c1c14201040816a0000ca2503565440348805080000f400341441902c2d42c1400341d01c28041c2200007100c6846072884c401080c07901007021546a410261005160300c049040000303164004a1030410036200400320502540d50340c49100c4d07440006407042801951015000740e600d420400201d14560018200c811b1140308a8403800190701c0c2030b60600c05141c0003140c0035007101150302c1103030b12103d0f030407071071180704039601c0a0201044000e800c4a104511000303084a00300c0d801c03030309907a0003096948500300024081e10400c140d651020040b5501200400b4081001c2c9000400c02c1e0500c0c9039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 443461573 1250 443460323 443460359
    0x5010f080303010e0601030e1902010f090803090d0812010902090a0902031509040309091a0907020f1c030924051006050702040f09080f03070e09060109050103150e090a02010306 78
    0x202031441c607400c00030708130030b820310042c4a181450340340e80001038490300c1006410b00300464a411074005128610004111000b8a0002c0c402c2068070f02d020301c17141c0b80200455450810858050b0921101894201e040d40103120480912000c154000030340400386070002c20364030b0002c65405c1c2c107180d00d5200d00c108030302055880e41c0c1648502140d42902d42000070210742c01074001e0a140b04003d907244540820354008903d000102034604284000070b01b00400916084401400603016051400d0200c2d41d0340c00c400c0380000c2141b204078010344913450080d4414034042ea0065980d1000459003409114185058420708014a160800090200300380010103000ea401d142e941d1032804695800f013002502c544400d44c0644d81c0d80c4e417003040008500c2001030030402056a5120b84900c0c00c3e40019084000d5501e500e400f0748140410450340c2d81c0d100c0c0001082c0d41c400d0a0002d605c02c0a158190350354141501301c05030340d008071428880483c02c0000e4012040e4401d036010311400703458507450b0456660400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 443462823 1250 443461573 443461589
    0x7090906150e010c0c0906141002060609040819110c040501050a0902090a0b1206010216050102120d0219090f091a090403050c0613060501050d0b010306020c0a0c0b03090105010f 78
    0x107a0041c0d803184140c10812001454800c40c0d41038540c4401e0100200c1e50700004c000c1d0f50302c50017000a1b05c0c90b919115554982261456101008004040d44565006207014407031134a89002404211300041521041c44410f01c2811070403000038400781041d2080d08002d0020f20805000580d140380030300030315040c1c5101034024400f0710700e0030359450f0180d00007408841c4d010f030313641e00089594a0400c02400440c03048640d15040c0b1304200002a04044511f103801c611000410400d10942c1d80018100c00b50300011200941c0d11803141022350024003035503082c426000c1501940d00302d0107500111160a0b80c81078190f040460b5070703074100c40e0101ca440c0c0000c032002c1c000c004c0c0e903000309250035036072554054001d042c51854024510b88560911100312100c406000c07500c2040804e04c1128800d007070260400b503407200e8074000309031a2400401014400205150780014075030044181c00e11402c09115070080f4482400e5845482c1c0c41d2858008a0303070844a58a020000601e40d0380d080e0042e01242c01031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 443464073 1250 443462823 443462849
    0x40f051c0201090b162f0f03070317010e0103170d1d120a0c080702010504051314010603020a12091b0b0409051005130b041508030711030c0319140a03020607090906 72
    0x4245458041d02e0440c98030100e00022103415000c1c103050002c0c4c1f0440342d203400556a075010519000c2e02c00703440701809107c440b02c4a001400500b1110944a054903080380d11498000c41d10b80200c0d40038030500294005003030903d80400c200b01c45403540350079151015415200c00c501c0d19034116226004010700d107000108100041004542004c00600c1c203c0d0040c940345191541304e0b00410240c4c6500d1588030714099403000040070610386407101e240909000e1a06600c0e02c503001c0002000440d80d1145140c11542e10341101c0100000b142504100c01e541c0360400446903034031908000150030911035220b10074200000226207056540b100026210000c00c0c96015001c902440001860702940540d00300e56603d01a40c502c0001007440030082c01e0080c01036558828624205840c0d00c860911180254440161401640c0d0041400c00d2415403104e100703003c0d1200b6080c45699060203800d5406140101b464803018140c1c080b4559100350b05544072091010350310608881101c1c01e40c460402001c42d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 443465323 1250 443464073 443464097
    0x7020a02090c1201061206080a0f02060d0e010527070f1e0b030a0b03240606070302030403061506090b0306030307060507050d0f051e0f040f051c0201090b16 69
    0x40d900d401d0b0002c8000081d20f0810365000750540a540c4280c010001103500561202030001c0b15004100103004000c000d4003220b24555204d19608040d04802440394034041002150408168840c2c2c0031040303008003c0c403050070141000c0d003a009001075140792a4010a03c00d000c07010f00018244121048010302040f468030f42401c22441c00e4980c001c4256a000d2110001880840c1d0310165001c0c100030700c400600c1c2409201018504007054040e80c1004002915510082c010b810704a5130152007503610316903800300340c0790403070a503c580d4100801444c541619540c0e0140b0300310b02441035581c1ca440d07244100d6140c0c2040801400300700e603c0c550642c010444a8001242074019680040c01410301038201040c1450380015070f840300e21081c0b840c03a910380c100f000c2414844c501e05e5501136104803108050070101c0c620314045000900c0640380c400c1440c00742c1d01b040020082c0390788651001081c1c580c00e0012000090107400e140d07000345e800c00c0042021905003800c80c1c200d111480034546a20030751a82e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 443466573 1250 443465323 443465329
    0x306040c05190312050a0c2a080c0a05041a04060308090a05451e13030207050d08090d051b01030218090907150801181503030302030a1d010e060a0507020a02 69
    0x840b06e07002d402003110902c5040b00180c91704500042820503c0f941c032142084540d00e0340320030305555100001c154040000c0403d80c1d150840c900003500c00944000c00e07600c14a201040402942202558019280c020000306001c090005405039a50444890a45039070311801c0003044001e01b40748810640500318a000061030032960440c5148440c5c69264100c021b01c0d28000c20818101d0310020502c801400416145104901c00c5a100d01d00c09036041301c000d6680c4000395522100d00480e0f00507414a5072010901c20f620f401e4030101c1034002c103040320401c000c0c50100d480d14107407000c0b0081c2456503004005950300070f00954107680c000048804808081000300300120328050242c0780a8024044003049007901c2c041c1c02c0b0002095600c800000794502080854000c100c0710030484264a082560f9180320110382d41c400841c1c1d054503001da2207488030070f403001c0148031801820000c10300c1c07920884641041034000e130408290345000d507040c40c3d90300051002583c05c104d54010040c0c100141000040c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 443467823 1250 443466573 443466577
    0x3020f091b16120f0809010e071206020f0a090e060a1805071e05071112071a042301022b0c080f030a05040b07020f03091e0306040c0519031205 63
    0x3108090480c0300d0b0203250740740c072a10a0356540041000895080080724070541100c0d500d42c001034004000c10071040710909494581000c0e01812606940135141b5406109403601a1241e903440c02d0381140e5500005034028220310064411020361350051030004109140c290409000c803502c20091454058031401c00d03000604004040c0320a0100c0c0b6424001c80c0d94a07500c00d410b5520443d2100350340d6030003604007840c01c080810f4101e40f003409131034042d0000324070104003481156080d8102c103181c06003454248004d0700407a013107418480c501704c2c1d4060b03050514071401e40b15030720286c00303880700440428012a84c1c101034a00714691381d09028070741240c55114090003d20385000d501e62504100114002c096590b01c01c0d01c03000065a1104144000e21030061000c41e0018807500051400b084d401850303a803a805403050303461080c04083e200c10150481642c85c0c41c01a040101550341620700b0b880c201031801900c0c0140c3d4054440790803035481803e1240742c0c080139250029420841c0409882c0e007110b2039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 443469073 1250 443467823 443467837
    0x70b03061302130306060828062304032f0714030c04051f12030c02041e02030a05100510020c06130302150a030f0912110102210103020f091b 62
    0x580c01c1007a00815001c02c1c00e00b0001e1032017404041101894001800d10700079035661003002108100c80d112030402a035a4090b200207500c400302140c419011805841048a182ca070301c21940b1000c42040b0400d5446850702032070700c160810030b003190b0380c2501c900140d01c4051440c1080c10783c01400144090300011140da003194600400b250303908030440d0045020b07540e041d1100c1d1071490891030038946468041c03913944060460403c800b0f01030b54040d20020940d5041c104040d0080d680c41c0e4031030815220700c40201e008808256401d6640341044000d00000340022140700310219450b43c40810300b0715041c4660704030003205134000d0005040360720412059070700001a00e9090081e003900040141c0b107910011036891491000c040e00c50602510140c20345620701841003c01c0c0c504462400000d140ca10307410300d801e00d14a000c0b0b68103200d088000d40280b0070ba0741d140c03940b602444000d40b110b42d00c030f80c4602e06a0740700381c6490b20700b0b100340c8080c0201034900b80c403480d54101884406400c0719030010086e04103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 443470323 1250 443469073 443469109
    0xa0b0304031e0e041113080f06010e100b032203050702010e0a0510140904060e010306060914010620100603030e06040e06090405010915060519060e01050a02070e010e060111070b0306 80
    0x14150300788042418200c001da0003242030350080c94554003455011309c1742c54010034612504944604d45102c541c101c0d1205801249845000480807032201300c510211001c0143d851490300e202c81007103082c00352a03070b04000022400500143d02c1210130303003480c034484007c842d0042c00240700c0155269042e01e00780001c0700c041d00343d0031003880001459940c42c00340c0d100a04030004a4866541582400300c10f0f160180c200400c1d03103052040200d610f1094200c0c00741100c07654a848416600c1101214144079400204c181d00c611421881035545100f652008084074840d854000c40502001c0034481c10303009174403904a034040c0c0d81c1d000402c14209088010ba0082c41407000181d00301955446004000340101c440702c0040d543c000c18070450810814600d620a411601c0c00107003407030540c2c0101007070f1080b00054100200826900c0089000700700300000780c5035074643d061482da114488003c20441c02c82c1c41600046808100c91a0310401240d0541a5583c00101e20714594428060003a51800c205403469 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 443471573 1250 443470323 443470327
    0x9030b2703070b010e011a0a030c0509040e010606090e041104110c030a05030f130c1e05040203150108070906090605090607150b040f020c030d0e03090a0b0304031e0e0411 75
    0x101440a00080c45014407954162265505008039008003840580107014107038200f0681c1c03541c54021100341d4040b002c6500e0041144c8007a40405c030b416016203a211900316041107000341824106411900551c2c0355640c07100c84041d561a0a0a107006040d68050800c1e1490b2004002c40c3c142a001020001c0c0c140c41018078002900149514690204445400103100441440700b40b01c440707000d8980190ba160080180b1140503210345052403000c0c032903645d031006100194203440a441107220b0040c580100b0442d12860082c2008040700c4450440c1750005914800150079039004240000c141c0d140ba030b4500107018102002610154031000075203038001030910075040095854078021600c0e4003050703000715160000c1001d01042d18903038808070481c42d00501000c0d64119001050721803015000c0400300c0d07440101c2c000c1c030b0b0451203500c000c1074001c1000c0c007000c15a040b503200114001c91280d41c60445da0700480708240e0718084030160002c00901c60300b84c550010b28042c1c00088900311120310540c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 443472823 1250 443471573 443471641
    0x130c0c050607080403080610170603010605060a03240e040b0603010b0a0311011205091f0b030109032c011b0c0e090a05120306030c060a03020c070f05040c09030b 71
    0x749041021610800042c040d0b808101c1050b41c041d4000313400c04400c1d144960740c128900e80140c0280c902e0714801203000240e0b0000742c0c56580035045500105005061683c1e10402c03014004d0140400004103026900c0c2e9400d8894424540c0310090304682c4480d0050b2115201c560f82d85000d0100500b10552541d2916000101640c45108040095100e582150344058101c1d0000d007000a03c00400590341d440e202c100a010310340440c91007801c1d0740c1c000c55454420300f0a06150014020202c3c050740561030013008008041e000041e1880c400e00a00641c42c081d64400c00c440c9003045160b00540c0052a07006074200f4125280350300c48991445848000a4161114408a842e0504964401481e070100d525001400014060b2851075000c642d41540396181c028040382e5100d407001c01c0306005078800108140e00c5842681074944446400c01503c028941e24451840800424011688181d00d080010303c46280241e003280d0442c1c5c0e00c03503012046556510f40e9070100c9696a400404541031443c406 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 443474073 1250 443472823 443472833
    0x5070b030c09011209020303091215010e100f03120f03090b0408090f0d02100e010c08040b0403030e030105091002091903050a062007020919090f0210020309130c0c 72
    0x1035445078040d0a41651203000b0000010a2070000c9114800240d2406900c90f0250301c5c048200d071003200c819101e0b00808028034410510b03060142d0040684500c83e070300081500d6000302101800741c806508440403050300c40031103800124080c407000b80050400f04101c403416014100407140e181d80760030001001da5068441280600c0708450450300340308001264980d500e081d4a02406203041076850380310f40c0ca8507a000c1007141042087d641d040c86849940940c450384a01c2036404020b520800160302c582d65200c02c1805500b00340011000300f1f502c483d54014a080c1481003500c1408000000c01c5065a94150900254414940550409601c1000079a031058803800b09000358410b40013040802c401741000c000b10341545049001000301c107210722041000300010343e078416804480d0052251120340108451504d0124078240e440e04101e82d10003480f180941c0090854000d80708807106044d01e0000300d0710307481022074542d4407072090b417008002c5c2c0900e50f000f848034030b20700e04011100c1881d64840c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 443475323 1250 443474073 443474077
    0x6090618030f0c05130e0c0f060903151b03041e060e12040e180601090b030a021507120e030d05090307260c09060105160203070b04091524050705070b 66
    0xe41c3d110307560040400040c1031100060090045052082000f01d0421000984030104480b81c144540314502d41002c540c0e86c0c141c219480c40b04000c00300d400d4008031031004a5204400c565511540004400e030800040ca6041101d105682c819001c1c040c040c40c510364100d08409045081d10000c0d510a101615448100308600c05109162030b0152a5072a110400c2d14520b00113100031005416801c9c00410000700050181c156608000c010500140310340100f40341c81440030000c0d5102c580d030038100d0881c01d041e1009000c050701503032400c5209050f0303040588000d000703c8809501a40300181985080b840742c0007800490304002c0644a40c40e070b42c1c1d82449034445402da400c00d0001c0040d18030f6840d8800030000100b841e141a1170b5201c00b0300e410800a01103009400180c1141060b5521071401c566051006501030030302c411080b610b4907101d810203030003002c00c4211207242e8038520002088003801d201e000842d482142110a20b00c0c2280c000441307103904000e50882d080d200d0b42c40042902850080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 443476573 1250 443475323 443475353
    0x80d0e070512011a031203041e0c0b03090d08070e0105071a0f010f0e04080d1e110c0d14030c0a02070801021c060e04020904061107020d0c080d05040609061803 70
    0x1001150400003030071300e10340c07940442d600644250701a4030b072014907038250016690b0040e00480c41210301c2d0f140b403510180d04000d0110040400316910300214806403081c02a500896031039088500c030112040040c0e0f002502621a00f010880740701c040440c0b076121384000c0c6101031207001000f120601440060211240644540210007204801440724150840c0c00340020300c42441280300320704007911000b41c035105058100c0503540d103443c010b0742c40c400320104802494030300c10010000707080f40c020f4640782c1e600900c0070b00c0100e0181c1d05418071014420002c041c210031903c807203a45940c950258101903648800d01c5413055000c1c40000061184083c405411959107409200002040c0082100219071650f04101c0c0020141c8080c80003584426107410b900542c820320004034511003a9120329103024140c0001d44c0102a01030a5081281e213440d403a04840340d10046801c42e0554520030b54641c09075009003c00960030f2041049944d00c81c079101c503d0321b0b03c0c2d02025184142c881d140c2441c0d19070528 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 443477823 1250 443476573 443476609
    0x60f0606070f0b060f090408030105060a03090f15060803090a0b4f0e1605090a060e0301050105032404020a0f060309050d1e113f0304080d0e0705 64
    0x340803c141403c103602001001c5c0702c01c5818541c82e03d0147c0d603a0b1814003040c051240144408524803056900a60004030407a41140e0782c5100c10002d8074240b001c500038840c03c14203c90401708009813204001041c1c809030000205415180c03401e02e00c141d00070b5000b8203c41c80360030642c48802d5942c4d140c1c80740007000400c2503001344910340401d002c0700d010313580e4807224420014040180c200500e00c003440906411401c00e43c0d0312140c0c2540c5080494040c0240c084155005030b5070300001070305c61b0b00a034101a806034154000d00103623030b03124101900c1d4116409040582601e43c888035841c0c8100107000c650041c40204582204c030b880d80c480f10512071058100c0e0f03001c286d58041300e10034400d0400044801a5203490004034541c01200e80c04e140742d001100c010b003840016400105508006c0c000040c4001030141042484072180c440b00700103844010b5002c0d100343d01400e0311a55002c503e000c80e4440e41c0c20800302898110100407403401028240402e0050380180540815150340301e80e1640c480410074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 443479073 1250 443477823 443477843
    0xf0c05040e0f0c06070c0509070c0501022b05010b09011101090503030a1a0d05120706020c10020a080f0709150e1002010203090f03090a030602090604080106030f0b18060f0606070f 79
    0x15851820300754000c2a813054500b84000d2002441c86481042030305c40c1500d0504a0744c0b6804819201e41400c203800400950000c100940c290451907843c003000c40d00b00748180d16000a102e60007088407801c0c01910414001000180702e254010002100c14200c4000002540f8060b512a6415900191032090846446c5c0003510840e1054000d02c03074062400701d489140100140e9100c0395248558184041626404180581030040d41c2d41504c80c6800382e1000e8406201070100300c0802544940c10942c0800d03010008101c0d550310b80c00c1e010340702d064140c9071796180701d080c86115a0030b403403a04141f03420002c1c001032400c0c0035119030000e54403000c030716000540c8904028648070305090704655958002da1040c0064000755803090b03440c6048035004500182c0d203070318450104204d44a503030000d1801e5800c11800108200000c0d101d030505074050051380035151103c0196014200000b54048515800540410491882e1404080d001a00106003a2a100700c541d28a5002c14400d03206036000d64038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 443480323 1250 443479073 443479093
    0x102030103150b03060403081005040504050c1009080c040b0a03080a1d040902031518030c060109050106030504030f08221419020303070b0907031703180106080a0f0c05040e 76
    0x26807004100582c8403440c240001001d002c046583c0b0712004101074100b0076050040303100c1e5122098418090b05001d001030010340f41c2410050380d42d00d01c484083d402403008071555841c1e18451800302c815541d07504013a2101a41050030000500300889400b03a01100c2c401d400000200460f000782881045030701c40c0051f40070785c61100721542081c160030074091802d00000b000160780114410428952a0031b202040d83c03100f40e00c0140805031410804814807001600b01070419000402c1c0c4d040300c41c00e403001e000f582e072582c40480640c0d20070b0700d006010400c03031244010b481c0c1c0103d408070390103207039060060748600344402c00700410409410b060f45c2c40d9201029a4a044405218101044918503400d191220a03036020a903280f00303649019007030b0002c07440480c0c041542440305034019500a20b2120300d040d5880d000700c8450344243c80c110303822046c90708050400007043c01000700b10703280359000c0c00c0380d804261540781c52198103040c21100026584404900c039a82c0e84541800c46010400524040300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 443481573 1250 443480323 443480333
    0x170721031505060c0a080c030405181503150a1e060f0302011202070c030b15030d080612070303021c02010e100618020306060405010516020d051b09240a0f080102030103 74
    0x1169000940540010020404c0c901800520b241c10f0941c0004019075030300b102102142180103940240d544035254030b11200e1250307c140c2025002d42910f41d040d41c9540100c504050f5103010112800ca039800c0c00c0c4000940c005c90542c4000b80d00881c2815001d0328170124143d00c0115090340e0012820624074010074015560700c10304203528100e20003401c602d80107007916034560091442c44001c050850142c00100e02100d0303400d9100300d8034000350031114044000e0307078003400300f80c4100c035158003c40d5200d801031465840015403000300c91b019005851a0f8140c0000c4501c001d0070840640290341d01d4468501c002c0c0c00800420325a0160140005a51130801c2c20302c074003144185070b801d20314900500912080769118000c403002c40c0c00900742a07907664003a540010440d035070f8842c00f0b584005601e04a505204010a0900c16400803584055004500908101c980081541c035481161004014010380391001400c0b0a28100010032020450340d440c074580c12240040c7d0400003117a5004401001045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 443482823 1250 443481573 443481611
    0x20f0a0305030a090e010503100b061606050109110a08070807020f0a15050c0a0e01080703110705060426090d053a0302041d0403030e0d0206060909030717072103 71
    0x60342250030341540b4081c0002e92715076034810800c4010380e840f842c2c203032540e82d90021904034a00c4e1080100544141c0d09080c001070400340b2921503000d040031105079a07020307408101c40000107150bc9800c0c0c15111000100c5690b480102a1021352040c1c4e41c031104d14500030054005001e00c20790803030981082202d00c80d41600c102900e104000c2c0800c4c131080d5656500a1410740014001386003d0200d541e9482e0110044e1a04400410041300006440e50500201250a80c4154050380d2483c0052102c005034180c50300110718150190307141402070300c0741071808640351242c5038040c100315206600d2205a5060b00e03c0100d41514600022001040d401c80008284006a0744076013011814107160210081e4200c80b41400d50b11000c1d0404001800c141c001c0d80502201b91880702100c0840090000195441200b5204a40703d80840b100099a00000208803a42c140e80107061844a801140368200c058100000450380da08000e00240301300c0d1421050305400d054140e80110712032041e040c004941e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 443484073 1250 443482823 443482829
    0x102070b19061a030408130605090907090b0f090604090e0f0601120209180106030512070213090f081803100603021306030803340807260103030c020f0a0305030a09 72
    0x115081c04000c10081c03e03052001510b19a80400c0340313035255194a4405007907c07a00e0f10700b41c030307184a40c1404550942e00c40c014041c0e001c029901491240c070f420800341c401802c00d00c1680c0d0b005208009401c0d0000b0700c20040c04400d107015240c00d040c540c4600415050307402c0c58140c00349a81c44010748204481081180a005181031120019000d00c03036000304a000c03d006105000d02410b91200f40c00c0e080c801d41c040401550418180e403510502020003950325030008c0016445a0001c0e800c000103c00a88a0b104070341d60f0010005030601c070f06030f80d607100c1604154800c40d19081d4041201c001e0740c17000c0c040d584034904c403208001170150451040204401c0d4101002d05074a1a200080c030000301c0220480e6082840e088400104c9807198054606111015004036140c41c2c04100500301c298020700401d01074280c80c0c0350f0a09690003461112201c0c0c0040ca0400d82e030458580041000c82e0080d040c80042d1400070b0281e034446860000829019421399008803070503030002a0f6240c5035a8030600440203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 443485323 1250 443484073 443484121
    0x306040c020f01020f1c05010b07030f170406020a0e0402040b070f1a010306050609070c052107050a0b060907050a0f080a0b031e0d0c030905060c01091401060906090219030e010b030102070b 83
    0x1541004409c82d41405100b200030700303010b0000401080c0e82d001e400c61900301011140c0c500c100e0f1516280140203500a0b503840c101140c4002c52510b080d2030309000366004e840314040c009040c80c2e500c2d02c407030400d818002e2050359003151928290480d95980c3d60300601a50243c4404642c6007490400e00100400080c400c20401c05074260950005d140450661406801610440f180d0103200760928214417604400400e03500c10b1401b0042000405a1541d1040d02c084407482110740c1d03003103400d4503203105031030300d003400294001c42c10302c1d00900607180d0a03040103003d40c1c00100301c410040800d01d0b061000207102880c0202c4015903140500410144141040919003041d166865540240c02c4c01001d004d854810100400e05255545007548502c6141d504400d04074900d496001c1c0150081c03090b40900740c0740904282011a0204490080380c1d15910982c00389504c140c0024001c07001040070290080107552a0311021009a4003400a001060300840280b4882e080003e14111804d0840d090360388 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 443486573 1250 443485323 443485331
    0xc031308060a0204050612090c0d05010b100206040c180b040c05070c1e05040f02090a1d092404060f29090105010503062107060c05011a03030306040c020f01020f1c 72
    0x1040d2100700c02c1e1912903600c0107c0f19070130348402c440d06040c101240b10b2990841d174900844000d011054001031200c460985180c1d46c4110948422611004100c0300500201181082005081c5034021040800b6481035400103016110344002015609075030b032881f0004902040250900c80800c038264001e0010864245140b1945001205001404d200705407003940e035400c040b40f4080690301100c1d100100140004003d90710f52007441117a0300d83d44042c007101e203003100014540d0140010101064840b442d1024032150000d02e604032001001441100c03155100e030741c2c1c00e002c100117000b41c0310221009203090340031300c0c405504502e40060ba602a0f51250080000420032643c03c802242e0b0003103001c2d100d045800c0c0c18800e4491004a8118421115106581c00050b00075030180320103107183d1289001b07211240b001d8400100882c107010f449076064000704003140187c0703015031044004070018010b8421152440e00d82600f240c004809255410350700141d82c805101155000300c0c40c241488034200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 443487823 1250 443486573 443486579
    0x70503040b06040626010b040207050d090603020309071203020a0501150503010e0325020a030b0a0b09090f060c09030f061503070e090a0303050c1c090c090c080c030403050c031308060a0204 83
    0x3010140d00140c0d485890303d0341101805c0290443d03400018060401d5699886070301c1c0166403007111a107200300103080000c012804034400e00840e40110401c400405500e4200001c500c442000c003078041303065109403240000054801c3c00769a01c00c2e03070100c011407840b528041c207142c02e4030048200e140290b0001c001001105c1070300405400c2422039070681c40b618240c40c0c404908207860940000c3e12400c604402c206004480760040707407a01c82c050314a40d0760341e2150781c0fa4550714401d10030b05540a80100300052200c00d084005040300410080448558000c2c0e4900d541c00c1080550354041140c020189054842c01c0401c4120000c19003180e980303015280102000d034407482c140300f005080581300c00204824820380019620000c00481c0301c12802d0b245040310b80c0c0100300240c030499152303048000014000086114041c0540b1450715140e000f9a01c0c0e0301c0200160f07100500450a104062041c0701515804201501e0320301017151900c00051700b040a00e910f0400014082030516004000034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 443489073 1250 443487823 443487839
    0x314070801030c050a24090b070b0a0c0305160807031503060605030f03041d0c0403140a110f030c09040203071d010306060e06060a030e01060b0310240e0d060e06070503040b060406 79
    0xc0c144240341c1a03030b40c41c9203d01890850f006070182d800600d2000010a1203012b00c001000510b014101c400010000032030302d5602541581c4dc02c07603441c1480c98400e0355100303406025401c543c1d403200e07280c60000342c1801c1c00c0740034107401da0aa030400d41c0d00035603070f420501442c24100aa02442d414004c000d41c03d00e40750401105a4045119040c64442c034034101180d41d201c403180a0328007941e840300d100f840180d010b40701302e65100c91800082e103414000b810603080300c3c20000c50140d414030018014107981d640721000c1c00030340030000d0070490300f602c100c800c006585561a949000b941084180c681c009514600b85001a45c0d29030700711610401142003071001d143d44031412500d0a003500d00b00031809004190b140e03401002c0e903900160030003100000300004400d5541340c0c2c0301039a600841c00c110324940d00400c0e400300010980c076040810815901076416140c94103e841311030780700d510049182e2050020140c1044401c3d00c4039800314001000340810006040c08460b0302c02420f88081000901e49086 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 443490323 1250 443489073 443489099
    0xa02131a071704030f0311061602070501051305040203040311060708060a0530070603140105030304090513050d020c04050601170a020c070b0c030d050105031b040c0314070801030c050a 81
    0x80140341541e411007100a030002c15043c3d03802190048405611640c4508020345200150ba4140300b41e801601d0005c1c5511002c042c100c8001403941c2d0040255038113000065079560b0104074001c0d0100e01001c40001c169030381d80011440303540f0a5445922035480d040e00b0a14010000e4001c100748011141041041d884621034801207a20480f801072400b07444804c0e0f0200c400c12014120145080304050380c0d200c40e40010004102c030f05640e400c11078111850444400e50100380140344d4190000c1108000c400f109410294002c510442d001c2a901c4d07255440e079242940c1159200e015810102c841c603242e1030075201e5254031090030b00385841c0101c0070b4444205e4880004185045255000c24440341c540410412803010349050b03c02a6a00c000c3d82300f038581c5c0d80d0001403450350800d00344000847c40741804142c00f0031150200580407a0a4000c00402c00505180740b0302004265907030342c2c000145118145518007846183e110041c965055041c108407401d010380086016114428007044038600314a2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 443491573 1250 443490323 443490337
    0x36101e0b0a0828060f09020102060604020f03150114070501091e030e040e07051009030b250318080307120e011a010e0a030506100825050108090709050a02131a 70
    0x7001c3d040910429402881c0d0390030015010742118940907212040c0b10300c1d548a4220035000341c080300c082e542c0e44401c01c41644980d0f55201254031090010450f9810707165604403035214141044500305413150388003440e5805c540c0302614a42e444024503030602074070344070403552000c05443c4200840e900b5200508001d481d403070894000c541d00e204408410304240060300143c40000d10040340b0356906880184000c1807800141d414880039004500e0540301c0c1c1c2c008071074506c40120f040000040b1154150300809283c2420a81441d00c02c0e0b110000a06000c0254800c07040c6443d00c19400c0781d101061001c50b042144520101c0e80f40403605040080543d10800e0160400d19045104c1a07010012402003800365000030407a00c550030500c802c5107204075094041c2c86055080781d0560000051040002070f2291501561004101040c0101d51040141d00e40c0014000119416141d0303400c40030342200c9045405011203580415104910102d495000004151803031500c40810502d1025900701d1140c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 443492823 1250 443491573 443491603
    0x3321e070c0501121b02010617010b010905190306140414060103050618030d11071511030403030c03181101030b0d1106130902070f0b36101e0b0a08 65
    0x34070260b00722650700040500c1c030740b1208400740c0717501c03031140a03010300040d01803a00e0a018003100100324100503c14170850050503500c0d0018107182c00240000160010307516090f0f0910f8082c080045900c500851951945122841400b1326160600c040c10b00d042c890701500c00c0c0c00034801000410400207040350000c8800000080741003600765035502c8c3d8403509520511141c106144104110525405080901e0007182c003c0300351000d001700b40b42200c1e0b2041560355040d00600204021a129500c052105011070800042d44002c0000010a40074210000c0351804400903104049585c54011034034402c5090360362041118590752001d00304000301340714600a0f400805c290b2881841d01c09044000c0c4070b0904119170340c03030072400c003030041800c01c40081e01c2d000c00d2400412030110000e802e0b40700c1c1c0361031501710303003d5440c0401611403232000810760b0301101d202e041001019400c442c440e0340c504a115101a14880001541640644442080f0907200320b244035400c018114000c6450800c580d03501e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 443494073 1250 443492823 443492837
    0x220b061804170d02090a081506100c0b04031205091f0b09040807031803080705060f010302061207030e0d020307140708031606020412150b03010203070c03321e070c0501 74
    0x140603c0003c2c0075414070307251b11a209090000e1507183c0130030600d02451292010780c04580d01d013014018041d400c0d500680c005045e14010304045102951802e810078880d01d0620804901580c0020039608242c0d00102e140e04040d29926020b44c01072030001c9078150504090103445d003120002054510b000b0405411008005103520030548241d544154000e000806030140c1d9840e4201801160802c40d4100ea45100e1440030034456400e40e00d02e40d040743d90042c8003506d080c14402403c001742001802c10750034103481c0e05207403010020a0001e220340c09680d500468990038142400c0000c8080344004082d40d4008400c10310811340c000c4201c458541000310b00320040469860120028440d0364404a8110040031080c820000c2461114103400110b0009025030030b801c4041600300e20065807454081000b5041130710000740074078095081d201ca44901556064070440c0c00308141c15403c2640380750101c000842010a07890308050340343d9000300701c11403030034804070303036160580383c4604c3c000c0c1414441c2d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 443495323 1250 443494073 443494087
    0x90405160f032304170f03220210050c010b041b08010e0402060304080a0e030d1e080708010911160501020a0f05070201051b0c0d0303050a0b0105160308220b06180417 73
    0x1030300041500c0942c1c0200c5649408640f502c9070242c10554505d4101000104268544203000d03036458230090b0028418080c07500b1844060710350340c4c8000508a25035403140440760943c0d485114030a10700c0700c00c1070390320018078501a0051084805800a00b1018022014007026803107500070341e0b6000d68000764007940c419500d03070151064401d00304100d90512a0720100c02d50306500c5140d04004500705070280c040005014400c0da012301084030108000b507254070042040700c0403030304030301c0c202c00d81000920b107090440340c2d00001e01c60694800b621035039000100d03d03101030341c000780342c1500001901d8001e04102550340001e00902c64030b48004607110900030a006214020302180040d40740040001c400f450071894098044d20044940c180c1e04ca1a0500d130310035550041d0212a0302115000b00c3d010351a2940c0d40507034108d140580024003024280c440c01400301644007100072020301601c0911030502d00705042103003011848842600550380c0106100011314240c803540118441c2208058550792 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 443496573 1250 443495323 443495333
    0x12010515010309140109120305180d030c090b0301121103030c0d081b12090c06091809030f0f180414040b150a03210201020a080f06010302090405160f032304 69
    0x542e844ca20081c5520341780302c1c8010801180c0640d10200110b46090240b940d0300b42c169210788419681796025900015101e41e4520b10a500c5413414000307504044400d241c441100d00c19a8000741c2010042d4141c5910100500c0301c00382151260440c1200194500451008081d0303d8010300201001840501070115190148542050b104004020b144135155040000881071008007510080720f075004000d2202c00f5401c1c00401c07101e032000042d0040d8a289d002a4004000c1c0400070500d0040d80014420011084000c000802003080c404141e241c03502955500c1296a014680510f0b02c91858840c8440445080d0280c50340d02540041c0904104d030703503004c4242840444c6103420f030b61040d0f0210020040003402d43c1006243d001404484294030300f51102a0300302d21406542030085034080d40000c0c101e00c40041c1c42a84118185070160030080c114022405440c802d45842141d0080c0c3d02041c299150f0101da170040c1e04c88135150922681d9020010850000c48200d0160203400e451000641800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 443497823 1250 443496573 443496593
    0x2030703170f0a0e01080f060f0d1e0503070c05011d13090510060602011a031213051003020a031521020103090206070308160809030405060c0c0a060206010512010515010309 76
    0x48480b04019036201c1251800400c541d5210441902248174840441c100c031100c02c944a1140710003510701504d40c4e01c017100b0009006020101280c031191101c9409640d40042c02c0000580d82c070131001903403500c05e6450800004500b5810250400c94520000d05100d040418140340d64007090703996030038640241c220b001c06040c500f54003400c02d06c07a0034044402c1c0e00e100c5e032009045038101d41c003c001d5901500ba128040c0700e00284915410390040100d900c10400001c001c0507020444007050b8030599444011038100302c40d0340e40c5d0781c01299000c20040c0c04540c040c016076505000d10704c0703201d01c07050509140380c03490441d41d09207422040001c0401411a4003c0e40408c2b241034005110340d40301c0307003940303401803020381d04030f039000041c25070341c2036803074009005200352030050025174003841c2231a040c082840060303000303625640e2151140c01420078403a124001403000ad800154060010340d0b04080a1201200c6031046a4912340e160200700840404a036500c103000f0b910074640421043c0d90341c03c04070300071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 443499073 1250 443497823 443497837
    0x220608150a0311030118080301050301110c100506180a06061d01020a3f0201240501210906050912071a07110d05030f0c07050606150f130f0504090203070317 69
    0x507211b0010301740c2071040c40700c0070394101d40301100240f01003405000945802d005102d046040756202c2440c203045050541c00180c0c1c02000940070320041c0c11141c1c0c3c000c82841c02640c0025500e0b943c3c800c01e020701c80c1c0c0400f4000781d000000b03214440c0c00c500c940000f5640c02e2050070141011040c1035140481c0da528032802180000c10341e1a1a803081403000401054841408059016620300002003031704602010004090f0141d610020014a141400559200e200122045100c01e0701d01108202c4556500c5096245805894001001d141c20394040d0f20f4800804001c40355900c0620140c0d00152802c5120820200c00070015686903c61382010f80da80b126050b134582050003104108110540c1c004050340c407600501c0d403180116200c04840d03001c18401e0301000340140d0440d200007403a034242440044100c0c02204011860052000c200007420b404c5542800c0303c030f4900348420881c01200382c0020018003c200c0302000302c0941c070344c0065a9110180b0009144030540e07004c9445c0b40c00c841c0c003038a1203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 443500323 1250 443499073 443499101
    0xc09040201051209250801060e0c030408070f0602181809100f02071e05010c03090c03060b0d0203010c020d08060303120118140106050405090f160e0303220608150a03110301 76
    0xe2904110481703d40030300d14000e0040035031a014000400640034031310f0a00607442410405c1c036540362030310b40030301d6603002030300596440b0b16542000001601c0c80c8014148009140d85100003120b020701045401003403100ba0a294003030281c140000010b010403801e00e540d07843d8200207100028110400d010780205240506141035484020030160410800350010310302c40c800800c0350b000c0c0c4010603011500c203901c0240054012241c06d00004000758001d0a6800009181c1b030030110650380041c3c03d440c076900d40e00006800c00100b20b072446070403a23840d542121045000d1801c1584101251a01702d40c14820f1440300b81d5200c2d104940400303543d2084003403990323140e4074030815038456801506540c080c0c0703c1c0c0e60080e001040010350407500c25001178015030a4030f42c250b126521261040341e030203580103102c90b4940001c00501081100320341d0415800f500b40001e9030b0b1b100740b42c0030b005042c03c18014040004000d4140304040c41c2d540300360301300d010b8a5000b005040100840310110380140b130030a0070440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 443501573 1250 443500323 443500363
    0x30f1b080301081e1b090603101b121103070320030408030609070507030806060a1103040807150504060905091306020a020a0512120103020d020409050a060e0c09040201051209 77
    0x2091400482c030001102d5541340800e21020544006540da104100704211102c80f02460400e81d510701005c405030400720041c221884000103045442c00c46041c02160380340c2c02255240c01c1280f503000b813940d010200403400d04010641050b4955019840300030610810980d85010b00051650080a0f4041a42c40d5000d101c0e2646414540301d00c00343e005850701c3e84580e924800260440748980201e6a04690ad941e41890507100c0701c0078851703580c02c1901188140003905e0003401c0d1041040001e00010909100200806d62404518024a64110792031008005040105110880c6c0101c010300480e602500c8100f040d583d24480c032408c2119035140104031b1070002034602c00301a4006803042c00e2a0240e019105103a0711152410500e1151154514403540058010400352908a6840c04058005800406c004034950b580604207400080c045442d0b60356002c1e104038000c0c0411944c0610002540c0c09071007414a5000a025401020503146040c10802c000440c1240140701e011102030b00740e03203042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 443502823 1250 443501573 443501579
    0x230d0209040e06100807151d0a080102180907030b150a200f070f1a03040203030c0d0203030403090e0103080904330828030f020f0a080421030f1b080301 67
    0x140068036481805e1442c0704141c0003140d40c1c03203415441c4000022544895244a00520314032920214206641d644240c2c1d4040004421030280000d08907040d00c224500e0002c11000c040184108000e0650000c140c07800b240c0c800c0a85803844102242100d8424283d01e03075010440071a6403101019170000202c0c01c960640c03134450000174103082040d401d4170580d4415601ca40a503503400800b449840c102c07050200001a40d44803910040d9000b81c00507003524640b80c1103095852a010301d03000340d14016840001000306242d84100d070701020706000a540c10403035146444844082c040c6907801403045903a4800100c440c0d134103052040340380b0742007401068190700464420448200a03c501c2c0782c94000c003000a03112a03005800710b44550b03092a9091203240f2103032000c03030b240c80c001c0c20b41000354464585c440f103101204000f001c2200744620410341da150b040040420600759011808803151031103409800001c0c0d0007a42000c0c50400d18a0103403030102c010000e074105084901070180400030008004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 443504073 1250 443502823 443502841
    0x211b0501030c0f02030a140d020a080f0703060501120b061303080d0c090503121606050f0103110d050a0b100e0901020702030c0306041e030302040e130201230d0209040e06 75
    0x885909032010080d0309140641070300c2060f0041c0382c9800582017000030a1003680a403c04d1a160b2104a10603418a441114103030100d91114403440b0218a005040003100e500c4030b06d019500809929080c03010342e10b8240040c10030440c4040110040e51103609010b10303900d801d01503502d0702d14540300d807022081e541d080a210325844101010007003030500118a04150003440781004507500600100a4145003181d940b0158000e00c0c1c800c501c1550080300070001c14454040d0320301400b074417840704409524602d0002681400c901c0303110300a010288403080840c0c80414007007002604940f510f0281d540381403071400040c125070807610240f8601c5c000d121100d141540604845803080e411500d401c1e540c2e4040581c0d40c2d00c21100188100c00c0d1390203e800c003858021060721194030170700b40076040c03c3d254003034880d00c1303401100c0c03c4100d1690711540000350f41e4486640c1c41505140030202600000609000362180704140000600a4000445000c00d86441c0e11031070f1690805815600703141840b0b102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 443505323 1250 443504073 443504123
    0xb1809164506180e121602090702070602070f06170910090302011a040501050a1503150303111203010b0d09110405040c0e09070e04020f03010b0a08010213080304080721 74
    0x41c01e40d0081c0365407030341c1540100c14070420030321241d07610080103440200e6000b000540c2c411038054031084000c11307a0f86c0040e02c60030922400380304250050050f4904002c0008d1400010b03500c001e80003c42d181c0300f042040e4000c0101503100310076076100251035455062031450701000c50046054286040f04480c180741d41036021500301c9801d403080c0050070800008220594100380552540325140304d00c100400c0e04840d80340d095001080c01c010407030f845106001c1200c00d400d54415000310314280491141e45005009644c041e207549203800e811941000200e0800d8011184100d41450740c0f954a4014020018003880254000070411700052a051401da101980c00784928024005074030b01140400c880441d002d07040e41c0c1c55005110b040d658540030480c10386500c9507110f402d55a60071900d5501d072108818030010b040000009a0344000c0f03800c03a042e50311096800404107400521080c01110404194103040b44ca0804035407a44126045142b254100211402080035048000d003000c50154140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 443506573 1250 443505323 443505329
    0x316080403090b1b070f08031c0e060406050f071e0c0309030b101701020406020a0f02130504140c010806031504052a0108060f0a03150b1809164506 65
    0x45d40c45240da2084105001c0005000c1d5076803e820a004c020785a548951901804003e01040070a020035081c00e4241401402d540960340b0a80300c4041004214001c41055004011483d040c2c3c03040c40d0300da108a51442b00c03202e9100404c03c4c444000010305118562003005150440e03003403170503401c0094500f84104d030544509224260610321098001c01d040c8256400c0301c880e03030040c000c40900c80c1c0c0c40801d100b0007003600700c1c0d0050170300341d00002c0003006100700d91240d4890142242034020300000246414031028202c0d04109401c810800d45480119484074114125100d12101d602c50f8030f006c9051104109400713810202c01150150540c19410f14004690070a03226070015499800500c110203a4018445401c050711010820001d0303044408074503219041c010000d0b80150b0500015401c07c8990408550340d025002841080301d01404072460300d0805030f811009841c980700c4141143c1c60300c2c0b141c61000107c040d00c8201440c1c148500c4090b940c445c540200c0136521000301c45d00080c00140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 443507823 1250 443506573 443506627
    0x302010204301e0c121101050f0d18060e0c0a0b04051807021c0503071e05070f0206090a2706030302060c091801081f02160213021612080a020316080403090b 69
    0x1000c04105501231000c503014002418a01498840b00c601c00d000030f8281c0106003003400c0452010000400c1c1503108003d107801d000005050304940d1002000f03503060344c60300848040c2c0c4040101b0065035440c0c0d00111400224264240d80c26941c1d40d00030b904040018140c250b581191480040e005036100b00114807600c01038540f40c000827000c2107240d482024014418010034010005000882d100010000310184001c02c01403030081603a02207400316006611114101c03401c0324481c210880300440e561010140c44c90104402461610020342c0c03414090524445079070005403c200b1915070403d800d20070003641c0c00c0c5c4400313542d442507401c0c0d9981c0180f0710390016400c4408255604c0d0014000c80f07030181000d580c280550402ca030200a001408400785038040395003008800044500e40500d44545402007840744500707561020083c00f080c0700104464811072041003000021402000b00800e503400514199420340c0d12460140d41106098009014200000c82c440c1c0202800c186410b502d80070003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 443509073 1250 443507823 443507843
    0x3303080f07140303042d05010c050d0b03120406120b04060e15010c03080601030e07121a0907050904060207020d050f0f070e060a0905061c0302010204301e0c12 70
    0x2082c0303910b900003510024142440c51080b031149140c0929120203a0a13090b00102c1082d00d00d82d202400c40724001c4102c808034501080e4003504ca42d007803083c001064420740180641a0100800c0c0c0d18038850340c013900c414012200c03094007864920342c0c02f51490040141040000640300d00d1480a141c0c4121030702c1d21b5200b00100c801003994400c541c00c2c08815411b403900110f60300c40c5001503000d0082440101820300c036845001894050904140b480c45010741f00c24030318a08141440c0e200d00c00c0080541500740d019610410440d11034400701c0307078411f4000d4070050304c601e83ea2002404001900380050710507c07450a1350046030170085014000ea40c90b810803100c80d41d079204518112004225051a803000c4450b004101074101c0d500001c1d03000340014800342c891a126020b00c0f150582d01001078005039408a4207101d01001408001c0000e0020203000280d080881c150ba030000781c1c3d0350750003452074480b584070341d840d00200c0e40c80501c15903102030200c4800e6254401d02d180e044090b90306403810000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 443510323 1250 443509073 443509103
    0x912081e04030201090b0903070c0603110c0604080705070e0f071407051b0306061e0f0415030c1805011203030e031317060601050712080c0906030f070201050105043303080f07 77
    0x10440321200c0d40f0580c0d14080ad890848103074000d0072400c0404000780c1040202d0385007038005026030340c4254402c000c4680c54007038a00b00580303400c08070342140d4043c00e01001405540e000d098140b0b54010b24030300e884041c84854010420320760169010007402c03880f80808003111415080441d24055105400300c0751107544030800c001c0650951800d507030f02c08030284011b500c81c0c24200703854046c1490252020803451351418401c40011010350054414081510052040200400c030f0001c007074246003014080380d41080a801721000050200a0034541d6501542003220300030300035903000c02c0060141c0b1244959a0580050030201804080c005018590010b46158001c1041d43c0e1440d4201c070092008500d03203002552221400703044101c041030103200030511a0f031607100452050006402d885480d080ca040041d0a40d10181c1001e441607040403a070744190317500c0003030607041210701220040d80f00c486030030004401081a04060b14000001550040200c440030040c110184141702c80c8400e110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 443511573 1250 443510323 443510341
    0xa0f030f0501060c03180f030b0702010f0902011e090e0a020912010c05031b0f03040c080d020a0206030c0d02161a07051c0207230f0c01030912081e04030201090b 71
    0x2024043d81010905440080010910881440c8900240c2c031032151116031b1220780281c0c07580a0b03a481120080c110b0302c10400080d50a016061803040091810b00541d000355001800020051020f9030040b05080e10608003140718052010080ca5010340b600401e0038881d81c0e10001c2d501c19400385008583c2c090316450b881505114a07080c4c200030350782d042e04580b180d5070702409002000110094000c401e0000f005070503020002980224450036072a04124034008459060481c040c0701c3c9415500420212005a140c810449500080c3c41d140e07035640341c204001d80300c020b00a6100d20341c00b41e0518000c03141008040700c3d0f40072000d5011040c6144d140e4981204589501c03d00c92030305030108500e000003900d0881e82e0060000315100c0c01d61500c6844002c10a000e18103420404507181c0d61100300d1005122100380094000d1120070f103002d103c2e002481c1c50b04000a46880c0c41c640c10061040002090814045400c039104000340b101d10b100c0d8100360500030b018003000c460070745a2200b1140481e08010b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 443512823 1250 443511573 443511581
    0x305100e06060a060e0a0803040f2c0601030c09120503041706091f09080d0c0e030f031213140d080a090209062808060a18020901030809150a0f030f 65
    0x1840040c60f2000c2c10b030402104440c1920520f42d901e0300b1400c04080030401003c140050006405031801c4940c8042c500000540004070312042c40c0421052040150b1801c1c17036032507070254000000c3c24003141c2e4106c0000202e4015100b5400402004900c1c1174240c100300c400302c010422038200000d058049420f4900c0c3ea625500f0603242101d0341da201c0b201c40341044e0b1212001d40008440a0300c0080d02e4409511407003015481049402c590996448080c0502c1c1e8010025019208080c4c00071308083c001441c2ba1030380c07441010780a41c60105030b00c0001c1d503800b59564000c1c420592050902d45d10b048650070090392204001d41410104603404002001400540f040c5903045800078821f1819031507070818000c1802d1042540048455030340300ca040c600700750002050081448400400c61440c02a41240c00c440f85061022060300c081c1390001c002da1381e1075980505490b001014640c0d01c100c2440000c034114600703c0d2075079800c80045050b030707401500900c88071148100c42d01c050251030070f0301007890110303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 443514073 1250 443512823 443512831
    0xf070b0a0606080109050c040b0c010b101b0224130e0c03070507120e10090602120310060516060513021c1509030e13020a1103120711160305100e06 65
    0x2903043c00041181c0e02182e00141e410911210003581fa0607180c44034120a80e10113241c1305040da456011020b5603050890a10b1100710f85450014049445095480400c0203086d60103403184103580443e1040e0f04880c440300ca841e415a943e103d03911080010300311012101c900c280040700c034040c00058104054201240c3c810016a52224034144a070390306c0e0300f520b04101944604003c0381a0016040352901100e020364401c154582c40740c55440c05400030702e001190760904050f072070b0a0045c480c50158442d65201514040d0514940310314407880503a00d0700510000161465003414140300040320b00041005a0900944c0d9098041042c0e4120800392101c07050000e04032010a500d14440782c4007640321490f440d01c2441d29403d03000c0910005140300074854600214580d00003800310070a5001061082c03000e00f810051800c0c041002c41c0b03c4c0322010000c200005021200080c0b0b01101800e010907000c5c03900c2003080000c8103899082c40c0d561824442a15030704249840e1803800031260004087d486 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 443515323 1250 443514073 443514077
    0x12020307090603050d110c0a0b04230f061e030a020310090e060a1107020301020301170123070f030b121b0a23010c140313050a0302010804260f070b0a0606 68
    0x1040c5c00005007101c0d40c1c550781c9002d41c00350240800c42c2d481c80c1d8401503048000c000007102180c4803030070000c0e96404182004107010102d074009405008544503540c2d1000d05a000b210398988407503050210303c1001d0240405611110300c00810801c0c0c21400b5406140140020000e50810549550110044400040b18244143d00150008803901100c0c2c00c90448400fa24119a0034000164082402e84c0c01c02e0300b000d20005140110031302c2e280801d03c10780d07900840207142500110351902d00f030100e120001e0520020820b94040c14026103002c0c1c0c01c000f64491003c4d09850b26004404005921500b0009801d0102611001c48041529204031040160303500309402ca0700c24a1000c00b004035003241c07110401e05000064941d0300120f952580040c040701e02d000095551080031911100041c0f0080d04203d00c03580c40c0c141e040c00542da010740c885a21542c0100403045004101407003401e401030f00a2075140040c0e000500d11600242c50019040f203d1040c0e44d03415881d00c500a6420036540d0750302443c80 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 443516573 1250 443515323 443515333
    0x160f0903020d1403210f06060f040b0d1803030b010917103908060d0804090b030a0803090a0c050303040e160513061125050f03030f041202030709060305 67
    0x1c504083c151000000050040b00c1c50080448822085401140c0c800045030840d84208103811541180c00d40c2e00a800302d882601e041d00e10241800c030350166018400c00e10b41c000c00c514000c2859944541c0091f9a01100100140c805143c020098034200502500152265034001170101050030380c1801c444042c4090305894203202d10442c010446902240c4901087c0550b10502001000c082401501c1100c510000340170103401c060881507016284d0340c01150080e401c44003003449601070ba004d43da00800b01003819524400041d282680d90320020345080c00c00000d014050600007820403038148030304036105255980d9802c0540364001e601c1060f0341c804c1403200090346400c2100c1046034906a5040050170404103014000000e142c541003c1e003c545043c1070854102000c1152a150b1124117042245456150301141c264000c1d41c840c66001d8008601d46d0b041c1c42d0390910a58000b02030045000351160b82e20b40d00c0d80071800020405038024000d44a0216500c00540070f95001d0303c7d00040200707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 443517823 1250 443516573 443516599
    0x130c1b03050a120902300d12050c210a0e03040302030706080414060901091a061f0c200a0b07030905010c0c0302180604050108010b0f040f0b09160f090302 68
    0x180c0c07903260740f90101103215520252000181e840d61742d800000310000d81e40003441c4400c03014980c043d0200100f03003105940070318400071006602081e0002c41c011001008a20350f103411115460302d00070451800c4500c407421a903110b0310003d60002a12075a0248414401c1600d07514615480c0d200f203000103500b41e004018180150780c0a1907002c0c2c2c0040c0b060002e1100b00114030702003801d011050b200482981d44a490b00002d20002c54005002080703a891190240c1c1804c81c00143c0f03420b44400c21740c6085100907412281d060007100c3e1180d50681045c0d05485078820010404201d40c3c1180c04a441507403062004921490302c8001da91f0040c0c1d02d925035101150801006403000e8540ca40c0894002c4008000400107884091981119840c00340400c60903080c203070f0401c015540c2c16048441e0036850103c6480b142e9031620185407060006440009801800101c0b013400b4282209039590807401e000203100c2c408030003a0b403001c3d040c02c085e5504c80300c0308580b0f4401c50340c01c5428071000e980f100d17501ca252 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 443519073 1250 443517823 443517827
    0x50d050a1b0f060201050412080903180f0d0507051c030212090d0c0306020702120d0203090f04060806010b070311010c05190c0209130507080604020108130c0302130c1b03050a 77
    0x40c51039800c588030801c24556071044080c4680003940c0144005035160f0303080c4000c11843c10341d90000011103042030300d81ca14003150041d0740c070b01654142c1c49280b4a0310661150649074160200b400c414090004224243c0c5400c040c1d6071904079125140c01001d0401c0c124031001c6100c41803004e0b90b90705902a00100c0c41001448115400941030964002c030a00c1035840024981808000214800c4101607160b500c0ca004021415031748402d03400310754201c901240c0b0141c1e8040304440d178500e8211041100600c1c040c001c54002c024a40017250b99200b0034001244682115014100440c480c0d601e54030ba01c00c184007605c0c2078591648003d0046081403003030303a221203015040320750385007550310b0201850381942d00091040c2c0e105459003034040d4890408042400414041c0d100a0300081c0018a540c0c1000c0d0300003000700310010400d01d40034615100c2e080400c03044040000c001c640003000340f13050317440d00ca05403001411089240350104600350000303802044a82140020b5903010b4a1300c5040c10619807003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 443520323 1250 443519073 443519093
    0x100b1b06010b130e090f0312091c08010b1c020c03070516031703090102070501061707080f03070b190f1b03090c060503091614030f031309230916050d050a 68
    0x140c0140f1b000b03440d04010090802c1001d0b20b00b40303c0d100034081741414003602c903500b4401c1002d18445030441c8215991003045e0001c2d0030a04540c80314000030b9450304082102c403800c060700310b08108201c1c00020700c19000540000034046075801801030320221540030050840070040d501c001882c1403240c1d0a00000e1200c000061a80006490001b500d0506555036182c01c54a003500504207004006071140c0307400b1030411082d00981482402001c3c240c10b004c2d03156640e4003c901000303011a0341039000410480214007000301c0c02a01c0702080c04a034014648a001030030800e0580300a08001c5c400d01c40c4614885c3c022a139101c1d401003003540d1003600340346040322994801000c0a6851040f034650107221401450000c1c010a40c01d44104014103008040500304800d61700890495442030154204102c02182d0904c1216901080014440341c505040850030081400c03030601c1121010402440c0c0002040704a05901e021249104e52920b820401042c0c864180000e42140d100c1c0b50240c000522a00d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 443521573 1250 443520323 443520331
    0x1030906020f030405010c0e24160506311e020303090d0b010510020609060c0a020106050a1206200a111c0f0210021603030203100b1b06010b130e 64
    0xc030240c900000c40c004546180d2090740c044a890f0b40d11401c03008a07691048819183e6041140e500d40882881c520300e9180c05000720303240765036600009510034421246007284503065403041c1075420b1841c000305407041506407004811032940c00c0800b1a0303c2c4052920200340015480405440c1d05015108013840d580704413075040b81c06110400c0340106030b40e640c821110120b0300c00c20464030b0300c0d070403e0188111031140c00b05002c25540f202003408400d90300030a01d00d5200c3c60b481540e9841d171040c003804a0140c2a1641301c150800e0311444086180c25005c1108641503000701418004203590300d40c2540c60000c00341d940c002c6488180300c03802c0318510400c9400300101c1b01c0c10071580c030943e03014040900313540820034150114150703000d030221203501400140b035403690400c021400c042d48110f00e855071004c0720b40020101075002000540c142c280d050848081d0a0000c601034440e258600008113421014903804d140d40700b0003000007000c40540040700c1c15100d0603a100048c4030701d41800290f400b00090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 443522823 1250 443521573 443521583
    0xf0602030a140a020a110d0e09091014060418030203090d1505070302090102070e010302011e18060f1d060409111204060f06081519020c03040b030a0b1c02010309 71
    0xc9803002120403005541c0100c3c1469030041c0e40d10300071800030302900c052007034100c280e07002012903040760307a00115103845140d0103075a0400f07590703112a591130a040c601d81036607901c18030f4890131491014101c00441e2081c01c0640d001c01007410b425980342c1841c04100e00c0100140d10030000304026040154030440c0292207803c1a402c3c1400001112040c2c49048500d000003903404079200d0880d603810407442000b0000401055101d5055800007855603082c20030001200220018450107688508040d030030300300c0020554024203407582c2c4014507410316051b4003030000317800411401c010f40c00c020034444000d8000f40369610f000d20301950a17016000c1d0340c21121100600303118000100300314200041c4940d02c10140024841c2a96100303030200c0c0c0c0e9580060310294018091841100d00c854035050300002d503108660340340c0b69810325000c040c0c4110706a01150340804980001c0c0c405200000d1801080c2c030340f1041c00140905400c1c40006090004e81d41840301d450060000503500a50022140078003a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 443524073 1250 443522823 443522831
    0x903110d1e080933040f0204050c04060906030b1c0b0702011a0904061d030f090a14090402090604111b0f06040507060807050d06120b0c030c1b10090b01060e010203070f0602030a 78
    0x61104d9584030504031820344104280070300341011850140700741d503442410261294185810190010305112150240c4418596514810a015640c04254405000d8040d41d60603a0308514a070404034030f03a082d50100301640c2043c10b002d103078009400e94412603050244c03118100b550f5580703880c0094203580c0c101c0454a8103805003410101d1050004009005000b100305540e11064414011203c010307500482114090740e10a407003d80e200d2444a800603012503100c107250310b4503400200200717041ca005c041c0340c241c0014011560401d144540081081c510241d4030503105178491580c49a100710b130010419048140140100e500542446411070075610b81142040d0ba42140901113400d5030300300b0000300684170010030410101e07014080d480180c6800d0f0a0450034102c4c88100c0c1c5014440884841c58030003201940b008208000030b4280a51407041844200501d0810404250080c004c02c0002101030700d0740300e000d500010803206600e03070001c100140c800141e16000000e40010340303003203001921 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 443525179 1106 443524073 443524153
    0x312020601121515121a011410020f0d120b0102070609090c0e04020a08010e07020a0c090506060714010c0e0f030703060903110d1e0809 60
    0xc4855032403d02c0da240d10440c07000d00b05181d10402d42204510001410303a165201c00c19041e80541c03100d0800c80c0803016000e00c9107009019030302841c60210700304003242c2842080000d94441600c1651602c2c03880c1c01e141401d01d101c905600002a0300349035490004002c1c0d208500d00c0c03480074002860182d240031006860110a0710840e00d07042d59070011441454000c000450500c10001e00c00c41d40c41c0220070300608195800c1c01403101022548002a81c41d9000042c070a261580094654288038a0180c5a00240000608a98125501748180c20010307407040d400c154105900000401c01900045000702210f10220005125408102881c1d11607100482d2000c1525080300c03000c84c44a8560070155000740194003040c1e104d00c40c008180442d03e42c054051801380301c5501084005583c41c45c42220499020394000105070000d0391140400704104003040d21240d01c0742408072207892 = true := by decide +kernel

theorem cover : BRFrame.Cov 443345323 443525179 := by
  have h0 := BRFrame.cov_init 443345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 443345323 ≤ n) (h2 : n < 443525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
