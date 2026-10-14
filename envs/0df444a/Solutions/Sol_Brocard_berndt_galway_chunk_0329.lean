-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0329
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:14:53.282563+00:00
-- url     : https://prove2.me/submissions/92011df6-da49-4fe3-b51c-fc26537ce705

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 58992809 ≤ n < 59172665 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 58994059 1250 58992809 58992823
    0x804121b0b22060f08090115090504050c030d0203180f0a0b09030708061e0417030c12010902040308091918020706050618070513030203011d01050f060618010201020714 74
    0x2d61284450000b20140901d0b03400e240c0c83c4a00740200c2c0860440e004464000d071825580030105100101705010700380803448170030405401688800d60745500344004d002c410040c0320742100c000e400600040301e125202035900c1c01205100603000240d1080d241807510341c02c905c80304031f81d005002e402400da00c51489040c2e5410015031240607120354131001502d81360001c0d00e0f034011842042c00c1248021908810045500000c02c01d4880364015213101e9950700210300290310520724078201c107440d02410b00b215041c41d90103901074207840d80188414000700d480c0702c0403111080c070211690207444a207a901340304d00441551111080c0c403c030a100d140011103e40040510030300c295020485a506c0f1001c0141c2000300d04065040ca100002c0001c2400b4020f0f00101001c0e88810307034541649540790700003070940c0c050400c1d800120065655008002500b4007810303410443c0d03c0200d103038a140000109e00140608010840f0700c40e11500141d41d164000e50481e4040c0c4d811285c9a4600821040703119642c640d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 58995309 1250 58994059 58994077
    0x30109050603060f010501050706090f03090e010801060b480f03070b04060b1f3902100327051903020304050d0305090904060e06060604030804121b0b 66
    0x1040000003009071a003c10840e110700c40307565031025642d0a000046035160000b8404888a558400104010414140a10705254800e41d2486251b5040098640c0900010b911075003550b03045c00340c18010384840d10140d42c94200420302c0c941c051300b002c3e10501d1318548001040c1d01514408070144c50034000380d03415060300b241c040e0200c6081507501072007150340348038903000a4a080003100108000800d6900154503800c00240340003018018040c3e400f030007110b44056036010035244141403030501e0f40c01c40c0c5203d00c0241c46943c0b9001c450700382c0303100c2031285100d00028860107011b461034000c24040e601280303e00d5210502c1c4440c0d09020106002c1c08000880c00b9112445814002c40c90f05256a805c60040c55141c1d025500303142c5400180400801c42c40001c6085c03101c10301c514051a25003881c61803040b80202c0011460281c401c0d091403c020b03000e421036008030700400c000c1c80410701394000c6400b200c8110f00d10442c43c3c901c1d410407241050003141c05100041e14240d0004031140b80030050b250b0b0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 58996559 1250 58995309 58995311
    0x3011a1c0509100b0d0302030706051017010902030c0a03050c19080f07031a0601050d050702030702090702060402100203030c070809030a0215030114010315060309140105010f080c030d020606090702031905030109 93
    0x1341c0041c0400014101c03101c0c0041c01139004116480c0081d1140e0480d50300807a00c0c8504c0b0280325101c4c100e4a00c1d9102c252045e0321203030740d503a8011056140070420f1140080060710800b06480c15502c5050b107a80e1000707035031405113041040200141004910001c02402100103580000030034030074807511101d903488165040a4038150b00070442c078031800c81a00402c0140c6a6910306881c40c0070050280c84001c1c441002d40c0418045080540c4616072281c0c40340600e940a0a0107250520411547c040e80019001c115130003401005501030010701201c3d0b105801410b0580c071401c1d44000a07107843c02c071290080d00541034514010b441c84010380594142c0d0340008903000c801e00102d00440849070803400d0510344440090302080120b02942c8801ea16138001c445021483d076a94a040382900d10a0b4481c01d010103610108004085003807103588903000c0110042c01c00b200284a00959030000905018491751502020503280c900820484906542e884041f14540220310340241c148e0b0000d1007440711f41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 58997809 1250 58996559 58996571
    0x7050a2d060906110102070210110105071d12011104060c1203020a0519180e010501030609020f090108090a0507060504150e130b0103020d0203040b0106030e0303011a1c050910 77
    0x404614641205a6915a8503820010f2804104841c000d91803046201555401c101581c00b50316403c8522072502c40641321801070f002e07005912400c40b0070060540e000c00103100030301048110150041c14203000219a4940115030540782c560051a0802161059400004000800030b4014031081e030030790300174052072912001402d815404e0303116001da00d0700025420402000c40920b19491818007107200c0c5480400039540350041803070441280c00160401085500400c410342c0d0502402c0040d00b0010415070400a4040042c103041c010f1400e11414442e19a0004050010800c0000c51045d000300488810750b9940e0b00c0600207a005016010000c01403410718100e050061800324405080500004071440c2d000c01c200e00140301c541040d60415800700002c9546088a0000e076005a0044140600075454030318041c04490014121011540081c4010402018900445044100300707885040c0da84048042d0002800004001c0841c214030741400d101041e000098100541d202c0c0c02010080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 58999059 1250 58997809 58997879
    0xf03030b0d0302100c2703050708070506030103060c020f031206040506060a0f03050c0c01060603270c06030f09060204080c0f1f030f06171501120c030209040507050a 73
    0x1e00c09500d28054003507802095442003094840d484548060550300d80314040211440c103c1c0d80200741840c001c28100742c1c0308001e10901c8024000803005000003c01807030f0300c40c640350102d0140d01051001419190303986042e40002c5000f03109056400b10b182080d070361b460120300c41d5000350400944019005619041c0054013a0410310211401008103454400c48402207039021230160a00030300c03c8141c2c02092040c180e01d82d409010381d0001d454a61404140300d6241c2d8104080e171141c5001e288e580b0303d4030300c03004004108030307411400a0360a54500401d183ca030102c0300d60082c21080c04014941440000d00044c1502c010522443c9140125408011030341e48008001c0c425601a60300d42c81013140c1000e5070030403406039000132524020711002042003990b82941580c14207114612120a07003041d0301c0200190060320000340581002c41c4501c02c01c0710940c0f100140e102007400000e0140f12141c0105003488000c1111000910004007002000d544031080241000300d00300101c21442d03115050040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 59000309 1250 58999059 58999069
    0xe041101020703020607020d05010902060f1b061608130f060c27050f03100504050c150f0d051807030c08010c030b0d1e050d180503010b030a11040e01090f03030b 71
    0x102c03a001400c070b07811b0410603000c1002241100400f01d8441d0358414000d401a1034500203442c401084034600c5841d500b1701040000b1140c0c1c107a540b40d2305500443c08003c0c401603420f00110320300d09540380c60316247d90b0316041d4030b913580c102d0b810207000b0054035080c080410105400c8010b8800c11030b590000c00070a083c030b154a2400314003154600d4024002028421405d01d20901903041100400300c074a90805e0490703c0048820558055803140c100d88040122401d003052131884031314074040003510304540340502c0301ca00d0190340103000007a0b44603c0400c1c2e01040c09003070103484c0707000f44e810b032001c00344d40f450322215143c12440380140950030700a60640040c0079224444039004041c0c8804080101c80c0c0e01c070380881c1600c2104194001c10749009901003403003001414040700640d214080541401c042425210744280d026a00c00c0c0e0401d0b0900c00903407000314100e00d01561141d03020000758030100004d40a0a0100c3d64080b00c1d41c1b03010700c074009002500e450341035558060b8504010641250080c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 59001559 1250 59000309 59000323
    0x52116120c0e0f0301021b03070c0b030103050703150603021908210f0702010c120807020618030904050604110d061a0f03010b070c05090108060a1401060c020112020f040e04110102 79
    0x210124a0714a0b40c03154a0903c007201002480c802400146005460b0302c42000c800c101040701c0101781d001050135800c00171808101d80140c04108000c40c155850b50b50390395980e10950200500e00c0407100e00c03c5400381c040d500204061a070007490340405000c4170100f489280400d10130072038144a21480c0885c0942141c108030b10346209000b12a03c3c000400038011131560000b4000ca041103046403050001c40c0305400880383d0210b5035501d250143c20715140080c40d0800140c04480002400288110b5144c40002100c51302401a68046110394402c80094010010020380d170741e141000207818880034185500401c01d4440e203034103009a0220100c00c0a03814090241100359a8404000610400c1c1001d4003800915100d1f11807001c4c0e10340ca490100d105501c00ba800101c06520180c00d100300400c080c0500000c0d00603807401412258034004c401061056030400181c14040d80c001c81c0740d00c070f10458044030203444d07068002039520f507529101ca1000c040125019281500241c64004003503201007103007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 59002809 1250 59001559 59001581
    0x14010f0b0f010c0213020301080d0224010909030c020301020a050d0501090c08010501083105010507020d080c090a030b0c030915010311040b03030702040c05190e0303030705211612 79
    0x20001c480040d50079005114042e0ba0048002c0c0c0c201000b069a8002980030300010805401c1014405e00082d1801168549003081b009003042031019841c80300030340504480c8034a10201d00c03040300c3c1c1070545610002c00d0004c0c1d0503500002d500780103103800100804e03451103455010000c5a07611700c110812a5411001c507400a180d2a004000343d41c42480c00941048060380e0070b042a80c20003158441001d80714061660f41681811440c052003403c1c071900340c0c0038216001800709090315081c020003e0000800b090400340c0080b0306840c16480c0c0702e0f01e040240d54880c1e0580311909010068a03181d4100b02c40c1134825206003a801c0c810a484085d01904aa80c03059107040c480d142ca0003040044c000001041d6014801440a00b000da0380c0d500420581d20707125240e656031283c00c1c4040b500281e000410400501c05501403c42e5251000000c072644000d242c170b0f020f908c0d581e503040c20952a4400b82c422403002c034039150912480900c5030054102201c40c03910b45411159404601070143c0d042c0c8949 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 59004059 1250 59002809 59002819
    0x90c0d02150309030d090f060f15030311010b0909060f0c0a2307050312040303060b090603040609020a050d0309050a150815061c05100e04020603040609021c14010f0b 73
    0x1e09028148540610b07000500c8509584c10491003030941400c80b407580b50140d03a07942d1002503071000c0c40708911807066a510b001d24188442c0150400c40301c501c9040d840000d04001071440501c095103402c0d80300c1100034100401c9801c060034080c42c420754822040c4c075040d41010503400420a01c50b070400498080301502c3d00c8006040000040d18030707008200e03100c01d90300c0400400c07410700080e03003c0c001007a80a810030002603403400e0034100141218481e420400f40548100400240c590b101c2c4192130b40301da40b240d03011138005298404210a1a140d62000790003c044c10b146804054210002005030749080d2081d52882d43d0390030a28111541502e02c00000c0390b040e0012903c50041032000d228208409800070340380003810350170303400c8040611340c850312510750f602d050000c03050f80c0001c00c100900328160840d00b2820260009051484003810041803695289840750464940c0b0071001c0003079000e0074a907030030030156080c041041850f0a00549503135103044800c01d051400d038071500e0340c0d94202800c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 59005309 1250 59004059 59004079
    0x506040c0605090306041214030a020a0815030a020618040c080a0507080103032109080a020c01031401030503091c020d080d051018020d0b0618131a060f0702090708090c0d02 76
    0x702c201d00d80095020b00300405c428108d50100499140c80154000c090341c00d00182d43c0c2e060f42000500f2401c003e0f00507520350131800140852540c0008042200e1901114099500c01d10b14410b0f031400310000f00290341241c02c0180e21543d054002c40c0291003040d406406010640c2c2d000300c1100d20080900000300411291102220300c1c01046c000b0741e10510141c0700005460080d40c0314a8003c1d0451544c900c016408011409100d5916000e05c011800502c003286034594151340d100d503224001e2100081c003070040b03068121031001da558040208560094614128131000d0304082025030701401844022500301b0b0302240b4034110b1211035204403031407541e440c400e4401519800010754000140c1d04041c0c1e8480303149100e250303168001819003085008510070728940c20001c0c0b0450f0074000088402451400d81c2d462025006041d00354002c0c6000c443c0140e864020703428429050140c4e036406034005d01d0100400180b20342011089006415a808071005281044104010300401c040000d4010358100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 59006559 1250 59005309 59005313
    0x9120203071418042303030108070603091b030606050a140108010501030c0509090108030a1806090909020604030602070c08070b1804090f0203100c0810081f180506040c060509030604 80
    0x400d1504641d0b000404004207a429212041c48440701654180e07503d079400d40d14000c216100103508520144170201440c25036141860f4541c81d0b9025116100a25442d41d81c00c508000c003105d560482d40f0303403401d04a9041926410407100421603401014041d8a500001284e0212640041b446410707050351400707004d030309180c0110040c2107210844810311130300703101000044d80c80c0d1444501808504000390344440c03051100504d03220702c0e404000d0b5000b100361401c0c0022980400440203458503005c0101e1358072198404a8401d200390352014101f03038030110340d01007040308811a1200b103400d0b172011980103e441e91603080491003155001d600c0b00b00c1c181c00082060409800200c2454003840d00c5d4880c0200c1a00402d09020982c0c0b440841141d442003440d071b01c160040c1c05150040045003080011031f003000a400e90701d0708070a604075010440015207800300046504140c1e10300d1040c054202c0f54800c203250080c0e8400c0207850441e149001910003140c1c4500c10420b0b00d003040300080042c41107071582d0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 59007809 1250 59006559 59006579
    0xe0c01030911060f120a020405030d0c0201051e13080601060e0f060c031b0f010606080103031206230406050d020d140c03011d1c02030406030c090510020703030912020307 75
    0x20410498114281c250750340219078900002d400d07136030454445542d5441c50740e0407a00c0642c900801d040c072914810701c07040c0030341d0b100040c003150782c00704074100000b00c0c0c9407d00040e20307a0f0040c05c580c9015085009903409440c1c606030040c01f101d0b10b1075042101070548904103192229424002e450001d0041600109103180c02141031302d456070007074203840c47c10001c0728509003541d04c101e090403103130b078540c80041c1070043e410800d184035040f485000f003000c1c50a0810080665506201c007504010502c04440903c080303640c0000e00134111a896220203080c21080850052020a56248118039124000920f0301304480c0c8804166402071040c4040240799540004e04d07084101e0000b0302c0d209061003066140c0382480781c0100400e00c00c070060b21038180c004a440c82c066038041c51200e026002c10b4403501c002d40001c141c4040d1440d504000c42e0201d000081101c090300c2d154011503012040c40e4140030341c282c010900da410307603011b9a02e484040743c03a949110407000d04003034025050742c0a403404010700070301c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 59009059 1250 59007809 59007821
    0x309080315180a0606180308030c091804030e0111061b0703020313030b06130e0a0206090d0503030f07021e03040509060103060b0c010f0b030a03021005062d0109090e0c0103 76
    0x200421032140b2019180340e5581c410b80c01c40781c0e4080740742da071081072040f04d412501c2000c1c2621001c1d114030320039055940f0102d060001402c44010f00030041404492980c800c101142c2620800e4044040382c5003074180281414000c2c5802800f00304c01400c000e41480700420310030b1251131801000c402070b01c0c105907001c841f42d02c07141c41a000c6010502039640c44030350140e111402540501c82281c0141000c0040100384d0940005070f592035460400060840e80000c1403541c1c0c050f03012546103071608040300c0815401d08155800403c90300000040190002244a01c00d0064805500311103000300d02c00b0307200c00d01001000c004807a40c0e0080c001000946045511298060010f240c08281c1980d01c004490b4a0740000b07e941000e40d4481012045d420803c0c800d039013086504800400200403030740c43c065244c00c0c02458046119071214001003940d2241c3e00984a103a5600e01e201d0103561284002d2820030b024584814000b444421000442c0100b0f4043c400d00461660050540c10070b20000540c01414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 59010309 1250 59009059 59009101
    0x3110901021e070806190605010302071101030509010f060e090105010504090c0308030406020409050a020a0807020d14091c140705090402060d0e011e141b0301060c03050702270703090803 82
    0x1281c10004200e4140901c5845d000d450035288105503500c3c001b00b480155030391500310034100740c8180141404140028410036070b400c02824001181d440310304481c1e0150000348107102d1540d05200f00051a08480c140789881402ca2400800507640ca0300100800d854540c1000b900511340d101040c030110300300900864109114050062410b55101c0c003540595900306c403216007080d07000c549200c0d5147c1210841d0791050440c405040c2c485010070007e0120030001850415415004c2880d6050b5280c0c410501351000050016001506031b501c4d140f1a50242042804103e0107009000640d90528040550182d07034010007a07820100d5103620400103110f10750b806400c4c2d648910903810641c5034580c039410032580d0000042a0030440c40400080004058410103100803580e81c602e10400034402640e040d903002c0d2400901e0600f8904080300c00d8002d40c50065482015140419001c0441d22140b04400280080703c3c05607582e020320684c00c417075007684054204039042001400311880000d18021880e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 59011559 1250 59010309 59010313
    0x6070b0a090506011202030f0105070504090908040801060b031e090a060c17040b070306060813060c020a0b01080607080c03150423040503030a2406050a09030b07030c03110901021e 79
    0x703582601e4940c42c02c0c3c420b910643c822650b890224081d801c0c01e00c0300718442c400c0e4500a00407403c1031940101b0b00e208612a07810140c0e0780b072201074100942c10003100d0042180304000c0c003203541c0314442003400750f00580d58002c018092102c142080d4500c0700b030742403040f11b910010b0403801b40c580c0c0751031014101c1d0f046c41104106982d8800303590b080c1d0a4120b0341c0254020101407000e40382a1502a003111000e03044141845025000c0203012111244c140d442d0350303071080700412100c030008000c0c0d28040800c0740040000705030100104550100042062042c8116510402141c030f40b01c00104030340c4419101c080c11112020321490990805410042c86a0360b002802a20784042c00d2440d49410410350b0226401d400010602c11680407500a90b10b08004460b0365600c040400d07141d01b25491131a10410060081c04070f0a104094090744840e40110342000000c0c00d0b51415010040041a51a50120229180c05801c050051810095030903001041c0c004003003c03c00c0c00c0501903811440702c2c01d50094 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 59012809 1250 59011559 59011571
    0x51c020904020a090e0a06050a06030803040f06020f0301080c040c030921090b0c06090f06100603051b070f051e03090103020306030c0d03090602070914011401111f0609090206070b0a 80
    0x42c42d54405c0380742515002c005404d0480e0245854403e03194042c180344603c41c141913091010401100c00c0782d800590100c8112030344e0008c1d10f0450003a000d450110161104007100001d010385000c141c52035040f00440e010803000c054a00190103c0d540381c2006840c1c80074401070559520010b0351415544c040c48d091525140c2d0303a40354880c005a0140d040305106130042e00910110f241e08000c08081e2090b10707070192009181481d01c1044a00c040e100d44000c0503268800b154403000240c4060140f130300300f111490b40d5004d850038101844000108100c56501c512911191000709560304030310109074001c0518903195598004402070b400c00340ca041e905000d803c1a0a00f0b6a4414568209491203a00c40811007440d1882c06424000c0683c000c41040d424225010907036101d64210300d054030100c2800d00041d1500d5401280c541003c030484031411b2042d040050010302180312000e401043c0e94109110b450f840342d401c00c096071150b21000390001814004000040d0188207510b600c610458400614 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 59014059 1250 59012809 59012819
    0x11030c0a0c0501180b010e0601050703050a170103061a0102010c0516240605090a0c020703021e040e01020d0b03030c0601060503041407030c17061608060424050a051c020904020a 78
    0x840b130744940072084910301c008200040001c003000d0300c1d00420f10401e4491441c5000030002e0074911035650001c0c2004400100841d01c24024850303c03110034034a0008040750740c0c60b0b1910000405d0000c2102403c42c5115180401562050081c00e100c030019545803800d124500003000d5030200020740403a80d910031091603048a000742201290060340083c400b0031420302c2c041c144050591302400c1e0000c09820326603801015038001814030112075041c0d80250b202d0210100005003110010b2a0541c07241c1880405100c40e10150094582d07501d4105d0b04002042d08941015920b202d40013103800785405c800010402180610040c40e4018014400a058001d08403030b8541003608541003100c03c466500c03403c0c000042c142034400c040c0c0e005400204030a007000f0070500b4003c84108012404c010301e00000601585407074104844c91180340040d19900c0140038524000400103014141c000d812504d03000480b890414400b01d1420840f10208202c4030007a000d1001c21f204c000d0059800084814000030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 59015309 1250 59014059 59014061
    0x90606012c030a050c0907170f04020d15060503070605040305060c03101e14060c0c0f04020f04080601140411040902070c0513091a060622030f050601081011030c0a0c0501 75
    0x80f074144100094044505c94000304120300c02c0140254082043e00d106080d8484d6001c204035070081d4894101c071000c0c0c0d0791440040c034000b406c00001020403a044044201e11030b403030b811010503110b0480c01e4032402d036191841203403580100d12014100b54042d0b80440c0b007486510f4000c60f00154400c1c240402d807512020002c0000118a11005003503c280504010000c41e0300300e014224003080f1016481d0208411880395201d82e1100c0c0e65129284c6403200740080d649540c1160310100080c6842da840d9035540c185a43c40c0d4009205c0c80d2000c2c25000c0200103149018420103850a00b10740b041030401e800c1c045644025000441c040703a0b0100c0300200894540c2d01c2c44c8800015a0850401152a1616107000d01c0022405911030745421410800d000700390f80c070b42085c1e031078505144403d20008844001e4601d00c500503070303001401d01120079044400380711004c01c0e503e051355203071400c6604001c507003401541201c2c403c0d40c0c071400e00d05052000c0b401c6108610000c0000c0c140c6850400381c60990381d01c2d024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 59016559 1250 59015309 59015323
    0xf03020307060c020a1205160209100509060d02010c0b0c070b010b2203020f1009090c03020304031107120b06031c020105060307061106040803060303040803030106050a08090606012c03 81
    0x5405a840400c07240d04004180c001c240100001d4400b901d100344050303448210f0700e1504044203051203808100c01d4a1141c07801c01c0203103015001080038003c1e0511140e810340135038150242e24002c0ca904000503156080c03660790303200c15503410794513423901e440035803900c240b2050083d048142284040142b00081800480054042c0880107c5540d8502202c42320601d0b41c85000c004851409411134204090f9503202d04055070302d2000c0d1540760340d00178004001c40b82d4001e075800489403180384c85603901d005a41a400f4600c00c91081e2141c40c803220a144206903a180b003441543e290b12046055100004c60718100e054214002408444485441d145904503500e9202c0c50040182c1d074510800c5601c0c83e0420145000388000c0c201441c0043c503640300e054503400c0c0204050315048000011900c540c40c200212801466001c0903251a540c562100400341d5001802c0381c00015003000101b0718589000c035000f13000f000141c6403208a125200011241030394503a0204068003039400503403ca680b0140f280d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 59017809 1250 59016559 59016563
    0x10061412100903030c080f04020d170403140309010e01080907090f0207020619080711030f0c030903030d02030601080a0b130b030f070807052e1110020a030203090105160e01050904090f 81
    0x114004910700c5c401041000c00910441100b0364110621015803606414200c0054219804088080d51600641d01a00c581d6000600c000001c1288582d1808040051300342441d00343c0c0d42c03a80b1460030300e00444440c007081d03d10342030603006039004002c4110b0f26400704c0e80d2519414005070924911384c000400e503801c255564410201082c074094426076002d0309030740c1e11807950300b000c1d122080c80c159155502c0c021600032041d12507001a1104905200300191510001c0080032a565180640260301c044d41048c0d6016000c940100080b64421445006d404400b0002921141000b109210320030050f14900d40b0858050027440c5044d00b5182052048001616480004120301883c084c280107203600c03040c100755082c14004c2038951040070b40d01d0503640150054905407040c0e8030392001550410041429051545200164695007103030150080c502c03e00f40940204024ce0380ca500000000c01e0380c6640400164400b40c0e007510325030044015194560001d880000c0c2d088545c4d8982400416100003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 59019059 1250 59017809 59017811
    0x312020f03100801020a1b0c0906030302101116020d110406141201050402030705220c09050310060305031e0c010207050a020909120301150201020c0106171006141210090303 76
    0x800018800c800b40b01c4000b032004800861401074102401001d159210074528860700c1105101c0f41071050940d80c01028044c40c003420030180f82d5074a80a507484a9401d01da1118608001d60782c5164503848094a11141c1c190f0600745042c0816802c01603218240c0204462021400b201200152510310484001d072048250002c3c08009000c100001ca0481c100904420780c1004e08100050710040742c1801200e038240e400142c3c00000d03e85c3e5118403242d00d01d142c1c0304240b800c1c10880c215903000816504445081c0d0a42da00315103014192015110980000740c4654010025494402d01d44c0c40e00280d04a81c034160681404001c500303050070f9070700030304040da41948203400c40c1c0258a0402034440d00520303407400401010144060680c905c2c04144a2038980d0301030460314103140ca00079012126401d0800008002c01c0f80c0b1000c00d510000050310040025110310305540342c69080134815141038911010200c480fa5000c5c404200c00820815003aa40c14024032907a992052458010642518800e4070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 59020309 1250 59019059 59019061
    0x100e190b0105040f1e02030415022808040c06080702030702090108030711180a05060a120c0303032306060f07050304030807110901030f0b04170f030907050a061b0312020f03 76
    0xc02c0000703848035401c001c130125213040140603092401e501920800745504001503181d95440c10300c5014800700c542c05500e4140001110500c0f10309c03034850322509020304203d81e91921040c0800301c034002c0e01114028001107181906010480c02000c0050340f000d1148101c0c3c1c80c0988070b030b010414651080e07001c690160310105616040158842180710000f000791808405a00907881e105040080500b80d48035180d600d9000c9000d0380c4600340c0c00d80181c00c0c0e058080030300a045290031038550042d4401034000030f103882c2e407240c03040e01c80510304404089004074a140941790001000419480700284403100030007003080300001003041c0040d0000b18002c0c003190380ca03807010f42882c0c1040d01e04c481c05103204003107000c0140700003095401c0141c1c015400401e407407050b43d16132031720140110801340d88601c91000803401800020503000110f00c14103240080e42c08084d45c8201f030148142142c0102408560b0b441c2c8034010030a0141490100240685445019605100c2c078030717030803607204140300412448000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 59021559 1250 59020309 59020319
    0xc020f0a09021314040207050312070c0204020703080402120106120803090307050601080a03090801110313020f1201150e09031204030e06070c0501081b160c0b030702030405180103020102100e190b01 87
    0x10624003561300255019403401c00139940700317038032441500720380c42d05c0c2020840440c41c0785101e4200c10000e1903003d0801c640d41c0e102e904020300000000c41d4200e20451580840051080c0e06010741070894007144501040b8040035611a505034100074600b890301e02c400e004010100c1c204100b0745008010020140001c00c0c00e50400030080007460f04034105580c1069940d143c00500c0e142140e1340040244610a0300e00700610008030084607403819175510440c95030820748080ca06502401c0143c04166040b0f980a60720000c0c51074001d802c80b100c98686d0002d01151820042140a2aa1151182c5400c841000100d40051490740000800341c0e2103000040e030074081940c201400903003280f0110b400c41a45070151018468500c00d03034100702c00c01107a2080e0035040140c1b5189140c058502c00c0d2034183c0768640014025500d4206106031442600c0d02c0e04280c40b60420885058144c075010b034090b00c0c82c0408084110058044c18558020b070b40718005000b00d4031914410100701e05441142d640311254581 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 59022809 1250 59021559 59021579
    0x607020d110a0b1c020901120504080d060e0f01050d1505010e040b01080309090a0c050d05010b09040b010c0503030f10030b041406010501030204140f0f06071109011202010c020f0a090213 82
    0x1a004201d141504000c00041803003401d190882c2e40d904e040c8013507a11014600101c070441103000d0700c0c0020358103120902040102c040050131700000214810010342c0e0741e84208840d05001a10b91045117947c41c1c3c0140074508142400d245100d0203000801a81c41c118403104003225000da01400808041c1c0d41030004009a0007001d500402c8094021400c15034664001424558068101460955151010942a4064020b0384d8004030891410005503a403006911116030050502c3d500c2585000c220100540c02503840480c001e401000542c11682c0ea17140b4604a44805000d07031b4188807600f040003000030082a1042c0c41144516841c00903198203496280c5000011303080075040c180144000d104002c43e05042420210007214960041c040110100300310041c51403086400100c0040d800050000700000302c1c44201c000c0c0c8001c6142d030ba81c3e141800485192610080c0007840745100480503103010540441c00301070042c118000d840e500c580d402c01300d0b84003525107a03a000301003200304201442 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 59024059 1250 59022809 59022829
    0x408070303080123091329010504150b030109050402041b05070308071d0103020304150e1c090b090405060f040c09061d03060106080735060409021e0607020d11 70
    0x803210a01d81c98070003030009044488028581d01c4411011b205080901c0310070601c064016503840141c400c003081c012184010b05200b401018019030610130950814480100c24008036458a40110700f540d0802c100c600203010040e00c1070ba40b01e9156251604117444d19401e034842e101060f01e030f969480c2c04514010304140401014401401883c03a0790380d0ba4000d5002d41144201c4007440c006940355117a1809140b58241842c0039800c00b464100d90801d2028009410901716090b0200761002814007003088482c111a401074442403c03041c00f200140d41041e41001b0703003010b4010f0003100313070007100340c00304041301c1c2c902d011100002c1340c042e0100040790300000032000125000b51241c82d20601c000100381d540b03006109010402101c1800200054170440e440c48a42850344180e100702a00c80c400154590841c0b009a4030614124021400c545098819042076545c01360144460b05c000346010324100680c0400700e07801600070080000140e44a04200b08910310509901003a0320014060245000b9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 59025309 1250 59024059 59024099
    0x507030b03060606040512240108120405030a021005120f190e06130f0b0709060806010206161101091506080c0d030207090506150703030509010f020a05040b0702040204080703030801 80
    0x2c541c0030b1000c0e54560b901103900ba114162042440d050648400514010904115148007442129260140c1381124844c5048a40500840d01003490315141c0305901c0c4554851550b1580c081420700005091449c00ca4045075002d08055007400100700003a007901400700c6404900c0e010800412101c50717040c0411405100000b00c04000391a8008000b954404020340303a80c1c09111201c81080420020a60040071580d000c00340b95010709005101401c560150301401021400f5103000642039480061054450300107090420541000918162800c030a252102001552180030f00b1011030146280c040308090700400014100e072518002034108880c035a00c0074400c0303240e5407100000c00e40c00510001a65414140000c480d141c50002601d4007230079546c090f21000c80428910301f03040e01540000d1050740c5010013403040d400808103081c102e100d806010000302d0000d01042c810590180050600b09101400041c5042e450b458901c5c03030404607038400c40002e441c6900611000e94500c0014150034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 59026559 1250 59025309 59025313
    0xf33020d1d031908040308040b0304020301050106030c0203030703090302010b190f0603150b03280e070806060604030b0604152c060a050105030a0f0213050307080703030203250606090507030b03 85
    0x1000010f51204140c40c030f03040e0080c001d4070a1105201081081307400861b4000c011a076180d03039a80814241e6001140c0a038403135482d0400006101d0b0107806910b41099590740510f04e1640d039107009a00401400b00181e0840d980c4a2001545071202c041c542480c0d84540b10340c0c1126031420341120440c2c1643d411950825040440306d851059a2014400544501c4030f08261a07503212124218820100317042c0c070b07024440e520010001c100d641c2d84070740b1248407540c0913601e08075102c1441980d10f200a82d46207400034000c10041012841101405801c18801000071916013064001030340451200d030002c050f01d03803800b5441c44081c680f00541007400301c602e441280c0345184c500c0005000c200288a1241400400030000e105036007258010f4041408540c001c5482c0c061540d58004111620702903036019204640020880740000280f000490381c0c198015850b0042c45145801200010211141a10345420304d0f000000d1603070041a002c0d000c003400008941c5010100203003a01d6200601a00035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 59027809 1250 59026559 59026607
    0x312120e01020406020307020d0312150914060f01230f040f0905060604031e0c03050606040c080f0402120f0604060209040b040209010903032f0102040305060c040f33020d 75
    0x40c5e000710589034a182c04031110a60b0052904003a45c0041025210301040e500e400403903845000003418000a48443c89410052400c02c0034400d1101c000540b203442e848000c3c0c1c004040b00b50311030303001900c600c0008014009603402510f80345e10746402520300390840c04400f203018015001d031481d0290050042110070300c00340c1841e401050581c40b41c0e00000d8079061500c0351820900c0d1480d4200300d54075921070180c1f004140c0e0303410010b88031802518024881e0b400d100e00b440c0414880d003401030088100c40c0310075540782c07a03950030402c00249455411002d8003501c0c0410b41048002e100481c4550b0148001503034602c0034100300700032102001c000300d00c44c6105000e02e009a0360f1004c402e000352a4141888145d440c0401e03800103641c507041d0f50f1481420208a10806460419001b50048a21070b104941c00c0ba00d403003401003900e004601409101000d00f28080200c030464150920701c940c0300c20000c0401e4000084110a0901c402c292140940c1c0701c002e00c04216030b48030305068005940f861450081c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 59029059 1250 59027809 59027819
    0x30b06010e030604080708030c09030303190501090603020609040209030114071205060105030f070f050f07030c0203010f0504020d06050c09040606021b09070f030504020301110c0d030605090f18070312120e010204 93
    0x85d501403058094001d12000c030006800d03042c02e0084421601c00101282d03100e00d03001c1b040c0d42540140d24407040213036042c5000003c4145885c01003105807540205a14206040d403400d00c802500714000c070540c95902e41070303012254072061100a00645440d550401034030801046082520009402c80381044810000c022503c400e0f0080301e034011090b8500ba50344d0321101e003802c40e050b0207203620310320403802e000030020200364214a0403140280f098009003d04003585015008807042100c1c040e401507002000c601c0003030940c2c0e0000c0d0b07000b40c14180403410721500c0d0b8007050407151160444005130b0b204211000c0340802150400b178004030708548507459458203510040c100e144014070301082c161204042801c40d5000e42008041091081d0a151540c03c43e0510999650540400c0c1000c00d15203d004610307420082c0c01c4502c100046504e80741240c841800d400594000e101c00c442e0701340100500400095001240441d51090540d51082007409000c2402c00300e402c146881042e50703104110800c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 59030309 1250 59029059 59029073
    0x7080a020907110a0b0c040806100303020c09090325051c09050d03020a050102070302070e010801020c073302030c0c03060105030714060d110a170f06060310030507030b06010e030604 80
    0x540502e462412000c1c500e10302508030f01c1c0c44060840241104540740400c440307882d04902920480c0c0700b00084039081c3d1074122411f5000784580c00040c00581011915102d50b0a04040036908000ca03102140d15118040a061603072400d241060000b10354006248814440c1c204180316440401494400c45099101d03400351078030030a80b14260180c11a040d01c402414001d1200400094100340203560710203451500944070b500ac4e001d0041202244400030a000105100790741800e09040010059039003000402041441014074407003000205400c10704003403501600d028208007062b00116121081403410f00d045c500035600050003640030038010030040c0d0b000034580c41240c500064903001d039150900803031224803c0d45460b0a000c4d0402243c0c0b000c0c425a04018902150141e48804007401e1000007448000e0003940c4000410b0056004549a483c100000716000765145a1004a07155281e440300d0a1000983c0281c4000e078200e000c001035540c000c40d10250302002100600801c2c80c25554480c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 59031559 1250 59030309 59030311
    0x6060a090306051306090c0602060108030708040e06040204080318010906050c070311060c0304060c021c030f08060307050d0f0605060a1a0c0316050f0d05090102070b070807081b07080a0209 83
    0xd4403643d00e81c40071400e4040142003044000741c000e034051017010600d0800f9030740c00d4614451040184030300800010486404816281c600d13a1203d10685420701d050440c461007100980901c6c3d001d9820000045c031840300304024444100221032500b40c0300300f40c0d4000342a03084941e00c01403e01004008841c3c0d4460b01081d410181c903030240307151024003011804503900d03015004000741c0b2840001b030045030141c0c2007405039034114400c84401903c1c141100759010001c0e2a2070004010529400441d400a070040d02440e61040c0050221074200f41c0e100d0010b4200c24144006039901500b0501c40f0007840000d01415034404e50544201c40b0051803c5422620680c03580d501c0d2026103030101310454020800d20440300d1810b000024070f004003120b03041440d141d1a16100c0041c03c0d110341240040c001c0d00907000c0e507088100503005021580e250049078602c5900c024402c0341d0b2400c0811030315002490510151002d001070102142c0c069881c162014a00203168001605e5940010b40090050b61916400b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 59032809 1250 59031559 59031563
    0x11a010e010c0f02040207140d0f08040b070c02040614040f110403080a0306031b15090302031f0e010216051608030406030b042d0609050105060406083c06060a0903 72
    0x10b00c954a001c1c10701445410710300d14025809800003c00b0014000200074450b403140503842035034680081e0500a44c0d000d5034150442000c10f070800d00080120b107020841552000e25030410010180c05940010101c2d20150440c4c88404110700301d91146007441d10400a180351170540c00c02c4060400e1106440d203004900c0002c110340c000041000f00544a5009000210741c01006200d15120160200040d0740460144007031031601c0c0c40c94544040e108591083c01c407500600905410700a2910031400e010180d08083c0e0020303280e410070a4080000d100401603503440414644036001c0e00e20306541410f04c0050001c0d41d802a0000c14000d040e8080100d60458040b0300b40010501d603002e010401408a54000e41d40c014124801c01003558003081a420b40c0d21040c2c1e9041100e103032114081c4040f110300703004458010b80180401d000d403500619059070040742540380c250032105171690b403994903070024a0a187c503030b25454072258503003000110a03030000d2003100d9190410201d14402030490300310b4800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 59034059 1250 59032809 59032817
    0x609071a040302061219091a0606090f0103050601030914010902011e020304050f0a050303030a1a0607030e0405071106250504082515030207021c080f03061504090509011a010e01 78
    0x3c1b41c18420184201d07071030040710b52000e20200300780b0301301501044040e41c01140e8560441000403214a03041003125248a03000388114420201e01c1c0045000f450000d1846040c90754885958001ca0140e03504151a8808a400850788a906100040c00300705281d2404050b150344a64a20065401000b07403004d6420954002c040c0e50702c03020000b03140204560006130180000018010341014580050070105614010300c0021001c2000b8804140308607240500094802c5190080525094001a42018507880c0c218034078904a082182010020f0350004616851203140001801c82c14001c080d421340b881c1007030380c1080e2a1110841d120810803034001a0485810300031a05131413074a1350040588240489406140305600000d0025800103009900c10260f241000803604084061800a0340d0301001040c101044607400c200d96800142c08581c1c810f800030180761403114018050801084900381c0801e040c2840c0c1780090840c2c0555000a403401c8105c1040380440e40c0069444088520030300e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 59035309 1250 59034059 59034061
    0x3060507020703120e09090c0a060c020f0306011d0a02041a030417030702030901030b120706050714060a1a0f150f040504090309060207150c0b04050c030609071a0403020612 76
    0x26040b8240042c40d000103284041001481d030601ea0701803c081c0c2c0c00e41c410756034081d1035218204140c0e82d411042013800c0d0300aa8004003801254420348440c1000352014002c0b070b00340c4608500081c10302409810845807508406076400419184110b41ca0300110240b030210318042c105510018090072800d003161039204000081010440110040d0410032030010002d0340ba8107064000a40b41d078850701020f40000c1c1020410f8840745495182590740002e1a001400000c0c9454030030346080e0030003072040c0c501c900915005044100d040c001d0743d2150411400c001103c1080d440c008215180d620700041c06111200c03411407490715804092801c40000c1e010141e00d81c00d100001202920860b005503030020704106814041507000034001e0300351307002ea8099030355140c0c80750b15405a0030141c1145000050080240ca03004c58401c0ca452030b0403d016102303880d140c1015601207441e1540a64070b40c0295031244000b0400b41044050707140910625080082c9054a1500006c509016070320712481058a800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 59036559 1250 59035309 59035321
    0x906031406060703050d09030e0f060c0c010f020709050106020a03080a0507021005060303070501060e040606170606060702060403080313061d0a061503021008010603110301050d0609020402041a0c0f1501030605 92
    0x9000d0b2041406d40c90700a0109001502e4001c240d88005490a4020401d240c402c004031b191040030f903502d581030400100219403404004680b0441c1c2207404a040d03015041d000714607442a8000c01e4082c00c4c99030014540d042c80340c07078010502030b002032456007005e1904060100d032560108100818900b19440454640c46001c00203066200e2040000c10725841e121000882903440f0102078450307400380404200301c5650f24501c40d160b980562191280c0c2e003103e40012524a8114041c0508600140c0070760f04054681d610800f059005941c94000c407a1401c24080404c01c0034003440341c0305206100d69100541c03210180f41e41d20449800020303c1d82c0d46034071401e0a1000302003980402140c0050160140e00072000f400b0341078070805c0c0150b0b00040c3c1071050704641d00c062041228100c40d006090314464840756210304000700f510783c00c00c0307a006408000004105081000c11142c50450f54035071a40d503c40d41413114941743c200c0d908900c00f50400d0304143c60b90442807045504607a004907002c5590350720384c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 59037809 1250 59036559 59036567
    0x204030807021e040c030501030215070308010b0706110c0f010c02030901020307020405180102070825020603010e070e0a060e04140f0f0a110d0507080f09031b010b0a06030207030906031406060703 86
    0x4196404ca45401386400e001903042c0c010074103ca000b55800d00e40b880280784810450321482c03002401040e044001042001c481200401e5664003c0c540000e41000d090351240d410307803103501914516032080038900c4d0004000e2003605001c504d030740000c626140c0000002b0f0b4036030040c1c038001307445580e0350740001d0310703220b500b81c00500e220820400031556440246001420b6420404a0800501c0d007004d2801c0001c82102001d107035290010101c0e41107a04e025017141304008002c0400040151401020781c2e1900c680010001a100a0b2a10450a2100c0c81400200c400141c2d0035202c82c0070003014044844050240700383c00c26021002c80c1940d568000404003c1d00e40d0501c08020301c40006404034100c041c83d400a8015180d994a40314140c880010318400e95206451944107908100896080c1c03203824031010001041c2c83e80081000d0310b1040000d0038034000c0313500031000303e90006400010954085803440160440d4181001a420a8280f6545066000b04002c0c06113000144d42c00034580070f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 59039059 1250 59037809 59037859
    0x10207020a09021b0d020a060504030c0b07080108010e031201090b060408120702040b0102010e151e0a1409030304050703030f03090206070606050a0b090603061c020a080f060703020403080702 84
    0x60400180c69070740d00e400c00025804810013405003004480d10303c8040001242419009500382d0013005000c5c3c064543c04010b00b409041101841844e0551100090072400604d224201030788031000c07250300d4080228250740c8000010403560b0000c02600c01c10300980350465055402c020b1000030070343c0d954804103085220b50307040641140300b601000607132952804028400743d8820f503402e2003803103622801079080e038450116140d0b42d9040110051440e03a43d00107610307030101d0b0b4000701103148098240c3c03e03800002d0944e180e030402a1645194401500c102c4010740d00b100000c8015845d500d03003612540e4403a034140c08020100510100500000c40c42038120120b42c0c0e80051400d0b030b4aa881c0e28021000340190700c600f5006541030f03400040c0c1c01e4140d0b420383d502a071000e082c00f0b2442e902c80041004c03440d800b442c20400e8071810b1549201680750011004081e010103001443d071010485241450010001c154a00b010b00420003400000c0d02c800c1030b5186a5810f4074001c0c405892407c00e1820190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 59040309 1250 59039059 59039063
    0x40b19020a1403180625050f07021e040f09051501030305030a0507030b040507020307060c0212160212060c130f05150d061e0303080a111b0f030d06050f030a1104020c010207 76
    0x12a01d420300026281e802103c801045420703800500049846e40c0503905409200c403592880b0805003c98005818030100303a4000d241801d050048006400c80010110b0b103540800c004044d82c1c0707801080801070100a0201c0403c0102c141e0101c0798903642d0018004e11008018113450340d00d0b280070520160003034004100c6480c0c020014451494000d00080d5241c00002c026a050f07070900c02140c41c2c141c0041a905601440d80d1806450300f00003100e100310441c6845000c980000c070f824950801010b09001c0240075405156580d40e46d404040322510107001c1d950401203c00e521684100034507600d248450003000051001d042d10b0701090032048004000d070b5448160200c00a49a4032103104076880780106592080d1507401441d111540ba8070212869402c00d804000401c12040c45045007500b20440b01c4540d40c401c80d0160b0300b04200d041d003543c000314540b40e222070310340c001071041d031a2680005247c40005e40080c41c07614169100c0340d85111241d241035020300c0e80001c48840d030200a40444000366 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 59041559 1250 59040309 59040313
    0xf060e241803070303120f0c0905010309050c0307060314090606030c040e1c030f0606020a02100305060a0f0801020316020105070e01030c050702062212030c0206090a0509040b19020a140318 83
    0x4d54a040203000480c0311040164291300e0910a07003c3c0907114402c11031400d00c0d40d1340d640b007020300700801174008104040c016103051082140c00c01407507404101107009846070355000700b1030f02c0d040b51100c0e480220142c10b20310b103500001c04100007600c0000e040e8480d00720490380424006011040c090922100c00d0411a41d101018442c0683d9501900080c441c58120b00c0f080200c0b40c0d035000101e8580381c140304000d40c045d40800405007514401e80196401c004000c0007207641c982d8500303410b001521164820071542e5008420812039110340450040170b0304040c00240070515004034010518841003180606066951418003400da1051042d00c070142c0d0301420705956078023900f03002c20848100e1001d904007412081404604542d41c440039100d42d0b80d042c0c441c20481c203015404c01145421407881c19800c0400321742c00003866032300c03510801d01680c001c000000c41c60900d0f0301d54030010a0002c90313240c0502d00401c800ca4a80b5441001d54020b98250364071183ca0b511294401d41d042e03540c01845120f14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 59042809 1250 59041559 59041573
    0x41e03030506010801050f09130809031f0507030209060d050c04080313030501050108120307030209220c020d0504050a050d02060d060e070e030d080606090102010e0303010f060e241803 81
    0x580c05038480e500a29090300d034482c4c07584e44c1c1d07001c020001d00d200c1e80c5145c01030441d801103100201c0c01103c0300c0c0214850300d0140e08081520000c81e150010b01002940c0d0f0102514001a189203240300302500015546429803401480d10007090f694400c0020314000c9507900d10005d05012801c100380c1e00a04a903201b41c035610101e4400d86600580d0500003590750b07500e85000014030450002c0c82ca1804e00545040303908660702d60205a00941084410f25000024604801c040c110046070407042e031106a42e000036860700e41180280340c007281081000034840708020500c410350755066150100c41b011a06080700b10080c2c070121b0320500a51800481e01420600c0c0413425800c03441c44144143ca05594101c04030310910101613035011341e0b50503107000c00d81d80b0700882c21604003813000f080750003c103000200c2e048282a00c00c80ca5540240d01109044038000403d100c1d442d403110418045100032210359403420561040c034030642d6840d0051a41a0000050b206102d0031885071044010b1401000d807202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 59044059 1250 59042809 59042813
    0x7030306050301151e1a03041e060507030b0901061b020f060f0903121201090e0f0609030406090801091106070f1a010501030c020a030e01050d111909050102070308070b041e 76
    0x3481286000d044103114020440d0240e203181704015104903079401c10500b6980d000d4400309100ca0b480070b00241d549007000e0703e021002c00198681c80e149a449080002018039184500408541d0007a10180c40b88020900400c801c681c401e0f0400c00b41c114550320444c0c0050a071001603802140280303182e0b000400400c1d0810304100800c0541040b10050702038480714021909081424810707030400420301c02c0c031600140008030040e4080361841d1441000c482c1519441c00d8a64506141120201002c0e84005400d0110301e81c07114202005000c29402400090712560b81c0722a002c2c6103042c2c081c00707182c02244007000d00000420710b521035500000e40b5540500b4110702601410360034003440d400b19061044450000f48009070044107950150f4582c501841d0101c01103c0c55803007440004011902e41e15180b106d010359100811815209600f99002802c0c4040040c1c500b1000e41c0c003050564004580c01c201040141e0b084904a55100e1502d103c42da41d41d03c1c010050171041d0b0300c00103562204c0aa40f1007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 59045309 1250 59044059 59044091
    0x2010f11040f050307120f0303060b16030f05040f0e06030c0a0603020703031802031f020d0606080f06060a020607050c010f02030c03100e090a08030901020c0f07030b07050f090607030306050301 85
    0x7003a5407039400b505501c0e0751240c05140da00c80c00d511540d504100711840c910003081d0540e901c04000c910034a40441d400d6a02c0045418542040c0d4060140543c11041001050780120100300301e2030311401c00d1400d203850010b890300b0b080f8451284200c590300c89800198517903007d0003080c140c090024801c4080f00e454004c0103000350020101100841e113403102e0540d04a01c9508220a02a4000e0007070090030000d021031402d9500020b103101c0496004e00149050000398052140a00090355600e600346ca80f0000d194070300c031800740c800ca0145104009a1001c80d6011070566130018150500d140c0e181c24071858203006110098941c14028804800c0c0420424100025401412105611074006858001199803010107540c040c001d980003002d03100005030f26001031360340320000200040c02c00182c460402c4c2006009c0101031801c3c1c21440c014810843c4400c07103e904110245805401d180c0c44c2d0401040902c40e040580f8032070300300407a081007094032982000000d410064020f111b21748003050111 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 59046559 1250 59045309 59045317
    0x303070206060105070c180b090c0a0201061a03071107030c03080903061b0315011b0506040b0a2702030307050714120a080702090c0c030c24060102070303080702010f11 74
    0x10005006210115282d50b11502c00d45080d41d03000300c03c5040c3d0500c1c1022035240750140c04021a0000c2d180c5281903510b41d11071001074030982d80403410030381d100107244000b421100d15401445000f03003001c69403550010740100350fa901c00c1240c01e2200d10315000c140007a2420015510081642071031103008020080c260000d400e4151040d0304440760781d02d42c011000740c0050f404a004102c014140009840c007006007420140107103042c182542da05108165813800f01400d88015502d0360f100009000410441c402e409910107091001040f00001e10000d505856a040c00214075030742e08850f0f80d00a646e03090003160760296102c0111350010303503910301d800010518001054401d40d8070311202c40c0d0145d0301051204195a01c10b56480c41d05607107508111407001c0c0680075441d030440030b100034900703440100000c00748804488000e05046c5020702e0318a680c3c00302d00d902501c50704034100c00c6c040181d80000e40c1209803981400c086459948071f0300103d00500460780c0400107039080c202110002c00e8450014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 59047809 1250 59046559 59046571
    0x18180c090307080a031e0e010c03030b01031d010501060f0c21110604030c03080703060e010b0d0b060a0306140f09060d030e04140103020a0801140403030b0d060f0b0a05041a010e0f120303 82
    0x4500a11b000803030503a0500c8814140d036001c078000c400c0510000303200740d2028010440504000400441100c10038000c1e42c0c03d4050000180e43d90030041c49541c1d00701c0440a042ca10034949000203039566a20100640880d91030203007141c4048a80585003401388419040c000c0d149421504c8524107402c004148500180054000c200803002240c5c0c40341c0720340218819180280f540c03140991818081d110703a684214001407132141d40d640c0c446181e80c0d914000308606401a40c01282c001d0619001030000080c11800d20b100314400483d0f040390f0b4443c0c030842035101108840e00c1d00c41d80c400b801c2c156503600e03000b441d182d0721510b400b45060501c440412264140c90090381d401c0891602c901d0464202d60b0b04480018440f00310700000f80001e8031070313048196504000381007080c1010560ba9030500390b07000003140e00c18040e101c00661085040c009107010043c00111000d0000c0044842001d00c80008201100c2c1000b0846400002d95210b006003034025400103001100c0440c49148600d40700c1d0004d9030a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 59049059 1250 59047809 59047847
    0x3160804331d0904080f0f0a031803080a0902010e120102070311070303022e1d0c0907121802130c0816080c030702010f060b18180c090307080a03 64
    0x60300034010b01c81c40c2d242d480781c0344100078145442d80b00000c0141c0320b0303801081200e9183c0c040140b880c00c04101400703040c0324115107a02e143c035409120405410789010145280f46aa000c00c035020104c0e070b0084006402c000c0310000001c841c2c08600048481ea1a8030f040b00da0042c00d80d90f54203d0030789055004102a034001e5852a502005840203a078581680b8071019005234030500450703240044814001110703403501c0101600c04080da1081c030b400c2c0c94074000c4108041c800c50034070017000740c814001010714450031038521130585481c1102500003009001c0e0203120995910030314005500c0902070707081c2207070001d284803091520920844c002d0a083c0600300c2c0014002c0c80400c3c442011201d0072804032a860f00c0f2081c07a03585160410a040d080108800c0456480361203083c456061403148030050501040c0319a0f40f481c1c0030070240c1c04e020b004801c47c0d0007587e40f80540b8000340007000c2070a803c00b0340812050ba55800810000b03151504c2500321004034090402d5143c2016000616464201641c1c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 59050309 1250 59049059 59049149
    0x32016060f090503070303030b01050d0e071401020f0715050405090901020d060807120f0c170c030f03090a140301060506031302100302070203060406052203180b040302010203160804 80
    0x308440c100340e10711411340c240d4040e10050001034029040554002c0040c50800e080c4245044220300359186e03181d42c21415000b008040c003003480d911440612400083c001082640b4894a0007030b95480a0700c20540d0040307040000c400f410b8030680c1140c0007841c00404000da14207044103140e00075402035265052031458050b0000b14100007040d941c04440d00303800f441c9034806880d00c40190462035000c2c101c0c1c4130070107400046100030703078039908051407080b9000800c0c0d4034040d038085c1440d1034203070132101580e81d000b07200041c102d590b240e81500075200b00c1611460110144000b0a001d00602c2d084994842004170030042e0303c075071a030fa040b0350440c02100c0c95400580641c1064040f84141c1c41d000e90160000f40000d00410280e8004a801640414601240105142c100b0310b811000d0441240002d03103640800d506010044928005402800e0b01b240c541455940040e540384548a2a00e40c0e880c2001c2680e400d2000080541e4000e0800c81800742401c1c1c2c59014841400d83c060314420542c00e0317240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 59051559 1250 59050309 59050337
    0xe1c080424051219020c1b0415031509080c2404021806130204090209040501140108040b0c040504020f041805041e141506090c070f03201606 62
    0x180300e01e80070711519240d140a4211a500902160042600c6440300f0740752210a40070005100403c8004400b002402c42c40d259219000d40214510001c03a114500b0007080c0301a800714200b6900031680c1c01744190342e0310800c80211030090601c021000e00403600c04142440d400b60046490303a012038001c81e10b000c008508100d000880b00043e9400382d04100e00c0044410048854510550001c40042c0000d111308a2001080d0170f030391040d00203a09554000c0340c003003814101030150354050180c0d1515031802542800000b480c03150010406000d486118010940014059003240d0180c0760161080d5603940c00c1e034107080081d900070712603107080302c9403552450ba1141d071604c1807a01032940a0319010b13041c0141e0841b03000d807c2c00c010342074070004080340280d0301040c02008032840d80c8081034207828081c580350b010070a8041c0010180c5035440000c0207008002242e8034038061103158103061095840c26041840b40704003d418421401c07501c00d1820080016110140d1117045074642e9840c0395440343c000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 59052809 1250 59051559 59051609
    0x2120601111b0d020414071d0d0b040b060d050a0309030c2102010f0207050301021303050d02031206010318121e0e010c020d020301090b0a02030103020f010e0609010e1c0804 76
    0xa400c401c000c1e20242401003080340f601c1083d030751481e80002c0c404520200c0240f07111300c40101c280c0e2690082012483c0546a40d501c00001c40c4401c942151b020300020580d0b00c0d0300c840b02c01d0040009100c04120340c001181551025181072420fa0090300301d03904031a9500d80a000c00c0b03024041900e440348182400641c254403c007030094101038113940345500c0200d55006442030824034040700254000c070781002c0382686003440913081c82090450914a1580b441c140a030802106115600454004010410b001140c0c460043e401035001c0c07030700141124032410341d01046a81c501c4014010302100041403402944072010003035082110003140c40c1180442000da0300d848071a1020b501154804c11a580076203003081d01450389a00160022890f190386a8800950103012925076099507808001072042d41070500c7c0010140e602800e040034070708030540002d001c0c0e014540380c1d81e0410588074a03280c0a92142024020744045d212604160b000003403070644242e400a0003400d609003040351202400300301c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 59054059 1250 59052809 59052823
    0xc060901020c010e0406080f0102090f0102070506040b09030102040e0703090c05040c0e0409080405060f0a080603030f0403020904050f060903070b0c0f1b120d05060120120a11010212060111 83
    0x205800074101d10301c42100550349000e480c0c0078a40d00507920400095441824070aa002862000c1c00040c2d035502002e0801044030003c1d03c4290456101c00000d002a80350b0000302c90079205d2600442c1d4a88481000190291086401510803c05403009000010307800d6000364512600c10b03609800c2194898051000702c400840800300020a51052441c8034106a40001c42040c00385558030320300f0740c440e00403c8480d80703ca0004144a000010b400c080700e42d00404070764110780118050f5281000e2808516140d02440c003001e482240d440021504002d0100b11071850441c0810581d8150700d880101a42c8030713002140705035003400162000803803400c8880c00302d500d41d2100072060350410b0380707184d00d85a00100e20415100b0358411040d02032406100c2d0005062040c894001c0410035180040c001043e1400500120305039080180c0341400344d807070100350900e0030101c8005054580070030050454024900010313160140d440000d404041d50011041d04d48560b80a88440740304109a000e01599041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 59055309 1250 59054059 59054077
    0x40b030a02010509060c01090c0f050102100b03070b0f07060903030209040c0504031a04020102161e08010c020a080903210d050105010804080d18020414090d0c2103020408031b0c06 79
    0x410801c04d00d2601d404d40c0030380202d0790302c03100008100340240d807002c5420700030b50882003502001c010101701c0c03981c0c100b0101c0140400d9032014803003200380c0d0002c01d03910740c8980503008401a000c030300c00c0311041002040d959101d4014030184084032090034050003d500000e122402603040402800c0058090021501220ba0056440c158000044114846880054412411405620f0003460025120a5003001500d844c02e0b80160012800150700610b40c01a0b018070016414007080709105500419401995904408250354600643c0c0000c5e060018003104a2580ca59091003010714100c8a0060080c08070001000c000a13601c1d4070040d2960344081f14000e003442d100304000096544141c000100b54682401c0c1c079040c400340c41d40010146c0c0c0c40b82d00201c035200d007a01c0c01c000b80304600b04030f004c840d42ca0030305003410b502e103031503c5100000c00c030786094a45400100404480c541d219034120b80003411024207480c0c40d90981150060001584081104240705030b5500e640c680ca080c408072900c1c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 59056559 1250 59055309 59055317
    0x40e0a0803010b030a02070506151806100f1116090c050301030b01030602090112020a11070b0f0406051b01020f040602010b0613170a02310905030301050105130b18040b030a0201 78
    0xe0720f00390090443c4d0b44010400400c1a409124010010303400300034841c003070342110150864010340c02c81804040c1c8210701110404641c54018014140c55841680d04a46a1854001701c1c403c10944242c8102143d1902040f5520610014007620116400c0f110b00b074801c413103814019241107800c115000d000c280000350034101030340c00402c009980342e4000c042c1007c06042c030080f41c010383d080c48002c83c0c0017685a00c000c00c81c58510381c40286001c0c020300c2c000c0c003e00143e607818000404000c0e807450169028035000c4c44400100c800080c400c5201428601040000030342d55000d24a02d4002142c1003849400d01542c2040701e03002451810300160b803e203080c40d5481c54082e41c44c0c0068483c09000d10806805240940c0042c2c0c005601c07240d001c4403104140e00041010b8004260314242c101102c0c581042e0581d140242c081300050700801200e0450b803003460000d07168075030303a01ea00000c465660f111100c002400544100c220318103142098824a045900b007010311909814180c80b0200410024001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 59057809 1250 59056559 59056561
    0x11806021e01050121031704080325020606012304081e011e09030e04060f0f06020606030322120b0601081f030209070e040608070306230403050d0920040e0a0803 71
    0x1807000840c251039418087d01c1c0041d00c103100c840b405410840d082d0b40030342d1640800020014207050700207a03200700240e0781110741c9210000e11002900d550014041c2e5040000300346a1300f60700700b48120071074602c10340303010700e6aa5507a6404800c2c0d0350f0340f450090800402404038800484c08030610501c204c800c2c56518000e400741201e84204000c000703c10b421024004040b040e020f1603140c038410305016244042c0300500450a082a074054056107500c03900031544904100400d42e100482a0740444000c07160845244003605565990250550081403100f040e01d0510403d00001d0441540900801e8032202e0781611614108ac10210380721301e0b5840d0144e8608410401070403d841c0056000b0400e18084054200d180c0015060f01c0d9141c2c007844080e80400c8062090207400c1c0f03d1200c11413521020698000800380303c0c000703214402403005d4148040031801c1480300e48a0340003203403c1640308459803070f01d00407001848841102900d016001d14034100320540f80800c0041d9a402468100300300d1415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 59059059 1250 59057809 59057849
    0xc0102010c1b021504091b09140d060b0a0305030307090f150804030f050f12010f0b0c060c0f070b07110f010606051204021302030108030307110102130504050402011806021e010501 79
    0x400b040304c2d020070713030100d40070030002900419902c00c0120840d4240c64a02c8602c42d400c1d00200414400e070000c1d00301c0c4080005a481d03e5454403240448994841d5003c02c1012000300050541d030407561018200c0d0100008110341550701c600108141c400106c007210b40c1c40e4445034640980f9251b0f01c1e0724004511000045404640142603240c014900c0e40741051506010030b4481040e50822001c0803051500d640040c4802c00310078503154041c1000200d51802e028200582940c2d40101905659072041c00180082ca0181c0003801c98011927004405041241480c020040c01d08005511115140c012201010028401801440112516555503a00b0100d004045801c11000a04100d0303104841001c9100080f040f800514000e262174405186ca030700d0301c00b10160909000040401c12a4030401c091078076049151300359000d489040d200000c0907a40c601c0181c0b030000d039990010590120348400061501c1d0300040c000d007038001c521209040f514034001c2050907104c00303014070021b030074040a4901d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 59060309 1250 59059059 59059069
    0xb0a11190f05010507090506071509120306080105150a0b0a02010921110c01050a0e190f080f0f0a031b0515150402070f020d02150f030601110a2613080c0102010c1b02 73
    0xa000c1649000014290150b0f5441415000c50a018640813a480e40307010001000300384714455001c04010444c1d50035400c039800049000b81240501d2030318400c0490003100191007548407500640d402002078044050210500c030212070101302c17041c00101403482d40911441e0100391200c20240c180c4949040c01d950440581302e40e0011002540c02018440c100300c0c0b040019a00c40e40140740045100e00d07081c2c2000007550130610329910081003507000c0b071101d0003003240000b80840700c25003600d424402c6034280c010721030b4000d0400001814612542d0329009048075130744852405031160041601c0390206010601090380a640000703421204001d442d203001d8100050fa000600d44010240a0305c5101e21070b401d03809410000c7d52201e035003c00b1042022658001c0c1c1035154011030000100074036402030380c81d500b0240c00c2c0425003000d5a1082c41d2460301d00303810001d442400340c0301000a40c4050719a85201d07034500c624150302d030040d07080400e100450341c003c0025580102c0c103410f1069220803d0b8080c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 59061559 1250 59060309 59060333
    0x4020703081b070501090609060c0c080316030f14060910050d0b131505100501050f03060d02030c150d06050f01020d110c0904030810060305010b0a11190f0501050709050607 76
    0x80e0072501000041c002031070a10406c4507451240c0b01c00600310100341403203800c0703c080c10100001d001c40304414401003508001629881003004d203821045040b804401c0300501003c0000e45411f0742802c2480107601c0d0b404114510550b001d82c2e1002346030f034548100d0441c29a0621032140c00051481600b004a080410070950004211903403507158202a03845688100050440300304140e641d13006e20240c0968680d0701c0004110900e0020300b021540c40b02d00c0701e5480007a181d00d21032a40d801511045441c14040078030a54401400f200b0309000400390782107154069013440003e2032030400003088600e0140440107240c003069008200359207180205469091813490044081c0c031a620141220766180c40307609104a100c0d0b540d944050030310000308000480c0f40c0d0040c0040c181070800500400e10782c40180c0e01103141500d803021800381805100da0500d90f2030b100c0d40e401e02c480001440240720b809104d91444034440e40c000c2215a4440204541511182c002c40e94054020130000002c40d10642c03c907 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 59062809 1250 59061559 59061601
    0x50a08060a051206042109050d150e01020901020f1b060d02040909060603030f030504031e0c08030c040807120b01060309110d030e030114010e0103021207080a050109110402070308 79
    0x2441160b0b140d00c001042e00c1d805005155066010310108030400c2500f207060308081c00c9156a8204001400c42c0180c5500141d006040c01407003200407240611021250500c0c0804282504100700c1032116a0079020f58409101c860242c40f072150400940c1c500010035000c0301000054400005e54100100b040540c080b480b250442502400081490f02c518030550b120301e8030071180041d10510314500035244140ca507640e1014545001c08110110fa000f854038443c0d035829480002c441c40303e1040030754003072340e0f80c060203401040301008201c0b00b0054440200f0070b640721081142c20069840c3d9011025400f20030005101800c54801048035038000e81010642512418890102e5103405000c0340b942d44e9110810380000e560030f2030003102070400384210902009107800000d140c1d03060981103090110188402401400380d010a15080031051000c000908600f00940d2103000701d504026000c4c0060348030550f1100d103000c9440d00940303807602c2203407510b59140e100d1070402c1d55030040c00201c0141c3d1b2a82 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 59064059 1250 59062809 59062819
    0xe090c030f06031018120503061503070c080712090b0307050d1a03010203130201090902040f0e040201050415020601150f020a060c12090303020d050105090103150c0309150f1b050a0806 81
    0x4d012007142c4a01601544800840c0e001000d425181001d0740b9400d00309401800303128040061200d036071a1107590603242c1040c450041d40d25114000200d841a80c80403000c0d14003640410880c0400249a004440b224500d5481e269026141c8494081622080d919203001c18010804822070030300716005401e05034224a0350000080300100802c1c2640c1c02110324074000402e00b101c207030441da0014003c00141650103021801c140c03d00c1c0c401481120380380505500c00010300c000a086a1140c01103802503c0d06015041c0200c68002c0040c1d0380340c03070038000e11800815408005088510030003510f00110095402411003902c3c9032905402000038a00910030040820240c1200507240d0107005401c2d84607540041ea00d410100710704040745c4040e0451403064800000400101c1e0003084400300c89810032000103801010280190020241c2c02c2c0d0040c68000e4a80403801c40200d50307030104808501101c170038040c405800801c00800081030304050702058003030207130881c09449504055030113800540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 59065309 1250 59064059 59064073
    0x6070806030c0a18050a0b030a02060d0b0a060507120302120c0d060918050c040903020604021309020a120b060406030507183c06030201050d05091e010605010e090c030f0603 76
    0x1c08240362448a4020861031521070041d48010300c4d45106061380042c0381c2c0000c000a035003640c0044c0e10f071010709101030701c116408540c508190816602198134503a0090003030840c5a565003001d0415040040309640c0e1441d0758000e50b400ea0700a000b00c420060b01d0380850740710790f9a12151016250050029000d1640d5160400301d010b26540c4203541041f0200000403512080b40d1502520b0300b40810001406542007118510000342c001680c650000c1e0304540100e0a140f06002660003402c0700c2c04065889142d00000280c0c00c01e000b21078401c61400b9141040540d69a80288800e40c0c200348001030460780700c40b000308000c100151594020142400780840c1319800c0c0001542c90012540140880065444041c0d000803540c07046c40c04000c1107440d043c041c1a00c1c60700060014054a1400e003802601c5600051a900080c030000741064440c0c01c1c80c04903404030982203402025140200c1303010900c0ca00d8000c041e450a6180503102e16050b140ca2850f6560341c110b1211040030107429940c141c480d9207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 59066559 1250 59065309 59065333
    0x150c0d020705033a0908040e0613050109050717070e01030e0709090b01062c01031e051e01050420070c0b0a1d010305010506070b10050d05010605040e0f0607080603 72
    0x4901c800c4041c004c80181072900659108040c1e2844076600c0342030031180382c180e0000000d83c1c084191000c440300220401c200e580c5000c042100f01840d00c540c00001450107002041d0242590b0209006a1655848096401407030414070b55422040d00e0138030110720b02d0340390101c0f258400c0d0490104803110313900b82c4500c1030780c9060800030f4410b8610100d1720017400d20700500403e50b0125071a8806080c014100f690101284540078000003c1e60350603040646a242d00d5030401c0d000780c403405040507001e1040042d4905540c0c3c40c0d02c8154050230321501d2104400000400d07103050f005440c41200541182e000b5000c1000300d840b4190b0000a048508140300000059100885005041c158005440b030090152100030b00080700600c0044c843e060510300001070100e9210001a038828546c8100d121185846001000c02081440d6001c84d034800d641e80b441c002008010b410441c1181c40960301808205404080d09446498050000985500c41c00000d41c4c40c40c8a4044e49400c5000034040c1e84c80c3d05051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 59067809 1250 59066559 59066587
    0x3020c0d080103060b010e0a0303050304030201060e070f0207090c3603030809060109050f01030b040302010e0d05130e130b0c0f0f0912070524130602010c02150c0d02070503 76
    0xc5026040841e92078401002846258040d80710b9003582440e0003c0d55028000004070080d07802c0c0806001c000001c0300250400d4000d502540181504040130300c41440c180c0401000064140c241c4401805060740c000384a940b24001c040e11800185c80f0f45018203420380218061014021000041804014002140d503601c005084061030095503604820b141004d0b010b8a0583c2c183c0c04940c00c2c9250004111480c01640c241e181540d45c0121081e0030b94586040490151a020312034091500469029403101a00000100200c01a03920500b998541e41e0004461449080301e00040400112080308001491402200d0780300c4c5d0202034032810003404141158580c1c100c040d01a40800001410484502d447c4280c0c0b5500d103400070080400600309008a1442002040710000e0240d010000109402d080e4041d82c8100e10340d002004ca00c02c4da40e02009020f003454600c41d0015009901403500040364940c001d5224800d4280c0413481d0828040da484000e60000e10141c82d07600043c0700c058103600d82 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 59069059 1250 59067809 59067823
    0x33030903030221180a050c09040609020907050306030d0305190902010c06020301030606140402210a0e0a08030115050f180a0306090501050103030305091f0911030709020d0b0a2403020c 81
    0x12400f26400b003464201c0856990907405541c402c400e9210102500001d50001080b50b0303000402c3d43c00c90303d980c40c0d42ca00000a850040c8000354840301c001c0401c000980e110000e184110740031000c03202c0c525031981d819401c80f0001d4404402d40c4801c400380d440200400c2d00030a50591040c9403c4c40c9254031a101c03607080741c0081c2c00c201c80058031260100700d18109065007450030841141c0462a018607005010200c040002e07000c10588421000200c100d14507901800800d60800240d5007086014a4034074030503031090052085500c8600c0e0f4200840d4071800c19115901c0041ca0700ca8580031680300c8030454190a103654541c17055002030b01000143c9503014800c0c0080c0b00d2000490709504624000c2d05039040203007818495407103608852080410400e811080c01c0c818080020740c0d00312030a00b1101c8080d40440f080e0144104000000c0751210b42d8010704032a0b084c12810440c400c0240c080000c085950b100f02c603030310010030140b18003e10b07400344002c68400a9007030040c9082a129801ea003401c603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 59070309 1250 59069059 59069107
    0xc0f170714040e190c0c0201080405010b03010e06160306060909091b120303050903090a030609051005070207080d051e130807081518030313060b06070b01330309030302 74
    0x1480c03c10704c588903011015000444603030000c01e00410f044020002d003550202a4007a041010250200301400021b500900c0d1001c40035000303000d4030041002c0c4d6642c84130b0a441c000c03c0301c110404d003681100d109120304004d440c4580e603280e50042c60440050050451000144e078450b0004100605175a84c2c08020700092100800700c481d201c0f1076040290807600c2c0204200c200e508100f002c0071080e0341d1884d0382000d032039101000090050701424050b1500d206d100f07404121615040500c51050f400007a24401c9481e00d0044815490041c64101c1c1c6a0282810000c0d0600d0000070a5940c07039164405010343c002007170800d446d020364030345400d40344c1a84e51b40983c0160f00480c0345010141491034070142c2c401990140d1100000c41075a000c0c0c0d4900c002480035a4004950440c0030421540742c000d003400c03c0300100104e80750310780d038102102c1c0702e130003842060000d01020035450b000c01184600f1185540c43c40700146105080304000707401500c803552007142015820026101d100c1c0d01c61a51a84040b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 59071559 1250 59070309 59070329
    0x105070801030302060a1104050103110403080a0507050d030b030303241f02070906080a0609030c080715060618140d05030f030702160f05060d0608061303030c0f17071404 75
    0x1502d1424080e04258024248000c01400e16030664100710b4142c0441e01150001c2c41d00154005142a000e1498007482e04001c2c043c0d480043d0914503550b110019200030760090702625022038506c0340503004c5030b17004101103070541c005100288455942e0304030700402d46207041c002c1c1044000f0340001103503010041222080c0c2d8140e04101e41d982d0358108154006404660001c008a5003005e91917980d03482444c800510141d101c0c000a41018071900100c03070361b1035101030040c1d1500900d107001200780380c115588468040c07800b0030004603507220311003103031800100007071100c02d203801c108038102008120030003d600311b5640240080025001c0000781054040441c040c0e4032800c080d48020b0400c6100184010740010101d014401d09a8014a0f0001c50380d04485982d56404183c0b1482c018220175484104507000b001c0070032079401c155920001c07040388690703001c2040c01d40b00c0320b00762480b040456101c0001030300403455901d079181030440340750015000d0500320f002c1180d02c401c0c0c002c1907100d600010640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 59072809 1250 59071559 59071561
    0xa020a0605071403060402210a0f0c0f0503060d051903120c050f0d0506040603080a020615010302040b040614070209010f06081003080f0702040e06010902070224040501051b01050708 80
    0x1110403845940e41140c81071600c1e001108083c6100f5510340000380c9100c0c45507500085015401c4401c03d0909890b05c0b41d424050320601d821072411006090480302c5800090421040c03180d8035205409003101c01c00941c8078181591900da0501840c6071182d1310441d910f100c0c1d100c02f450300b4605410030460061081d40c6030b041e1602d098240314140c0d10022200018004284081c403003e80303d407020b691010615500002d1103603214030005028019680c0060581c0d007001850705034060740070500314443c4440214001c41882442c00440407441135208074400b0307090601051203654820381c100c404201c3c0c090401d03400c2042940000d005100700380e002c0040c0d070b1180c817010000540c01181d8180e11564401240d80c001c4d1858032002581d00c1650240107a11500042e9a8210340d01c80c0e0012072484030100c12100151f8640c008003000b50301141051348500b0019140c018116a15810702040040c901c2c03441f0308091074500159a0ba41200030b450000510001040c03060900034826a8421f14280e540d03240c803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 59074059 1250 59072809 59072813
    0xb03120c010e0a031734110d09051201020702060d090201020708370b0405010b0f03030405061e070f050604020405062707090e01151b05070b031305030a020a 69
    0xb19226000120031a40014040c840842c1d08105d15070000094038040101a40d00e022075000f6411041c01000d240a01110b0082101c81500c0d08442d2400100e480718016102000721680d40c1c0d1720300740b01b41d00000d030314400d0a000700e091003150010903d04410001d030030154950b0008256401c090150504980c2d144001800e56a040080200400f4848046c10882e80813807040c0716503450b00044060030000308540603601c00d0a206940354065004420100750342400d140481c0604181c2024911a8509115403c03003443c0210460b0201c8400400381442c00300055802d80c8142c504c0c200030385101400b800703d003000c2412003500c00451791085001e880c5601d01441044119900035140501424410901940004c400040c10401c90098050251543e03a0000200c440c00100d41103503200402c034800010710800203085a002d070016944940310a0b40e6056400d6480152501e80541154804881000b445100d040119000842c45415114001c12070723741030310b154840c04070307040113078014200c1303c007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 59075309 1250 59074059 59074061
    0xb071101090f0e0c0702010c0204140a230f06030309060a1e05040302061602030309040f0603051005101401020c0901031a0108010b060f030a020d1d0f010605060a0f030b03120c01 78
    0x409881e404003401c0209050800c0f040a444000f04181940030380081c03043c055a000c2c01c088070308180d00620600c212002050030310180c0a0a4402c0413036182041020b02c0d03044646080501304440c2105d440c01c00c0c2c1d84480524403d000c010b8806138040c0000c000d00303185a02d54034014042c1801c00d890341c50f00c503500385480720414940e1010301030400c5000d11041c0700590f1000c08903851914400c0c410450402d40d030001a040d481344c01c00d159806440c021540ba40621150030500c00c4034080c2e003d591101a60060768000c0d40c1e03003160b03442c03220000150148084005a503a21101110602c100d075580315040020500d852000c0e001680d003181c21a091010507581e0b01140da024241400080c45031500c0c030f10105880707000e0085010791401c0040000303003035000c5640c1551205141403500348100040813003941040202d11240080e079005102d1624060340b41406070004480001e44110700d071210380c000c101ea4250b0800303080400c141d101c90301d2102607507003040f08550312003400061075908c2000001e054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 59076559 1250 59075309 59075327
    0xb0a12091b030309080105150f15040906140d0503040e10030203030307090e0a0c051c0b0d060518030301030c0302060901051b010606020106050a05030d1b061803030b04092301060b071101 82
    0x217045a040c6410071080106104022001d65815146168610300c4100000c402003909075500002d644042000030312480c0326002001150b07d0150099051071401c1d003441000307200c1c22000b801c1030b4001c200c100705c2040b10011899102c145030308041005a129400281141d1003130315840c0008265103c140441a45150040e0700b003443c1c150308100750a031043c806460307802044040b901484008245000d0f002158220391120b410080074118403114600d48500188070588e600c80c218149241404405800003040301d060f00d0300102d0340306619241d035081040c80e51042414604000c000e201d0862045104126900c8840b0300d00004500c01e82020002421140b103940113038070511000c48100700d262008541c1c3d00413201a840c3c800300100d0b10019604403400b0114000b401585403001c1d41d070000d610125445401d5100307980c01e011143c403520402c000d840340f0003405021002d00c0d0407440c0040352800402c42d050581d6a0010440382c4d0303502903038003881d002104155041d0b054150004403541c5d100c0d20300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 59077809 1250 59076559 59076569
    0x16170d0507050304030903031404090e060915040b0624031512030f1801020a080403030201060f05040204060e01030e07081b04050c0301081207020406030611070c050301060b0a12091b030309 83
    0x1203803d600d8a0b80b4002e100e10030b44c5c031002d02808050103000c111010800b04440281030355810030320a80c1c0f141c80c00c0c0303503560004070360100f2107000b980a0b03d480200648852405190024001c1d00aa12200d00708513041201d005040001e000c685c0454072808140c5010794030420711612003400f001c0c0c444c010b10420002c46054004160020049160007142c110181c1300308090941541d441e0794000c00050b0300d4500e400740041d1080d174000c1400010140e0540004040d19117106070704210f2641c0c3c0d03051000340c1c0500d00030f060204809104e000415442a4459860340e407200e011a40300e41e41e22032099041c28080c86405400115002d5640b50300d080c64003a60f074101200d846010301e50740c901404607032202d0000c18956035102000406070250750b03ca030008000383d03800000400044100c168031401a600003013049622040c0b00b40d0004981c40c06220700c104849641c41401d05e00310b12030000f00d4041b5400d011010407150340f1965000030850084074040c86502d0360000c1c084480c15824050141b05507503201c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 59079059 1250 59077809 59077817
    0xf0b041a01020c01110d030905030409090b07030c0203040e0a0b220204061701062304150f02010b0102010b060a0c080c1207020102060f100308030405030c0f01060504060603090b0c16170d0507 84
    0x650341901e40002840e00c3c0030141b074900040c45240301d1a00b20300754400c071b41c800c22100b41450900300c00e20245104040c0640c0f01d9480401c412514103100360f07224000e070701c10030f4800c02c0c0110000c0c00d0115190803464203440028081c90126544005680c00714148195842d04079901140c184011500241030300c0e0030344603552441400c1e46c50071100030300b10800000340344290f0601c00c15150038581c171035090b20f010304a60308a5611203210b8180042c5500740301c01300030006600b0725120803050350062040035003506000d802a80741c6517801c0000d03106c2014070401190f140000704072000f100c800070300c018400f08109a104559030021800024600140544200c031001c400750300344404900c014690004690380551620340304d5480782009429030041483c045203900403c086000201d00640c41fa1013511011641000b66503200d100880c121058004000c141083c4e420100c0e07000d404d5a40503104020203030345007000b00c0398507980d83d00000c090a880d910001001040e07400f058081030054551141052038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 59080309 1250 59079059 59079077
    0x506190b060f09030a08120610110d0318050a0501020d14090303070c1401140108070b12040807020a03150510061412040c0f030305030a060b030907090f0b041a01020c01 74
    0x9081c0c0c0314180064110400c00503000b500750300c0510400100b540c001c00c0245c0c5600da032002a0400c040119550f91003180c241c0144030485006070010130b08019000024a4600c408100940041141c103201c0b0500210b100c1080002480c20040c1d041030310311490000d078440c0c10800309130b0217407003011035001e01c454a050300304880e8100010949038000c541d4a815940507148d824030b03034031560700318004410725402c15102160315210700082604071140e003411240110fa44286044160042421144174140c050340450089214000034104241c0020928030006550340d652801040c007035054120f00684910422503099101d0700020010030700b506082a0400c41140c2d036900070f1180e0b10348a0380c1e811288010609224000740a08e02801c100900ca501080c0c0328100503026410031035900c50404e00785040400c001c007400c010750340a0f00c851001018030504060074607014208290072440140d90360000c0e003000d66034a0050354120304d202c2440c51076450a0200081c181203001a59a0611512407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 59081559 1250 59080309 59080331
    0x50c0a03031805060702060d090f080301030809030c030d0c0b09011d06010306061212050d110a0c0203010609180320071403100c050d09020a03020d12020d020a03080708150d050619 79
    0xc008c41c0c6030514801d5002078100943e160105002034140805042c88802100200c10000040c00400740618220b084403401c1c0303516000c0550b501c01e411009000039103181076203c001080c4510258005140d0000894503c490080c25230910760359402d0f20002d03038840001002031201600c6990003500036801c046000803281d856882c092103480500c54100080011031030000880d0b81d001045a02105240d40e5594a402c0c170024950380d040801a0f10030f5207047c8000501051501c82c5828403000c80950004200340ca440c00d44004da022040350801d81c80e0744198000d007100034828203018011a000e10055011440305041c5041070501320101d02a180480c20000190000c0503940c441e18601c8020844030303a03501c0401c1d1448890b900007034101c200d203040c080820440407e05648501280d084581d010b207818400c0b81e0310a09250040e006c682c1c0c50001c10090340c45410820380c0141900c800301101f4640002090704543c0000b8107851a0f0040ca05200c0f00304d074810681400d45e05040000e104007200c0c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 59082809 1250 59081559 59081569
    0x1b03060305070e2505030a0f05010e0402040c020304170601090608030309061504090206040902041d040308040b0a0e031201030309080c030705121509030d050115051204050c0a03031805060702 84
    0x3409480050380c0400300060351090880c41314018000d0740914240350507450b14003c0d02d00d0300280e6090b01034a05242c102c03d8460003610074a07040340d5155068003180d8503035400780801045040d02950441c00104000301e0700e10034640d040103002085000a00f01585400100c008540e641d400c88002e035007041041c0400d010300007904680260002282c00c1c000e0a1800c0040d00904001000175006440400d0000b40d161265004d0001c4440100310103424107009240d047ea00601118005d01041c007901c08140480d100419003944502e49800018203a8040d0458902e035421042d2504411596100140205940301c0c19602c0117040001c014500b00207100d0000e40ca400f40790003210f015010a00c6401c1481c203040000c1050036100d4541c2c9003040c2042d644a80c2c130f0354020303c010725001e070809000041100c1d45e9130183c2c3c4808615940c0300c0c00c0045422a03c624101c0180051b00d0320703c1000d6085045540d043e2444e0015442034032800d4600c280d9002c101580d003110b40c002c41c4280014050940540c40d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 59084059 1250 59082809 59082823
    0xd0305070c0201081f0e040c05060a02030406050c010f0501170c09070203090103050a0f0905030705011802011b03030905061501080c030108072d2d08100207020111010f1b03060305 79
    0x7090030181c0403650f50300314954405c03a220081884007020080c001031643c2400541c140140e0140300c1100d081d82d154028815a0b10510701c42200503401003004103e280d20440240080161032130021450f0051504840190354007030300104101844075241ca480d090003017110030034982c4c0030740c2c44400c01e18111001a440303000e42d150301d0341815110800540c0042c2d1590084241c1d42103e003003005140c0032410241c0c0d99411003401200c0b80d41c078144514040305051070300d40d03c0007a8143c1d02c02c204551204c0705403107400b00c540d10032010302d5159040c0d04000769003032000324400c10b0003010072250705a40d01c00041803040082c01d501c036000c0c0100010710040b00003288c1e2905846c0e00156840d20740c18100d0482181c50140c1d2154800c3c044aa440440d4401c0200c0d03031071007039010b066801d030490f660f61084180d1403421031190200b2940556a03d403500030664001e0000340e401410a2500340d00403c109a095411f0380300303500c107815541c524142c944071001c0502c0d07980c040c0d24942008250b01310341d030b07503603444507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 59085309 1250 59084059 59084063
    0x60405070206180c0d031806110601050d03050909010603020910090302030a231204060e010e011d01140f07050609030a0801030209180307060501090e12070b07090e0103030807020d0305070c 83
    0x5002d03032404400d80c8104181c1000d02c0c1c0c082d000c24541525030500400100d0703e47c1a1950a10385d00d013002070348600c12201b1400d0b0141031400752507540d2174038003080342610410b04100c00b4032100340950312080d52201280c9008040544026070344202000c20008807208102018050050000c010300c056100007560b6044907a0050700841800c0f902800320442d000c025420070540d00c16118040d8095001101400441c1d0554030784c00b00305c1d5441401503402180b10a0a140051004002c500d402c01a101007141a00c8060416401c1d0102e102c820656561211520305a0010001002d80400008010150303000100070040c50504101580c020a001c806102c064440c90810010910b140e207002e410303180303140074401121740c3c074041894020040c210034400d0400c81e0745000180034420802140c885131100b0361040051803c041da64500c1040c81c0c015015a04002c042600855101c145a101d280650300a440d1646107181c0450005d01d00b402600c014000c1509003400e0001d1242c0000304d00c881c080d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 59086559 1250 59085309 59085331
    0x9020c030304200603040609020a140603070f0e040c110f060402010516081b0105070905010504050102031c0b0a080f0705060708030103030e040902040203100314060c03010e0c0d05070512060405070206 88
    0x32120b00b10501002510700400d54481000418041044010362101148c0d078400e6841300d511907a2400c030620003100342121141c101008100080d03c95200701b80600445e000d0303040c6105c0070071403c004103044504040280001c103608040b0721880c00010440922010720210040c06249081c1d40002c1250040120141c060b41c1d80003511401c0080c25400d4841c0c007140d2000f000d41620400300c40318081c1000799881c00c085840c080c03004c1480d503c40c104407801d955060b00158500700c004648041c40e14152420040103680c0c40b060b044059403406030b0b0300020031100004080c406184585035003840183c1d8070140c4603c00070024040040c8450040d80d0440e509070905005600d4900301080c090680c81800a50042c4000200444085500d10354000d80e40a0300801285840c41c42c0343d02e59418083c5c2d40c141e03e0210a0004100042228504507404800c01114500384403c00e58020140c07003059507402d001c1070001c1400010302c1000c84c45168001c808031801c0c0664141400d002c4e4540d50040d000001e00c8c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 59087809 1250 59086559 59086583
    0x10501150509151c0615080114010c020301180302060405061005010c06050702151008150c070f020105040f180b040911060901050f0315030d020a170912151009020c030304 75
    0x41d602c2030f0644649180424100a4011400c000000141210302a4140d0040c801c6100d44103c3e1055081f141070381e0010600b800998400c2d00103440301001a20103c1e450b64076021444160203941e4500075216200340c004000c5401c1914026060550091040d0719090802004000ca80e03032103c01e0030186a003000001980d51030303c034000c81c10a04030444078408640c2110903c070075a602540130000f01c0300300606860740e404011055803b8440d00f95018032400398117100b00c0300411441408480307039074414140070f460559035407140098131040b82c0c8001000004001ca80d4500181401494100d840842e410000d10000b41e4650400014001405001325408101c0d08481c0e401901100d0900c01007120f450b40744c0c900001d40200c0110102030050107809600e40749451540001a06404554880080f20000100303a03829407554110a401982c05003000d0f98020b00300350b0a0290f814007250447e80f8503a285050004050004407942c012006d00c0d1040044403c5180d010043c0e940040c0e0040358803c84e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 59089059 1250 59087809 59087839
    0x29011b05120d110304050703030906140f0c010902100f020c090f0a051b0f071101090b12090309060304050606030f031c020f0705071d09070e010e040203100c0908010501150509 77
    0x141510b00309150f10030300010a01c07003070210010b2600700b01ca2207079940f01003440e19040c044411450040010406590510080c0805070143c00584510700030710b8000945400c054000a01b03c200d5414080045110b11917070a266070750500c64034015490645071000c2c18100500040001503005101103141603554000c0740141811142414101003241d1595845e0100c0e4a02222690300c0240f003220410034020100304c20f54014910303e4101d070601d410705403d0094492a42204030710042510700c04e80002c2155011690390340c0b02540c02140910010030662502d1000e00d40b409506030079450441c3d0081c0b15080480041e4000c08030b080d02c8042c00940c5803103030181d90301014024036000900702e00580f280401c1c0300c00601001c1d0380d45a0380c0001203000341c4920001d90b480b1443c900520031503884000051220b5018941d100750494409411510840100c8114004036600c0b88032060002d00d504004122694007400740c035015011f41c8245984510303000601a03c1403051242607405001d2011520340703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 59090309 1250 59089059 59089061
    0x30106050318010c1b14060108011d0115030803150d0f03030c032c0703021e0a1401120203060d06062304020306030601050d0c03080a0207030303140f0105120129011b05120d 76
    0x140c1b02d920703041181c4a958441102c00d0203040513841143c1a2161000310b041442c10501031000f1900c0e4000d5143c2d5070500350744960002e940020469070a00042d080c185520f61a15140ca200c846c1c0601581040c4101c207103401030564550703945440130181814803a0411450304940440e05290034901040c4402d80c8030300c12070a101c240e520107580200c0e00c502c5203031544800400c5410307128044441e40005911541748007850345440d000540010100b80c50302c50078034a607a00850308003d0080031101035055541c0c0721415a01103400c200c02c44081c2c043d030b10340c80c4200e070252280703044012201582145008002309666007014420903110f07a04040d00a410304c4500f5455101840d00301c0d035a00c0e07071131007501c1004e541c0d4041840110006880d00c1007030310301d5102c0c0d41d454038044c0745d00b0a08100d550b460a001c129446a1941510a407556250382c1c2d1401c000ca0504080e940c0711000910a5a50081500240140c48491940d180076403102c09500009200801c0504180c0c0c80c2c0c6450580315812105020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 59091559 1250 59090309 59090333
    0x609053106030204020c0303070305070503040503030406020a050d090f0b0c070503030c090d1b0e01050a03030e191e03020a050301050106020a080a0c06050411041d03071115030106050318010c1b 85
    0x10b90410305c00211954200c0b8040002c0d4811155620244000d40322030780e0441c2c0c148400c0350302034042d400a20120740003035440e0700100003103281ca00d0041c0c00c01d1401509030040780c444880c02c0b03c100200e6610b010420591181c1298041f048040721820700295466484c3c580c44000c1041d5100a000195805070340d48400d941104150400062103982c80d80c01102c03c0f00c82c03040e01031405c540e9000302c00041e941c40c111407240306695261303031002e2040711400140841d1400380004540005a40305000c166100ca01c1550041c4801106601910302d03c0c50040c84110010380c0c004a0003030341000010f20020340c0001d0b122524650200b15542c0d100c9540d002190660100310000384071508200c10701c018028507820010745001c04031020800c0000007000040303018113580c40004180c100b0b0100c500414038412003190054400b4011400f86113282121142c0b60344240c0144d00800c3c00400ad014400d24228403046041328403000805c01101c038a032015102c0c0ea14100045442040000880100140c8450f40d0f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 59092809 1250 59091559 59091563
    0x50616030c082208010e1c0c020f1002030909090d08070f090803041d060904052d010f0618050601020a020405040203010e0604140f070e01060804170403050304060905310603 76
    0x7030b20034440454024070180c0194400d48070b9942c00c007180c0d081b9100012850480959191181c200f058a0714001a64046209403069900000c2100b0360380c0729807a20603500e0000b4001c0d0380a145e440b1520744c10401c075048050170b800c80650007042d0b480c82d4503030000320b07041d000507442c2003060500c001c0c9001121151039942150000380408680054000c000c54960604006c0141e8518082d50380c0f070013070040003201240c0141c170030b0f407000f42201303d0542d18681c40754207500d0b02c442440000c0100c01586096030804005a0b0b205039a906040051126400020140c03071062041880582080b4000039525065084083e1080f950344001c2401c5503000d50000c015004ca40043d642d0340e2030300e8107040b83c1400111401c12014050082103010010000c600c04d010b41d2510800c4030026400c1210454120304001d0040f2030400c0b4a20a50122140c1103020b8401548900000e680c2c0300c0c203003100201144040c2d405180280c182800039852400c00e1040c0e503608402c0c404070542040c4854034040040d081c1d42d440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 59094059 1250 59092809 59092837
    0x5070b0306061e0310120b0c0a12060e090d1404150c1202010501030c080307020105030117070e0903040302270403030b01050d11030a06080a0f06200d020a0801050616030c08 76
    0x101c074000f1201005580700f0141465103d0045540381c80e0003103a42203031507000741480c10f10400541c940000d0006052103811600e018422405503a40420440300d060b0004a4644a1141000310084041004210031245460030080e00e51076080d20074a5802140184c1e0070181040404071400c911968501d00c0031508401d02c01d00340d9403000d070041c0c001c090a0100f034904c03071007040003c82e000c8800030494011b90350607503030f13146180c0c60301c0c11032a001821141004050b015019002070010303a203d0b40180103a1844014554a0345184100301280c55414900100402c40e00d030500c454905610303105074850b8040c2004030b002a0384900417201ca229500604080c140b4101c10f110b12084080d001d184512080c96042110716107030b0641d07541c0c4655100c002040518050400c1c070005071560000c1020308003d0b135500c0b104011b5007003400d245810036440542d0240e07020880802140d80301e80c1d15801464203454a034600100007842e03403000403042001809100f88007200504002541d41114180385110384 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 59095309 1250 59094059 59094097
    0x62d010303050a080a02040518040602070c03030207090c0c030801030305090a081b03010f050402030607050705070e0c31270507200c0901031205090d050102040906060c05070b030606 80
    0x7074003901079080000100d0010f400da03000510902d0030f5208803000d40744010200c0c3c0f03040c102e141c1561159600100102c5038190240201e030005002206807070b0283d032007a00685500e83c1850220b5040380e000f111508100111400d000d00805d800c9004c1c40d0650b900762804564074805240450311070010380d030000030b6034031444242c603010b2481820b041640c00000c4009020448007140c45e142594401c0d079010358183c0108000c00d250900580003000d00a01c110241d03001c01d9550742c0c40e1203000000f21030340295020001800b00c4007104210551895207140881461044000e0441010304a8030b40904c0e4047c4030485d01c468120040b0303000240410803d060107001d60300c0e001c0c400a0500030301d00070381d801501141c4c00f01e1120380001300d03030110a084050001040390307185480d10300800304641044028801e04103e002034544680210340550390280001507511407030480d00d6000c031180ca0340070300104403011a00400141020a81c07004442c500c2c6512070700d035201c202c0000d0301441880075458207401128 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 59096559 1250 59095309 59095313
    0x6251406090d050c03090d0212010c0905090604180305090a0807080d08070f020d0c020a080d08040b0601050702030606040c02010b0a0f18020c0309010f0201060b070c0302031b0102062d0103 83
    0x6480e5200d09084015034818400c904000d4410740500c01c00144d09401c140107202060501603007080d60540002c0c00700c7d0212100b0300d00e10342190f1580940000040c6403400c244294141005070940007001560300300100039400100f4a41501048002410060300082c81c4460350b46180000300078200040079203001c20354401820369103010032061030022540800000302854040c04101c58045115005002c0310361615a044404030305001c4100d91042c1700751804141400204851036480c07401e03841e811100d05041c10f18004160000300351b541009810000c520040c0c5011400e036802c03210a8401051100c0500f005034094075044400c590420135542c40068800080d1062400303c81455507900398410383c0c01e0340c4000b680b01d0305904440382d070302c02c10135120342d54030880c2c100e50b82c10054400000c649454a140c000300390b0104a06132401008030b4401e00c1586800e01129241c8203034072110030230b0803d4110003c2e4484200500c00c030b1980030364401103820390446010550080c00c0185140100d50f86074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 59097809 1250 59096559 59096563
    0x13020f12010f14060a060c0602070c0e07180f0512010e0a05030d0f06060503010509041a0c0a12020306011b031b030f03140402061b1e0105190b062514 66
    0x40c080c1d2080c26400c111080c1507584629480c3c2e8042c1101808a4a20a043c840203446000e11003074103c906603400c2180a002c1180c00d11040c0c040c02e080d00303a00c082c0d810806401007421042c3ea0007100c444c0380c0c004c420840c5e003519005400840b0700c10f4800d447c8828003c0308007801088102c654040500403110b0b22030400502000410342c05072600300800600c542d008180c01110a58007512012520410051140303160502d81280d00030300c501d48404001200e030300307110000c02c0c064420140c02c0d0804a001d5910542008070403074071a0111000f1400d51a101c4002040081d090b81c48014029404498005262103194109010401240c89400c26a41860020071140c6085091400a89400c410504c002d001006042c01550004c0c0704a040c00d41d10794009018101039003001e00340c1c3c407a482c2d1030444c0038203a00303101610b0b02c80301000091a242075140010400c2c00c0c91030240c0319030b03e13041d00c207009543c9000030359030556607619030018050f860034030060517065280e0026141c4080b00000400700480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 59099059 1250 59097809 59097821
    0x406020c090f010311010302030a0e01090b01050102010f0b060d0b150a0c02040b030303070f0e01021e01061a070c09020d0b040207050c010f030b010203031807030b090c010207060e0913020f1201 85
    0x103403071800700395030742d49084654180c1c01e00004240140072103e00055603c250050758003c608164001a900c0d4000031980c01c55104900032a01c1304440c600410013980c0a104800201d10400342c1403248250120004099101e291403c07001d195032001c0780c0c8d511b0344600801c070284106441e80d076070381c2d1101414050032491340c05e04100d1055060002c00652801c02006803805a07005844070313181c804d184401624030b5200711300200c2c1148550080c41d080c282212810a141d550b4000c000600c003030800c1c014040208111601000d44041044420001240040400c0840c0c6030391100585071500c01c60b03858082d262025480343d0090000c0762030b0082c0400410901101ca509032100328041c1006003058098075000f17a049405a041800000c00c50382c00e030300040301c100061205950344980c5070380c0c85903031100054604209a60001901d4131165030100f080c5400b4140ca030030003000344805e40300010340110340284030380359140c2c6c1d1581400441d15503c0c0c80720110700008200210081c2150201802007030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 59100309 1250 59099059 59099083
    0x230a0c15020316030605030d030f0b041e0b04090b01030b0403090b0703050a03060609050d02040f090209040c0f05030309100f0207170a020901092007030c0c0e010509090105190b0102010b06040602 86
    0x100e2601d03c810710034000c1c8204000c89002501401c100716450005400070311a4800012030785407100c02c40c400c20b941d140b140901c540142800d041440907120380d0401110f203080c00031800f992401d16900c0c04640d240a01d41d04499024606106035602c600c2c04031010181070348080352100c1c020031500101600480074081d1040156805c0000c5a9110400c650810040c4689034004155100300d40260920b40c0000da509901a480410301000540c0400d00b020002ca4003560110000704003800300252090410f001418101c0003103041c42041e100007012000c60300142c0f41401090110306454500238000d480061500e294140710440e802d0502c0740c0c4480e0341c848100d1041610000108001c5540d02c03950318400250441143c1c0340d0041c0c2c4240c1d4069008810940900045c10410000501a00c2410300904034054003841702c0d5142c0130078044091000ba003807240300e074145010045402c0c452440c007034412649440216140030501c0041c0d00614a82c40322540083c000903010640680008200f85080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 59101559 1250 59100309 59100331
    0x801050408030105032505040e070b030103030e03060109060522090c06050a03060602060103080405100c0f0f060506010203070f0611040816050307051e010f0e060c0616230a0c150203 80
    0xa0082d901c28000b8019500070361b0310b402d51070400f808141029489140411800e108450065454840065458009a00480000d42200ca10045900741070040d5401048900c1c02800f4141c00c0c080011700c1c000740c4503018001048030461198007082107400c19200540c0045050045075110400100142c0c0620300f8030012a0800200083c468800980c1904907038012000a007401c0c01c3c0020002030209070a40c50080085503414400070582e450b0300d800a0354410112440044403515000b0240c810081c16641035410600004d0042640c4c00726102c07003250b120300300007000000a8200c55031030040d50071003a018840c0301c0740880c1c0c1e0342c1c2803141c8200b074840032011a01d003103a60308100004202820108005505135000c040001e500503403058413810070780d0900000661801022503003a03085681c1e405a00e6022a040c0003444c40760446a9901210078038081003c011200307034034010601082c200c080100307c005500003d20f485082400141a442055512261500c86510000c0d410070350361a0414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 59102809 1250 59101559 59101573
    0x130b01050a080a17120109060302041107030c0f061b0306050f0d150b01030b060a02010507090f0b1204050a050f070e060103021c0e0705090c07060b0609090c13080105040803010503 79
    0x103464521450340881d1040002414840807a80d00c4400000709808048001c100170300040101401d4808046d001e0f00c800301e0005110b601d140100010340b4000011505110070030004035010030f0703210040302c2c0b100b0f4200324014941c045525043c0020003d04205c1400c0c07251448030100b83c290b040d00410201c5000300d41c0c0c8001d894000c402c000c07000c031404100030070901c004c0e4944481404550485100202c050500041c0c80c1640008201d441e07000d001001c3c0142d541e88200400d1513000b00070f41004d440d06030000800207041c06001c090b0741c49013602800d891541d1400007001c000d0304100c4800b405501c0005c0c0c940036180e4542c144d0340c1741481c0c0980c6181c003410800103820355200e8403d60b0f2005207010780c940c01401059841000800e080c084107051805004400704090f280c0b444054000d02e6580b00702650b0b2001e609040040b034030310703505081c81100108104041c95945590050300000e843e03040a0340ca0003000c880b400b002d0b41580c05200c0650a100400c001d201604010350304807501a0280d07550 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 59104059 1250 59102809 59102819
    0x10f020405010203071b030f080d05070e150d0b120d1106070503010302011d03010504140c0103060503070501050a0516030203090108060306131b08070f05030111180d020a0e130b01 79
    0x2603004600070389005910a11401010503246802c0712050030220705020031180d202c0c2c0b5904544840240d00742e40d1118002004004941203215082e404541e0b0325011403003020000c0012209141050384001c180310200e0044103c0ca02c5500400c0d840c2e8000b060120b08500345080c02e9142c1e88a11014070129420384581c030069400490f50302e101e00e1865403610f1441e03086900640382c80c072020081000504100304465115102446090300841c011480c803010301e04850b050720700d41000300e24460b0400d81881000c0160ba100021100240c1d4001d007130007a04c074035881c202125680503040c0341214041140d242503052540110042101000a9985400c41d51381c0c0f0301410354650007070350019180c0d800d6029800100e5564140e000c51142a111481e11555841401d07a20b000c0d240d40250036000050b03001004a45003d118001c042d1032440083c3e414001104000d081d01903190440c580030303000da81816030441d902c0303084040240c915803491400c68188584001e40c4000c0904003294280c01010001c14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 59105309 1250 59104059 59104061
    0x207050109060816050d09050a0b090a0506040b071112180405010308121503030a03051e091203060409080c010f0608030408070b09040605040504080d140c040521061008010f 76
    0x140e0b411601c0c0c0b100d5549842c4125081440380303081308410000d0500035080b0810580c042c80307800c6405000207155069843c1400b05901e034001c0c1409895a001d4007207080055004103041e41d1054002511070f01e1130340c503040c00341d4142c0417180e5000518024082d041c242a00580d01400e00000003030160202d00b81800203010172074000b0300021709450030903c642400b5000b4803c1c0c6503400644000d401810b21610302c0031900d5a0030010b40308001c2070b114020800c14005104110303002c4168600d8201c403a003030000816803214840da04000c00410000000703455520b442d00805992a80410470300e0740d5505100701c141c001c1a90440c0252458105500050341400020030384069410320800381a41e5403801d805220395500c0f01e1003064101da00c030440010f060350b451089621981c0100520f55a404003600940103c0740d143d9080041154944240a5040465800d803015110255082449c0d034443c0700c1c0111807100300d150b20807c0c82c410201002807030310204081da41100c0000000f0320130b0702030010000b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 59106559 1250 59105309 59105327
    0x903030801090c0c12270501080a0507090e100b0a030f0c0e150d090204060e072d0806030a05070603020a030b060f0d0902061204030818160504020c12160302070501 72
    0x40004c0c520206280403a03844114042c007140705050070350040c0031b0000d400141103c2c0d4844400c9401211108001e21358100843c7d90b4021b8031003030300300018500104041c1809140e401960440040c0d40c002824200342c0b90010b50150214002c001d0711440084070081c098183e0b10031821180f8141018044c2050040e000c0c4110000300070482c905020109083c66003640104044100290311a01084050384030340c80b4500c06448a4507002c1406d02e001074001d840071141c0e40420103a180681d114040d00027100200d4115091640f9104285465250000b4540f089549000d8000d014221001405581650081c0845c00b000c1d101407040e482c02104201c064044c202030308001103001c00c50400c0d22220303179005000300340c4000d00840c2440641508150242070444046003c07426020511a003001403c028418982c150001400360300b0200f010340c855800b480c41010300a9070040780f00d801a0b038041c8014034480c08036400e0580c0b92072120450000c9003541d0041900540904540440c055214002131 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 59107809 1250 59106559 59106581
    0xe04150c0e010f03020c0102091207091103090c06180301050f01051f020c06070f1703100e04030512070e1203120f06031902030709020a1101110415081510090303080109 74
    0xf03c3c4003035030752006802035401500d80001c10756081184248680d80e03491440707503000010000340106824900500121000401e000480300800c2c41005106e01d40002d2050207960241c4605481d5080140034800c80440e000d003d41e815400c0030b0030442140b41c2c59145904031602194a0002500c00415401103d400d0002c0800103801101c07c101107420004000c3c40c01e10310130540040d45189a44404021911f03041c255500114004103100c0080a0740e80310402811059016403000c0c10203035009415071203410903a260540c640800201c080d03000c1c0c0030100707000102625411400c03032402800b5449070300a9041c0c111070242c01000c1030030202d40450041c442d64025000b0141c3c54080d5418694240184108a0b8540704030754011a50283d0790019003004061034803810808560030082500351101d05041000400051200308402e14204c0f1019022840a0a0641003621425800a0b651481290031030f004180c1c520501c0345154005009004c41e0f0090380e481c480c50340ca50f80d02e0001c0e1030254440e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 59109059 1250 59107809 59107817
    0x806060a02030d20040803190201060b0319110d0606120902240f1314011409010507060204030c0b090a0807030309051e030a060b01020c0103060e0a0908040e04150c0e01 74
    0x40410307008156020b50442c1c0000c0c20035000310031030322103094545d81c810b40080308207401c0460900901c00009000c400c02d1700b40d600090204909141d004480c50000402c40240c45074040100d003002441580600c510302e80480303060380c0c0d03802100b01c8900034040500c140d85c00640100c12008000754a4811070551a034014040c131543c1c02c00241e903e00d2850030071200c070b60003a000c025400d20380d007910300288048450b0750a80305400c2d00e0600038140581d03c281090b41404003040f0740746000582201101c44d400001d00744180c840480742010700007400356403c000c00d1808500c1012403070a0001000d4404901c08031401c124180c0c03201c2c1241d031102e000d8440200401c515040610107890000305203e65200c1e502840c060014103400028600100030070141c40d05075594480f1041940d0601c140241d00c0000e0a06004d41781c030740540306006810080c6140c1c0c01595031480801042800c0301120000d090400c500f90b9070b42001d00b02000440b0350344002e201264540892800900d000d0800301e40d03002d034144c42d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 59110309 1250 59109059 59109067
    0x1e0603010603020714070f0e0f040c0513020409050a150807030c0b03040305121302012c060c03070203030301090e1b090f0901060f0303020703110103060b27041b0806060a0203 77
    0x7200750042e4000c503d048440810f10740d4a506460010010b0000500340350302c24504151400044582504c4094032480201505000b08008070b225250000100d4500342c85048a007140b08078102c000340280c2e00040c0e03134503040c0010300c6012107280d0001800c103002c0401003003030700c0c1c3d0700c0540b1507540c0350300c3c07000900406e134040041207011118409103501034024100146005018400c403200542d0071030f40341110084201030f00040d540e105d20740d030f074041000369601d0340031080d02e01110080c0707525006034034443c5500040c0005501c40610680e48940c1d405401c590710707961110006000f4181211340030200740b2601d10014070801e10f41c2000360401c0e2019008429a46940301c04800444004021200300c0d901c4050020b060202c0d4918107000f14000da0290040e5030961420b81200c14103000ea2504160030860240206001d51007180c114040000380ca03a01c0040701b04d400070310000e800700b403a58001e144c042c20f40c031003400d500c218000800459841c030b83c01d903884a00300078640c000c001c544001640240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 59111559 1250 59110309 59110319
    0x10b12060a0c14030903071502040620010908031008010c030504080906070203160b1209060709063006031110231207090501021608060712020c100b1e060301 69
    0x140c080c010b00741552400320040307410122000c0a9900540c0c2c0620f0940c00040c800c800c0c0b08400322058188400564150720341407804100500000d07107112404120402802800070020302542701d615140c3c1d22a510545034501546140320944092062801035400c02c0d40c00b07602c8034032038451070f03201c3e42d0704c0340200707061103400818811290800241260544180050000c02c20780ca05e10820040031100025562a800d01401c400d504d10050958561075014000f400090f54002c904201580c040d4a81070291411080301d004000d1140071002414210701d4124250b40b080a820076016a8024481c0b86131101c40d0f07600307114030000d05000f40300015140120708611ba4413100c03180d100c50b004900c1500e052083d022046240600203a80c254041030750202c0801107540c06202cac0d007550040b075500d10404580b500f600540c46040c0205881c007040039084285014018135810344200c8100d0908032890121310454103001000a200d0161154801c0040b10700200c404910110182c5006015142540d10f00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 59112809 1250 59111559 59111561
    0xc030b090105101203050903010e011e110f0c0a0606030f0212160312020708070902040f0503120f030709170f06061c0f0204060314010203010f12030c020f0a050409050f010b12060a 79
    0x44c1e10101c00708102000702040c0d0740d03024004c0d03660040721140009104007240042045185101340c240038024149081200c034000000261020110a4610940e071003401e500d800d810858645070007070100d0310b017100c0402482440c40981c140f8138404d852a090704c201c9504401c0d9100540001c049001c040d041044c40022501c550500c00c050890044610490725000f03e0390400d89542c00000c42d00398081b40030002c410f04124140000c0c21b082d1702520030400c1c128050115441480e400c1e582d030044c00030101d90168820741d5003600602521a004400d40302582600d900c032040045120441e02c640e1001c40c2c280e25003000795512103144080540044042680d881102028020041e43e000c1c0d41d900002000c90b001160800140110800050ba40d45c10a02d0f09542007100e5048010200c0c2540c0592000a4002c10102850f40e01190100200f44413000002d14014803a0082da400c2414840344000300a1300086004000c18130100034000c1c44012000d1004c0b080b00c0e104032a00d0765100d90302180f40c5c0025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 59114059 1250 59112809 59112839
    0xf0901050709261f0e0c010f02030a030b1c1a060f0d0311030d0501120c0609050a052e03090b010e0601020a03080901090215030f40050a0c030b09010510 67
    0x580c01034849000c601003810482d004111508503132261902c0400900b01000e001070488a00b003420000b00c2c0381c5825500954030b0280550b140141540c41003481000d0b62105501f0015050075804108580ea1906e0202e14a0581d84240000d510b07100003c0f030071614092655a038480d40c080d0100321004811746040740c0e02500710004004501042142950b80842c9004590282803551001a030b40c003e04d240841c0c4400603030303102104101c603008040c040c6550b4400c100088890440f5445512041c000351014400300c01020703503804941403021f010845401d50040548a8050000710505030b9845803e0407010344219103160042c2c202505410000b4082c0d80d07003d030006910400040c9805260b40407800c9a06214102400700001200700a000485140c1a40c1d010100c5100d800743c40b4420010840c2540804407401ea10500c00180300341c021141400002d00103402900f25410341100341031100340005240010340d04071130a0000101815414050300d40a1220040420705003031034581081207400f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 59115309 1250 59114059 59114129
    0xf010c021309140601060504060504152601150207050306131a01030c0e0a0902100e031002040f03061805030304060902060c0d02011409010b0612100305060f0901050709 74
    0x2220000e2041d00e00308a00c203a04110784a4034180002540940c0428907206050b0300100c20090100800e006040c0e01805450486440444c0c1251010f2101c0c010f460304a07001c100310251010415900020031003410706241201d000c240480709040340540120385600c110301076950183c0c042c0020a0140d64000f0340414040c1c010300e0f40b031914100302e0008a061503800ea10548144030000410701c006c000c003150490300880600c800700400d40c01580482d21038280702c8464010302c882c403072042d40d098174140607000140328164000c40d543c545880c801d003500718180c082650910b1038041002c030144006a0140c20054101d8019410340d40d4a0780c4070b00c05000d1004049820403428441044180010444005001101d1700040b45803904082402d0305504010049002071f0b040c4406150240c0b1aa0100c03031020514a111910707583d00d524408103201c00b260b03c010910710450701000380005000030400c0c014a4000001d01082d01c42c035804030740791420713030068801f202c8440300aa58030030190040818128 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 59116559 1250 59115309 59115319
    0xb090d111507030201060f120f030e0406270203070504140d0f110108070e2808030c0307030906080402090703020c0109050303090a05160e0f040c05060f0904050f060f010c02 76
    0x103020041540c0780401040e45400150104058003059020b00408000c0c0c9034a25406d0302d00f900d0481d03110314504841d0b00c00f030040d844071003808003494407482a01480b904090700078020b065640c00207200e405003c20141ca4040c207145640031010059008590242c61507035102801c0c2403d00385060070300320b0005a000c0c1c0c8a49101c45410000b2204003100c42906e0165040d190054526030014080c684010600c8003002144801c0445690750034202204c146203426500c1d0080480000d41020b00c0c00a41100400780300104041c40392170301c0040100a0b003442555540310042e0f40f260b082c0d401c9882610000d5001c4454000910420b100340d01401c00c281c42540082000c840301e844403130170759000740e850100d40d4111544040900038100300c250320720414100d4840001b454500c04440302c030401740c0f550150010160103c1e040c040c44c2400080a400f00078181582e0b40c0c0c0103440c102140e03100742c07885c0d0700803414080010101c00013811031034440c0364040c150004440c5100011513040c001070000f2a408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 59117809 1250 59116559 59116583
    0xc0303190905011404060f1b0c020409020901081608010606020d0302030406180c0f05011e0c02060c010507030209040b120a03080c0408060c04050301110403170d1d1006050a0b090d 79
    0x2c21401d018001124120000440319401c00c0d0800c85e0a0300c9441c20010700141c108031805080e82608405c038580e543c400d1800b00901d1400d07200041c054030003968040d41c0801c4c00800403800813004542c240030782040403000500c481c0d854030a1402e803103241c1301d8000540c10200c00e00860f24080d800559200f44210000140d180141158069100201e001651002d075186c000384052540d40c0c614801411090074110600885103103444040344514003460b0801070005118002c645440e0251010945040001d10692810540050082d0072041c9401d02ca5800c1c940d60003690708100f0480c0e41040c5004001e40023034030340e0381c5059908030b6020301401640ba00400000402000074440d9600450655400b10380e550300d06003c00d420366400420301c1d0620001000300700b00013450003c12505150031000c8298076050002440703802080d00e025807858200052048039121103022405416280800404200c0c16844605110b817551046c0240500ca6038208450380580c6083c10010003079521640d000b00708 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 59119059 1250 59117809 59117813
    0x40b04170c01060f0902090f0f01020f0607050304020f060702131e060902040f090506030d0309031806020a0b07020f0c010c020406030503070b1801020304020108190609061e0b0c03031909 82
    0x241c1c010002410903035540c1e142449860070030090305000b44403c0360154140701a010004200c0c000b8840301c507100e207010b40300803001640244280440106d2040660b082d42c81c0c84032001d4040e071700407941244900f034110789261840c54104247c5001c07580160032910314151500540c4002e000305c040380785000c201485415800a00d03401458060400fa04015032902c2c5845005440c40c00326421a0031007500300010040503490000d02c02a07904180e20f008941e92074913050690f4401d1607200c104920010b03c01000c500540c0008200d1502c1344254040c1e00203540d2160202e0310303559009100607194116201e0940039610600d00082c04a000a0000901f140c0d81d40e500791660b0b1118104039036060b00c0c0e400f0044101800c915000d000c50024000350314510302680000c0c400340d8001c0120480800800340410214415030091002c1c3c141f44c01c0401c51075880d14404241004800700c040c0b1b041e100f011002c100b0140400c16500d420116a005504607190706e10116008034401044907002c6076074002d5000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 59120309 1250 59119059 59119103
    0x2030c0901080a060e0604110108070504030606031101020c010804050d0c0503130806011e030b0f040602070210090513020415050c0f0102190905120607180306110322050303040b04 79
    0x4001c002c2440100660045880c00c038041e680760b400a182c00d81c20007801c0001180030803910280c010024a400c2c0c0c0c1607600ca0405540500031500b000d800744c2c4c60900007004110492030718030384440c001d070200d4080e07030410401151130740000c4400400170f4115101c41c5202602540550f04505c3c49801a40e08000148600001c9032810b41e02030130081d40950010040040681d401034100c040b15101c801a0b142151140c5800d4000070b401da045044020002500b8440140d06580341d0a5008100c1d07a020307810550000c0000c0d44ca070040500c158142c09071b2070f080da09030b40300321000c03214800b840303403a072105418056815800160344071307034180204000201c1010080c8001c0c203400d50200a00d5034040740b000d100810009150700518012a121600d9036140c10340002c1142d0b009a80b460034881c0d0300344800000480c0400d540c0010b1500e8140303000d9036881100140510701c19100015100001c600700000051010b81c4400054616041040030034040b802d040c6180303620600030800c10551840d9410041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 59121559 1250 59120309 59120311
    0x303030a020a0809120a0e15160303290f1c030207030312061811090604060e09060301050c0d0b04020403021f08010e0c0f0c070506070305030109050105010903030c080702030c09 78
    0x140d84903030001d05111810380006a0680142e50f501c002c10b095415028002401c1c8111203400c8203000411007a1692a940c001034003103070010841c44580c440003d50186d0710718000300d07071044020904041d81421032407075404249044200102141000d10800014446001c04201c400c54111101c441c41d490044502e030099a22944264000e064152850900a04540c1280384000c246410a441001003004030101d01001400d083c80009000128070f90408035840f4088055800007000700d4005007150f0809010324030381e10242c80b9004155142010035080b0b071000c03540052040028072004820103c2c650121a59450150005140c20703240e40008414030150403082d82c80b40503162041949960100c030803401450ba81002c5140d5051011702000340d0b010b240e0003007942e030b00d0219403203a91000c100188401080c010701016611012410f0060440e8000d0003035080d580d0416000161b0b651180c1703049400c03242c160361250050021a40c908107107512541d0280c0e0300d071040e0b10350f41060355940d040303007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 59122809 1250 59121559 59121571
    0x702040204031a0105060306010504140a05040507030b040f0902010207031b090204033e06090a030606060305010302030d0809060c030a0b210d1e050a090e040501020912010902010e040e030702030303 87
    0x1100214180d068100f008541600710381e004540030b02c24400103980242c2682c091b610350340d502260314a81d04005c50030250306540102c0d44941031205015041e5050360091f17020300003d940510100135a001c6100c03ea4008240007401680001400c0010401d42c0d840300328186d4210000c1c12003240c5c3c85400384141e030441e4005460801450319148a035031007480c3c0a01d4520314660003e000010702c6c0c680601242e90a8009501554000070080816607401d0292400b842c3c0c040010000c03203865180080040c1000d000403402845881d401e49541d40c0969191445131003100014202950343c012000c00b250000b900e130b8085652940d14141046d070300c445844060480411001070304403401c0074105c2c500010015048240300c0d03885d8003259111005048008000c9490a0050381d400789130300200c4400300154070410b255a0040b080c00100841034000381651003040328129650ba180c1440b040c01c80d00d00040c000d02040310306408540038100341e08840211000303001a2030400342150042410365004540c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 59124059 1250 59122809 59122823
    0x6030f0114060103050708040f06020903010e060406090b010506070b060f0d02100201050402010917030403081617040306050a020306091329061c20041d011d010507020a0b0606070204020403 83
    0xb00806940d041c800d2a9129415190545d45030901b526180c152004c4002d003d00300c80d030000b440d03500320344007500850038010b806802c582c624501400e2000c010700001e00b08540b100d9080c0c0c0009403600d09803054602440d0848519012525407000700712030300c510003003400e400c04e1020000c01e015a84034418803601d25800d07000400c03140340501c001803030240c0e690040d00c10054071030391680e8442800001d44094039400f5102c241d13101c80c450030383c12610300107c40041c084803183e4041c0c100c850704400540100c4e1320515007803219496007410b000c01c0c0d0000302c4405400002d0b081c00191051800312038003203028003441084407030f2007501141001084000101303c2d20b49030000c0c140207043c24100990100580760314160201c032115965a0141c0c1c401225400940c1c040601749084969113584c0000541001684400d000d10040784806001c1c0c0801403111480c404c1002c0c81440100c0c6c180070701442441e942c0e0281c112426540d0303810701720071009021650880003c0c0300c810010b8490303100030400b841c01011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 59125309 1250 59124059 59124061
    0x405030a08250e0f040c05120702070510230c0304030c0e040c030f0c0537060f030e0102040506030106091505070816020f15030603010605240306030f0114 68
    0x280030340400d10152004800c0d04448102c8480c036038204101d02032000c410716143c0710b41259400014030303040c60915400e03400361808030300707290380c0360080010000c0c545000b01c501da15542d40207040e030301c5a040c0c3c4982c80e044403240d0007070300e801c1d8800c0524802003442c40c00c00c2d440c10074051034040d800d038108840200599000050a00601c02140107800040c01c5510300c80c42103142664a03c000701c0703841d201c01000105442c16040820403061004406003c014101e80307070400305c11941a05200b450401c130840b01011020340c240318161500c40809613003885c0c9459144c0d5800720300490041000702001d44e1255403e0001041d40e030740b543c0045000b40000d903a543c44450070005001c2ca181c1484001105003c0104203031400148800c0c2036a0708446100b8a000355100349001141c090301d803c0b44080e030b10142d82c0d80880201c4a0410142d4010703241580200280703a1114140311041400e220080309045403042043d081d828800015a40100040c003035440440015800d5400e540724814810080e000c004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 59126559 1250 59125309 59125327
    0x1101050c15070e0d15092d021804030206010b09010c0c0f080d020d08070e0f06070b040b010504090201080a090c12050f010b09011d040501020405120703050c040e03030703150e040503 80
    0x41c02c050014811185001520001e96132603410070b5403240c00014854807800098107220000700000d14a425261f5a03240341c4048421038046610034140403881020351840721a240c814011003144107650540040c420703a401d009102a50f5041800007504100e0b8112051000841100d881001404413180c48138400d824207040a04142064410204541c001001c0d01070155100460a4215255092100000074a1004100805040308407590014030000b402c500300300ea19211184500d001d42e2178483d084e601c40c0104800d42e00c4803103010340001c0744c400200d11600c240d540031021040c85604486040380e03507000b80000c5940818030031356490300002003128044100303009100314071404a88854403503041c02c03050002c1080104644540400150000342085000d5044401a0500801200039200c64101d8180c0c0d070142d50108441c5800b0b4807100801a040c24050f4584081c00640590b0840d07590420440040c807401d9452003810b0010000081c1054540c4e0f0a0f0b401107020708040c581d10b074160 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 59127809 1250 59126559 59126567
    0x3090105060316030b04030207090c0e120c0109032411070308060f0901090203091011040f0504050c040b03040c090f0e0f0703051209030a060f0e06011a071101050c1507 74
    0x248042c2c0681c114507840c0c02c901e42c0c1c0c1c8081605580d0f2045482265031500e080803460020283c105171011340c584402e40e0b4909070001980030744514201d071220600450141c885841d0720595080b00e02003105848103200241e44690081c0804405a100d50280c0000d00b0909050380d80c065450104042c00044603001d055018422552014050303a07200c3e072070203512003c40c0c0d0b20f5205121b008401a40030001c641c08900a0201c2c01407140c50302018403200389000d6074400c49034014841c01c08030380c4980c0000115410a800340078400c040f14501e003410300e45401d05074400c40c1c1c0300810031070b05696400780c046501080342c8144a000c08040000141d0080480c80036441c2c0045403500d224160f208000402c0041d4000420100703105581205640724a00c200100389404010350000b09102c0c100b280802c1c0440c902d80c0b01d0a242c000d440200c1d00240d0380d4005403d1000c403c0d86206000728403c20035500800c07002c1c100c0000b40003040c504070b0310380044010b4050034904100c3c00504400c074560301b4090400e82c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 59129059 1250 59127809 59127811
    0xc1701030b180304060210020a020a0b010b0405010908070506030109020a02030c060a050a1a03060402100201061809030f050c0a08090f061308070503010b130e0c09040b0108100902030a0303050c040f060503090105 93
    0xb20700003103203000d040c0900a0360760788065001001c0c0c50740000760724060074420300c9400041944510030a109503168101c0e001260418007030310340040da0081d00050083c2000500c078044481c050244ca00d16400e20088001a40c0203400002c2544000c000b40d100444042084500c0382c95450400100e9003007041c8030106440044818607844411010038107a641e50200c0c000f43c10070340c1150911240c1048681c181c1c090965a03201d0680022407070000c4000c0b188503041001950311035515a07010452444040c1c1d000e00400f08014136940c425900300c00060f085200802071100300a140030050041100094190381c0440c3d441002680c52503805c1200b508100042c02c007426040b002440f5a0300d0610108981c5c1200382c2c40c486c1001e8940407150305421050040301c840003409000c1c11120b140c9402c040e0038a0340c0a1040c0c401c80d210f1314001807000316a0340b2a4008a0f0b80c010040c01604519441c2140a41000b80c283e0180b1442000005182d000c503145600007442c191300c4e443c0d140d1425000150171510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 59130309 1250 59129059 59129101
    0x13060b0408031e07050c0f0a0b040305060414060c0712120612111e1509043305060403111f030c080604050c0702060304060906050403200f03030a0c1701030b 69
    0x310074041c07803000070345c042980400304a00b1b880e0400d0710b00300c3c0d07000201a02a503900500d14400d00003804000d000300802c040d84204c0c0a10602e0854003c40c0070a144e840d18100c5550340e41507028491007001a0b862000048024a146444c4120070004408503040361026441007044d01074100040041100007115000c81d0b040803180000d642da0a24401070080d140004c40714440d001010803910900c0c18001514180503001d8420801681419103864907220202034114419115988050301c6412901024099520251156081c00c0c519a07990042010703210540e64845901503d00845801800d100c003260b0b076250b5000700c3d5014000c00043c01c03e01004e414180034905280400c50015100001c84004681c1a90055a04d44c1d850525400518440c14020f0543d0f0500c01400141070703025400aa100403400340f041101000b100c55960348009518203201580c00520000342c1c104c02541c00108001040d0600304903101d588040c070a151042600b0850340380741d01d8014000ca2003105008a40041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 59131559 1250 59130309 59130367
    0x3130f11090112051b03060c0d060306020f0702130504030c121704120908060114240708130b12040209090708070b03070207170303010323060a0c11030403020108010513060b040803 79
    0x110225006c680c442d1401009110011000100b01c0240e0f078265000c0001140c00080464a030046801e850301d03168030220f4140c0c4100090403200d01e000001d8420940200c2d45500c528005800c0780d550744a990b14500c000c1c40503c011482690428000c1c0d41100381b00d0361040d580308042c480b030b442001c1e12000c619040520581c0c840001031003d10070a18060300d404d00102c1c0d035405201d2100710341c2c0c41d1070079400040421401c004104102000b1101028040d040000281400c180b520340c1c003400740c1d500078446110a140b40140200700942003d1143d071380c00103110000c0c2c41001e0784465100386030280b01d45c4940390940300041004503290b41440040080c0c440c4800c7c1140344183c5005503580c0340010300014100090102e0484442c07114103224541d144400c600b540c20a1400e41144d400500c0b45600f03c10124520000c01244114007004860a03658161a0b50f812642484c09020701e014440700001d4500da03454001043e00d0846001034030060202c0030043d9039400c03003103000180d6a00c80d1603800c9011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 59132809 1250 59131559 59131603
    0x20d11010e12030c0f040f0e15090609041104021804050711030a0509040605220c031b14070614010305150f0a0207020a0f0f030b0c03130f1109011205 66
    0x3070004100340944035141c0a24a0700d90300c070024442094415001004040f110000b0006100046410610308480842083c010b09581d6945130500b42c550801d01640d1105104001404a01c0c00240f070b56045401481c15515403080100410226400109021204900041d0300304071840d150103050340c001300c079190443c11205221403a80c0d0702d0082c00000300c20711002050b42200c1d0380f640c3e88040c00503c07006004002119211180b050b0807105499880141c500f866400c1040358003902072940202c03402401c10b615040501c41c1140c64481140c0d2100e07905504000e00c0b0301107100d50240c0152001034004d210010351662404503c0d20b080c03c56040320982c0080100b10b01001803181d5658004186c65015950342681c0c4009541c85d002904400c101180382000420030074881070292003608e2044d00444155203420381c6c5030b6000c0c00101c0d80040030040c5015110001031000701420f80142c4140d03803015111000c4800964581426045250300308400041c10342170100070850f00b106070306011050719034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 59134059 1250 59132809 59132831
    0x3060a02040501020a08180a0902070519080904020f070605180d021f09150501030c151b06021b0f030a080c0c06040b060d1a0402040c0503101e0e07020d1101 69
    0x540c45c01202c003400800c80818443c0d01130201840c041c0c2c0016000b00b0629445d0380b54080503009401000c0140c4251284c104243e02904060f0442c0c4651504280944d050405c001c040001941c42a0200c0c0e406e4101071201c14000350550281d54010300381103603c2000f00140c0f02c0c4480c83c104000c200d41045500c503244040e80c0c14903a02c81042040484540400c1c03035449400d00c0c940d03000c05030301480c032020315081c0000244000f810140094a036901c801e150004082c400c119410860600e502004e03220310303450500020403503801401030440c10a03c2055001d00921303581d040035000d0503000b409400000e400e201c05503000d4007495004400d07081c0e060030030700340c0c0c840e0750395440340240024070f6404800089569640c7c0d6688060140b80d00038015000080449043c024184050b00c1c2280102e041000c01c1380441d00440c00d8038890100340c404030070001d00e4041000210144025075800c00341c2d0509010808441328400c107449120142c000744055440c06100078440c00c2240d00701c6185915000719940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 59135309 1250 59134059 59134063
    0x30705040312051b070503010e0a030207140f0607080405040b0901080d0804080903030a0e120303011505070320060f06040506010509010c1e03020601061403130201030903110601060e03060a0204050102 88
    0x2040d680c00801d1180d031400300c6030b0191024841d03101000310300d00307108612a40080000501c1400d513001600288820b041030a01a1f0f91000c6001000f805604110f10a010031408001e60203040e580040101d619980c1d0840403840300d900c502c04c1034808a900142c14082030400340034494001d00191a126155031404000c56151b402d60807494080005c508042402d2000b00f40680d00c1200008060369961307190944d0107003100c009504813a00481069580524400000c02500c0c102e8444801c00c4000c0d036844042241c803a445001c0450038001000c5084c052464131071a0000c050054000800b464189603c101e020240001d11140c4240c0c1030400f00195030b60300c0300580e40d0813003082c00c190305480050325180b50b60308400e01c110003811502115903400e140e8006000d5048500329100c0f08000c822041610825220855652542601803114500154400c0c1d0140c3d4150b4002d00e02182da940380102e82c9070914400b81d01c2040012802d40304001c4501d02406015000400f14504600d414070f0100003039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 59136559 1250 59135309 59135317
    0x7020d052b1106060f090a1508070801060909030512180a080d05160519110a060516020316031b060e033a0b030a1e0309090e060406050a0f09060b0114030705 69
    0x40c0a01040710200f541940150400d15030300307580055100406d030b02c2700005656074000b0301c5002d1040d0300740304000440d0340c854414a01d001350140d4400b460074191042081100a002c3c0c08803211100c07126001d4440c2c0000d000154626105042c9240d45a20b420720407000e441024025582c0000d00c0102c0801d256008000c40d0340386c18130710750380303c50340303401410103541302c0c100602082624000d0800202c10840240d00c0903220b51201c0642c48043c50340084100d070740c0c0c000c40c03440d10790091140c2e0040380460f001c1c4174446002203151f11300c003a80111507600c00007030311103584d003200c000d40c00481d0808452160740100c01c017415002c10fa040071041445803500c141c0070480b1040c0b0199540740c222403415182889480801904040b00301907030316880000308604840a1001da00003401444049034541c5140140a101c6e80c002000717181944581c0c5800740240b41c0070b003458160f5680c0e0401180c03015500c1c0940e207000d6029a500144c42000078002405601005140403c2c6420402c10042c0303440c0c100b8151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 59137809 1250 59136559 59136589
    0x60e0a020a15021e0703050a060e010c0504030c03110609060706090b01052d030109050604080406080f04021f032007120503010e040305070501060b040311030d0e0607020d052b110606 80
    0x10046084d0110130103410021150000f503c1401088001000d000300307030300a46103400302c40008200200c0e03c0e50042310603000d2404010496007075001c0400110340c0240240f008040010034140ca000e1a42c2c1c0041c00319400540c080311541d0b11035800c2010f1280034130b00a4010a81505c29200d0310101d806410f18080140740c4089001030104106101c9490075070149483ea40e1190444044c0c0c00d05050407901504244201000034104000003030422020891203070080b54042e081182141c2d50b00540c0c03100c0c10001980c001016074036034912058020700c64140c0f0182c80d00380607055562075a810010104c40503c0c0210080c00340400041207078004420106a21540500d41740382c0310b40107480d001e4003414180d442001c540b0000f08010040c000b0880c00c40480c603500300c080710162000b500c030913505052400f6045505c640f0a002080150a00816110f0007031310880035990b51129041c0c0c1104c00141d05203030f25035050b4402d0301820b107050b0007030750501c202402c01c0000c1c10716240c41c400199000030340300e0760 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 59139059 1250 59137809 59137843
    0x1080c090a03060908070609050313050a0608010306020a0c0803101805090d0c05070e151305150d060b03060103030302090319022d13020a18030f0803040c03060e0a020a1502 76
    0x321014031500c84146e6011a0388050148030300310a9081c059541d410002c40c1c0a8004884080096246080400ca0b41101d9407611001110381c0b81d030300e42c00001c3d00300074940010702c0400070145c0300182d00440250711079a005801c40607610b0401108080801c481a26455061b2030503040c41030030480042c050121208a2500c150783c40403030700e421410214241c1c889404c0342c268500f031000701ca0b2031023001000403038162807000700103031001440419a64159100c445001c1c42e20b00301181c50400f21056202d41c0d01031640841c2d64065074010038030381b450982c01580007aa0100b8941c0b0345240038440403944685001c882e607070440c00c0f40c00054070354107203041240445589044d0691282130402034011018801841c03c00189a01155a00a9403101c5100400100081c9201c2c1c803070300010306800d06880c1c01030810442000159205441544003400a0b42d095400340341c00800541540600b004040d4a0300107002410b07268030502a4040150b00105990103000070075003c16a4000707000d817904442d01803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 59140309 1250 59139059 59139071
    0x3020f090d0512032401030218060904060806040f020f032803120510060801060f080a1512081e09010c02130e030d0501080d05040b07030e062701080c090a0306 70
    0x281551400f82024903002507450003100f04107600c0105c00368140d10b60405e8000c0880404014011800c80c03040c03054031405c44980782503010b403500b401e9018011900e400707080003901940b0b4001140c6401401c840803110302030681c00103811820014090149084c05030010f00781000f00f40a8020000b040c0c000400308844610401014548140454903e181e8280020403080c24801c3c07000c084030b403550003958081030450000203070842c400d01590048184998030000301d6110400d000000c2c01e03103403500c044060320030b001c045807609454a6400386103101d018107a54583c074100c4404a00384000c1c5c030301c080000c018010001141d812143e131003803440d8100c401c2c480c000040c0c01490014444224040140c4c40042045112180d440e40600d050300d018104403403518003144021140c13407086000345003800005010120009000b49507509100c0802411103040c840d140820301c0d03000725884c80c0280c00d848103100a052a507009500d190300b02240001c15071030416014040744c1c0d0351000b03101c000c04080d5960 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 59141559 1250 59140309 59140313
    0x1018080406120b040606030c020c0102030a020d0503100305010e0304141f0c17041805060d080f1e0304121128020402070b0a1401060e011709010209041103090d03020f090d 75
    0xd840380f410301c0401401000860f03110301009005241480440b005032040c8800c00095600010640c1c500541a138028269401c45900c01c41c1c80781c001806264101580c3d00c004030014101303004003101700c501c0c0300003503403210b18044104006141c0105070301d00460702c0310b01c0f155481c445214050203104240c280070030340903998580301100c10008401c000803000003140108203620a58140500b9006882c420303c4585c541c601085801e0f8034207003001341064400c1101036542501ca40c05000307060031205816079a00c0c80e0641c0c4c1030f07003a40304940c1250301001e8915120f00340394004d1002c06e10711314104003c0080700c5200d22146103181c40345840150b1804609031020455a03a60100c4040030f5002d540b04090f400c150b0121409481e40c0000410794100c4600041ba806e44520991850483d05954884829400066100f5072020281801071a07540812400740c00d81c8950048210805405520996900e00070600900708a00702060381c0405004201d018010111281030712112141101c612031040624 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 59142809 1250 59141559 59141561
    0x80a090317040b061503011d07090f080a020103060816030312230603010e030307050d050601091e0801060803040605041401030204050a0b030106030b0d0308070c1b0305101808040612 80
    0x61005080c0340c03000020002048060700000d8080c14058841d442122005c6101303800d00c1c00240599807480401880c40200d00f00c846d480070b43c0090300390a2030102c007512004000700c110b40c1600590000d50084890000710b580c140301d000c5c0100b01060162221320340303550b481d410020302c0388005403c00900b40c6200d00e84511076070041d203910607140c08084400842504440001c00200e4849119519020750405001c401000302d0303200d000b2a558082ca0310b08040781040c01024090409810825052070100c0c140c0c14034400040e841e039175003d0170200310307250138045401e5640c00d401c000c402d50000e210802c0710310341080070360b02510708664036006c440c0b0540004a00034003950b44090f40c4031503001400580f00b1140c40c002c0d030586501c1e59041c0003075610030003070201c3c2c03d01d496001400503040d10002200d451040d00110784552040c00021488403880041c030610900a810964141c3c00c810070207403103100c03588651001c0c4100010704101d00003458445011501840c402c0005000e109550347e202e064007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 59144059 1250 59142809 59142827
    0xa09110114040807080f010c030203070824040603030302180109050609060d0e061303020c150906030702010603050318010e0f01021c03060308041409060103060f050d0f061d1002030403080a0903 85
    0x200c200700d1340c0682d5503608060340e40c44284a4281603518120411028078440d0007104c1c4a03001e0340e21001c4045e200c143c60340d9001000c2c110700e410b0001c10f038406280e1503500d0f4040c540085001c1d035000350325003040e07010001403846e40c00c003018148190040201f280341c686906941445e8003c66010303071a502c0c0c4409003000f41086420f17903070190182d80100680107154444542190b4081c1e400c540036a801d1100b80040450030ba0141040c001c4140308000a40c600340005541c440030602c0081111590b0b035031200c1c0b035a00080c50083c4a0069050240040d507130090740c0c66050030045a001c000c0c14103881c00030351500d264034000c001e01c1d284001510b000b80d000c0c2d0095070046038003510b1941c0d1282d1f207004034040d81a0040d025445204545e020403150b6100b17018020070303500081241901d092030801001510154640700300d51080d18488100301144070703881a401d00d0781c4007d2620030f120104850160901e000781d038005c02228810b1041c0300100e54810f0003207074801ca000d00006050b880f1401c0544004213 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 59145309 1250 59144059 59144069
    0x2090609030105040309031a0c090d03030f060e061215060409031806020304030b0603010506030c0103050a060e0108030901110d080a0533010801080a0803060d02040605090405030705060a0911011404 87
    0x8280f60511003056400341481080720301400b04500819110a102e0103a10801c0c1d03900c1c1903070441800051080e2429001e88031410b0b210313060004200c030341d0103e44030a8400551003e50145141c3c410441c090070010200541c0540c41005070849014400201d80840300140169020744d13a650f058204140c01101c0d8152a500d1541c004010b084c8d6500c002076595100780000c903042c0c41c1a03004902a402d05014a9010349001009800602d10034401140107010090a044070561200300000d1204c50b400490760103071490102440d528060040054401c16003c417050400754003040030003030a00d5001440e540c11001104c408240c1d902e0301c2005000040d85e044032a11034060001034840034450346658941c20800c01c2c1c0b103514160b80e030b9101c3d1a4503200610b03000741400b8020800170740c46281c40c0b190b00700071038070003040000c5061f11000454080d150486040b2030a50001800e4000d04c00700300220b5030320842680d421711841e5803035a2a805500c0109120340e0503c11951508610180d040341a0b0380944 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 59146559 1250 59145309 59145311
    0x70807170a03060f150c062d06060c0c0b090103140c0903060108030a020703060509070b2b0b0a060804151a010e0904110607170f030f1501080a020906090301 69
    0x1a804100c4000241d20080c0000046403500c440001c1c442c040f0000001240c3c00c4d140d0420291a005c40309540100c1c05c00000c5424030384d14000301c6102d28850300c003040c204602c0b40e00300440c8005a06001c04940c06c0d03421202c240880441054000360201144200740c0b00c0c054901a241c200c10801600540503000f04020a80c00100800c04403050042c0039010b80ba03030442c1224216603881c901d0640700d03c034904107040141c010001c00e00105a81303400854002c0389840032a402aa034900110005420841c015404071211102403403001d880e80e8114000d00e0302d0701070100a418194000140d03581d909210b000103111910700081c0600c4080000c552200700303040018051042e400d40c0c0c10460054241001c1e0100341c1c940700d000e03141e04082d0403592243c0d50005070400b415000030100a0180c010042c101c4502e01200114401000a50f021b082110310103983c031601c1c2d040c501490900c510700182443c0b10342000f1481038407a0381e404012240c010074440c500681d40c1011001081c00c0c0c2c402c02001035015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 59147809 1250 59146559 59146583
    0x10906020a050c1c020606011b0c0308030108070e090a0f02180406050a1a03060109090f17040f0902090a15050d020c0d020f03040303351014030703080f070807 70
    0x750007200401e44090510203071035a40c0c0c03242c03080c0c4100c504001071030401688003c002032a107502903036685886071164400b03c401414250b580e0b850380360b0ac0750411900003001100400424104000d084040c0c03002d40802c1030186041e4546a030380c0d80c0d540c180a068016070700002c2d0250f485064100080c0c09080844640d6460a0300f080006000d064807100c086910f80f0400000002222164000b1300e00003e010304185d0f4609035140020300a610700580301c0da840d0003108800218414112426a407020700d4040e20741e842c1410a1070032120340c3d03210441c20342c01080386680e40d07501c50a1070300580b0b07824031141c038800703480990440340e0b40030b28080343c043c0307500c00039054111807070014480701003041715800c40701c008404803501c645034090342c8001008200c0301c0051002d40003100b00c80c01d0180e181c0e24058803402e0700101405502c100259206d9048003000742050041220100060341041c41c16001010400d2956480c1140c1d4401c044507990a110045560410440040200d03482e072500a2803038001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 59149059 1250 59147809 59147827
    0x40c030f09060902121902040e0111070b0906060603160819020a09030b101d06030a0b0a09020108060105040f061805040203010e19090807080a1806090602160f03031101090602 77
    0x90120f16401c3e4400d001000294400c80d000140201c000d03658130f60940c0608119034280006481c103103040c143c4654a45a000c04070303980d404007a144840c0200060b13002c03410800301c03150900001030300060103900d0820070042c0c070240c80102961030748c0940c54030204695a031000d800f00800700b2004404010b0000800170381050b031203501103098900907245440c840c0c0f294165065290003070b2003115070344146402d82100c034041150714154030102c06816a501401076680e8034221000031640b4550840c2d07900510025035034002c408139413240c021300301a0301e02410521002284c14981c42a03404026051130001e040000c0d0344101401480050000e5481f9616540740701c0c0c404204a07043d00042c050314010501c1e440485c000d1811f03d50300010000e203404802c0d164021a640030359550014010a095901c52071b0403002e080c1030041145580d0044040c0c10268001d0500c4a4840c1c5007189822581003407003000c5201d040d0f0301c100d030341c94101000c2003618401d4890142c04c1c010340103400648041150b0007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 59150309 1250 59149059 59149061
    0x30a08031512061e060405071b1a010b03010312030507080a0b06040b1308060705070c050103020306040902030609010b040e030301051008100b04080105010317070c0315020c01051302030d080411040c030f0906 91
    0x35404640e86210605e03074901043c4407c5407401c0750800c0c0091000304101e4840d6440902c0704490b07030b020706d0f00302e800c0b055842001e5040500c00e0b0702c80400300c2c00000040043c0120b01d40061080a41441c0030701403401c1189000740703801000790980140c0c60b1b844040c00c8003603840c20100d500800d0100b4401c0d861300c03c00014091072001c107109042d484d0103100c000524a92061080b18103a5602a03010040c01e4107100044009410041401da0410b43e90711640001da0340800851384103400d14400800c0ea403074440b003880161041d42040d042d09500510061045075104c3c540c0300c0344418285081503240d6100e440351002c2c0c1d500d80d0b005a000040001d80402c1001041d04038905032409619039000c0880b13078100d0029541705210019091848401c01800040c0784065111040e50707003200090b0400d441c022256084581c00c2e244054600360f8000d007441182020301c40e80403e80064145203205140c035450720001f441184e40078074030969541551144841c080d034410b07a640d000d10078041242c02c8080c680301e8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 59151559 1250 59150309 59150341
    0x901020406110601150806040b0409110418021f0c21081008060f150a0e18030403021c0602040306050f060111030c07091505090403080a0605030a0803151206 69
    0x20020702c004800002200780040d0036812038011486800c019424050200d80441005c2c0156a006071102140c02e8581d8590080a40385030082107685184424101004201c40008a0084240c2c40c42c0e000354016a440210400307004003480068001015082c40032603185011230700007028040f0180380b0f03612548400c0c00350b2503c07d100d51a030001a840b04d103408100d0000e01c0c80346020507813111000422440c01c01c18074640200030701c07281400021000c40002c0d85c03c07805070807032515400d10b581042540709103000102c0b10716100c00c01035032605046802140501c105141e18141c2d44007200300480c1009641d0341114000c5800c50010419410504451403c1f1a01500c50600048100c00d43e80125003002c0110b0b00b4000418009280c0f40b440c04050b1000f601b4031042035180c5035081c0f45d00107100e071a4001d12610441c0300750313070b038800e10302d8032005000841304141c021a0090703001510749c4000a00c8002101c0d086103c455018040d4214600040e1020840e0707150340945000d1101409161040c0c1e44102d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 59152809 1250 59151559 59151569
    0x9160201052410170a0f1a090f071205070c050f01050f13060f0e030705070603060b0901030b060d0603030e010e0103200c120f070c050d0b0a150305010509010204 71
    0x2070126844408900c803844034408089088489014058007032850000032860000c5024108400c80340d000d5050146031141c112000746035280c40300ca01c81c1c01d250302c2d40b0803030b008528224003040c0722440d8040811400390b002041040700e8000100411047c90081c078004942c004648410b00041c0342c1a0001009550791140444e454402c0c5002486900818002d55114000c55248100296030704008962203203801c8805403040350344da04240c0d000000c14060040c2c2da04a200045a480211349015440c10490360701c03a508041c03820000f80883c400240850b00709950901c0c001c5903090501000030460720030b448008a00a181400c00070826411a08560a0400c241c881d445124805c6005400b52401e40301aa40b44004140885103041c0105026060b94040007040342c03c0c100b103a08507071400d540002c00c03500480d000800d2820400042e0908080540825610b000c104151503490300703c400b00103050710700c3d030503121030212480781c070b0705c0d12042c0003150040e00030300213030424110240c001d5000b4010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 59154059 1250 59152809 59152811
    0x31f081204180b030a06021809040501060303090611060105040b0402040509070f1b02010c0204091e0503031b0910030b040b030d12050705032203020109080304060510060f020c0105030408040509160201 88
    0x8600c62070320a4443e2102c0f04501402505581d88030b96a81c40080d0b11040b000038403214007003403002d9151034002d4051710851060f000010300c241181006010400c5d16448501040784929100c04002e601052075411240c050714042413810400002401034001d0f6000b054001101c2410080340342c2d8080c1000900045076250380c10303814003c4116410314040e80750701070301080c41c0420f904014142a40007200d0380d4000d901c2d20040000910603108440b00e060380070b5410b54000f100303000d00a101485080b2034008020710803403a050000c03002c034034503100d01d201403030925a544410300d8842d103540e04622254080201918000242803e02501035070f000e45184200c1840c000000c2c0185000b00c0c2100d010b45800001c0d40107070390b0790f10541100042c460030210300b10b54a0300f90308000218880042d5000380d100d50004a080d140c00b03c3c079610b80201c0e982c80442004066255071410702c1d00410701041001c0203181c8143d9a5546040188545c41913510950700491030100b0405040d41c88103c0c040324041a0780 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 59155309 1250 59154059 59154089
    0x50a050f060613060503060a120807050d030506010c08030603120d060f090203010302030a0f050f0a0308070809010501030b0c0a020c060708070308090303010506030c2a010614090c031f081204 84
    0x2d000190142d011501c40a10f2109801e0015a0240c0003546c0d0211006144072152a1605810200c080300102c0889144a01003204001c110080c4000b414007400c610701041f6030b2a0210000380700e46405030000d4200440080883e20540f424090420070320030300e8030103507034400d50b6655080080281d44030390708208031241c03070114008082c0d0080301d0480b0b40040c0205a1112180c4038020f030944c1c030644c2120144151030b10300031400410f0080d0341103507009480f01010f030b25051401a104d840005c0c14501c65900d06001800026824402280c1110340f182d906900c2e02d0724040240e02e0f05402d4600039901c5400403444400300700e182001401c0b0035100e65104202601c0b441c120701d82d240400c0c003031941e01c40e40510000b1110300310302000d40041d1180e059071040b41d40b00c209104980d1100c0064000a42c2d4407031109004c0d40802948035544080c06507044040c501e07111080c0c0e611030101804405180c0500a0881003000c868028030000c2d224240075291000035083d0810f00300d902601c650310541c4d9a03e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 59156559 1250 59155309 59155321
    0x50c032505090f060609011209110a05240a020c040e0c0a0608091c03020f030703061a040e040803070c050304080d0905011d01080402130609050621150910050a050f 72
    0x32002c1c0103041900340701c0025110002013000581041b005c0324104042a501e03000118864001c0e0740348280211035040001c0070903c01d1103030005003034002074000c40c047c0b10030548180030701421321080e0100e044055160b003c0102e080b41004c00d0184010740c064108180c403100000702054203d10760000b01c50003200241c2d00d810960b0242c0e0222403801d4145c22074407220528112400c012020981e0b140b40052800081c0c235420b2220b60405e5072840000b076503554040c8070b6003031a101c210070f60b00e02d009145401c00c1d103400e10305ca00700b0400070401000701d00080041520940510301e2082c60a0b40f150030b90340c4a81d01c074982d0300e50703a1000e003d60100040d448100001c1c2c6501a10f0118105d03e02204900300c032444d10001510050b5003e4001ca130001c40d04142101945440d10982e00030b42004040401c1a0a100d01084802014203030381041c650308a081c0c00b1511034000a0a1900200e404117580c03150350b940c4841307410001d4415000071254180400c119004410364049889151081001162520303a5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 59157809 1250 59156559 59156569
    0x9181b07081b240c04030b13051006150c0c12050319090609060c1104020a02030403030908070b16050c03060c04050918030406031107021908070b03060a0b07050c032505 74
    0x1c00c0c030001140210800ea03201c03e860400076a5020203a80040d40c034150f540e5581c5016400115508042c424006401c1010040184940c0461100e610f00c20f01205050009a1004111101086062146044100381004804444d0307030f0080081c00c0540d03880d1440c41c2090354581c0d00407008000701003080d102054645026040c1da50a94819644050b00d8904090040d100206000e0003942d8618980030111a02d1740d640c0000d00c2c4030303002a4051038503280f961801905d05035058010711441e070000481070001414107c243c0d08142c9101036841c000201e242442400c03c50b18050352a09030103080200726019170500024070458009581c0d07446d0303d0741c440d071050945001003000300456030410001081558400d40050b148150030240c61440d1803e1070740020315450400d2154058001c07201001c001c045c100f4050400200000348816156107803503800900300329454002d80b55038401c00715420050040402150001c035901a0031181c2c0c520302c0600113819904280d4045406e0880c10038007091501784 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 59159059 1250 59157809 59157823
    0x8091207030510020306040906060621020903280c030803010e070e10180b040e040519050304050d08090409050c04060b0a05090d11060307080f01090209181b07081b 72
    0x502414020803500d0f010b038040e50010f0300c1c0d0b981c419110349100d0003082c040c0c86480d00038403203070b100c00c0c44e84c0e00d08003c0f002d40c42000d01c0e201c030042031040c04a103007162404503e285280ca808144640044004415540c034607543c00b0b0054007000860f000842041000b50085069848c11040c02045540d010021201403030300d544195049442d0f00410080d10f0302442d11451502030321031803801c005440d04d910044a4100b58045443c000d00d0106000c1446814080961001071111000340e203c040707500d683e83d0b41d01c00c600c0ac050003150300034440014004000b0942c0c0389040010001c2c48181498107100e6a00c0740c1100500d4403c501c0c1460000700080b0300000c07035090700f080d0b443e07041c1030809400c100180131500c51015940024080c880600c20394403040190721030f41036900e400d0f80904040900c4030595005801c40c80284e80b041080489650312000d50030000103524980c0d0020307580711201e4002024801081c454010008078200c000c00c100900540740c14000c88803645615180b6010752651510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 59160309 1250 59159059 59159063
    0x40f0c17060609100827460506160e09061c030903110d020d0816060f02090102011104050607140a290a050c09010302070218040809120703 61
    0x4020380300804510440d0805503000c80c1c014401d50600a4a1000c10404d40f00c0c1c00204002600c5030040040701c19030a031000014510a46180c0c5052440c1c183c000d03582c46c9181003180c00441c0d00c81580b01c00070350302061203000104440310442d90010151030041000e03d05881203595000385000102a00d00808691101115990300c0c0061a11f50b5014407025a8000c0c0050340c00c580e624142d00c40300c40314131580d268668402c0e61160710803855400c0103241800108200e42c40390009200070005661a00c400c003000c1900f0480495880961110182500350070040080c1641d080c82180e24491038150701030b2101c50030a0b0000e00917890741029160300c2c3c0c41a8040d01d5442030b002d21030100860900c0541c071746a0305c135102c1220034408482c1c40c0c4d2003030728400f0180c4036402e0412041d41c100c4252002c0e403131904442c9810301803040d4206142030f2403080c00b40ea0380d03050400d5800300340d0710199078602c1410510030394034040111290520307003031001c865803064241d07500800114040078091a000910344040ba0b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 59161559 1250 59160309 59160317
    0xd091a091c0504050f01030609050c091503010302060d02180a15020708010204050d0f051f020405010f030903080103140a0c170c1503010302040507030905060901050402100c02030a080304020102030f0c010902040f0c 94
    0x5030504d0704205003142c280105504041e03581c0b0b00441d03605001d101d8a13000c3c02c003d15802d6128a101c4040240c2600f0182a14000309420b000420041c1c032800d0030742d280700e01c3c0c5c40c50158450040b4040d0784600c80380c00c0d1026501001001e40010580f104030450311b0205196801d407401d094031545905c2c241d101c0c9110303294000c0040340b1a40041151528010f6440d4030500c10b03515420300a8108500c00d00d1400c40d0402142e83c0020304001540e0030012140e0f0080d0f20341801e2089442d1520060703c2e2090509c0040c01442c1c1c80c0712000e04440c03040c4429041d060b440b00c11038001c01d03102c85003600c03d00112880042c443c03003a0032082c1d015107040b8000042c1c0210304142689181c0c299400d0001038030000e003082c01495240c0c442840003400a2001610580c244030002520b4039103401008006038500340c42c4014014401110380c003603203000c44e180711040e4221410581e640c4a47c40101c0c910310940701140200c80c40401c600c00302c030b01c0641211000074001c607003c0c086150400c03010000c035207a05500c04049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 59162809 1250 59161559 59161567
    0x617010e090c0306070905010806090403050d0905030f070302070801150509011a1b0c09011e030201081905040302060108060c030c0406030e0a0206040f06090807080309060d091a091c05 81
    0x48924503000d03803050710001910140c00031003010038a8030505844d01c2c0c010610111040c441542d2040c06036600c000200c0c1c14041d80c0c00c154030060118031a2481c0e0005240e26140303c102400b100b0400c44003841c210303a0f8170030b44c0d034101030030001e4448440b40960328195083c20301314174900702c07800311000c10f0f100014002841c1c1c0c0d1820307901840b03c9070707040c0000c0d1504906100004407050380c84140c09092128501500c87c80c44500100940118141c010740031744903400b25010754801032044000292603080c00c1036092070b12000e00c0c5d0480051040400070309141040c081000b00759020078628101d43c00101100d0b100c0e01c480c1000c41d01c5000441c1c0001f18640c05000030499644a6082415542c0314442507500d03500036600443d41c2395000707402c0241100c140031020006160f1001c5540010070001000e0680d59040c8280b02e81c4a2040240c0302e0700c82c7c40085440f144621540e8401c1c039440d58804505081c07252480b6804548000c104c6841803580100741ca00c1e40100015003040e0f080c00c0150351050710f4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 59164059 1250 59162809 59162819
    0x1614010614120c0303030109060e060306010807150912060c08180316110307060503011404020c030703030207170706090204051e010b0f070503040e01050a0b0a08060402071e120801061701 82
    0x201820161624030f40324142e210700c9152828002140030f0400b0290110300039082404882401c038002e41018083c1d4044030041203121804a0300c90b040d00d58654080c1d03840701414904071486001a08580614034500f4054010843d059014005000d06038881101955074210140c0701c01c1c8132400c0164058004000911218200201c40d40c9070754440c03110300c001d0200c05000700385401400d8000e0b001089000005008056241b0b403860b907098012a0213514040581000c580c9901a0b004000c003415004070300441004420f00452840900c4140c540780c030388039a1309103080a001c900c8010b03409030345800003007000002d5412102c0c51a00b058041a44241d01c0c200155046502090a41c9001a0103012a03000039109200400050031050305d00155941450100240b124081e44401980d203404c01002c4045600000c1c51a80880100c4005844447c0b50400f04400915007440704091100181594100450701c0d02d1404000070560760200036a89800080d101074840420f1041446807078001044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 59165309 1250 59164059 59164069
    0x20601060f0c1b080a030c02031605010507060b06070812060f0d1113020f0a0c05070602011413080d0203130308010515090609040605090705071b0605041202010309081614010614 78
    0x499100081018080300c0d13a0f0b00c80070b0f418400c0c2900110006081580390380103610f41002400c0c0c2e9221404507400541e0300e007400180c070368820b1300e20003011603407102424a03140d5100000d4569650b0000b010503030b00c10000d04c00c01ca44040c00c0303038079502c144030300501d1070b07490f04020400d0700200c4c0c0c0c070892041d04c1115103001c0181d066130440d02c041105408205494103801d40c20040c100b5140b0544818402403d01d04c0d0036800c103e00c58220b041103a1600802c50201d81d00e850105410000f8520900a128503508107000144645500c1056641c000818024000c40352245545c21034000d944401081c0d80310f100304801c000da00c0b003850030600d00a01011a0624001c0000c10000300000c1c000185a69500082039117920100c40c6000450400305441d014080d40c2c80c0c0443d121624034501000003800c046025050f030203030f40181d0b103299080701d00580031a4040c1d404206003c0d0002001515480a02030004407004c204078202e80800c0d0180c03068046040500404007500c40990f4102068490300043c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 59166559 1250 59165309 59165333
    0x521070302040608030408060f07050a11030c010c05030702011a0f01030f02090a0f050108070f020d0503071709030306010909060806010b070f0b070203030609060907171807080706020601060f0c 85
    0x5541405820800001039031988203980c0100040c0c4051178990f45419003031400e16000918003200d1f0103000c010440400e6001d82151071295450420114207900c1001c0c42d4518014428010095031800f880307094180d81202c0510b2041046500a00c020a14042240c1035140b0100845030801503803688806a9130094200c21804088510010309120042000800f4005036901c10980d07504000000d01c07031941d208418950115980c2011303001d0580b481c100a6079a4000d403100c03030070088080302140e64a4801d280034482030b541d090240140781825060329850b548191041d41c040b41c0d03208000144803455019200848103800080c1c480c2d6842d04545900e5075105c079074210f5640340207a854400280a0700c2d49640a040725a000b1038481ca0540300307020f8070700c1019100780e101d00204420014178a50001058040050b041c14400164403200c400780300e140035825400e04ad81c000c0c0c4102281d01600000c61008444040c4d0840c0e0303403645d90728000e03a8000c4520791220009801140110007050003c5080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 59167809 1250 59166559 59166619
    0x3110d24020706091406010e0103080306040b040b03030705070510030c12050702011404060b0103050f2e3803010f090b0621090f0609100506030c030a0305030702061005 74
    0x26240c0b401d141c2d40c610480b00b4070b400480315102c819807203950800080001c0d40c054182c0c03103200c3c1031950442e1121819400000c000320712a85e2503061240d03080d103d9800c240303000d840140841e52034180a00d0a1174407010075006d880c0c012080c0c460f04c040d00c03a209000c0e032004000715032501c22021101d940d84002a003030080518040d5034032584ac180c1040065040548164021000041c49020040006090394409040610b0400141e4248038a8a0345a001e60030192005c2e46c002412985034110364007050340c83c0e03020302d104031102c0c1d511107034011003031a40340c0e140300304100d43d01022203000e00d801240340028002c840d01c940c08440280710640382a4812851140014045402d00180d59140f0400001c1032450341028a0f0040501c034a82e9420422281131a810b440600a9890300c09800c079a1503030750032000c50071583c844000c2401d50310f082c40300c101c0d10f80380a4295100d465030381c10041c006170b0064031003070300520940001800044c4040c054400ba110010300e000220400041020240380c110000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 59169059 1250 59167809 59167811
    0x11060307170612070308040f080c0f06030406060803030112030e031504020d140601090f1a01020c0618121f05010b03040b0702030d0501081c020c13020a02030403051603110d24 77
    0x3010001da040040800542c4202066562182000004030003e0202c9d481000d01c0da03c840300c4402c440e5100030f00c42d0342d980816286103440303650383d04080010702520b610207a6140000800440c61503110111042c051380170307031550203160992a0a0503614102603240c0d190405004010400514160010080d0345000f00c40281c0e80420025145042c1142a804080b2059481c1c6501918079194091699400190b05c0c15240700460480080d4035122b030800b500c0d105070310000301025036555114111114001c0a031075220321071491100307181da1365040514422230006c02c1e00d000101ca0683d014507816035a0340c010071815501c1c0c940e14840740400140c06401540814421f02c600c5c0303401445014002c0c4031010081040440d01181e451561020140740c000315040107038003d059444280c003400c0c0001e200000140c0c0c80b50043c40c101d095011365003008200740140958401403042ea501c840701541e00517400c400d880c01c4000c003004400500850000c100c081c0e0140404d0700018407445401100303900e107030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 59170309 1250 59169059 59169079
    0x1060f050f0a081e0f0105060a140f040306060e012904030f0b01051003060e0c07210305090c01030207030c02010f09081009050c010201090203030d0504050a1e110603071706 76
    0x4200c5690b40c0141191078005658031003080141c00040b10010b103824400d520040c1c581c103286980e0800300d1414081c042c000c00c400500914454800e502e150002c02950900313a0300c944001d119111140e21510060318081d080c0540401c43c00310f00c4241038100c440c4a0a99000c2001c5001c11441041ca628071030a1a035500341f00010106694200301d0b0402481020310b401e0350340c100020400c80401200301a0708062810b00c0a10413501c400103440e07080740c41d61442030348035001d074544900754450b1410304010b110140c682c00c2d401d0b1074141d00802d0044a002c420b446105086c0e50044040303000f1000b0203030020b07580c4c0c445400075500400c07100111800914101394001e0300c81c2d440d00d05e0040320756589031070390b035031500c0302001d020041c0003800c00d1990920081c44002d0b40354000a070f580c0a101c9e420303071100369903d0101e41080420000c1000c4079500c603c540c9055842201090300300340350244141c810302841d501c03c05951030600101c038170411081c2c56000402003080d409100b600c130018181600040046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 59171559 1250 59170309 59170327
    0x305040f09020a020114090705010e2b0507050d0209040204020304050f01021602010e1918240e130c1502030904090b04020a0602030307201606020d0216050901060f05 73
    0x51100d1010346440351001da03481c2c540d694001d00311481036030314829602e0800706120051001090840864809282c404031910715130b4009090311569000082400c0c0b200024803a4066030b40100c01c440500420a07500d509a0300ea003401402e50f41c0e80802580954038400140052400313070702444c0c0180c010f1080340c540100c0c44110a00b280d00c541c4044c11445100560f8504645c0d1200c21418001c0c0e007036403003000d1150704200801020000b805021f00030385001e940015000c000d5440b20700b07a0441c1c0031250400c0b20341110700c2c003903044c0340c0e0140102c030240e0900041c8101e404104001c4001e079002015080c1289445441038a45039643c0074201140010885503501e5a503600514540300c1c0207580040c8a03042c40d2040020140659005100359013040c42009205900407060003090030030311075680c1b040050307009400e0400302028900344102c0e030801408078400b070f4005005000c02c02690221010001035415004d142070741407044d03c0e0302024501c01406410720582089a030f4108504000e400c1c88051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 59172665 1106 59171559 59171579
    0x203030403080901020f010606080a05090f0a033f060e04050a020904030c050a031206050f030c1329090f04080a08060a0b0c070e01050a060801060c030504 68
    0x460503c20590090151004607008030b4004c00c800340d194032000e810342d481902d880d004030346000000b0740364a40c0094441e0200e2400c40040c51500d4180e501120120700300045892840a00054070240030240c00000c0329041154242184020a026054007101d6450b0b000401100c1d00380140300200344085007580d03615405580b2910300d030741c031f609007a142d425121000400501c203081d88401810303031084a80c40c0070910f048040c000a941c640410040d4010041515403603003014043c0d900b03d141c0b080d88040540311919010408106400e8050030309503c82d00300305200000c0c81c00e080820701c0c03c0103050380d100750f03201080784503401e140c1c6942c0100e0280c428040140041180420813940c1c41424007002002165030b51680e0b100c189880940b03a03805846580050023902001050318500521042c041d80c01c10341d503552150b0b28084007140d0207050030005500b40401000007081401d10 = true := by decide +kernel

theorem cover : BRFrame.Cov 58992809 59172665 := by
  have h0 := BRFrame.cov_init 58992809
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58992809 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 58992809 ≤ n) (h2 : n < 59172665) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
