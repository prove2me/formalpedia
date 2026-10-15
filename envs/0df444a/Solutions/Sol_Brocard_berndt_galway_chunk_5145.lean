-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:04.348612+00:00
-- url     : https://prove2.me/submissions/c3f882e6-8c9c-45a4-8eeb-d64a95bd6df3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 925179856 ≤ n < 925359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 925181106 1250 925179856 925179919
    0x70503011508100f0312030b0105041202130b091602100203010605120910020f0901030e010908040b09010c05070311010f0306081002090f041a12030f07080a110303010e191a 76
    0x1502c1021040206d1790b0303848407045426031004c1c480005200700540c3c0e140103600a403911450303040c0107003016260240701440442c039000c4000480c241e4140c08103038032601c112405110036205110540c1060350410400034030440c0c05c0b0b011030a55040c81c5004000d0300c83d841320000e424103001d01046046005121055840450310001c44d6100b415400c21600d5802044959003c43d10b01511200715030810f000b643c401c16405000c013445c00c3e06045900815412000c2910304200d1003078141030000d58100281805540203907802c0c440c0750226000101001c503030310301d20000c05080c1882089074002c000343c692010914841e02584600da00400703d03c8800081041765030040c18449005815007069861441000040d00d1801e00d502113141b480e80e4901c56684000c0c2450340030080784000c142000041c0c4a8920507151139070420b80c50194191441c2c000780c004c0e00e8040104028440401e5483c1800648140c02c0340c0c05004606013402c40c040c1250421720717190f0160840021402d40008010581101ca544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 925182356 1250 925181106 925181129
    0x8090d1a0a0b090718030201032c1005060d03300c0305011404090b010b0304140d170114030a12050906130801111201031202010f14040b07050301150810 67
    0x20240c1030440070b01a64201e40d8020781e40600400c400e14400c00060711039a0000c01c2c1920950324507801100203004c8203c10549030f220007900c00d52800780205100407001e001d040185185042580200d040702c10180c00c05100c1c540c4540d00b840001d402c142070211244070b403003591602a28507000649400c89040407411514030b41840340c22410303050b41c04603069446180c0042c08516540e0700340811604141e2000c0c220b841d9600042000c1c0041c0c0000395440362250940d550114146004e01d407030203c0c0b40d550540800c042c03000700b8092180110700c0718010010000e4440107e9400c802003a1601f41541e00513110001c0302040c1d1003028002c0085401c07407200503208560b100b4500c0305010520406005142003942042407458a40b19000d082d580d461806194490b101d900e1940c400c030384101d44803030601c159502c80240e03803448003c52190103060046c1107a0940741d0320341380c544010b0300e00c40142035005000741070006000c1e0094119502031000503600305030704103455a060903401c0003034607406001e0041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 925183606 1250 925182356 925182361
    0x1b0e0a030602090d080304050d0f11100209031002030903270a090b030a0c17010f050c160507030204050a050f0f07210603140102130602010207030e011b140606100c08090d1a 76
    0xc0001501c1075080081c4c5cad22040300c0c070720450341103c0703001e02d40c401c01406910840c003240c030f101d13116402469196401421100c09503000071801081c4c1c0c10443e5940d291303402c042100c0110302d410b0890042070f640341d1030761800030904850004012180b03600a940e2155680c000b40b02c2182c5082154850403a0000d10382c00c0c0d060740c0d911003030300c03030107548841c041d1503500700340661503581014001c40340280c49800d4420b041c030f0144000841216074000d001d4401d4803840c040000942c0b135030310410f0701986000390007096515040c204804201d0001e02000c0030320150504000cac00f9a48200940b5a12152441d203000f54002442200c01500b010780001d0310325000d1510b004144401580100010403030b0a0704403900e04e1fa2010164200c1c010384a000d00801c1001101040d1988030715440641044140c462601c8001d05842d100d94081c43d89004448960184d03050000900d410340300d07258004100e143c03011291455a40c1e84001e400f810500c0f600410800c80d240007002a180419441304804020342c00303052 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 925184856 1250 925183606 925183613
    0x1090804081506030703030e13050c0304020a0b0a08010504050a020c031b010516090302040f110d060501020628020f04030b07020106030204050c04121b0512011b0e0a030602090d080304 81
    0x19401031064000d940b103501d00d00002038460141d034910401c401005810002d00e151416150190000341d0154884d030360707644084c520413461298502820450034201d40300d181500c103010440c1c00680202c09a06d005000355030032140d0140f12581951350070b86010a0710b469a811071006406600c2c01c450b214007011a4058110072848074a03a0002130303440007403100e500d50b80c4c0c0940c044542d1100781d0380090300b11075041c400f50a003600402034045000c0000100e454495000c039030f903a0001606001c05070b4803070000304200d6a0402c5403507005100c0070b03140500c081e0020201d10703184102d103c44030324503a000310b10000d4082c0983c0540340110b81015002049190510700240200500d00080b4032862410020510a10450040d642554103110320b5000d100c8640d1685c0040425044841280d48444580030649071220810900d100180c200080380b1800751042c000d0a0684c218040c030200140f0301c2000e03076941e541e00b0444080302e40000d070059807072040d035010130b1107801c90300800b400c2c042c400070a00c001c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 925186106 1250 925184856 925184873
    0x9170c0613032006060a14060a1812050606120304121719090801060e061008060d080a021b031914030d0908040e070f020714120708010501360b040b030109 68
    0x29190880c0c00400c0715131503a50346083d004441f075500b60052014400300da0700d54015102d2000654940324601101a521041116414207406040b500f0317801c12418840316043c0180d0312102503030040095420f00e402c10411604992030010b024203411008810100c2c0c2a1030302e000c80d4234250b65044c80c61411a05298050b00c9919980b01d40010366180c1100018803059000c00140940d10043c0804500740750014101c0b89640090422a40302086941100004501600a00f060400c40c1c010b0111110440d4020450307580391910b81c2e00a400c420041035403603910f02505461603138003855424501184901d0649180100280c0c41d08440c580f00d9240d00744140f50025000b2685055107400c2c00e640c425030700716549000d01403454056440104184100d00070740300190104c05015220f0454294240c00b00da1030031003907900000180c1d41d20781c01400b078100d40c15683d000810b0b1915035200b103005042e041003101c1200d8000000d44559507030b2000313142c0d0303a10b403c0740301c0d00a0005c00a0181844a06040c1d19 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 925187356 1250 925186106 925186111
    0xf06051512030405060a2d0f0e030604080409020c0f06010b190507020f0402090f03010f0c080c12190b04020706150501030e0a02092809170c0613032006 67
    0x1c00c03040708120401c04400081120306444002e402541040c802503401c0c0c07503410140380382d480c0b6280084602a02c0e428401c0c0000900030850341c0c0c802440401d00c2001d41105005204540240c112100b000081041c0000f11400c440b004003005989074000540c40e41402d119030b032035000343e001d6100006135501c01341c0301501c02e800e001160307140f0a40703c484080d2100c1c0b01d0490700035007110f131950000074246016400f41c00c078494090096003030b690352007000a08480b941190306003442e03580c4010f0181c4640c80741c2c48a82c4803001004991411500740060001c800005120054035501c1c94001c0a0b215555005040344103006030040d5241c1d00145094005004448003a17403040c01e4078200082c1641c4617000e078810380501074018018000b199020301010f140d00a0040308a0060700304c01d180d4000700303621500081c0201c42400549022540f410401c1c418005c2c090340d1924900748499004100701040310360f00001000141c0620703c4561406840405080c00c4002c0304155241c40908110310101d1a140b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 925188606 1250 925187356 925187359
    0x3010e070f030c0e071b030302090303071a010504090302120901170a020d0b06090109061407020a0f030302060f040201050a0c0311010f020c0f0d0c02011404030209040305090102010c080f070c0f060515 88
    0x50079075448034001100020200c8142c3c0000302048103111b025440c0106d0b03040c2c10780c02840c01614240301500440c0c030315030011300304851514141e4400909a04036000346405030000321414428041c0d80e072002551500c890695590003000014130300307510f0380101c910300c0080e4513540100070940303081d2107214001d4024181100000c0d0411000c0105e900e0071400b260581d180503115554042d0418504454100d24031480c7e00d1001010464440981e03100d0440500825800112442e02d0b03081d40340090030100081d1503410f064152009120045c2e8001c81907414a600305e141c0b0500501c400e0808407075480302107181c55400e5190088440114440d6002040c807440d0080c216080400c510307641d6580e40c81200c8030100002d0604140d400158810942404030840d86000c480c10a0348075000201c642205407001c0b00800c90024400c16103580a001c1c2c01804000703030501c84144e01c0d010100c00c141c00c02c0200f00e00d0800800180e640204082684290741c20750b04140200071615200344d10440f5001d0007a01c0c0d9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 925189856 1250 925188606 925188623
    0x90504140601060519090504020708070215070305070210120e0d0e03030f0304110a0f0603050115110714030a0609060501030201090e091915241505120603010e070f03 73
    0xd00c50002403518102e071503580e112880c1c40044150107290280c103050300700410959a100140640c4c407400903003d000e008000c4140e40341102d104004c40141500140c1514010078010315021036005401c1c0c946035034043d9000c92000303550380e1044070340003240c0c091690200e1401155100782c180028100c00e4082e480c0d02c031034145130101c070109a524040e201002030744003403c000050009215101c4030b2404200540a10405504e80007415400001500130000080c1d031980100141c010000040171180ca09040815a100d10402c0d1107845580c01d0003203502c04503002c811080e041d00d04012001da2240c10140800c64040c443c030700a4083c140a101c03e90000e000c021012406c0d18003201140d00504001d801092901054401c61702c80c4582c2881c2900c03034003852060301c1c5c0700e007510340101740e80540048591001c6009041c1c01444412a94010500005050300008420b9400c682260701329101c00e0201c281c1a07640100203800f40444141c0c0481e81c0c000c4140c0029041080c08441080c1d03813148180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 925191106 1250 925189856 925189883
    0x72403021c050717130209061c0f060504030905010504050f24041403070e09060a0507020c0402041806150507031d030f030423090f04150e0c011106090a17040906090504 74
    0x45c1d84460450010181d8088504408500d003841c0c4114105040c5952031402d49245441e515a81035500448005503000d81c0c0380d000700b004059000b00c82c000a4102402c006040038201404aa81c1d00c20302800380f4000c140f240880a001e240300c1040081c0500c0c2692a076598030f445020306200010040c0100340279103d0940080303100141c142100384a00604d070010881c13560b440c0601c074007402028203d4020750081d5410f0002e9616940000d1014150424040c4026084080ca10084a443d944503100918020361622252540001112644ad8040c40c0011140401d031560360341411240004039498400c0036011840c50030017001a1040b038043c010500c04007a244080300302300c0c0c0701d40e2000c0c0f540603c0c100d0010301e5410980c1449504503000f101400790f5403121580120490b111420310402560150280849940c1e10071380304500300900d0805401e080c1004840d16581c4d000c41000184440701811614013480c0e00c200a550041c01c8280301408040c1c1d81d081000020801501e042d501e100e51b00e1301c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 925192356 1250 925191106 925191121
    0xa03060b09150703031b0905011d03120f0d0c0305062e0309111905030c030f0c0603060613060302130b090f04020c030408160602072403021c050717 65
    0x2610003001c0080d04000c5141000581c00102e540702030803c80c18145d5442c02401441c045d030101603031a11158861490690902c00094101080702e990918540b03a0074125402685010588006603540800b0039900c414080e20011000d004290243c03040914121450300b4550b45500850301808054072485110039542800080c1c060000000c0302031801c5c0f41d401c1c0c0e14002d101e0307405404800c2c000e450b105503c240e02400030323800035800044048881c1403090305000500d020b0010070609041200203003480310840c9196034841682c00c008034070914010000a2a40c0c0310071044415940d992070025198588a0101a009411120061f00c41c001201800f01e4603c400504596071620000c003c642289448010031000e0350207400b80e145180010301002452040800044001c501e01c1c88c90f0003819800e0500081c0780c111540d01c0310b280c082200003c20803030102c4105210182e0454500940d0b11005c8660b5084080c0107102140b12181c034080800c40e060390b00804114040d680c1000d581c1b41a00c80e4503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 925193606 1250 925192356 925192379
    0xc03100503070b120a110319110705210f2115030c09040c120609350703140c030304030216050a0e1b0307023403020603070e060f0a0306 60
    0x6030712150f1904000d54044003248450b0f01d43d00404e1a140426100510280161547c1065910b8080d80aaa50001c25424030b030f40070f00c4440008140400d400d184064030345659950007055059119034004998110801007182261312003000905030550352200d0280c003a24090704065410200301b01e841c00b19805844801134420003200c000d009001481e891000c2209002c4050811280038030038070000604183d034400700c3c40703240d40916000641c41800313040407001c00720341f912a002d0700d2100108040d40700c0c2c0308103210101640c0c1c10030710340d444143ca480c080d44d4194180a804202e8403001c00c4084501000200462059129609482903010840f81d0a014103035580110b65000d416104103109420848240d03580c0500044002c00400e124070904203640d078400c0d614400181c101049060030341e014800c03002a0340401c40303440040c40110181882c004044da01009100d17150000200300d0701c0c0d00c0303030884404441004262a944521410007002c681e070061480f94003003401c11400052005045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 925194856 1250 925193606 925193609
    0x912090e16080a0203102301081e01030f1e12120c021f02070b090105180606060703051b0f0303060a090b0915010c0b010e010e0919030f1103030c0310050307 69
    0x50b00c8421060326807030312010180d040185a058000483c503400140113441076080d6100c8450a0020742190503040001000400c008110440c02d0001c180200c0c5500d118400b01d90440340c1142c1c0d16003d45c2194507080440c017107038882045960341c9420840090104100346035108030280d440d084008190040b0510642d100c1d942c104025030090803000ea1514141401c0000c8448480d07801440c00c00d0300d40d00c20340c4060003961000354503036441013040440e070522581c1c1150000c8400060096140c500700142d494400d000303004040140204410560703501c0e1003590401c41c1c3d1004251202510b0b0768000d1942ea03041240c0940c8100e0302c0b83c10015880300a4428080e0354400604404a03d94a4002e02c440c0b09007000c18050410240d403646d200440c8900c06500d01805241c040350b155549031411040007003801510a14190300501341c11074104e411006079464059140c14180302800f11507806844042d948059241c507400008200400503950000444c03007121107401c10301c955503c03031050550b0394909 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 925196106 1250 925194856 925194901
    0x212030f0a3209150108070e010b042102011418010f030209090114011e210e0c010c06020c0f06180a031704230109051b010504050d05010912090e 64
    0x581e090002c164a4100240f948000b002c41114010000e8402201c0008026401352005402400040c0b0000001c0c411060040000ca002c550800d41030070308545511010142c80601420403107072880c110790082240f2501d2424507042e16440740d2994041c021031001d406241e03400a200100700d2601640244281d4800f0b0320090100c408a80c2001d0554510802048005050203d13001c1d1814004200214202080781c0650307500004940031318140880d2054004440d1209040c04d0848001140004072503021041c00d20f080c1c010020075007001c800034442e6045c4410f150040300e4008045180002d50b040c0154140d12070b5840345c1d000315101a480341c18883c80200014140e4000c15442d02c0030200c00e90f005070241c0f02c1502d007140c15441070302e8090f0b09008006490b9440306411001e100d005d0102c91141c00d90690154800a0b041000070000d00c41c60041c50b02c64400c07a806542840700961000c1c00c015441803446030158040c0d1030241401d980c91050a0300703440c00d4800075031100c1c404000340d01056203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 925197356 1250 925196106 925196171
    0xb0613090b0a0b070501140708090d0c060f0c0f020c0102120d0c09090f090c08061512190f0b1501050d110f0f2214060a11070b031e0618070212030f0a 66
    0x8044011640c0003443340040e205240c03141c402c0c9084503018418001030002a0300c91510f16045a1006800c00010035610790564003e800c00c1502c0541582c1124200707403000d400052111400d15066a01c004590031208903c0d15040084101c03800ca50b20000241c1d000b00e00001015642e070140c66541c00d070499112038a11011404400942040d00b0b130550080303402001d60307442e280d01d00d50b04210341748d00c66426980c0702170794101c071028000b030340d202960428400a1098900240c000c000317841e42c0301d1348010001d026a00c400900402c0d105400760340288031130b2001150380d030744401c01c0240d15810610f4140b19502c10207910140c4030030b050b03465404460840d081080a5400d2008004040d0401c00c02c01d010310210050002140100f0321029001e010980e40168507401c00f499980b00000c8003455044003e0348000a2001c1541c400c40303030200d50b50a0302c2c010012540c69900482c04d00704520040040140d020050081c90040a103006104004d600d9003042043e0b00c14581300985440e140c5400040c5a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 925198606 1250 925197356 925197373
    0x1d0703061a0d02130c1101090804030201080705070f080a0917030d0b0a0f0905060a0302060a020f0d0c05031c0213060e010e2d0f180a0b0613090b0a0b07050114070809 73
    0x8035080051030314110704111001b0f8400c0e182e01800e43d40030100803500280c00003018000c5603040354845402490510b0001c0c10f02005d0740c0c502210086449002d0900d00010070090101c074405d04103140544948082a200f4410745400159207130400c0400c1a07a07142415440c01c00d908201500d6003c4488000803042000e10307019000f0000c041c013500d100c0e0032240008010000d6103840006040c2008a0b5008001c0e084000407998180a0060500001c01c003110b20b100001c12000000e94820382c0954030b501d000b89000181f00300c001c0c802d00c041c101c01c1802c04040010006c1d04140455100a02a241e000c41031800758200181c86221f14954000c1070315884201c40c02c2ea80e8030081502d90080949440000100c120000c1c400c2040c0e21403281d81350a807001004a480301a0140082102094605500b460481e06010b410b0f038246021350b40d0100d0313a8400610441c1c3d10480b800b0300400506088a030303112a40e040440c00380c100c2c401194004103486c1e000c50421703441010b89074840c1c240c41001d031150a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 925199856 1250 925198606 925198639
    0x50316020312070f0c09051501271503060f0609060f020c13061a0c0c090403031e050718151103040506030c2502090601031d0703061a0d02 61
    0x2005402641c26110340924a804002c0c800000d00036207000b042400104051841d0000044d84203030015500a4200b00910013001a881440b280600c401d082c040345c040e40030412084900403414911940c000c66100018002c0c0428031403003091411507030203000c05501c2e54450801e0000034403e040008400d01d004000c1a44181c2250550f00e1051064404030550000002c813607030064036000700e2071643c880041015030f4a10989002400020100504062903002c4258031160391003030700d500410180002070105031003907004400d2603036044103d000c0c8110981e0084010b14007103900701c01044040155400c21815035a189040300d501080d0200e40380740c610400c40f030410102c100c013940b80c4000e01011034142d41d0807001d035126030114640036803a603116010090702000c1c1030302070000950b81c6000c03c0d000344e1940c400300345d408030003828040f810b5000b108070765600c00d040d015240704c00c1c000c102010041211039006010701885d00d024016a90b480c840800a808034401e20017503012800058820a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 925201106 1250 925199856 925199887
    0x13020d02130606031508070e0606030405100f09121d060a03020c011a0a0501090f120804050d050f120a02150c09030a0804030b01090b092a040f0e130503 67
    0x2040d101529035402a070441600350706a4800341c000710042a207805d115405c0802c84d260880c0104100310080460034503215140880040103400035020f514000002014060b0030405e40c541c203664a0b01c1000031720340f205070280050901d680211a24035401002000e02e0348a00c5191030701a08140d45480300380d44210030030010743d0214400b40d003419002d00001006040c284100c2d11a500726018085c480c3c9002810000031841d260055418860840c3e800c1c06106c0c10681c084e0242c034175011150448001e541040d510034001c50b4412a030109002e420700c4100413020461034004c160f00c1c01100c4040c2400780d41c1c9841030049291060050b40300c3da09468200407074009035074000c034080462518010700301000c2030034009000c4090785c01c40b03000581002004039610b2aa401881000700800c90171a0003800a0841c1a001d13100040c003142900500b0319042071400318586154405c1c001c1da42d00d80e03592114480d0282d032403190100116801d40003c07203201351a94a00315941c0e100d40514900f94040340349001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 925202356 1250 925201106 925201129
    0x61d0f0405041103250b0f0706092d1a01060e01052118060c0712210617060112080717040306090b181209040f0b030105010b211302 58
    0x18591004400c0700a541c070240031401010100d044203003c02403640140c202170300010342c040c414080d001c01c0b00c40c00c485400d070144c07246e4580c00340002c41c5500240c2403001d894140c07115069000790143c003110151070003110740407400d144141e0502e000301041002a041410003442402e0100d5951140ea010641c031503001011400103081402082c10b01ca440400d02d40e800448010a100c101c00540940050080080307540c002c40c58901640b03000950390390180708152458514051040c910000540c450108000d042c0501d001e50741006503e6644400c40c2c03000d624080c228501d40605000490607551483d0100103013900203000610b008055507511071508103082810780303180350620001c0009015030049000c40380c005d5000151034103088040030800c075005102e15956611445590350343c991010182e408000088600044d6800609900b07800703030083c02c40165155291000101d84ca4130180080d1040380c0340d2181c40b402140380d00e03441c48481c42040c0c2c0c050b9050002c01c0c2d401e07001490103001c01702 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 925203606 1250 925202356 925202363
    0x1605091206011d100f05090c090d1b05030c060417030c010513030e031504060c0207170a11010815040f141608160518060f070804061d0f040504 63
    0x4900300603821506011081c0c201c0b90148a072259488252201c40c0c80b050740081003254a451110301e0407501d9169110907202e114044c0941400007940b010100781515001c00c005014008224001e00e04040c092210801a0154840919001c582418006142c441c0c00401070b002d140362905000c0c01c00f0302505140e03026800e0780300400581320041002c0c0030755402021681a40c8102c046603240203415142881002c5001798403850290314035140352800141c0050f044600050400101e01089041581c030303400c04031030807520103840c81901000080c0048858081c180340c1e45000500001100c20f8030003a00c098447d140c40b051081c40d5403070300780d02c282c42c914405100000d01c000614550140c200c021240750300c52000c14101085e00c181c000c0f0489512800001c41d8980c144041c91000d40240501d245246c01407458007011103164450800311840c9a02c2c0c11441a00d0302454541000260320500564001566134102c01034055450440c03403103410402402c10440c40012030a1100420b4000c1054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 925204856 1250 925203606 925203619
    0x180213060305030a09030b0705031608040201091d010e010f081b030106090f0c090b130e040c03210f1e0f0c061109010305060306040f03050c0f0709020403060c08160509 74
    0x1c0014810401801d190b551612140803481c55418150a648002046202404800c204002a4855441164043c80414203065102d503e4500040351703650340d10b03040b041608d4601d1106622681c54030288604a401d50b44500d0b4440e03885082c55103038440a0300c5151810b5201f613810642a0345a151002c600d000060700000d00c4603a0344c180001a00c05400100341d404d81e8605141001c01e51055200025002a0141a183c0b0708065a0f62290079051300c502c0703070300b085801d02040400c08075120311002560420044e101c00c2030202c2200c00361030011a00000840d00e52000240710303500030811707104140520ba413441c800f84070200341600c0305821407081c0400c200840e091103000400900c2448142d94400d480581c40f1101d0400240c100c9502601c0740d4460740c054000c00c00042c1c05001c9540c0314940c9450f0180c2c0f10840b07005024030b07048400ca0030310801c4c01741c031030042010080781c0e000e08212806004140004103032404150b07a00380094075051207150001440d00d0b440b030700800c0200301240c8040d029 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925206106 1250 925204856 925204859
    0x70b0a110729011706100317070312020706050601020f0625030b040c0e0f040513080c161d0f1e100302060f0d0b03070e010509100801051510020118021306 68
    0x4054146800d030071241450086441e05a604a8100520b961201c031b0110020303005410764a031004030340f00d40f0312601018031000521104143c0704542015045070789035025034803141c4900d405405402d0896816005203d80c4080c0c403036200c400140580181114030300300044441083e82c004241e42c500704a00107054a070611001c4507141e6100b40242006903903198809084010100311041c0442d01c600c41c1300d070b8280740034042e001e907620a240c650554000c1040d59107000707001d4940d0518a40340d00f01c815642c0c498000081101803411424400b4500182c88042035942c900d00486207013059408030700503662100c15440ca084100505900708004031441d00c1e40e990f5030b03130008480344c0c40f8600c820010440030a144112002c02e024080c1244400c40190400c142003540d190f5020805101e907500c58041180400c007a026500c1c00440903061060007480145880d00c2010303040c2001880c4d5500481b01418802189032040c407501d208003512045c25842e19140740c08022110742480d03002001690b90341c80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 925207356 1250 925206106 925206173
    0x308061203070b0a0612020a0504020711150309011103150907051911120f1204060b1e030d020106060c030e18090a14010207020901031e17070b0a1107 66
    0x2e4501e9600c40c00c04520140380105100e010344040380d004100f800c0e462412000143d541d9a01c0c00195070302a070b00140c4034500c90400a072a10040005d407074000805414100902e000c0c5070086100d00034000c005d000c003658880420703c13541300440346039492902031a01888039240c1400781c02e4200b01185003030360a10422140d12045070747c1c51200038011490000880142c00c10500481054840c2024401d017041080c2d8246c0c4400d01c54074102010308080980080c08200035684000c0f501c40c1c018100518040c40e603411811411886010705129100d0310160fa0f07c21441405408160755150343c4080d0980c138641e40c01c1d07500c007004550250744800d82415a05011000d409000c1c41044040010403030601d8500700314016000e455905482c0c3d9004212440240e120441c9050440e0351001c0c4001d141518a03d20840c0d001040200030115100c60441c0701d48180c03102c2c0a00b9034180150b000400d02c1d21001014000c44211130425078050809011f6071000c54400b0a102c10320388400c8000c1d800c80c2c40a0342c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 925208606 1250 925207356 925207363
    0x910110102160b010f05150f1e030603101a0103090512030f060901091103010e04030c020d1511070f321006080102090f060d0902060708091008010605030403080612 72
    0x200312182c02c290509056052002e607100c03150040a50a40101c406414000845c40064403030070707119940480001c922030b050f8019421288014107050034880e029510446600c0c040d4030035200c040c403900c40c10008280300051841022034104569203a82c81c1040b0902c01034015201e01c007410f80c2c980c0500c0c0c60103e842d1208070700861140c08907440d1550382b850014100654034006800c080140303868044481045d107946002c8905440c1c0c410003080c80d0b640e07149411100150742030b01c000e404c16180750410040000010704420012150dc8090005101c00c9030429000d0040b10000340c40b1340691569140410105a202c00415603610441261245c010b4407003440d40e2400200500b0b154408c00b280000b4019038403a010190091070001d520302a80c0d02c000407c290310311840c251081c0400240200811030592018100b580e0107400070b5100c058506104050b508800d0000d405001404440c3c2a0720303110358401c905072080b0b5143d090031611551002c503010000113002d6034101903400001c06200c1d4042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 925209856 1250 925208606 925208617
    0x3050c09090a050a140907030f080c01020a020c040c020307050c060313050604050607031a0f12100f0603060b4615020d110330071119080910110102 65
    0xc038000700719400c207202140b084680740084126114108001e00c4845100402c1860440c2e03003100a5517006681822b01d44602c1c40f99035a000801d610004035001c000b50049100140b00d2011034040080014480e82a40c8a10a1300c3d002030064100d01c04070800d84c80c01a01440d0001440c5480c81c2d0404013075a191454180f0075a401c1c0e070f103a88540d04002c0102da05000f244c5885d8082100d50990000a9001c5626240c40c0d40c0740600c610a0800c2162500c1410030180410b800107100a1241d0040303e0061802406540800e90340c40303042c00c044132003908040301c0c554000e02e04132040080c040c0c01840e881c020510b2043c0400303140d2659118a207840f40c00035240c00003600e110001c400a84103000ba001e80303016040700d2520103210941101541d20480070040d80c05000c5c4580c0341092031004024400c0008041e210400c030320f10840f00a000d6083d82c40001c45d044040d60404968100226001070400e0051a03080141407840821410905040c4042d00e0b1001c2901c0d42860100c07007101d04078450036038100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 925211106 1250 925209856 925209871
    0x10b120610060c150c020a02040f06031703040503040b1605340807170f2b111207110a06050c160b0a0e1801080a0b01140d0303050c0909 60
    0x1a60901001c40007040070032000309801e080c070703a0b5002e2081c4d507003850301034002c0308900507150f0340c84810780b0313a50003881311180b000d9005000b002010700000001b4018541400203582c0c0c890b0003000f503040072404200706e0f030245070407000440c1070510382461481c06510075101c02c2c07907202c1e0789080440003030300401507030050840c0d0754041d03000c5d500540c016214801342d84031139803001080c984003004203480c0421006d040d1040e008014000c803441d20105072034822151100000c0340315204814800e600090300b5908440400c9501c611b02d10320484003118402020300080ca041d411800c0d020102d14219402420300303501c20074811100400200002da03500341158031000203c0d900107000101d00c441440010f065505520300403000904121810030780c0d014100700700c001d1000b082c050040a540d00c4000c1d021740c0381c001351014040c1d0313110744007551568600d003001c94520403a84004210607000f0315a02b8006480600114445499610308078042c00c0041c0007642600010024900c80303440301040c10b80b18420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 925212356 1250 925211106 925211113
    0x30f04270e10051e0703051b03041101020d020a03171b180301060b0a0801140312030108010c120506010c022202070321061d150607050c0f010906140c010b12 69
    0x303080142c0c805442c4001d080c0d004550010160090224012060341c2e000303a100d00e00020f903691500c41d07008100700010004400504003200f04030800c0680c1002e0801e154080c0d081c0d40940c41e03019000c1e03a984400041c0180400c1d540201d240c040d050190b9150362005401b00890390700c0340c0c1d90160b4152907000c8034040000c41407248030004241024004c0c14020400401c41c5890607808402c000c0444006004125205091025400c0725076400c00907040a8401c203001030f5901d595403101c080c000e04034008004c01041040c070f04019a40003030700c5a94490728060711140700180310365080050b025030850628403006d18480340d20546401c14030142080501c40d8072564000c0403400280c000602c641380110144900b0324806200f40c1d02034039000341c80c408010441181c192211000d442c040c103810f0300510740000300414030b035040c03110001c3c0078401034a06640d80560050502c3c01102c1451860042c0c00215400515031203850b100040280203280812000140076030303900000945014014048254961 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 925213606 1250 925212356 925212373
    0xf120c160f11030f0709050a090206040e0f10180c021608030d15060e060a110312061305060915030a02100f1403161407240c02030f04270e 61
    0x807402040030b1442074220010810700c2001e140c01030b03640e00380380590b07032880c0e898078042000320442d60404459603a004210b541c90b5a199500c0c90781e040402c5850f0102c98007a1004902d4070740c48801e442c0203503101001c0301c0c07424941428106010b445200c10a90851251005403428803254440c0000a402c441010310b0342da80701c0d44036140030b032404060703a19003510400408200007a0820014072800f0030559441e42c4428404105071003032400343c601d07442d25010000d11203400c01440c55079113208650403618002c01c2c000d8181040221070046800340d03000903802c0c010035144001e401200480100080846a01c540580c0c0400c1c1c0c0243c00c862010041854070180400c1503030045c880d400b0b40c28880d003605082d4a04a178000d418200326600c0b69091000002480000e2070f450b000f2118047d4100e1004034544181070180c0103644140b00340d03a82c00c0c0f4942200e10190354404411200310b0b5043d030640905050800c010319140c60f845410030000ca000131180041200d041303014220b400400500503001d4034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 925214856 1250 925213606 925213613
    0xc07080f0c010201050f071803050d020304060f1106150f03030f0304120f0f030f0b12150105181f0512030405011701050d03030e1609020c0705060f120c160f 69
    0x11458050041c103590600082201d07a11040c400254007c980d031500800c01002c1e940101000710141e0806420341c0204000d40b0700c0990004000c2080b200d1640d03501c500b504040a003204c1d42020183e0664964008101165503105220004052460002d010350502414400001d141d0b91100000724220740b008030400082c07018100c4c100d41004501e00f40240c60138020507004004160592503042815602c0402815621056004d5000e908003c0d150702e4910b100002d107030396a01a995100d4034071580311000481d09040051028108950190802e142602c490a03509022400301654000c20480603200040b40d41d00c01c00800c40002c2108043d594807070070100010050081e60340b0041010304990010001900c0e401202100345806203400135071001004101c07401e0404500d4a4102c0d50004100892540150790081052059000c00c5842d11669a414000d4a0040c01d0001007002c00501001c00341d01d0750155019403015281840620300710006002040d100d00103c8103407010011500c014042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 925216106 1250 925214856 925214863
    0x60609031103060705030708040c03020901030f0b450105040b0103110915060a091a040e011406040b07060902060d0e1014150f100503060a0b04051302030c0c07080f 72
    0x101d95041d00038261520700014090441c0c0300c0541940c040251800000e0b06204000900030003450b030080c1050415603490500b8a14588011825640520301102086401d80030804000005d44074140044101c4020302422040c0011705840400245010b01071044000b0284074039031059100e01c41c104040e50450400c8002020801c500b10b0007980c2d64420b00003014031003a11110180b00803a00e0311360b2900200011181d00581e43d110a1001c454100030088110110b00a00b0540312090b0048a003680c2e600b0000a03241c03001041907400c22001c00043c804100804000d0000c42d008101c0850700c01096404528541d01c403100e4004082c3d56035180380d440b81820b22500c0d2201c900c028040c4032484112200c0d05c003208000d01104404100900d82c0b542d0364170303071205034400408010680507018030042c00291039030b4001c41e500d9202d018006800f081103001001541c0c00d031140984608118000c0c40c01f4075000394006402c94458480500442d01403d508004100242c480c500191070660700d40d42e141480d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 925217356 1250 925216106 925216133
    0x120204091b1103040f0b030a0e0a03021e0c060304060c050f030a0902121b040203070212030a0203010603050105010c0302070b030c0708160b1b19050c0d1d0406060e04050c0d06060903 80
    0x890f0001c010800c50001022501030a51380612980c42c2c2c1c07070322040040802090341da02030035924001c006000c001d0540100300c2000c4481501c042d44089000c80c0f45841c1c4400d0f06914265000300180081400700d443c5034000e0f4203605180c2841850500b5401443c426038008039030351a041601d030318070801142055002c0c0414600941c008140006080c015a0103c0c0403507a401401183c1c0070000601c0d2600c0cc10443d11011000d08042d640c0341452046900070b03501c240038200c0800e081500000c0e0742c0d4803c1400c000c24a40681c043e01045040000c0340466903c050601c0e60482c806015031404550010001c1c4a01c040d070f5807030303400c088040d0b00d0007001b0303420700030701060540603120034045024040300c0440b00208a02c04441c1508421070409941c3c90061150340c90041c400c400b100e182c1541c1003140d144810014038141342051801c0c008010035501c49018120002e0445180c1000030300382034019a0300003079007408290822441d480c0c44030403101154443c1000070101c41d020000d00c21444001031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 925218606 1250 925217356 925217387
    0x19020a3309080a060c0e18060a0b03010b03160306320604140402030603030403080c0304060e0409021c0218190b0a030c06180902030a020315120d120204091b 69
    0x880e41c900c2c006000c2e40381c40c0c0038200648200c1d12090001c500500c00c600c0405c0020000b8121400c000c0710303143d0400b0192040360141e0150a6a4070046810203c030401d036412600324812943c5156140700c0070904040d9000d2540090580341c2c031000c61b0080c02c1b11031450b4071a500c19013103698182d62420322010305007400b541901954040000780070781490303804c0ca1140b0600070786001da52074075084040380c46c5100e168406001c001001c26003c030000c0c40800200121281a614040b1050021040100300c40c8064402944106505442c510050300406580c20242c0018405103403945868141d241d03030388041f44d00c0320160507000b03020300c1164014401d034000307000300340ea902e650300e0f0840d540c0410201031070140c1c5c028407003150004c0000742c5c0194402006030445030425912030400c40c1c8041e010390800d07038a60f504401c500748c0e1030b40e8904181c8100420b42902c4002410300b9803416030251481c10740d403960380e03002c1d80c0c0070007001c14160710714042d00310b60002c42400c40c814608103240080090f0500411503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 925219856 1250 925218606 925218617
    0x13b011406041d07050409141209011101020a0903062a050c0706020f060103080c07090204081f1401050103050711070e04050d09140f4209010219020a33 67
    0x280d5010070009442000c4d140180d40000c5c7d080d21500b448241460801030002c0603105c1c0076089020030110402414102c0400e895001c080e64180c0c00d40e40c00e074014419100700254a8500400c0440d45a40000350300c05011501040100350f2030074940043c114100007800850400610509900740400c0600014501071002c0c180c4440500003098441c070040c4000350902d0004504001d0410013802503100030b0088410455a4076581c1c100e598541c20400d40c40300050124145009071500140108002d2102245448109030f0030000107600900001d0081e008000001140c034010b55020031420f0003604860148068514051415524001d0a02c60301000c0203481c00d01000001140c010001201d88100c8691116214080104148245039010300901100c000c4148034203411614241c28800060000343e81c1080c106d443e45c0c29244203400206005a202400b100451042080700940407031004110400c41507a55110704849201511a044c02501811a001000c03070700d80b019002244690070030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 925221106 1250 925219856 925219901
    0x206070b0405061e041b050d0c080c09010506070b091207050a0c060c050307030305040f0609110406060203160f02061608031509100e04020d06021911013b01140604 72
    0x1011800704c0280c40281480c0c0c040460100e91010303826000041d00c00a0182d5402c0305c490304010001044510501132039004036025581181403030742da45810f80360060038007498902103039201840904000c2580001c1c3c0903002500c01c60b14680d1000b04411350041000b82000a61810065030102040d88400103020100b07080c45c00042d03000c002e64200e03a0305410001111340d150b0401c3c2d003031052408002404145032070026010044c0c500f00724410400c00383c408011203a15400183c0c0d6a00c21117030f83c10b20390501c0c504240002604503070002c17461403014000a00b812415000c04007419840f00c8101c3e0304c0b007004801c006180601c04000c3d017008000f00e8072105541031a56440500c4283d5004103049807001d400080e0940d150504040c400a42c080c504550380c041c10402c064a04112808010010704100c910031031a00050107028007960700c1c40c8080c25040c04100300c031100030041d100d0049150b07000e0136588070146003c3c82180743c410f40c11501c034001490074104100484580c05030002001c10a10107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 925222356 1250 925221106 925221151
    0x705130b0a030b09070305030d09060b03070305030301180603080c030429091224160327020307030605090102090a08030304030c080901020705030115030b070f080a180206070b040506 80
    0x1401c2003101d4001c4160380c0240c44540c5014200001a04080c000b4480081c40d8600c0c00ca03a0340c00070b402c1501518041100320b0200c4201521110a4403015005078070520051100e102da9521705041c1e40100c2e140000c0050f517030382d00c0e902a07801082000d1150b800200d0304010056040b80481d19100044104025219142075a500d40d0b00031100f034140107600902c460103220a00f00510203001e40f006080010740c0d050721002007500d020840d005045440c820328081c00c83d6009011320680344584103e5042006030300c402c0204120000c120581e07042c4213019000000c030740d83c1d20416000b014140009a51000f02806100004070703503a00a01041d4010400c220210743d00c041c0c1d01400039803040300f0310340e50120080100d141c1426504a03681c11b5182507058512000707950b040f84120380c420500c1700f07410707901d200b41a5a1018a021640041011180018021083c07648032100c02c120405070020440c80740d0f00480c0e1142c00c845d900f00c0e585a43c4c04240402e225040008540c04020342c0c400304401110402c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 925223606 1250 925222356 925222369
    0x1503050a03112815021606061205060406151a181f120f0e06150303040344091e031203090f06041b050108070f260106020705130b 57
    0x101843d2060580e81d41c00d0401c0740140401a040620000c01d41d1552058288a03410034051a41251282d142a4001480c0d892034500081e40c00e42205c054885d07556030b519000081e18002c18140400108100040341c06012400b42100c1c851444402503100c80907070808005030b54010302224030681c810311010040600003030341110046801d15100c0342003d5924601b8000c3e12a00210712035550408401260036100040c9651080c640e00503521081c903024018075480e0b10071800702806440401010449000e54480407010303103a8000c178518480111000f62020b88207001c03210b00c80c0c1c9500081c5a00d0342c0d14007103410300080225200384d00003a032400300c00281e8841c000240710a40a6000c4001003d14405201d403400c030700350b818203642881c034241c904090b0142400070382c502d0040800d0301c0440c0f69440368000c544680e403540c44102514140398025641210003203510000d04604000b8100348086008404d4002c061540040036411b081c8000c0000000e111081c03030a4903481c020200f100c076955139 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 925224856 1250 925223606 925223653
    0x60311040b071e0203100e070b0c07030b1902041401080610052212030e01080c090f0108040203010b0d030f021011180a080105010e15120d0f031503050a0311 69
    0x794824102c58000c100c419980c40f0080069070602900d41190f808404a4000c8200113900ba400c0d00d400c42d413141040b064a01600c109a0070070b500401043c00001e07400d650080d001415460300705016451007034401c1c140d901c00d07082044840e02d8144010000e503000b010190304443c0c2114240910000b03030500038100c0c0075002001c0154000030044804814030008890003034030121008000c0c8d5810341c03c0140c00d070031480b0703000d9000911500001d4180c1d8800425142c0c0b40c83c0040c0400d03c4404a507004440040024200703903850b550307840c15080b041d900c08040c050014802e40342d650350540307403d40c00303404c101c42d44020900160401c15503c040c008404200c030030300c09841044240355840074004c00c5c45240540c12aa407650710341030001ca5203181c04001c252050710320780c0c5950400090102480b00356074180e81c2c01c43c500d900464001c44894080d824a203008425071600007020b50380481c462141104c0c6074415203203034102c4050242130581c4034100d4000c041c100001840010b840e242e86030f4504166 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 925226106 1250 925224856 925224863
    0x50112050a20030105010905010519060c1209090216020f0303070c05061e0c160609030302030d0f020c011805010506010309050d081f090c090e131e02090c04060311040b07 75
    0x800c05042d1200c1078450105040c041d008100703030360311490220020803003030081038441d40000c00365885110358140c8101c19100c5681d00c480403074107181e5483c43c2d681c2c00c4000c41c03000d0040751080420b4203909440030302290314840d4400c85960390240140700a010000204c540a43c0042100e8800300c0c004241c0360b0304441c4152480e40d91035a01c0300070445a2440310034840c615203400500b48002140020b4003201b0500d0f5440781c40821982c4140640e481150b910004025030406d00c4a8940d43c0700503404a0300c000b00050300940340141640d100c1307086404410f2400020546003440b2410b01c6002d11865a0104c0b0030309041255800584400d942c56015030070804c10001c40500107400d03401219440c06038000800040e800c41750b05c03020017130068402681d243c070002d48a008001401302911030360900401c080c1d001c036003000c0d0154580c01000b1080000300790341850b280d1056001a12203202043c8582d1410803110f86a9041c41c800174151740a6418040500905010030300200030300e042102c07603041d030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 925227356 1250 925226106 925226123
    0x307080c03061e18130b01091a04020c0f0f01020a03060504090308010509101505090907030b1507020f061810050c1c020a0f03050301061b2105070f0c09050112050a 72
    0x7900002800060b08070320764040000a030401d1025509808185c644458418100391080da81c0312680c80c4104c55585501c0e5104001d032030803c04442c1090b500038400e440700002551441c1500c040b0061410300a203207407042c0d9a50005981850360307070611400c0c2c042d040c02c41d810700030300b005514000c2c41e0400600420f4454200000801c0c2103a500b060020000d165000d40316004540200d0007903d980c012507411400b55010700d00045c41503100c1d10072214040350041803080d0ba10884680c81c120346c0c00100c2c00f240c011007a00840d0403103030b071a04098103401ca803a10403c4040b09141081c045149042b90018041c448140400c1c0030109011500003081280c84900141e00782c035804080340341003d5010090310383c403500e07008203042c0f650100003107040e10007e0315a0320350000d452807204285100ea410140803012215000015413070079402071101c1600c030b480c10508080311703502c0c3c3d02140c00704007400b04d62901629130f0801083d2514085e440c01404a08056103856170320b6111182c0740c12807a54010211007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 925228606 1250 925227356 925227409
    0x30106030b01090f0b1c0e0714130e071401020f06040204110712032915070c05270615030a0906110a080406060e1308090f040c03020307080c0306 64
    0x3441000404002c101c02c4031080c1d40c0c3c9682d540200101d50094a500d406c02418031800c0d40c0d050b01d00e0140800f104200c50080c00224540134824a014285107200356100240c44542e046032181c50040041c041c00315001ba000182c5440178031958490f035800c2e480e06640188100a0a40d580030420a91003501a01e01060301c000f11964200d56200f40f00c001045150740000040c00980d06a10040700100030450340121842044e0054041d48050024240d0146030940300c940b02c81d88000140070710520406440f552544c071180011180115000c80e5030300590701680c8080c3c070311440c2e402d5a03005181507415118603100d03c00080c1d001e1000a00c0c502c15141c540e030b240360400c9019031090110380c04107420b0b15110110440c0c01042d28505a40a44801b800c0050100300f00e0303000800ca0340070308910701042610804036520504650840800c096002003609100c0070181c9071030040d140005c94941d80103039640f17081000034203c03070800b80c070505071070f01d02307100300242515091215001c1c0404a1045041c51 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 925229856 1250 925228606 925228609
    0x150115021b03100e030702040f27080702030a032c010c110114030a0f1d030313060603050a0605070215010b0d090c05150715050601020a020906121b01120b06030106030b 74
    0x3021440381c3c0340407924281e10700b003400308040040c105061003101e0900c1070152000c600740503101160b0301c603a01c140e03500d455440c841204040c1c081103240b18181050a12207990002800c1140e900000d4000c5202130761031441540c10284001d0b10120301c0c2030340455038504400004c0c041e00f9541c1005140003060520488568000c100480179401402499503a9180030700c003050191000413002d000c414241045280419188006610300541c41030066045568100507440f1401c80401c0540d42a6a1214007101040c1c0c03e10108020b940146004100c5060070301d0000d00d0003119280b89030180e4114401030200560300d100f100c2c4000440c400c0450068240d0403d00310000855014503480410710400e02501c011800203804114000c103040400c4500c0c094982c03055600480e01d803401038020846035001454074074100c2c2e420a601030181d000c00342405040340d281280590034145006040400542c141d80e0240e4603010a29641009009600c280750100d03200e404180600420b054444c140946103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 925231106 1250 925229856 925229863
    0x30712050d0c05122a0c01090f030b060d0f06090506040201350a0222060e061c0519050a1b02031e0d021c050702190f0b07140c150115021b03 62
    0x2a914a800506000205041665850a407138200c7e0202d594584002400b540e6003102400b00c0740c021118001d60359401d020020001d140c103004403804051207100b90040742d6540b01d9040d5540c4540002c02107806c03d0b00000d0400340000c0031100010403504003041e03038409030b14548020030301303654240b40145d1102c0f5481c101038010601100b004030f0810b01e491761009403c5c600c0404581098031114048444001800203900c00c483d0058480b10b401111400d000c5401d502050b4840b2450000110407c80c1c04441405d03140e040d2000503055841c1c40c46088200040c8138624242d86203400194034012184089802654682070f003130000700030220b1103d1603908581c044601c840c2c1500c60300f140c142414450300e00200803d841000043c8a0708179054004400202140a5190040d075803158081c001d903121103403080b00414210400071031101c0404e02c1c410034005481c85c074504101030030a8100e0035001c01c1d5800c00581c071100c0034500e03214034804480d4000c00c0140400c94414000c403980e20042000c04e15 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 925232356 1250 925231106 925231147
    0xc01080c03190b040f2c0c0a06050f0f030a1a011115060a05060a0503090c030604170705121c0b090c120408130e09100c1409010905030712050d0c0512 66
    0x1030303103406d18481841003114404c0d810842c01550805524806104c42c07041d44c0c0b807280d82900c0c5d40100c1c2c410380074403605000720083c004d0480650b801603e850034401030b552044e001500c60142076038449100b500c415130f06000c1c01702041c80078039045058a981010003070313031003052201499140303e02c00081007003600d0302c011100203000080c126640d2249603580040c903a510480c1d01a956009640d224002858046001c83c040c82d0446d0349190392074603007140d20400c0c0d80018002c645a215074030141045040520141c0551014407914041440400300d281040d20390030301c0c0c80c034410100407080001030b12540041c2c60040e00c048074495019552880c02d488244203c0c40842d5081c1c0d02e029000070b410b2002c02c40c85d4840c42c2c00e4400d90f001e0004442000040d9480c5601483c0410720100080780441002009064070700030501d05800701c2ca0317495001c20304104440d000683c51503805150542440010418200043c140b860444086071842e01c1d01c40c1c542c1c10814415105101c005000115001480c91144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 925233606 1250 925232356 925232381
    0xd020304060e0310061707060309030915030f0519240b07020a030b0c0d140601020618011508010e07060503090a0602160212070f0f08151f080c01080c03190b04 70
    0x200c2941c803003d600c81c6c004088202c020052291850124209110f4003c3c001e06a515454400d1170701d041c00c803415040c0200f00c805000f0503a80b1100d0741c103c150701c0d0040c01c0c0240080804500450001c940310b1080d1400c11929003000a04501080700c242002d0010108840001111507180d585508c006202c040e06070b4000382120300b00e5024001c5e1500d03008000d244000020300c0800c003045c20784c04a14030b101400c0354818003581200c800107070305080d41c0c1d1810030807008901c00015503402481e0a0301c128400c542040b80300e40c1d51040300030000d8034100082e002420a0742030640c114581000120ba0b10020280c1c000c144580208003030094142c0041d20011041e070003880001c00303aa2100400d0b40e030f00307010700c61042000b4007150002607548490341c202080d940c0c004040d0540c5c184003280103c02d4080601080c850184076684401000e2071441f00f80003820985d00a000c210a0a8000421500e000b0700303c0b0039440360810500c0310101018484480c9000c0f08a0003007400a62000040d004204460069 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 925234856 1250 925233606 925233611
    0x9010b21040b0603061005030316020a080307080705010506060304020d12030b0604180f1104030308100b070506150612010e10150f0314071704050a080a0906020c030d020304060e0310 80
    0x1008000b030030a08184501815012181c45079140150710125003068400c141c0c140d0405c04c400796032007044640821000340040c000d0001c5503a80c241d403c5c40d591100c0b40c00c0e10201e02c041401c80c00c0110a020b059009007048070030a04606090f00020301c22800c0010003003407984800c44450081d4023a4110218594009220301d48803580c440c1d15005c20101c1e80000c444086c506204050903042c0e605c101508004403d80090500381140d03420f8902160142c1300d40f00e4004580030004000007508001d00311548940042c150905084041e0242d003068643c05501c980000e210340e05180782c40d680783c1411182c2c4021003940d40e495410440366080e283c4d0b0485650220b040c07400c50902c0d50440c50400d44122141d808001700c1044c0c030350071102c06000f6941e020000c4d1111030025002d648018030369402034062020b6884500ca603070303240c0c40c0c1544406c0c1d40100ac1039100c4c004104154051200100a070b0301600604800205040029201c2c4982c1c010322060281c1483c40561035142000504403e600f0103208 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 925236106 1250 925234856 925234861
    0x405010f0207030c1103070b16030e06030408090a0e010e16260106120b0d0b180a030818150105040c0c150923060708060f1e1e09010b21 60
    0x7040c0c1041d04d241980c1e41c2c00341014071945804c0016045003190b1200b80c0f90303802c189104c51602c030481c507510000c0d130802ca24002019016030303401d0b0096000703c0c0314906041e65411840c090060305507080c0d004c012140d400304010000c1c01d82c1c4409503a0312030151400c50281450628083d00c0d10214003810010300c61450550703074600490044844c1c1607605503120400c00c000080201c81c183c9401038200c80d0042070044107200014510103c45810242c80388030b001ca0704d07a040c030046103010308880f826000503400905100d0700880c0100d207103054440a4001c2c0c01c0b000c4084d000f00c00761000620843d40943e82e46e03860310394410321076101e8060050f40004c220710542080d00701c2e00081d210200c01611800100301840411100c58607942c1100c11200010388001e17030302c0c52002c0c0e0381014002d001c5a0018511000c1c00c41035559610294410381000c142d920018072100144400300c07d210481c0c7c00c061426200c88441da5680100d142c1c1102e40d03101c9a0f6039030390a190300100b0107a185030300805004600c2d209 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 925237356 1250 925236106 925236113
    0x1407020a060e010204050102151e04061401060c0b0609040201090513050105190608070c290f0a02130e13050133030c03060203102d0806100b030405010f0207 69
    0x201910240e0003501d09001420303002800a08038811131140c10b0250303020030804180b16035201c0d801544240d200c04516855004c0c0c804d004000c1c003080750111155035503007900814014846c426940076006a11384107510304155503548030142009000c03148140e0071017001400f168414200003024140c00342003061210840c1d5402c8020304005c0c01103074400e0031618070300c0100d13140141240b0100c0b08650350301c145c1621204829a0602108001543c0c0035441012034005103200c000b01001708003001401c0301e0f0603c2c000440754840080074141c200c2c02c900410015490240d0403000e0002d60310009110410758840c82c05285000c8119403000300203508000c02c8807807601880c0c503520707440c0c0c03500e510780c0d010441d9490031458403d0381c0e80801442d10f410700000341f001c20125805583e00014040d0340503909500d030b6200d401e10302c0d184840c460081c14032030064100741900e0381c4000020641c8800070816410503064203880e8175660701a80250010120024003030003801d4021074084945090110756800e19400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 925238606 1250 925237356 925237363
    0x6030506010803030c03011a070c0b04060f0305090c1302090d0b0f010b1e0d0902150d140408030f25020a0201172a04180b0906011407020112140702 65
    0x100564580c011540000368840010046034442c503c502e18035445d43c2e00b4035607094883c01070160302c040601002c4c03124400158500d0382d0a0042c1030103000c19919145405c00092103a032400b09074800701803c0100b03001003000005045e032441780e0100c4462043c1c54540003858000d0142d8007046a0200580350300034140200c071304805014100380b82d80d4089a070f0300c0c1d0440d8a000d206075030030242079400780b03c1c283d40c07128413000c042c00e092015003101081e0324140e50002208148003501c9007107910340024548501038070070711661015041710303600341c4d15a02c0c09880741803171808002c00a05030a00000000ba50b500f102c55024440c0d803218a100b25411031082d00700030341d201d104840481c04078091100150915621040d418480e4500340000c46085c0302380081c4041d0005102540e046400c000d0001043d04450188094241406030500181024041c1d04028401700050036490610215848a9204544980446800035020b003000c031801080d4005040003458000446904226a081403081c05580407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 925239856 1250 925238606 925238609
    0x18031706060d153320010e07060816021018020a120312020c0c010f050d18210f0e0f0409030206100608010b07470a0c09031407081006 59
    0x31305415113116400e032015041034404040b41e000e011402050740c44180c410710040d050071924005c10324001c1079244031582910f00421080801da048a035041c040540d101e5512031348401c051403031024102240034069151a009007501d038100d51035880400341c00120103944c030380d03055010746641305c22561100704129002000d901140011804036031080114418000d42c0d504401c15405031600c080078000540d140502c0c2440e00c01842020701400d40d503d10548250038074140c9100b4420110b80080c5005090b841075590b45804101500c4050b6a0040e407200d0192040180741c1400300c0c021107050002003005a080303401c0c6a01a0410440108040d0f000c034409018800c1c04003c160f555031194801d0b1a10b000c01d0103640c900701e1050104001142008110342a4440300351741c9800846441d8000d100f080032034114444042080300f20718140c4440d202005540035030400010030010000392402090000c00d4803018040e0204110b0f4030740351031011b02c4404020074840e82182c00b00b800809040000e042903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 925241106 1250 925239856 925239869
    0xe060403020d1511030f0604020304060f020a0309171822020f1c050402030309010c020a120503030105100e090406090303023c09090c0304140d030f18031706060d15 72
    0x50903c8904582c8840003174038060080188190b80c1d664418007400000e400040050b07400b20340702c00030501d000b4080c0c4010213020b81c03190b601184c1000c060034800e564048003480d0744064202084420014041040a500d50b40400c8403003994200301040e5205c138034103843e409156a070380b0001c1c1ca8240c201d080002014440d03005800b465004100e12001c0c0111170040303a01a406802c1001600a10340c49500b440d920103200138411808a915015224214200640216855880040180028544107090b1007003e003040c0390a41542c000007000c58610540a040200348070f84a1080c0020107010b03405841f40401d04001c00103048207681c20680d2207074048031103069002560703007005050341c0c0f802c012241203513000352681c0c803039490322026001141e0004109071035080240860820034407003807140c0c100c80c1943d981d02107901540781422004440041d907001002c01310440c502070029420290110710b10380c003810b00601d1581c504010a44030301c68140580034040ca4941098036030300c151135100342920380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 925242356 1250 925241106 925241111
    0xd020a0e010f0e0d0303020307051c06170f1b0a0308180a05040b150c1501030305090108012c0421020109051006051318140f0d0f0903030e060403020d15 67
    0x1249031054a560154004030f90300a03001102d40b0b00464065002140c07c10344e02d1401a10704040c4000d40c614440e040a40c200702c654941d003040050300d03841d81c032122042d00000040c00709520310306551540d03403c00215000c8402000c00d00414547d45000000000715080701d90302ea45d503004448840d1001c07143d1b21480e13124810a68020407142418407416140c044054044030460010400b1f0088a800040e09680035100e8540740d010010384030a0045d0081d4030030740310251240c1600001500007801604041001c081b00424801d40ea0b0034011940c85034824007a1421058840e41040124810004402a070344e20480d0b01034500d140c0e0562022011034016002e484461148a2814042c0c894a21803580c0c00182c0300c20f02024446544c3c4001c803001d040d9151044031411550f034010002d0070719404a40c11b600149070f840d443e600d003400101c01c038034002e142955162000c00710142610450307000c0902001892041c4408036203400c0201c030061034000302036800d040250302d0140c21841c0c0304101e0048150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 925243606 1250 925242356 925242377
    0x314040f0c06110705090c04051513080a15050a15080a02040e1519060f0308070b090120130305060901050117010905100e0102090904080d0c1b020d080d020a0e01 71
    0x10300c01c80c0c0c541c9124143d40090082c0501e014100421144054101c0c0100f00c402c02c000152a5606c000e02c9001e6074a290341b403610b484002c502590310540941c0705042540009803220001b4440d1920100d4083d0b411100040980312901d0081c01000514140307011185616008a00a00c00180c8102014030803101413119441140c07159844900c0c150603210300c0160346003c60310280010081c407106003007803900000c54540c1d030b080c0e4840140c502d901c03d80d50b400c0001600801e02120101d800da118120600030b000b1a5180b075442d40d00031220203403140210b01c01150010300780c4c580f4030740200216002006c940c034a0510a141d070780242828851038a030705030318251400780b101040c02507a0606402002a0200d04403540d0b01401900541510b50043e560070081140944d5928204a001d1030041d000389454042c4086040d0480324204d8600090100640a60405807400d510b6448034581c141c521a40c05880c40c54102502d000320301c1c900e04580c2c0041138003001c035a801210064600000d903200790303761 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 925244856 1250 925243606 925243619
    0x60f0b040216021c150605010e180109110d02030405100c300e0f0f06010906030f020d060209060706090204110702010f0819060627050604060f0314040f0c 68
    0xd11070a0ba2010000420100d580e01500c0c3c00e00d8a865651003100f811001030303400b82d5400c041030180c0b0108103c2e503561240300741b0841d40d01c01c541d0411281c0956104107ca10803460600514105105414540e41c480c400c1c101196541010b49800191003281551a418245841d9440d50030750042c0b450054600010f54070828440d0f90094203107601d1165941181e0b00d042200e004c84064018035101040d1640d8000c0c3c1038035000c001c490103224840d000382420103055407205003001410382c0207007009410b0203400c0c00400c082a8540e04103580c1241e4070643c1d10020b14000029000c0c240001f540704401083c5e0380148017041c3c01950010740300320b50400010141024200090045640290010f141099510021801041c034641c1018000c0306071f6440d01600070890341561420b41050703002074101080c025040a208100032041d40e840c0005400f182d080a010850900482c402c50040009031085040814041d42c400005044009102e00310ba01e06030905d51481880c8080480d01144c0450300003801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 925246106 1250 925244856 925244861
    0xc12030504030b091f05070e091906082805120a110d050a0804080a0905033703050f0a090b03010e071b02031e0309041409070b0f19110109060f0b04 65
    0xc0010140e00c2c00340c85c620140c9000040c00c00821010a020015030340704082c0d55400480c1e031090074607400401c0306454042451042d940c2591001d80780b41d10010400d01052800054092800e403042d101c0c82c0d0042d2107090091502e0352110403910035400000d42103c0340d03648220070b50340a2100c03000311443d016848004403202d204030b20340100055402400b08001540840007885180864a0b00c0c9407101d4a8100003402d010140701c40c018076100d0003c4000061141800380daa20321250910b40444a540d601c015009101c1d1500e2040724407030025089101c1c1d0b0103020544040c20003190450303242e60311074000c01440c20058a00070081490b0130103034030000b000000002401039010f406009000d101542040d000c1c0c00c40c0e5103039001e40c0802d218981c1d1a441350f01c154800f80001d012015020b0415096441c1803e8203034000c0c00480c0410041c84048941310b50850720a0b101040f034411441c4021b000c00c441a050080607030ba419400c01140c1c809124150704940040c0054010402c5082114002c000c00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 925247356 1250 925246106 925246123
    0x70f0b0c1b0d062406030608030909070912060b04061e0b160b1302011e020307030e0a05220c090806061201090804081c0302180d0c12030504030b09 65
    0x806501c0041d01c1d4125440c400100890540042c0c00c4112000543e51483e05aa0725031000e1043d810202d880384440d200c003541d0010041005007030800543e0305088440383c41c0d10808070594000c1000001066200f8440c20b03010000b03241e488409407002d281440d020b0f025181d43c413481380c400c504042010502c4074010b040640706584402406a03082e1030030403c2c583c41e03001243c01540c40c2d4180c181c3d4001142c82080090700c14506080f0401005100340300141200c0301c4188900340d6003d08005540c81543c00208560743c0caa0141030900c6510300250010308042e016400c803079040100c010070640380e40b044c140540c1072a0000c0384c041c00030303101080c0100d40f042420b100740b4032139a102d400420030301e05006127004042c440d42800840e62049946070980d4903801584139480603840240300380c0c41e44207696840403601c00d4604d0250300d0860340c202d20b01c0c0e83c004111b00e041e12401280c1004c2c410096500c86500041c45031495400f80c822031030802070400e41007444280da00e01c14000009164a0010580e01c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 925248606 1250 925247356 925247377
    0x9120d1814011b03050c1b0a060201291f021b0303090f0904050a08160c0501020307020d2901141c0309060c031101020d0905011a0906060702010302040b0408070f0b 72
    0x384550f2243c1041d8070368004404098050200820010f001d041c024041c0d40c590080340701141c0c8804024000344a0300c5411980400c045924022240d5103501c00544009100030500e02102e021001d01c0c000980960400c28541408010364030300c0302e40d038035000328010301080c400844412801001d2014992203208465444e0381c800341c0c4070f50345030340d07807400c040d41c2600180618122100d0492561320780825a1115030140e0849000116140402410350100000740c0020b201540c14140187e020550700e030070002004169282c0c00324800320000809650154101e15011810a2940d40c2c1503c01035407407210ba406d074042c85a41c4844040a00e40c00c119200e801d60541d50306580914005044400914840d812402c00c907001045c500d4005c400d0028200c180108800040d50401e42c0c500b80d0b0840320b80303a6040c00b60240d11161050555200c0412590041040d03c042d540c8a040d480100c0c000d03ca660800f001010002c94080b0360302000040c02d006964608040d0340c03055032074440e0388550b4003c504618 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 925249856 1250 925248606 925248617
    0x5013f05070c080d09150509010608060108032502030f0607030b100806030a0303180507091a09161223090c09041e02010905100c210206010b09120d181401 68
    0x10000500c1940b1205a141c000c2405020320150200c0010035587d00355240c00c1c3c181c1d150381040c0302c400c000b40b1000d40184600c0300154500448140fa00c0340000d80c040e01c08503c0740b400441d1000b5500e050218614000f02401543d1580c0740956001e070003000c0b6070341040c0c090317154038598090403401098103d0054000500401214440d40e50803006840d480c0d03136100541801d003c8013400a502081381e0300c080d00302e0b0840810100101c102c0c1d44c5104010090301445140800c05020340d00100c2407a800401960345000380000502060b40002b030a803e11601001c28501d4604103107410100b41f03014000c0c1e0f4060252088001d6103810072006a00a90303000e49291014001861079090a2203042c48040c818100900c4041c0d450f00010209040c3c6e803146008500100b00203801c0000000d440554406585110301140d650004000d540d1390b414050060742800002d0303030322059590340d1b01d018001013100d4102c1d84000203001000307015030031114806000c0340603010003041c00c00304003103950b41031501030303580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 925251106 1250 925249856 925249867
    0x41d15120309040513140d170103350f030414150a0b0d0b04060213091506031a09070f03111206010f1404090204060909090c05013f05070c08 62
    0x1000b00130100509001c140c40501c4c401d4400007461a450038400751003c001804207000c002d140a0007074030303030220405030032280280103000052501c1c5074000810780034404103000000c8010015582101000c019001c203c000c101880001459001544564880e034202c0c0c0c00147d80307011203599020b080c00b6604203880c0040015071042c1c41d951185c1b80c2d03020300911400e81901180c45540301c0c00810f171000d83d821a0001001d180390814045034400501ea6030030200000080b00082c4600c0d1000340c01034004064484031203903209005e080418448240003085100d01d0308144070082c01c560b081c1001d05000c01d00f0410101c4001c01c1c48400e607041c0c02d0508d18200503607135483d4011959225641000020300006420f5844100c402c0f1010700b02900201d080181e855003464000b030200c00c00b0358000c0003a5414650540300140b0800c20410454500f8240f240c0001440061400100c84408481c00342038124450903140c401d40c10080c82c00c26601f20410815601e41e4402240d030f00401d0b07600604040d204104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 925252356 1250 925251106 925251109
    0x1d0703060e0925030f170d380a1509030c0e060a0911040b0912010608012c0c04021e1207030b1906050a090801060f03050616020a030311041d15120309 66
    0x6041208031402464611f01080500707000121170a080c400c0041e240743c500f51455110701c1801000a14048509100d9441d5003070000921829241c080d59081100b01c410744100d150280c00214040c4d6848851902c881d612740d01541c45100c4110b41003841108040380002e215806072003844007829160001602e007908000804070540d2040d44525001400034000901e101004e120702c40143c010700c0004a00050b40b5600388121402c0d0722640d41010940c0b00600710100d80005854080423003c0d02e0140c0c032510702c070009040300c5105801c100200800021006001c00b8200c80c80ca1068a440d10300b04240c580a80034086e15800e948220b030340b0b0600700c95042c080140a10041e0000074801e250140344035484600950070340744103030311041082d03e04031800d000f04041403090301e41c0402e000c00c0340c1108145882009582c0c401d40003001d014140e035001d21180b20700c8543d0840f40982020000740410403e007103044946100300700c4641441210184070080c55207000154418400705000055051000120 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 925253606 1250 925252356 925252373
    0x903051207080403021201090b09010b01171005130b1c021e0a080109050109060c110601060503090102130806060f010f0e06030a060302210706091d0703060e0925030f 73
    0x60142ca03011028000000160b89807440115a9101d207400800c2d00b0300603107000c08800001411105c0b559040500d11605643e000745c900d94a5103000032406c000d0303100c40181d9002c006040e040b4a40001da8822100d00c1002150004006001c0c15103244036114240c1400c00c41040391150004d60081c0700e0244e0413031181406411217821400200f0060b400c1b0350b2180310900311281e2a004aa9503511100700f101403000c10301c05c0b25044c500c01e041c00c1d499220200f4085448000c140110400d105000c00414a081c0003541502e09a014052041011507160b040e4240e842c0340c22500c00d0302c51604006a01d8641d440354006216149041d150001411048003c0180710780005021503102307640c0340c03000030142e5034403003040c0c201821300071040c031040800c1d0001506281380e07900301600b4805028400c02080000e00303411803844078210006065900c40401c00c8000c0c01c0b095100008101c00d45040c01024100030801034251030301000c00301c104d0012000c42005038407481c4009070401d0001868034011440a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 925254856 1250 925253606 925253617
    0x30a020a110f1b0616032109060e1e061512031908090109080301053304061101060f091112010b0403121b08090a0e0109050a0c09030512 60
    0x60810741694840112220320341011028490800e902803c042c11440341000542031018005032000e600c2c01190400b446942020400d0007410080d5181d403d044695480040c804400c00da58018450085179003040000b41c0038050f0f89d42d0a90003a882c40c000c014204050b801034000c411006030000b0303a1001260340c810791000c031105401c00200340c2c528090040501c000c0c0107a000920b6240d41204850070003c011040040c0444402e070315104d031143c003042e803683c152030454400311000c0701c201d000701a600142010000e1209112402e001e4004111990600a081174a607542e035108c000006800d0f0140c00c1e90924490300301000d1400351f050218000d6508000040c2c49005140c528001454540c4605184268880002c0040215003031040004278444114801014070703203609010310140322510503564a0350f00500351040082c4402c19034580481c1c0400401f28600407503001d6a440341c048001d007004440f10522186001d590341200ca00590b407400030380c1d401c0070042c41e6048480d1401a420f5001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 925256106 1250 925254856 925254877
    0x703022101090b0f0105030f07090902011e030506030f03070c0b09031204060f02101a041e06060c022b080d02090a09200901120b04060e0f1f0b030a02 66
    0x8424186a80642401900c80c0c09114050f0b4010510300300c50210102c08042c0c120ba0320a80180f07107410b40d4039a002800c1d07402d0f40d140c2c4c82c00191022242c0b00580b40c00043c0c4d4111030602090860304c1000d250581c0c4801e12444050741130740c3c200c00380322250035140d201341c0c0d0005110b80034030802441111242c4028100030080681150f1741280202c0b5000f1490300103078414400a01c48091081b0303e582c0c1801403000324112954240f00180341480b0341900c408050b004180a6030352140c80003003503840003820510300030303103071108100c050b0710b5440c000d040f400c10301e10a038025015800cd005058001d00400b1054030b0301c1889007003d10001c0d1b5a10703c04c230750207146070080c02a02406444916612032030440000c0c0304804001540d040c20440d20309402807030210260090340140705040d842e0360070000c01071820a00090000d04510020001002000c40c1d8004d000823185410030041041801908075001c1d48900e44900300381000740100710000d0716280030341103400c1c0c01030000c03c0c449582a0050305403800c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 925257356 1250 925256106 925256149
    0x7030e0a08030a02130806011401030501031e03020705090106050a11070303091502010e060c07050d02010b09060f041121010f0b0a0302031806190c050c0304030807050a0f060204060801060c0203070302 88
    0x1c80d9217006031480c060300302c01e03940c0d00b0881c0108814070003000d8640c06150282800c2c407442d0324603280d01c45502c1210300311002c04080034001c182094400d0100c0070203010000e00400e131075612210000e2568006100c0c550126560304a40105200d001469a0480e0f42c182c1e140c41c1010306050340780d80c0c030360b0131011080190340d00c0c1d000090340c1400600003030b0b104820455005480b041300b42801464010b003081140c055902d010703082e0501c2e403030b00114280e0240040d01c248201e8003507007003c2402841c80f81d1032420303400f4010401d0042d840030405e0352008ea624510b201066a6282c104a04a001343c6108145150008100b00b02c841402034001d103610400400040c030800300030400312820914225000100c500a00c80340c04030610f064880e40780150003500d049400c2c000f0204900307550307115502015000000210303421041041c200540308103036500401c0c105c2c070680540b07000006074126004030001308030f40308004504070348240701c01218290000c0051225501d19001e100c0e1070805c3d41545e019420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 925258606 1250 925257356 925257367
    0xe0d051038090703180b09030c030c0a121d1509032b020a020609120c0a14030606040c0804170f0a0e190803040b0d27060507030e0a08030a02 62
    0x98890078024400515000741d00701d404520400c030480400900d03040030325140c640503681c08004541c00061055000d9020410b5444403910a4070358000c25400d03010324031001075400850600801c0d40c80089109035214128a500e07d03405445101c541c050701084460f1081ca890410700c1c101d161070f4092400102c1c40383c90040c103103000c2421728140810004017a180220600d003244500f124a1500d056a8400341801080550015026203c2d0b004070713034410f09614407244100c2d0001d210070184034030000d1406a4556854105802050721484068820f0040030002003990425005058610780c03103a4a0748120382d43d036035807070029941c115100812039005021264410145c68010540f40c030345512041c804491202c204005039180c050101044440c48038200f0040e1000030a0b03405503869042100e4949c668212858010304030503803071034803500c002e0b0a2180040e042c15203401c0b00724041c24060083e07032360303103001501a20980e082f405603980c0404500004200306002464001611640161408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 925259856 1250 925258606 925258661
    0x120908090d0614011a04030f08160f05011a0a060c32010509010c140a030e160801150f1a162f060703080c1204080306010e0d0510 57
    0xe080c1c0e44121951980d81c1a090324281030691114010702414003465807000c240290520240035520000301148415555441000042c200341c030310490340e0124800741c00459007080c107613103110078100362001d510300b03080d940d81090216018201d0941c041c0503044a10300e001d40403900856005001c4c3d40e01d00120345183c5000300c5200c84648007981c08162202c0d110030701c6081c0350840300d02410070a01030389040000794004d9000a60414480d1140d641281c8a0b42203803810380180c448003510103a0760058901d07052885002c1d130038000903a0b061400800090780810000c601d8403d59004058810742e01c4c8204019840480309600c810f0044141f1003824084408900b21010005100468040b4000d20b5650100103400300790000c1013402e803450b41100ca20900200d1404e210b0a000070b800c1105d0380002070328a0b80302c182210f1011000785940e810500d014240003005400665034103002556452a040840c5030119020403000d4000000c1c1c49002c2001c0d07601c00007000020200c001ca258108200c0505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 925261106 1250 925259856 925259869
    0x309120504060e060c0d050c1509010c0306080609060c0a02100f020d0c0f05160c08060f060405061203040e091e150606210405030f0a03061802030712090809 69
    0x1615551038080d100d03420039070003800c00881c1c003e206010706024418004c00304000070742c80020044904190b0b60310501100011300308075410034400c0381c00c01041c0901c9080801580010389031b40c080d983c00c212a0703845859040d114402a02c0c9003549a1081c80810812001040203042d5a03d09004031110307040b9000000b000da8103004544040e1540c00b00d03d001c1584d10a024287c0c0e000e5003458540c01c4005000d034017030b00c20b01441c2c010107507144080e03140c48200309c031100c1e810001d804040111800e80c039110f10020350340344c8216200781c013450401010580d20f060800d50900261415005103042c42c1c03d00c03866924440c4014050041e034402c1d2044c2d10b80040d01011480407000c5010060403044440440c1e140d61114090146805141c04000171044414050304241c001c810880180c1d10a8803181001d910391300a040b4209100540000c240200a4160313000d4070854403031000e01000001d0081d0104120300003220944041410b00303241014540280d0b00c1050700503c84c00801d8100007200d40855607 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 925262356 1250 925261106 925261133
    0x10807080a0b0406060806210616090b04030f020a080c0d020f0d17030412080c0d02070c030602040801021c090f030c03110d030b0f030c0f100c1a04210813030309 71
    0x11418110a00001d030614007219214045030741d03231840a80700003446050f80d80741c000f80203404c2413504840000c07203e4860501340004209140a00b074a50303880f818480d640303d103e004100d10892102c2c0c00010010b8000c102c1084440004242000d241d456030280440c401509140c01e6000c05180c0e0390702c0c0090141000c02da466110b000d002e03520b9146c41d182170000301102100b03540510042004210941c5510421150b0b80c5076105009601d0392911310307252110001503000108210f0000c0b401041840d415030281a02c0c0c5001c00e040620b1a0301d10b5801411281e0181c03000d030a0509201c601400320380108007260046200749000c0c0c071a84141001582041c0000c1c034042e0000762280110303003aa103405404000d030b150040b0090328803142448006100140c83c10bc2c1c084c0542032010303182d05a1802041c4212040e608a14a9421000340300d100704e94088040300c0440e42555418980740c0090b0f600c2c41c01c9011000c064407296036a403150b142c8801d82455a41c811400c06484003e4200042d400720318680 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 925263606 1250 925262356 925262369
    0x60e04031107062d03020d050705210613090201140f0d0605060910030e0f010f0203040b100b030402060304080d14010302010908030a020303060f180412030b0d02010807080a0b0406 79
    0x1ca1008503844502d040180c540d20a008001c0c03690012844101c00020b1001000c1d0601c6404603201c881a105801a0085030030354482c0714540010420100d80110040c03120300d640c000107801e9500041034041007050251111900f02d0b0326040d916122140503403001a031140141442400c0405503846048681e105407401d5100c0308000c075046442031190301410b0040d007000c031000360618038000701085800a200e41030004140d00d8110344240310308207109401141002c80000c0c04142d00c0810310b000654030988044a5070034001e800074110903003d60804003910448250704d031554855408001c0036070009401540e070400c003000940f00740700e524800c00e4020800d0b18100d240070341c5980009081d01c03155510a82603a0420080480d103640e0110441ea41300500f120408040c0241c2d8001c2082e120850250340c500c10036507420320040c002003a0302c4100580c0d26a07802d0042c03018a03000c8c030216042d8203000174003150b00d00c4042440a4016000f00394059015040000c1071a0030300006415180c040c1e0045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 925264856 1250 925263606 925263617
    0x7020d060902100e100305010605161415041a0c0d09021c150b0301020a0509040e0a050d090807060302090f1c05120703020c041b180e01060f182601060e0403 69
    0xd0002d04100300b4811805c02e490070300300295850101301920910842246216000c01ea060320010403001440c0700d103040001c8411100c3c540b851411301e0705508000d68080d902e900c190358494139581c3c45e0b44046407044030740d8907005042c4000016048040c0c50004001c990000c0100030400c005080c0e0a04140380e54012401c00018003c141407400c21500c50802c1d603030083c0d004101c0e14000e81d8019085030200e1006590014510112480130b0b4201090050000c26030302500415079025a884005002610072403002e545400e0340c0d0384404c0d1b0403442850061074001c040a82a60200d01d0140c2c555a800320070381c24800d0710945655911410050700000c800b4030620046080014143c0c100266841440162410481e02c030150004a01e01c1241645410030800c1c80c0700ca0500e00b008030f458200040c600710800d5402561500c90140c82501044c0816000075070442e4070b1000716800000941c1150f451035941c103104805090000110403084651400d15901c5440c0040c0e2001d410030b185100328040d0743d03138 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 925266106 1250 925264856 925264877
    0x1d01051303140c1209130504080405060d0207080307050304020307060207030210050a0c0f120210090b042901090b100f0905130e070e18060f0708101d070206090d0507020d06090210 79
    0x2041b042c084c109092a94051400082200050b44082200c050340d40484545171a18120400301e00070340704e00c81c001410148003005001c402900034003e540594030031019501c2c8151a0b1000700c0e6900c016120181d4846000094008100d020b000201560310700c5142c9084040c00719103500d0452090b100f4226040c00e608a0b451240a07410702c8101c0403a550203900744240c3c01c40e911480da48920152019207224201c80050b00b10170074010700944040c503002048a002d40e50340c0b0148008104482540e4003803e000c2c10f400c1314061003511000f020441c1034440d44006c0d0704100034441d0380c8002c68042d0842c1e540e07414031503001c9d200c1000404020716090a0740d240601c1c08550000c8021540c44800e00c440d440350302400b41c0f0244c0303461000d510100913307080c0c1da15911402144a0f40c40c181d4030000c091461804020040461807600c070703200d51626002c0711443e032102c404050ba1642030040b8480011801c2c05071200601d44100030010789401140c0114003030715140c00040c80766890008900c0459820540e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 925267356 1250 925266106 925266109
    0x50a0308010b0a120c03090f0c0515090907030e030c01060e0a06050402070309060e0a0b1603140414090406090c08070801060e0103030819090804091d01051303140c1209 74
    0x400ca405090a060940d04005943c480980100c8810612500c80b58642001c0000d0b10b2007544040c03041c40d0004084203442c2c1d560308010072004030b54021103018003044001c5031a01403122044601c0080041c1008941c7e9a501808070020035036251110203074003040260f1301d002c1d4001d002e581c0c080c21900d0b1034003241d400d0210f0024221000c0c0d6201703e000c0e0380103100c080d01280d04001100304640c0c1c1410008000c1409000040380d060710b40e0006500c102020654036194072100c0c0e0341401c000d100303407034207030201c2d4481c0309980300c50045c1d02c20281101481d0304003206a003403040b090340d0018480c07440405e0781039041c1e441000f01c0302242c02401040d84400400c20881109000c1c41008000c13201004031194150f8800401040e80100002c101200310039805100f21880c2d4456a80c80f504840c030aa103450715041c69001400c0700800076000c0c0c00003202c0d00c0f404840d0611400c0e000359a42c08204002d09083e94060b43c889a52810b036000303440d414440001c6031001403182110145074030300e0f40c1c2c2d0b03640000c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 925268606 1250 925267356 925267367
    0x6010f15121a09060d0314130812040302030c04050c0301171218030d0809060a02030403021011090a0b0c060a09031713061a0108061e040f06141c080304140a050a03 72
    0x3013a10744154100c1604a000c00c0c2c002e54241c094840c0f0340314095803400d80d0208240841c2c202e40c8414180c0c4202d600b0580b103001184084c2040c1c0303208405907070a04140b40c0801050301d400390354018180b5003c10040102d110f040e030f030400200c90384009031000d00c089200843d5075a0405803c041c01c001c000b03044184246000e103c00010071502d4146890181440251345588110080ca51982194004080760602d4001c0280d1000c90714070503424440e4030403502024500303802010200c1d009054803140802d2041d4100b041e00e42c410a504001d040c550b550701d4600c0003811520070709500f44403030151004102e81e0a031042e81c0c42401001080040e01b541e03882c00504850a00340140804010050000ca00c3da0b03100c1d03501c1d600321008848006080b08411900d240d08000800c1e2260300a14101002e04a441503802c01000ca03800700d21a04010701507901030240103027030290007418821710340025500042488002d075400501a44a01116540f40e480151419668140070f40341360b0b001e21901010194042d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 925269856 1250 925268606 925268611
    0xa0b15030601030606170f100915172e18060203221a0a1b0801140a06020703060515090906040506012103120f05180d0206010f15121a09 60
    0x14a00800100c1e8441143c072626032001d41003e080f038882d01f011643c841c0070540c00c40003411001408009011281c02e00b01441144e6100e40440070300c038007603940380103080400d92100c0c0c2c3ca01c015074680c2043e24810740100d030300100e500c2c032913405680c0c1940c000040c0d20190498a41c603c122001a43d9041c0300b403000c806552100320214031003058007000303070000e03071040c03001c4400000002e0b505030141c90f00c01303011020f07208450025820302100c2c0120015550700401d007074100d0305511510a0120301030705c18009030090314080c00c00960b12401c0b04000042d6143e0084e03a008511103540d90f00c210118002508210302502c2070085680510180028070105120302d038010035070310183d034400320095489645550324041d405002d00102c4041c2d289801d407160014401440d91403010090740c94171100400c0e0002c0d134030a4035807440c41682d10b695519800011500d050365005140c40104501e03011604110030010300c503580400c08943e81d11403484882e401201007110585012003000a402800e004640100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 925271106 1250 925269856 925269869
    0x50615070c092a0e010c140a03080f0c04060c0507080a0b190e1f0e01050c070b090c03191b09270b0402010c031e080f2d0a0b150306010306 61
    0x3644240100284091071000325910506004403c0744c080f00058400314102c3d40040c04450826030644806140403035081c0c0340600c03d880301e89542d21030303008982c4400c90848404031030600800040c401e1038000c030b440b01000b5204404840100e5103da080d20301b80311950354115000016107003401810f4400d0401c03030401c564034500030881840e0901159546e205036000c0250480a0f02e40000a051210780251004030a61002070080c1c2c1040c0c000c108499001040650b909420100071500300c0c003001ca96000031364070080050400030f01460b0180d010044d28034081724100c41400c0d40f03005010690741c1c1c1c48005c0065403000142d02107e50140030001c14085401d80c100000c100d407400002e10b4102c95560829028039101c3c103800035503d410344010306082d0341c440d0b820100e09044039819512032081c03881010081501c0800d62200311807004107411809803000da82c556a020b180780e6501d00300e441944181c2182d0041071888031034000c1800404c48c5440d10392030b05070000c10030040d5601401500c005141c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 925272356 1250 925271106 925271141
    0x1061116030b010f080114160c141b010203070c0311131416050a09120515040807061a130e0304050d0804030b071404031101031407020607080c030c0409050615070c09 73
    0x20740109034800c7c80f004261494840c0d000e00c00c9003010b0720562101c60242ea0051803034400401c4c045030305079206464454404002c14050908540e54804026507205541c866030544001c1d08603a11001024002c0b643c0c242c0155410b0340341001e00300540a03015200070083c101301454107100540b0346c45002c520803440c040c440200202840258403003055821940d504071161404400ea1401383e04021003035041580d01d00700b500901050210100003031542c1c0d4895807080145200e9002450f00c0f0040d000103080e401500080b07820385005440e001340c7c5c160b54a034400da900d0301c0e4885000641800d21940f050320b107103001050502c10460022001038028001d170034851280140c6800092951140c0e003c010644064810314805a074041d8002c0441c10080c0f000e041600d141c0000001d6071114200d68000000f22850f01041c2d9461aa00480b030044c0644c83c0b201d440e150400951002501000d09100d420140001d1040121181ca1000c0c020700c82c454045041d200f0f1404c4840410703519083c424100650 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 925273606 1250 925272356 925272371
    0x20102070e10140a080d120b0406150e1201060f030302210406110111030a0516090b0a030b011b03050705070614090909010b040f0b1804050601061116030b010f0801 72
    0x11555040889480c403003d0704055200c00d0208030100071030b901c000007a01c65403080b00e40c40e40c1c00c540c0c8072003019807566080011801035400c0000f030b2007091013001080d0100c06c805000c541e100348258504444090240780107203c0c038140c070508440c07035548410520b030f901000134800c040c0d061059140b10042400b50100c120507039188188180b245100d0102400120302d85405000170a40000e0b1182e03a01c403100b66200d117410807944014040817900c0070614803682c00c00400040c0503a00c1041582c0c04500c540d0b04000c048802a0020071307030819168140b01c018031488000b003030013060420429110b076580903144c1e401e5103003107464000c0030707000300060298401046e10340c1d10034041507616010080703030032007995180c5a9259004129451125410900382031003e40c0602c0990800084001d058442a20b120b4103e1240191580103960040c0b00e50040c4004100e0a4400d20030002800c8a00c01500c00c1c240c10041440803403401980704031202c1049400400001014012000040100307100902810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 925274856 1250 925273606 925273621
    0x110601170d020c090f040c08010c020102090a060201052a090307080c0103050f070f0c061b02010c0e100905240a03060503061b1c0b06040f030b06240c0c040216020102070e 75
    0x80b00041984842c40c2c03160f000078040c42031406007c4000d1000c0070081004c0494844000c1c042c0d4040260380d401001d29810006816105214036407045c80010b00b0b02c594030701c4840f2450038003030300b441d0a07100c884c10034003038001903540503c40f040081001c00018104040c2900014040e03e030000c044030074a4008200700202960080f030200120078481c0b40640c7c0141440ca0300200414990003545107414000800c0d0341c203e80c0541c49281c182a2076103030701c0c000c4165401000780020100240c2400591000010002400c02107492500c941d81008074840c2c84814502d01d10194012410340e4001a40381c401c01c000314201405542c4c0c2014298080c190100303040402c040c840c0c402d0b0f926514003240300c442500d00c22101d59002c010a01c00003052540d469940b13a103841031192041c00240ca540c04001c0206565103001111404922806c0b100e03034002c01f4403030080401a40108145403814000c00d070240d402c603600ca200400d0400d1a11001e281289d2050000915080742e640000d01800d11400c02d00888 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 925276106 1250 925274856 925274869
    0x8010f11120a05090118080307090f06020a291e06090408070206280309031202090114181809100b010203030a09140106030b0115030b0f060a110601170d020c 69
    0x8420b2104001c2160307290b40d69400d004100d8000d5600005080d091034004200700500154003d41a0b50390381e612058070b450f08030180085602c034040140e40102d19030000900f0512091041c4042201600003451040c6125190240c00319219403181000c440381321180c0c5031014005401090a440c02c2c10f1030b25040e030f98004507120b8104043d1041d40003003100480007550390b406004622042c409914507a4425202401070a800d03c2c003100418441491030b0114082c1e4400d807000c03210141d448406011104d88883c0595214241c5038130031080321002c005040c3c40d4034a000303090604401014015151007078005007003100c008007165000b0b040c44c1d8148035036030b400020b481e008072144000043c000450710300745942100d480e8541c11607508001c070010030321030940e007814100d90390603210000030465803404400302d0300c100704d40d1640016035103180507075400d01c54013615000c90541844481000c101c04140e1030700109a0240e500d10300d13400342000400e074003844007060900f1540000d04c00603509400180c40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 925277356 1250 925276106 925276111
    0x90705040b04020c0106182406080417071a1e0a021b061510021507030b27010603061d01140d0c14180f1902040b0408010f1112 56
    0x42503032181c400d04580e907500d41c103c509000050000b048410b569069070b5a40406000c0c46940440ca4080c40492450400020200207004642e056800c2e50410f00141c0d14910080e1050b00d09040140402000e032880300004d08000d405002000e144140c80c0c4601e180000e001005c0242d8140d503602c40380e0805184c404103c1c0c20054210025846101c6030322014010710307001d8810546481801d00780302010a6aa80016503c80103030f650101038181c0a1060380e4506040076922807103010040022003540c030a034000e80409030028a84512020b1100c850448000d84541c1400d0720010040108452900361003590014216000c00c25620908140000000401441103c841c3d65000700c01d020540d544a410035005070b0701140e088009500c640f000492005440012402881884040c542111001e8a06440ba1004c02d02024039540c07101080011300401103450b40c002a001d00c000306048a048c0007600c003510500000040f14181d1a100034161004105030400000e02040031078110041c1008031035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 925278606 1250 925277356 925277359
    0x1524031b3109020f0315130609020d060501020601120b0702010902060d0c09082d032503091a160c031217180312041b03030e030606030f190203071d04021503090705 72
    0x80e4100c074000030880c1f6044d40381c046141d0501c0e251001c1030030420355024025022a2034010460191510300681e502c1c2c4085c096200c2152040e01c64500017a4460702140d40440c907840042a4140c550b40450065002511a08401e544900d500040c959200c221480180591001003840c44d5540d0307200c056401d00c41a40089031803000140341d04008040048603940c50f8041c035003600316680d4240a82040b0040d4004a001940030800010342515181100505094004101d45001280d545458100980f01000c40700c103220b00f540000415031009451030001c1e82c54441074030341d06003100d80604d207801c000d118040110b5140c80c094420b11001043d52105140b0b59007002d02038990342018038552404020031814191500404810590312118620904105a04440582d02c6410030580c03a640d824150b10740c154446200105500c0100101444050019040c1c483c450744400712090901580807540e800c9040030340c00e2104600301440f4590100c0c100725601411420400c00071034840031b03584500d9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 925279856 1250 925278606 925278631
    0x90c091d06072a03050315120a050c03120310030308060109080a0303021201090504020915060706092d0b1b121524031b3109020f03 58
    0x404003041403411000c80d1081002200c4041ca0240790080c0a09201e4000d4240c0400326124500c0c615804012a03007069030580300e031030655480704000c0d00750001c03560219501520703040328080201010b000c0c4403841809800900503001c4030710300381858446205400b80b079075601002040070b00a510b41055003665071500e000f100c143c50b2040101d80c014200c0c0c00911880c01411106410541c0540c02800c02d440d503e500f5182d6a81e940742ea51080f1901210065001000d5200064038090100020040c0c04001031449041400741d849903070032200703d260101c401c00003902d803801c4555402001402d024030128102103244c1103c0c0c1d02d520310210090528440d0180b40701c5040040c206440030b840d02002c991403108560300d402c80b5007082c0d007807a180030280501030540000044000b010300800c07445d1400c0368818078580f504c0c02840424051072003c4565090180030300e02c0d01e20448503841d40d90340b0074025030000520840801240c400c0e016480b01b05003034410403022405404100a495100b280d03418007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 925281106 1250 925279856 925279871
    0x204020a020c060c06010807060509100e15040905010503010605041506030c0c060e06150103020a02190c0f060c031106100b0d061518080106080a082b05040312090c09 73
    0x9a01d4102c02c10116a4858030103d84042080303c00078145049a0707003001250003180e61003800b83c50300c2c82031400554005089031003046186001c2c800e40d50f1880405002c01900304006108902c0381d410130b4120211480c4c44500421162600b405400c01420040b913080000187c2c044030002c031004148901d40605480d03001450060340120105141d81c0d4000c1d80a02100e401211655156101140c4080d00210b0131460495154480e01c29681000900e4005222403800d9014880c10248007020840351b61001d42c1020030b2141c400b1504030700501e4582c4401c01d0100c1c2d00c2c1340180c44000c04040007410703980b00c00c0802442d000515104ca044030b846911007940d40c6080c200c0d4038090015504907221814113088180241036000d0098103820f0356405a0110054965a009003038800e00d02c00c2071001e900020704500880c4008004202d0034448004c03803032441480055403440c500584603c210226a5502000141508808114401c2400090412010f20196603840081c1414060680398075500d0b84c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 925282356 1250 925281106 925281127
    0x3030e030f1b030c16030311060106080c0f0f2b02030f060904020301020702090f10060305040b0a0225050102181023042706061107050f0616030815030c010c020402 72
    0x100e0b9641301d000700584202c0b07401c0d18000c07941e40070f140c40103d002422142034480d0102010544505840c0e00b6a54048203403607800050f000e9410010100651000c01c0145d14a0548018020100c00026004101c0c00c0c500d166841082d486050000c00c0080707004100b005034102d00c1300c261691104084400c05002e4031680003190080c01031240013900140c0e2041070000c171003d0b180d01e1510540340400300000d075540300c49003103042e640d055500402080c0640003140141205070094100310030008138205480da0040091039521211540a94951354000b400c8150000310602003c0c07488005d40d410607400000e03400003080880c6d1810540010b8004d80003441d0a1a00c64049074020918100c180700d810060780100d400020004030000b41951030440000350260048440391001c5c140c00018010f418504024410002044c41000c0e40c450b0301001540640c1446080c84c8020f42e000c1c4d0380d64061032030428005d0040c0861081820302c0780c0c0c055901c105460b0b0b40110226120355050700c0150719074181c5503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 925283606 1250 925282356 925282363
    0x206060d0510151d0114010e0307030f0f02060a05041a07020f010e01030b04020c010501080f073c0b07030e011409150d0207030f020c0103060e010504090c0e0705040303030e030f1b 79
    0x300401c0c1c40d021050b11310040700c001c0a6450303058030f00345022481d401c0c010f180103680b40d000b03078090180c040d000b01e14104082000703e042e50342264003601001c1c641c02440c5d0b0004a1660091184a0100344080740a200c041d002d5a00480c440c1701c0782900e82d10348052900060043c40401141504114080046030300c5a44242c00408a421020f0710a540310a258010f55001e00b0003401650200d102d02c48510725010000103a001c00ca0759542c501c000510341000307224001540e0042c500f0151900250302e914040340d800411030050a41c40c555540b41e4456107002040c0d800561006410043d1554481d00f0303090b030240460f850018101c5113a580c0c800c80d140045440d01940c18280041440031950030306040c1c200c2400c7c02b102051303509450425551000540031200240a24011038030f07054018040b604090740b048c40e00380c1c0500c0c5007480c1907940b5180e01480140031640880054008142003003056050f0180d80c0c11110b20002443c10540303204c61030485805580c0c4800b00030403940c0c0031070750b8120060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 925284856 1250 925283606 925283609
    0x90f19110102120a0306031a010506041514070303050105031e06061002120304030203030714120103020f011803050d090f0e0703110d09030504170109021305060f0604090c0206060d051015 82
    0x40001d1a1120130400001d0028042480140d03100151b032445448144000c1581a0503520000d19035418039007000182405905410111011b00c01036103d00d0601c4260b002c0581001407003a903011a240d81410145401c000d204c004444561140450105c2da50001160541e03001d00117540c0070602e40d0311240c040303107000028034400000c8000081804113065000c070095105440a0311070301030301c001e91419034200740700f60a050740950803d407006000514100c80d2081c01c44d0014501514805020b011144080d45980e0003103803558010805207070195044542e000040503403685503c42540f030316282c03407a2410024102000c141e540e03020418030004110940f8404000902d04004031002468050519801402003140340080c4203030000c0055014052906040e0f4003400d0808184001e07001c80c8040d11010b45040e07071102800c078043c18280c4800300034100401c403a1101041030703a10014042c1c28803401074000380c007a0015540b8800440c82c001540c16140e11120400a40030700881e1700501080d0b0039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 925286106 1250 925284856 925284883
    0x9040309231504090b1e04020706110c07030b1302011407020123071506080a02090c16030315050a030c061214150103050a0c170406091406090f19110102 67
    0x6680c440950002e081c0250094900d19601000710b00020004c005824803911805500c0384002e99101c81182410380180803072501c40c0c3c0703001c10400001c00e40c1c1c007481e401c00c1200e903280f03501c44d250820901c4600c040f4203820a006000c0d1150100003900024011081e010610034003900001e41e50301107900c200c0c44901500812442c0247c101400b290400860380a00c00948050f000345d11b108043c0070f10752103981e040782e600744000c0c1031010440c0d0030320800c690b0080007060984400c6c4071100315240130210000310f251103542c0c0001c00c40b076021007098012f2003030340103140a0985514284001403600d201e120070f45080b0b04005504410310718540c00a0010400f50502030380d2801c0034130100418080c00200c03009800d0300c0a2080d42e0340c22841100310f4400340b480b0800036200800b10404040314028494000d070081d0000301e040002511420005000280042c01e0350340007004100c41680180086110254610081d00d1100300f03010103800c0380b811400c4e018208065502e40d20000b0780c001c0081e03c445001c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 925287356 1250 925286106 925286119
    0x30e030a03092904210509010813060f06050a0f08060708092e05250e0a05041401050901080a05060c0315150a0e0d0f0b041b030c0f050904030923 64
    0x2d00541c6240c0f00030f640440724522804050800ca642c0d940d54079041c2c84d031a64882d030414100340300441e40002d000d402c5100c420445150700010640c0f43c0500390301c100c00b00d00f0200b600b03803602c0b09100344644aa800342082c840c4852061096441c00726886405ca82d4902c1d1400342900d0340d03200341d81088150100c080b940311191401c455044960f40d1045816900703160700f0003840c0d40e41c99003143da4064001c480d4500101441e00f00b024a4015125550b41c05e07000340401c00c40c80e0315100400c044494400440c503400c504000100400d02c2c100b54800d001d007201901400d01e54181da62000c0e41e070040941107032136182001c4000307554980b0000b10320324101001000c040e407911100351001e644e54000d154500000e9000021101c3d01c1c10400001d00c800c0b94031244034103012640f5101c0c20700e41440035004441004e0403100c03c1400415280c0708070701031030082c1014103800740313410a848031280c3d1315844180030b5036190040002080e00718548900304e94240524440d4039040110300c03d01d42d58010030050b403050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 925288606 1250 925287356 925287413
    0x1309020a0b0a03050f060402090a2616030c080f071211100e030c18010e04050f0303190f0903080411010912030305060f06040b0a0f02031903020316030e030a0309 71
    0x3c0d4940c00c501d029415a5804e0780d415103d10041c40144d210705200141c110400c01d0301000120380001c1c00320b080402c6001040703100c0c0e480b40d50142c10030a10400e903290210424405100703018842c11b481009003d00d0000746059030600010a8590919100b141d444e80548a102e90500c081e81d120010b81010041085482c3c84114602070980911a09140e000748601c0721440400d00f80390f07070306800b860301019002c20540e1a21122034640c80c0010800c9450f8040c0c03c2e05040c081108202960040b000c00ca2801854210b224508080303644954000c8105801d040300300c0040b0f500890010b800030380009490000b24105d000594034083d040d07019074070305841143c0c0103080c56031541c040390062801f2142c0911070140e01c000c000c0980282d0150301c0e05240c00308203051980c0e0040401050303c041e18010b480c14001c0d29221040701c041040d0b6035001180d0000200514200200042200803690382070070820807501200480e501d00030754990209041da43c4103040b05000000b1680c201c2c54110400307014400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 925289856 1250 925288606 925288627
    0x30504170304020d0c150e0301061d040822090f0204061b020d05030301090609050f27150f010602010e0f030a1107051302070308010e131713060e030c0303091309020a0b 74
    0x200c07245c0c0150360010302030004410b0b8501c8d040c011101242c103048164408034a1028407031000100203002100c0c2c41c6d00030004041040207071041c540d82c04890700c0045e0062071030400d02c0c8064174140c203032400000d8410030080c4121a00703c5400d07a0111006603410740300c210244003103040035506403000742440c400400001030f45000c0e40c101d14282d40c01000706102d20b131a403143c12460321109498018484205032400c503402008019a0421800d015003251380f00c015030f80c04910174020507140030890107080700050065a809026140205096000510742088001003554490088664150802032080260a601901080090b0103070400401e1420729200341c40c2100f0082d404014100c0110b24004000a01c00503540c3c101c134403035000c406407082d0100c440d0f50381000103041041000380c11078041c4240240702034201d8146001e0013050301d40c040851604c81c10035282042402d02c03103201e80c0c42084a140541c88504010320303908001c10b40412081c805100144510780a5006a0b103030b400d010070b505140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 925291106 1250 925289856 925289879
    0x1020307170a021e2104210303050115080402010f2d08060d08030c1c1e1a2b020d1b060c0209061002010e150610030504170304020d0c 59
    0x584001d07000c4076813001e0207811000280030125000b44041e00810b840e00801c600819211a00252250a0900c1d146c0c031071103480d0400c0c0034040a410301c6244180c0d900c0816405226145c0981180580001d400745201d030300801c1200000c0009040140140f82d5100050246c00341d12a0740d030740d55481c500207000c003900c06103808000801010014054502150190800d4400c41c06159001a10545980e480e00d251801701e90140100880c0300302038500520320b2003103d00c60010160110a0809000720081c0100c074140d0f40b40b4062403180c84096565a03d55580e13039880c4250329205c062070103070b01c0008101c000201c0290140c2c00b035041131540b03130b08900f0000c0303a4140b00104d1180c1c146410006450390400c5035503041420b002500302d49800c01240062074a0814044940a50f00c0041445105000b1060030f010365035154141001025086c400c0e1031a0214030b004188003149010003e134540340e2a282d00c54841580b64122155000000c1400d40d22809480780c01e941e0406035075070b0501e83d00c006200c45c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 925292356 1250 925291106 925291117
    0x31409130f292407060b15210108010225021917150103120302071b08030a17090a380a0e0109031d0f0d08040e0906070c08090102030717 60
    0x202d204956014000440440c0f0380ca500302c540440c8480c20000c1641c1d0303c100070540100a168008010700440c12900106401010044444642a0418040d4038042944401d060308032081340c0c0d006100101c0e0502c0b5864501d520041598032000030b0b824a80045030100b80403031440044024400300100e180302a202945400d0080901201c030050713001d200100c4011401e01004203803441c3c02107103820186c031070b8001e410080d0041c0d090b04100104030070255160315059011b04030076000071885401c565044101440302140d0306400c180c4031300d41116110344400d507241004000324a00e50002602e000c80031018100080a1074000c1d101b246590550340c9000d0003107a1a0007514142007884513240410f020b95111254141c1340c42c045411814210401d010700240107542010400e568410130390758102c895407545001d02503003540c035801e20f041048801c500418032003a660018040c010101c0d481400800c0442c0c00882d110307110030f004070040b03045115075140504122240090618101d01c003000520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 925293606 1250 925292356 925292359
    0x180a050910050903093c0a06050304020f040c0c0602030405070e070203071205030901150306020703080606070b0402010c020f190810060e06120f0316031409130f29 72
    0x500034140d811072036058420403115041070350424070640d400c606000d00d004c00032156007a003a1091740724040d0a103120b9401041c01805000000310510540d00301080a00050002c514043c0c2c614a003e401144103410300707646c02c038046c0d0f660ba0b580524840c0304000c1a83c0096000405650b43e0a240c01d101b551491700340a003c2848010801160740903000008988025034000d05112401803200800d0b1980c0d0401071200700c0654942c41d03015000c4c4443c20b00c4c9005180308950060320307003405040040540303000400e0b0a0281230b00304981804a0302502903180c3c031076030918145424160303031b1010400c0210400300ea2a045441d41b1559501c0c02d0003003000c00240d0f1048021107015020001d011403d83c3c03500e1103005131256111010034401c0c1018002415504500b8007200d03034a4400c04415440c5500a80783d40d4091140382c007807681059400701502040c03a01d0a0086814000608001788035030313000c15428254280c1e106040c1120f04260780004808510b150307000b40c400394951031000c008085e49100319 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 925294856 1250 925293606 925293613
    0x60b10050706050a050f0f1f0320060306010c0f02240901020d39211d1302180a0f081608070605031305010507120e010e0c0f180a0509 59
    0x5000421240700d41e0344100c40030240c46c1c149481e03010301144200405068000d80000303c074690140c401000350424011032049040740c0010284003020744401404d44403040c440c000810038042075a80c0f2020051240341c108040810f83c011070300c0040c1418904828560203d10342034a0000814002005050850801c0e020f44401c0c8604960031201d04000810031414103a215100c3d25412180790002403254007a80e51000904115860304000781c039030703640c07030307110924107000308007206a400301442c02e40300c80100d00d00002c0404003002621001071a4081c60007194045020746941c1c1a001c00f01c0360840015114078030841d2200a4100f52050a005c0c14803584030ba4030795008001c107800c8110045400b5a03000d0170800381446802c988561001d0b12200f40102ca4008080c00f00e0070a00c030f07441c0108402e4645000414800c494003069407404182e84c09140d24204010101e480041442c202c040022101c07500384100703503000180790440c03403241202614002c00810086220381d0340440c0c007800200044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 925296106 1250 925294856 925294861
    0xc120c010e0a021e0307050301021317160b03060319031107170703061e141605180405060414040b0105041817030606121e150a12060b1005070605 64
    0x3400e0392071594042c001d4210025611100c100800c2c900001c10000c40181a41c1640e0390f500002400da030800f000c00c645990b44400c00f003010508036940b05440c03119003000341012070845810690b02c08001d1081d8601101c2c00000280c0310f139010310801d1500303076040c03850303201d9540241001020100760501c08d400c60b114028012485a403001024200e100807032000b418102c2c1540c0e9098042c040182c030207004564810031503d10319145000c0d4556030080c4000301844c1d0b2421041008a445501e4040824480d04010700c0410b00b00003038903c49401d00564001c146503d8002c00f0034014601012544000d00502081c0320420145002140c1241d0040b54284441039080c40090f00301000100010700c4190030f000c0450112021001030360344031034020205803c0c0042c1c4102c1d0310380e0001c12250641201d4845952078503201842088540140c80801e2814800207501e010a00010240c06040f0456a00000c102c041080c070360030a100b03003500640a843e440c0b500d40320140294100c83c9040b40c0750783c1031a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 925297356 1250 925296106 925296131
    0x30702161403030f0a020a02060309010b03100e0303040b220b0a0c050c03041208090405010b030603281401110f030403090509070906030207050a0b181e0619020c120c01 74
    0x1400aa103003000b4040c502d0500080d150f4922030b40a4080380040d805a2001580581e9444015512916494001045810f028420141000a41044402e00c18a4105d050030064000002d80c1d81c4298410420702c2c2d542c94040c1c4000106031110904442c03e6000d0045104101e9041e4006016111140080c402800c105038103a0707280c080d00080e44d140364420b1000300261100108031404290140c400c5910741040100840c1c00e640c8260800200d0110020074011903007010080880700c0941040e60354140701c00240581000b040d180c0001d07111411100c00715031070200a60019081039240a0810b5440408004201c5035030000c84003503000c40c003903090000d5142001c00c03005d44100c8190752105010ba0410400350000d41240c0410741d51481032a0f031043c002040d40e65000e000b1111000b40ca90051012604581380c005500820340c2007549040383e103241c10b540041e00c143c000d1101c802102d50505124503c1009009400e414001486500000c03a00030344418018041882d0407402406207100040d0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 925298606 1250 925297356 925297379
    0x9060d02010c03120905012a080c0301141206070f2003040515070f0c05040e010204030c0603021b070e04030f0219120507060203100816060c0b150603070216 69
    0x12020340400d001c40d95400000f407283c0c202840c02d1040480000303200c11151615400c60b05802c014100b5206403198050740354000c80c41840c0c0c01348543c50004981d10f401c0180c00090700041c4510303804c041c07041d00d41044541d10300d064a40300400c6001103407214504110020320010040682ca0701041b5110350360a00152500b0180307101e900c22034000c0d0300c2c06d0320301800d12962a4055003011180102802808009241d00c0c050042c0240102c0800000f5828201080700301d400e40001034555a01c108010400252039100c0d0b00c5c100d0b011408c005803510069803141020792003000004201d40107005010442c50482100e403409640a561074507895480b00600340c0e61208281040c030445000c400444000580002c100002210a4a0440c0c1444400c1d45c440d01070382c0054503603e0b03401a04503424030000c0010451071525407900b00d28005403134039140d4041c1880e444081e0203800302e4140c1e030015400160303181d011150140c01030481039917803420381d200944403070106000444181c40a1300004100c080c81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 925299856 1250 925298606 925298629
    0x130b070f03260406060f17060103060f140103260307080f0a0617010b031b01050301030308041a0a02190224101a07060c0f0909050403030e0f0109020906 67
    0x416000c0a400c516102500e080602040e1404806070101c81d00c1d60750000748204900491107050f003c61440c3c248002d2082c8401541c0200407100c030010880c02d0b88a500045041c1103030342040d00041c00301c0a401c290b10160000c180b0302c1c1e40c8070031810000010412244008508804610803000080410290b040c04902c0181d031800f000550b040301045820114a000c59003012000c02c00048107590751445100f950940e40140c24035035034844100ca86800c1c00e100540c00f643c42c480c00c10505440c0e00d80041c000b804103000141c10044060001001c00070391800c503032269540030103c500c2603d0182488000ba40c40100c1e052119504038665507602400002ca25044502046c10b82c50400841440c0c200313451401407091904a40640300000e00050f100446200c3c0c1604280055079580941001400e1701c20224644040046200e0f0b09645580d20a001905a855001e8041041e0f142c2c0c1c1000ca000d004070b0230550030507010f4034110440081c0154883c0a00e42d00c04d61f0200c020399101401c1000c0c03503045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 925301106 1250 925299856 925299863
    0x609060301061b021306081608070b070507030c09020306010e15030c09011707050306031506030c0d141204080705220504051f02030f060f030706050a030f11130b07 72
    0x10300060200500900b0307080000720140805030800140c030303000200c1d0340c0019034030380e1441ca6503018107100c0750781c007841025004001210810403d514040149654900b144100401000c0100d008000c100003400020001c541000302c0520468503049041c0c001d510958006001c1a0348203d40c0300c0303e051034581914182c0c0140c1000d4150b90740c502c80c40d01960f00000800b4100100306201030b44080041135103600949907591120380b41c0c0740c84014985850f0384038008401d420148800c010403030307400042c0103440d0401690a03030943c4609240c0100c001c0c4a410500b07016000e9071a0003801d030480f500c003610850f8400421a2280760307407241842644c149080d209282a490700c00d141c1c00020703841d007207070380c00501c103604603003901d2140030390705600c40c51880ca040b46268000003405171543d400c01140381c010000311204c0c21200d1401c40003e81c0c4003050301c100d10a006020508001482c000e41c001c41e00c1c602014400e000c1c01015102c0c0340050b9200c3c1288880c107400c1000c000c04c1e14840441601e600950 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 925302356 1250 925301106 925301119
    0x516320a0e0a020d05010f0905130c1a0c0d0f020705120c060c1e1c1b0b04050304180b280e0c0409020a031a0910030803180f0a060b0609 60
    0x500318079100107040141011007054003009100440c1d0514802c40b8000c10444c084080304604041d40c0401782c1d40c0140050401d040f00c0b801072000306020b04040d008896035010854070902c151240903106019040c1c4501a50041404600300342e604031258406030005a42a146800d440f2001c000286d080c131203000195501000e914030b9103080c0304008100840a5408030b6145020f10120b01a00d1b8a035081c1c0d000d084d403c031001c540c280a030070a032601d88118207420301c861142503011940e0001400100003901062604002c1800d00000b4030860f03002d880e2058602071001004071f42000039106c1c04624600801240142104032004030003402a00035030014a0380c030007468400e0034202000c014008804606080000050b96410380c03009000a15440e10046200060035591a00341c2d2000c905090241c034117401004551103400741101f050304e5008240e00e449464132809039403450f00c0612058024030400180c0c0c029803c00080c4407601c544180807e10045000360207000300c900400320100e07040031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 925303606 1250 925302356 925302359
    0x150d02330301261e150f070e0d03031b020c01110303010f0302100909090609140f030a0507030207030b01121509020f040c02030904090c1401030207080a0305040516320a 74
    0x5005503141180d0490803c00c03502d01e04901c002c150806507001d289042a54081c2d1390074800d0301c00c5041480c0d44032140d03008222441c90b15a1024204540c00c0096620464001412408150107540840c1c000128200310b5107100802d840060f55030146148114040340210107110400d403c0003040300c0c141c0b80075807007504543d4616401d0103080041e86c2003000511880798008500303020144946118140698404602c0607900d0804a01c1020706038040d04603500900c121551184002040780c0c0b01c034841c1c1c540176036126a141000c0b81818a650401072526030b10500003e134441c0034042244005000300c06580e8448001c101a000301d44007084003d4110b070042420004500c0c00d648080e800d14010300507286000008400a41180e008680441d41d800358a6014040350805001e0b142c02c40030700303003011813411401e0740b20390003940541c080d990b042544420000e0708124080c0010085083d4141d944c212140c1c50350101c55100e0b036030b0130401014040801082c01059800450760780100d002810101c50389 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 925304856 1250 925303606 925303649
    0x50102041d25090b1c0b060309060f1305010212160801061b170a0c0507091a04020906090d0602223515060a0e010e150d02330301 57
    0x454034482d140e81406151040064030480c80c0380180114142c10300045505640310000f4003c64040703060b010302a1006000f0003d03440d10000ba19904014103009c10981d5039100b0081410700300c0c079280b0041841d4004140b2140400705445200c0c01400e003803101071542c0e244641d04480c800c10074030403c000948100c0581007003a485201c1c0110890142054903103210a0501c503403a594464000400000c040c51401c0341400000e0114034090180d005050008103610000a68214080303208680700d103900084214003a41c80004070303a41c0480c0503000d042c026041d410102d009402401301400c6514000c00348071146400c840ea02c01c191180c0380c51054100050001554171015190442d25084001340041c0100718010000d178010b40906181310042807408505202e000441a407104140410300c60044c071400b802d072408142c3c4090f410300122007041c02a400543c121110f0318001e03400408443c4105030800302c548620030311259010720440c2a49654481000b10311007403182c211000380e01210380c1d005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 925306106 1250 925304856 925304911
    0x15120d0810050901170f1f1109091e06040b0d030c020a030c080307110a030807080a02030904060b040302032109120c040608010b0102060c0406120c1209050102041d 72
    0x7246031588280c40d9030300c0d100420b85100d000e0b0041842d140d4865641d0a912004101c15282c2c3d0101e10060548a103400071007803504041a807581ca4000c1d107442c0301c080031026031020788204110041c43c0e141c8505100d000803401c1d0b0076541000c1101003003900015220304084c000d0f442c3c4040c0c0581044008480780c2c40803100c104031010204c0e0305c10040d00000002c1410361f40c201c2c020f424418003543d9035110038542540b0305a0614603aa004110307105041001c42c241005070380d031041d007103002a5610100c1110481c2180f04070b00310564131614244001c1038030041c20000d032090742d00c03d9084489105c1d80942c0900c0300405800748140140341080120142d0810401e410000d58100c81266101c0e040d03c0e0004080e140d15070800d018582d501d00c0d44202541c1d04100d0309400404102980b40780c0360501030001e10140e4451141c4500ca40c4409010084500c00c034849002c0e40034411041010b800c091410300c0c080d41c00fa20442850b060441c07004c4a040d004103003803d00031002e0690381c00703c80f18440c1c00d1009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 925307356 1250 925306106 925306111
    0x60901080430030c11032209022205030102090a05040f02040e04050c03070e0f010303031802060703020a1205120415270203060a020a021905010b150315120d08 70
    0x294082c81907114480340c4030150b07941d1001c035440d014050141c00540c2000741160400031542c0c08009205010000c0944080200e8003404501d031500d11032480c0c4a56030303542282c2d41c3ea222410980c0700041c0e44601d403e071481c1000d1606500b40101e98030315680c00400d802e03805103040d110750200151030100301c1c3d89000d1740701e50f410900c3d001015003820740d40d603c84162900115003c0d030f0070350441184081c1d58070701407180c80c01030001c5403040c0ca124100349440c0c0c074100105020040c00d1503501da0951007246009480d242c2c0050b4001c080f03a07540d0b0000d180c001d44a800084080b50340c4420304001c0e8038414020b0068480d00444403801001326565504c400c00c180e000620315020f00c948c0d4801522000c000b514100619006804080844e1142481414a00200140345a0711280305101c52090103a0220b03201d00071101905101100280600302140182984007600c1c2c1d011500035561003d441740100590b1090314501c0400b900c400d4504148840010007030510140e40c2c2000c0c03100d80d80326000e40090b54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 925308606 1250 925307356 925307363
    0x19030b040e03160c170d050a03090c030f0501050123220603121b0b042604090b0102010506060906041e18060513091110020f01060e0403020d0c020609010804 69
    0x1010031441d18030504590007103048220b5164014034243c24040f0514144000f0321200346512482500d041e8000e840f21582c01d9403104000300003900790031340740c07094025040e0150080890040a56a80317058184511100021038095080c100001a2801d500709585c52078424600c1440b0050035480412813241910b040c0c25000394800080d400c1c00d1295841180c0c080c42c070514000c24906880e000182504030080700b0701d1360042004820100040d08000e4050308154480300784a0f04680280d40c480c020b403d40c02040c02400380200d80000c440300c49801082043c94283c00800c080e449400c144074081c85801e4026402c031f00200320030002c415581e000c1002c01c1d5a8030445c206c815071145035072801a141d094003000140c2e200e04080c485c078034204129a0304441511802c00c503022482c1e0f41c10000300071044855122302c000350030340000355009000d800b5108034184000c000850322100081d602e04801d031000d500602c10f80103000e2305a8001c3e09684a550f030000c106900b082074240046810b40c00080c02103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 925309856 1250 925308606 925308611
    0x80f0703050d050a0204050109270f0212040c170a0b01031e050d0503100e041205160204090606080c0312030c0702130e0d1b0213150e07020d031119030b04 68
    0x100b00c952644036403070281485000140e5070314036200005003800e05c9600640c846a00000714500d421410f801c01c00660049244c0200d41d1140c3c20794854001c0c050a6904024804144104010003100c15100010b96080c00611840c0c81e60314140c07280d071040401002400e003001e00006202290b04900088045242034501e900104140d075500d900b0103030802403d4010400c08024812850415919103000d824040c0044140307240c13680390071100909200c042c105210740040d9040c0c4030412900260600e9070040c005000309065460080d00500c003074844c04105000b0842c1d00c102928010900841444041c04d000e421a02c524004200b40d512030401264099290b0240071103d607090b008884030081701c2c2001d4030301340c0302c194000303442c44d4403440b0380d9055441424010b500681d201e203880340c42600c80100010300e5441c030308010020200250040290b4400e802c040190075580001d94003031406003503805004034205000a8211400f03098030800010341000000c25515100e940254a21403001303101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 925311106 1250 925309856 925309867
    0x203061f0f0806040b0a0c050a0c03021929071e0c412d060c1b010504021c030c060c02070501031109010f0518030d08090606040504080f070305 63
    0x812021007581c1d001c1511608502d08210a10000f080721a40c0079964400c1409000a041e4008042c1e1242c0d99800050142c141041c2c41410720070003412540c41130650313030b1124130a00c90403c070070034041146e00144040c5550440001d00d6843c115500c2c00307035000b034903000703544440d1010174030707078245242150302c02c2000d0785080101107080d200180554a1803603c1c50300d0305508000742603406042100f98030340f4130016021640c3c0104000200a4248444103008001ea01d0140701c0028804144801c1d03140c1b031b031040351f003401200303400900200200c02041880c260716582e01d401040c2603a208a90195000d50500f80b074503d001e08151910380074a21034500403d00c0c8160b661000210b820703048040005071700012091116580520a50003080c81c0107008c24200f0007d800020070060013104040c00700400800c40e602110601e2100703c100e61001415600502c1c025040281148022200c81403188613030800303e44242068401d1600480d04007081a14000031b500e265121540220401c0701040420810b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 925312356 1250 925311106 925311119
    0x506060d1e051c120510050105041701020f07050c031501121e020a030c0f060309050616050415020309010801090203060a0501260f0f01170304030f061404140f07030203061f 76
    0x20b0483c20f1101d0741c803040030304a601d07207100044a9008010956034240d5040c18040340e03802005a03401c0b100030101a6a49081164416000e40124107020410751340220b61081000400b0030054800341c019070842d09641c00c10040306440c45d1083c8a030300c04840741d42191101140540e5804841100b0950480181d80c1e12070380480c8410450b0b500c180d881220350700d02032003140c44131903404008210302d15051058031102c0d110180c03600c0c406829003406503482c01000003980d00860a82d4024601040180d407200d03c0c06d14003135165441040b581d4002504100003003010300b02403090320700956024041c12652420302005585400340303110420030007445050841002507040c1c81540c480e8103d0701c01181781e810700003455098a174043c0c1003802000c1e4596029284440004161b80840e500840200011081414460000c1021943c10170792112307810104402e1020860103002030003010380441e40c07014034845c25030317440300a0f0b401b00a6058114401080f9041c2e088100681281d5030314010f24061551501d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 925313606 1250 925312356 925312393
    0x40809120f010c0f02071e1a1c0608030d11040b04030309081b151c02030c03040309080309010f031a0d0f030e0910033c0506060d1e05 59
    0xc004224070340c400076207461600d900b0b0040c5203051034503041c650310305840755001a483c1c103c14010340040f400d510302e0401c000e5a5442681c0020421782c180003440c99512025100d4640c40040c0410621219040000705000300e48500d00440c5e194802035820030000e104030901134451041c04400c00c06c020300c0046400000fa100400c01588640c8400b00041c0c42e01d03e41798208090f40e000030345410340003154070040d511030001d02000720010981055560f160803100c0003810400c42224022a8400f000300f1010105100065028600a0300e450303c0e610b0b61600030076680d01c40d0b1030321240040c0b0101d0701ea2841d940a82c00c8803070081c2a41003aa0f11a000b21008204540030680301030380d0031080c04506209250b00004034142000096900e40310b945801080b24103600303000d00c0010644003031904102e000c60030000c64203000c60720303140f000400d4200c0c0e5880c400e074004048600350741034001c840101e03400c2c0c9070030780010410990120101021006401d0149e12040c049001521130340506003400300010000d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 925314856 1250 925313606 925313629
    0xb040606050a03060f140114070c120201020f0a03140706020906030a060315090503041406070614010906090204240512041b090e0a020603060111030d0903030e0d0c0b040809 76
    0xea549540b41c0128400040c03e071000350f0f000c00050605804140800115884e07112429002800e16140c10501d0440341c000034850400c028000f0b075449040880c00403213904008840c18008d030b003103681c81010381078003544403d4540f1005000c41c41000704107810050700b9020305051802100c00500300718181000c0f41c03482c0d0048658105240d52000207000b01b2090501c00c00862810560400c1030b0a4996510b503540e1007136002d002c40602d100200c1c4000d90391100c048410460740010b040c13014030389a0101c01142d810a0142c20070a505140000c11741ea240b42c801d440880709044071081a00328424800c07203150103041400004c0120400140780d0440007010020f00840c0708809011403072485561590128209800c6035294030308210b240d60040c5800035154031440e804881041d681e071180300059586403006259030002d8000450490700483d136523030010a000f030080c1c0b0b042c84210901007080e61903044c802c0b0141c0120300943c0b4800c000c034000007401d170b500512441196141c042c0c0c4d0800980d410003003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 925316106 1250 925314856 925314869
    0x191e060b031b0403050d05250606050102010b040b091b19050903190201020303060f03010209031f0c0822062c100b061204050106050d080d0507300b0406 67
    0x14030212000a800e44058550b00202031400d0a01315650261585038400c1814200b042c0851141215162084890740000c048100300c481040c071483d10f4009810303144138150265181146519982c2040d0082c3c2030500401403032502e0031341d078040c00b10b1581840400200403d880c144849415080c4513018118003281541b070b9285c9400602c801c06142000c040640742d8458803c128090050b6000000e030b903003043d0704071031200401400102081c02805074407891a450b100324491421401c0d1200001103540409680902001c034000c1e40a460001040d1901a60b03011105e4a19041302901212400c2140c803400011502210243c0e0f1145101d50071a070024425107040303550b18061b20204100001120112402d111004030040040c6140c09494501c1400d000d05d0800039080280139404000540801021444214040c4c10100000e42041600355061480e02c004030b99454002c1440c0c0d43e10002016441496030a030b645505040c0c0c00b0b40d0f03074900145803285070004840c0d842d8010100500b00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 925317356 1250 925316106 925316129
    0x60603021e0c10060305070f05060406050d0e0c0a120303140c0906030a0603020d080a030510060509010c0515040c052d0d05010b12060703150b18060d0e07090c030203191e06 76
    0x20030301241c41c002300307582c45103200d010304105c200140c0750013000b81c4070407000c000300c0050b04a0400e0100c1c2c0c20140803d211550214a4020114a0003084e903044042d42c1d002c0d54080101108100140245c050b080d0782d540100d000078082c018080c034141005640c00b1040040201d28113a0701d40c04141d0340102d10904481c10400030440c81c1503103502d40720b015030141d4040032000810346000c001410b1031041603075607410040c0000302101400410403001192004042001c2c0840c601403c000c00e00d04424014035102e10b4410191f015080031030301040b207800300d892120f440c28034688400c20101140d0200d0849071552100d50b109460b0391141d8202c8500a03206010b0301d81803801d000001c0484502c1f04411201c21032908003400300c1c501403800d0780d404081941907000070000700f0300081c00c14054103103004150307804c1001707001002e08081039040850391000c00500c07044c404148140c099010881e544070400c0300e0041c40d881509e07003a030085c1c80700da2042c092000050006c0d403000000d07603015810100306001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 925318606 1250 925317356 925317359
    0x603041e030e150310031112030415020d170a050a0b121501080111030a05071106150f090f041b2606070c081903111b01060603021e0c1006030507 64
    0x1400d80b0990100500e0404103807451401c4c0410945c004000e0001610f90b5038156520280c646801100e05000c0c00c0c40701c126501d6580c0e40055401c403103503202c0030000600a1000301000f0f180100806264100b007240084559510303044110020100202000c1015032a06101007207500c0e03000c4031140010350800908408280202a040786080c1030388030405d13580c5000806034a1183c0441602c0e08580aa900440c03a600e824600b29484282d0b0021071909010743c03c18810210120040c076004000103841d1b2000d480411010030041c3c43c4200c400a04000300000014001103445118003501e034003054034078400c11b8444030410103250b41d10903142003941d0b040c88003240f015403c00280e94804094a03104891a00e2596104802d001d180001c52000480e104140000c2e40260068861815038401e825202c400f01070810006845040e524103940d40f0b040c0c008208184203008640880001440d110501440e410003540765500c024500b040a000d071a015840710095030146000550140004203243c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 925319856 1250 925318606 925318609
    0x519060303030f050c0a09061805040606081f0f03030e03070b0f04170d0e310629040501050a021002040806061c03020613020d06060e070207090b09060603041e030e 72
    0x8075070151141001174800d1013880941039125503080305031040c0d458288091022410340410000f00350b04210b03800740c1008804910140e10001051084500040c080010b840703c481e01312580040b0300400621400000080c00420b0240d59844c90110700a0100c03640b05507101c210308a250080d05424021a030005020050040802039919001140c0d80107000503200511016254007036001405001d0007089464540c0300c00e0b801c00c05c030070081422018414103c0360a80c004000d08041c05424401c0c045482c0c9100304180d0f10351aa62108000054036207094280001506e183c0c1009c000c0408620406801185030040c40c0090310060446500800c032a0814004106500040201117049402489a01c00101e54001001608080c40e04408102082030703001040003120b0208001d0991030a00c00c0001d244030109014a1040c6095405e0702e0750142c8030803140e810361360001c1e00164401d40349008501589410320082d600725100b5400500e86111450404000707807413400056010910383d006c503103445d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 925321106 1250 925319856 925319861
    0x30319030b12071203200106081006140a030803091603060902150a14070f02032a1903350c0c01090e0f061201140105030708070609090519060303030f 66
    0x4050b0110050684036081440d0f41340701c1481d001024040182d40c01e031001c158242e050700c80203c030704804028060a51a001d21a507924040c4099414403458a6800540b2500140e040003440400030046030100e443d503155940310341c00c090a51082801100070941d41c07030307070424030705030043d40710310000f240d00c54a50041040c10b410320345602d01c01c2d01c41000380c203140592049030720020040c8014034586070745aa0a0008000c2c0c5640c5000307405100b064001c1c0c030450302c105c220514a103601880d00140040c41c2d810701c0b0b01007806103404411b040d4030725030a100146041c4200a2900b0300468017095407114030102e0109110a54081c865090000451081501003800740200c2303482d0a00700f120307200d40761100401701c40314024015981c100e41000401c14075554034500d10881241e800081c48441041e00044000003c00e01c0f0701440b070300c00c850780007035107940102e0484210f6070681c88111489140c132400e00007401d002052242d007045820f051408210ec2841075901560203554005241e82118810f0001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 925322356 1250 925321106 925321129
    0x4080c2506030225030309021e041505060715090206070b010801060b0301050a0611012a030b03060603060412020a0b25230f09090108011415010c11030319030b 70
    0x1c06004000b040c113148444c00f5007004003911040c41290440d0070b401d044004202c0610020340c04102c00c244010321080d8210110000041220104201100319a00303441c150045d1007442d03000a02440381c100400e0050055902c1400311000110b40d003119980014555404030701c040311a49481c9006101b006002d100740301c058000390703030002c0ca1075040800003145280726124000402c011780034144141d04080d0000e14400f2120311142442004a1281c90000f0843c84203600004c2d1502c10380345424500022410f01918010740607003540e840c5c03512403e0551032440714a0055210b40e00c131940000381400c480510400c6c40344904d448501502c0a000104002c0e6070b845420410190990b042950704800c1070020809403044695030340c144016130009901600c0303862903000b840d9000009540fa019000325012094400424800d60394a40c010313403114010494141c0007404d144542c1c0006019007201814420b80141240e06140201198280803d20b03000440c0c0000c1d01c402841d0100e0901a61001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 925323606 1250 925322356 925322369
    0x81f050105090a0c050910020d121104030602070807050d080604050c03040b22020a080114180303010b03070c0f0302011506032304030e06040b090f060306060a030504080c25 76
    0x155240100081c0c184802070820300c0e8641d6150000c00700680517508680e0780e44406003074194425807880c07007c2d407200f46050080300403402d018001c1d04070100130301c1050b02103420809110305007415515500025000024102d80140b81000b400700030590401c81c1c1d420701032103030362600c0c03c500c0c0590501c0240c402c041d110150040c01802031200182e176040300d95a01c69410300004003283c81100b01e00d10001a06940070790007007016100402d01aa0640241d00e1a14000114450617112441e2040011145056140c5607400500c0140100040d8500561f04180c00d440c1c681002c103036540382d9205185091004401503951203000c0744c02c4180f03a04075040100f0071401d04100c100b4a80c1821907501c15450007012900b080040080c017018041c888080d1207850103080181c40b15107170061458207a1226075024443c041545c114401c40c548502181d1081c03401614a0303003880c0e05643c0940160101a0040b54041c40920440f070303482c01300704441500c80420507002640707201c3c00760503104d0401c030907002203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 925324856 1250 925323606 925323611
    0x9091e020112051021050106050a080706080703110c0307060c05090307060e1807020f06011a120a1b12050f011d090f120a1704032f0304081f 62
    0x260250ba0000c1090107002e0481502280740d903034140c00f10003990300c2e9402c04240c00101150060300c030405042141030341031060b802000550745403010010403408910034000310794031211b803d020443c459990590014400d003800308441e5240d400300d01e15130700310032040406540041244024000540940c6111080c1400c00524146e40c0d0300110362628258064041403180b104520034060301c0f00c207900ba004004801045205013400725009440d00d003900c0361761515100d023200200d620803c8100c030243c0d103039000c480f03546414403440c5024459000100441d2085684840272000d100c20484070200e0186155200d42012014590010403501e010707042c01004080d480060007056401c00007101e040d42c882e02d030103e01d90b481e0000c161a000904810401500840300100c00c00484100a40035036162611002c000300742d003010400200c0d07c2100c0180024550403a944000720a030112020342c02c890002c0c04641c481210074061940d44250b1164030140d1148100002e54120f00c13149048428865209 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 925326106 1250 925324856 925324913
    0x412030f050132151b0f010b01020d020f2a13320406020702060f040306230f06091003060e03090a0f14060307050c16230319020402090a0909 62
    0x4150700300c4001d6044e21400c100080d11051582201107060a400c000e002164000404903080c2c80c0a0039603403800901511484520b80704150011404004103446140280441c001d10103c1360700141ca8580640503a001e880c00c61f444584a500b6442800c00303008101080540d50181290552210038810b2111440d060031202c034141c80c030341025508180c01040141e110099800014214896110300b4004040002400010490141c009151104194101506007032140c00701c046e01c02c0c011a01c05011000c9000010050715080d248290001901045001c8860f2607a0f21300c1c0881d900100c00740110761010418800616181800e000507080c3c25a140040b140307080100c4940d51800e000e03191003400c0200008051b0380c80398040e900420002c8044440003a01c0002040c2c085820b4001e1007449400c0e280d00324240144403080c24070102e009001401c94401e0680461014209040104d0b40683c0802c20700000343c0d60300c80d10070050001c50500241d01d0001e4a000031201c00e03d0517101341c0b0110300012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 925327356 1250 925326106 925326109
    0xb180106020d0e15220306090209010e0411090403020c060c03030a0608070b18061e09010f2c0a0e070824100e120714090615030412030f050132 63
    0x1541c40040407035070609a10b030440b414105c482c45d640302000081e2900420300000c2400a070307400c403080841c026240d980c01d0340d0701c48800d008a00b008545c003030803405c00006040b805042c2200a0740d03220f402881514500c1044e0380002d642644000d5409020b50f101100b84811024103220b040010301d130a000419140d071802d81d80c907155006050003602e00c061155041c082a0f202e8804484030308440e140c11518850b03008232104c0880e00118001c2c2d000608084400505902a100c4000d9614180c1c80f44117001e0518403055001000841c001c80c0c00c044400000680881040b81440c018446501d81080720324020420054055030381a400b844202d418a8840701b40e00c90300303080c0000d045107203056144030b6051804a0407807904000000e18900c106640056068040e074150214050304a5201a86840b61010000048031184111041c0907040004c21700240e00f40081c034681004505010540c2900c1030023120459000341c1c860404010008100e420f44154041c1048803402e1007044410140724840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 925328606 1250 925327356 925327369
    0x11a04110c07210501111c0902060d0e0f0105070903030206071d041a0a0b130e010503100207020307120b0f010602030a080406020c28020f1e040c030b180106020d0e 72
    0x81480d41c946040055a0303034000700003e042807081d8100c00280089840460b83c0794483d80604820820b04400c40d030310202803011801211400d80d00149054200418002c800c1e0041c001070341000301520400d0310390b41036000300b8098540702d00c10503203441c11080d1031424041e007444001080f107820803050120502241600d0003070850b120b1825a030008540120741c40a170a590401c5800070b51101d41301c1d0002980d01c00d0b030801011900020914241e8240d030342c44a010002d6028050f89503d604040c0d04002184640c1d40a010190700040032180017507a05c5851341142261510b00b96446c12070316041040b050003403021280100303c80d00c000c43c90155140c400410159001c0d000421480d0005907030604100200030a8960303d10030040789641c00803043c00c0900704520800200d000d41c0010466903211301d003266003107441000550040401c10b104400700b10041405140b104141590307a124507281d0f861300181e8000e40009a900c80d8200c1d41082d001178600f0300040c2d401001c000f5000024180d549508 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 925329856 1250 925328606 925328609
    0x20a081207051b060a181a0402040b0604080102040e0f011508042306100504110d02130b030f0718140d1e030203210403080423011a04110c07 62
    0x320100160361240c020480e1680700d03010349003100e454026201c00c81c0a10100e0303071380c3c0648800c190410486a80c1140c111018400c6d480c040c0001c2903440e960000380c0c8900074084e03803040c8000d000080b20541100004d00c6c0e42c200307820484a5a5021900784400d420608100d500b0107043d0541303811a62410240308030310700c68001d500c1c042110100200d000c0150726a500e051280c81d2080c50640403111446640e958103044940c5150640385039000190703814180f1640181ca18080d10760b0f842c181d41e00c030704203010f580b000f079078504140c23900c94000400c007040780065800b6498030b500e07064031414241401000200e0400102d400f01c5500002042508000b141d00240ca04054031019000c1e17016090070400680c01c2040c45d0440d40c07041c1c800f00c0405502000808190311502408580940792600c14140800700302c2d0000d020503601d00104000c00c0c00c0002da40c84d00e42000707900112000400c4451400e40d00c1d0010b000d0070070700303401441215a25080c01200c000c98110001a0700741a50284202d5448005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 925331106 1250 925329856 925329877
    0x801030b01141c1a151c0308130f0507030f030305060406270615170705030903040302041d100e1209030c011b0804030503280c02090705070c0e010510020a08 69
    0x1100740860400444100006440101001d80b04e5286050713941407010044404000b4400d410000888a01005004012207001d030580d481500e030307682d892030101c0f48504c401d074282c85a41c1c0c0da20525001900400151025601c50000980314031650715018003030740c602800c6030f8800e5007000340501840241c1341001800c42d5403143d44400140c1c0880c400c0c00201501d401481c604120040010011038020b1202044d414841995096650315040200d0b014041513404061540081004002528141e0452011100047c1d0310380e220322451100c0d03a02d06004006680c2380742da10b0700ca80c1810348000b8003038a504005e101c410940342000b8000041c3e2a400c03026286810710000c2094450301d0074851502110481e030010300240c1d200d4517424400c2e40d1381c0098041d0000c442c100c004421080300301c01d8a000021403142c85440c0c03d1401c035802c008030710400400c0201004028444140420290506a4010003041c80a2016541080306220300e498441049405641c0040000000100c080301214101d104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 925332356 1250 925331106 925331149
    0x91c0f090b070b0c161e12080f041112100e0d0306080c040e0f060c03090c0d0803270d09170120070812160e031f02030c0c0307030801030b0114 63
    0xc00e1030b45d04c0c0c1c00044108010f409011042c80d01c1500419110703520704032078001c284180d65100021003c594080e030403161760b00c003210500086000100280d01030b6080e004000d2100100d641c42403045131605120b030f8203010310030707417a0480c0c05c20540c024841003240d105586000c1c004142450640c2c0ea803441c3c0041c0c52401150b0720500b00c045458107000242c10b11016105030b4020703060140319600c1e00d07001a90303100c0c003500982952030030600c0e03d0107001d0305071303a400001a401c59503480d00b1500c0c2101c1002c0c80120007922511800000202032190b103124401e2078032085601070420520f104503030010134401030168548540c0d034001d002d40b54404a00141c520071125511412440c003040540034501805003820084801d10041d00c64900f10a2034058030ba0f0755146050342c1800400d03550300842c80084440701c1e0305e8900d43c5405c2089400959000e0342c0e00111503d400d041e045824a15808030409400007240f0303000500c200b1400d02c017240d00410202000074890700316000028004908070000c00d22450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 925333606 1250 925332356 925332367
    0x4020d0b0f0414013e030f040c050d0c05190f182f0a020307020316050301050702060f071206051804233705010e07060809070e091c0f090b070b0c 64
    0x1807200404400d0045c56910450712810282041d0310800d00954040b200031058050104a9040154100c10309a4025078031041052078035003880400300e4a4902000103030002a00465803102001080700242341e000b22554200800018580464944d0310360341d070314106030f20141504005c0d084d0341e640c1200317a031450055030f803401010264594810702e88000e415004e40100000110f04405004003150b01c1940241308a41d20803504907140c040488150b04c00c0c0c040d01c808142c84500c11003403003020341880f482c0010300948600000c1c0c003003800650000c11181c01d0204000c00c00040007a49508031800780790014a0f07080401c130b03941c2c0700d000304c40300c4016801c0001f0600b1249180b2000d00c84400d100102505480310701c5050031800b8101c6400c0d556594880c1ca800040c2c000c1c8a1442144100b50f58030207083c80da4109810304075000e03405002c0b40c89512500c0c600752000c0e2400380600c1c4032501d0f5611520002045624050481d040e076500c4a48148810f0284070040340c401c140326076010b52080c0d502e0ba07440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 925334856 1250 925333606 925333691
    0x12010e0a0b010528230a0e03010b101101020c340806010302010302030a1d0d02070b040e040b0601030902060a02012406051e041a030910050c0403030804020d0b0f041401 74
    0x4030940e0659041420070410000300c2c428440300406c5094502e60b40c4840080e0218149801c0c2c0d60402ca503140c001c4d1084003070420f00da1007010380003007010b5003c2c009803404140035551894034107038580c6021481611170100500d01e6110107142c0e150130300f5050504000349801e92085d01c840b01444081c0c10300da00000080c0c14032407140c0c49202000d00e6180d500300c510000d40240c0356103020915a15002d84522103001c42c5981c1c042d820381d411034103c0c22072490940e031165140c50900401810440c14140c0380c0d00d065006950700c034060100f241c0c250f4000074500500c05118040c1c0580398103142144d45c10034409014165201d41110310751301000c08071a00040c018030002d205885030380d00c2a6100307440c04920307501500c18280110f00905154040741c40c21101042804201c410550343c01d045c2400420007040082d01a402d41c683c0180020240e00120a65480314612002c003140d03854040c00c400d0040100f00300080700814192803c00000300071503094048910300410488c2d84600901c1040000040300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 925336106 1250 925334856 925334867
    0x90606050a06050307020d030b100e06370507030f03090c0810023112050c0d0c170f0705041a060406090e01060509030a0b0a0212010e0a0b010528 64
    0x202030161414440c507a660794000e0280e04140c1c1d0100050042d0100e00c0300b80d5220f40540148102d0041c080c020350709800c1c10035a1030709030300d1080d2034000c0d0062116210f00c00300c002c01141c103080703011551714002d072619103044002a00300c2404400c1c0b04040c0075100c0400e40c003062054240501d8240090501d40c0d40c1400d00c0340c1d100703a0344200700510502d051041c2e20320054026000c1c81d00003900d14a00801000440e0388035420002c8500c0029a003490704014154480003008910360091040e100e40302511400701e401501e840b20166500514050100710b02c2144801c3d500860407084050141c091000807102e444004a105051007030b6242e02100001010000d2020625440100059591640c07008082c040304498800e061044642d08000600e403401030085458961006014107030300c40d81d0f5582d8020703064025210707a010503401c2c4004107445484a00141c064080030104c250f0f035240105402040d60f1480000c3c9040243c2070009507072342c40342030036400d040c2290381d071022428400c0080101e92 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 925337356 1250 925336106 925336109
    0x70204020d0911040c021c21020d0b010f0813060b04020f1303050d05040e07030f06051210150806040206030603010b1f09050105040308091014040816080601050310090606 75
    0x1a01e4600303841c0d1400c001c1e032100b003004028401d8605100a842e20402070361580d007140007c078020841000e592181c24450039518910644011401e80c003103110080300d50480e0803070741060309a03503034651030382d9055032f085081074840ca1350916242d03034030386402400b03009403e09aa074000e2901d07450700451002555540c06564400e00c403010080c0e20340d0f0801040001040661000740d855000c0d43d00c813822001e21402c1102d0a03908503c1d0f86070303110b0f00c1d648803c600401c1009909a042a40c5000c08692540c6814280302001c6001c00103040c0341c00240162002c89140c17159038012013460100800080c0c20115020754020b80448420340c40c5c1d503805c00801d025094031403004d0303070060204113626800381c89103900701c2130807049644d05e0010546503001034620b403003140000303002c0400c1840040c42c60702c0c0c0390004101d40e10b035525060091094845002a40303401c141c001d1061600503105403850344580c15003d1008006000090001d949041d0101392150002d80a20352919140c02d40c500900a49811990 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 925338606 1250 925337356 925337377
    0x15051309021c0b04020f0603040b180109170a080106090f060c0510020c030a0305070804020d02040911120309031b0a06050a03091509021c1128060503011a070503090607020402 77
    0x401402d00740c9800190702e10b04590481c40360250302030020440c100300080d0391090740e010f00803071403030346444039a1080011545d0f0354042035929100d4001c00100811f1480c2c0074400c9101c04951107590241000e00301e004140c1100d001c01542a10400c062a08000c0d5642100c00900b0700704030000c000e007041030825501c2c5c4d0640d80401c0c000201012402e40c0000204a000c01a54041050752100780c01141d0081c03060341e010703620003a008820346c0507207446c0e0311003039074944503071a1021051450004114921071115047d822a000411219054103080c08880743c05040d40b100703141c90701c0d80d1400091002000d07004640c01c111000c00d10424103070182c0d018500c81a00130300c0c15055501c45803481c9018181060007280503c080c041c483d000c1e12007200e03040070384941c0b02181e0314a4503030410a00c1444080c990958124140911183d02510708038003010000d44940e03594240c1c0ca6040c60b94100784646103500e02c3c0c05400080188101141d004400ea4104d0001191070955540721800000d000e401003000f4072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 925339856 1250 925338606 925338649
    0x3082d07050705070b0726070b07020c0102010b03030c0a03050c0712080301090b120606130b1206090f0304030507180603020612040606120c15030204150509041505130902 75
    0x8540d0603004005041d405118400f260905501c0d8543d44440b800381d000010002028a504800005291803101a407044607000f1181400c84039121034090203816180302025030003d2000004c40d581c2801a5184201c003600214602070a035442143e03204580760014003082808500458420401d111950050441000800e807020044c28040d8143e8002e119401d03030b0a1420309098402c3c1800401e01943c10880b80180ca40e6030780b1481400000c50b541310403514069034800000e08103a0f102084418803c0d40e04009103a50b180c41504585001003516003a49603600c1800204000343d0001054400d54166450b40303900750100c10512009892150002580301d1340104140545c2042c50280e1845240a1003040c00700325034412158040308240100606404501001400444460151200d612040c0e150040c0760a40e58418509030921126034030000610002c0c20003110325160044584901d0804130304199035181c480001c0c0c0c040c0000704890b440e107440d2004403046d995241c0b5000b41e80c1d040c030500fa = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 925341106 1250 925339856 925339861
    0x7080a0b06270a0506010c1e020f21061807090b0607080a021b0a06020c210105070206011d011d1e071808120f1c022701030903082d 58
    0x20b0000361070b0441d15001050b1800000402941c45140004101d80d00604144800c2d0410304031140f0002c10044160f0b005100300e140540140c071061310380102e6106160155801c82005441c0c20704154018240201c464400c90302e1400f1180003142c0300c1c04642d0f1004001803501c1070003010425074040c40e8030140903044c01040f0f042c4583d80100c1d4072001680d51055651104200c1020000001494010100183e00000160301c290405292814209130b07082c1050f240901246452400d5aa084803040010703000325004000480b0b03d1804903c071101c09014412156051030b103092600a5080520303814800b102c80854411010902c01d1174000d0140c41c00030031640707051030002c0d040302c02c90b1000c004001400710b000a000360300460808071001d0410800792400e200c0e00390005864200c05190b2194826004000c07400400301e10080c6411102610350900c50346148040c1c02411813400001810b150810013003200090740118040d0384034003075000c480380e0750323100300503a600b41d0769075848181f55030589005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 925342356 1250 925341106 925341169
    0x3105010515030c01020d23090607060c090603050c0d0207030e0901030c150c0507060302090a080706080103140a03021e0a0c03050f0708070e0606090f270907080a0b06 73
    0xc0080c0c641c020b804483c4464048401240e44051251805000500320740300e619094100d0000c40d0350040482e050181012481000118182e004a008850080e903600c0c1034107141d81c200c09070390024805400e081040d0716101030040140c2c07080d101003a00d0554000303101010140151041103805001501c141a0796840c0e2400020b9400940902003d0030903289228911511030345200d8299035201c401382c0780c0c4514288040e4083e4009155042d44080891b101085042003000141c0052a05030380f900100e500d58100200c40810500c1202501d401116007203012030740015141031020400d0b01c0807111004c0d4228a607090240703039a402004c2840b601000414003a00151641c107020f002070640d14125900e060050703940782c40740b107031100080c80034000403141d00d0814040c107502480076004000c1d29500f200000d10411448225903114001c8541e0b50031101d50750036032990311030580c1d401490014240201d02c0d548848ac094020042c001d80400100c240e207402800c0d00c08a03055000d1080b0042c2c41c1c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 925343606 1250 925342356 925342381
    0x38090a0506010503030901020304090b060f0f09040f090803070f2015090d0c15020f0301080d140c03040b07060e0118110316030201030e012406120531050105 69
    0x80d2060311901c400440e41d4a004005c0b90440e0105800562130103141040b941c01a02c1c440c80840d80c0300a06000001d00d03182404000e0500300301d0039869650ba1000b4008210441d00701103540828a4681005400007451800c03c907600142c031410400d6003400ca0b54002c541c84501c10412410700007241044090b00c000000380c080303000c40342107440e585955031541c0450b40d48241d44030400000b540c0c40c0c0c414000c90080d61155098070079140e809450301c2a401031900096000307a209180950000340c1071040c003940016076200784ea500001a034609080842e80990300e0141d4000d00c1c00030403001a00d202080410f07070190a801e1b030003a0082c00886950342c3d50324448501710000340d80143d0ad1580d4000307185400b003950982d09140360510a401c03170458004500030807604000c00d030299611060801d9894081108038028910389200004241c00d0040080c610711450800910980c100f0b41070100c9148004040c0c0d05001e2403d85e41194007245046000104000081c0900a5403a20040c40810030402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 925344856 1250 925343606 925343623
    0x31a0a09060c0f02060f0c09060a0507060c0804030e040614060903190303150b1608220e090f010e25031506052707050a26070f020601033809 62
    0x41d02515811b903200c40c10341484200132036000000020401c98059a0f2a0041c044c1c014a45589030490420030301c0d0740c0d0700044500507174481300826130880c1044101903004013042d95550080ea0140b0040b46003412070411308418549052040d180845d845082e51010414142d040f00ca0395440d9081300c0b0340c2d0a018004181040b00450110344001c2c0110314102010102c85e44042d103c1c03000401c1d10b400c0d0711a01042c0c5c100c103403282000d07001244842c000520240d90346020304840044002d8605020750100e01e08a00d000c4013001690501c3c04c0319010483c08101840410000488803a45081029003c01d03000c403075400082880400543c2c201d548061a40644c041e03d8094612f5909092486240600c9003001c2c1d20440f8101e140b50000303107081e446400945a210700b42c5c10040c3c5555011990410b080d0f1500c0c12200c506203680042100240e030003e8002400e21181c00134000da54155202c40300c110301c0c5000a07140c402c0d001050b118002d2015010901c5103010445049070030b04203280a0b5803248010b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 925346106 1250 925344856 925344887
    0x4080306090c040b1c09051b040e010e120a0c0803130317060d020d0230010c0c0c0303180b0a020f010e0c131109040912031104031a0a09060c 62
    0x10900028266075038902140c09a031410000c0314109940c1c00191241740103d49103010005403207542d490001242000303502d052050000070303406164103400500040740c0c08080101800d03810001606404180170640041800d01b04281581e1143c0049050303915517400c035001840100000200b03e100d05081140c042680d00c01d9a4260340c41c01c240407024030410b42a1526a07000c5c0e22581c015005142c04403e4a140500c0a00021201524050300c2144202105449005030050100040368420207200d400480c0c42c40341013072181600142c40e5443ca02c180c80c000103003844004031480301381a030424071160040110f02c008595501e44014000c2d21030324035841c80fa5071513081120402c1c1408002c240c44003441000741080f00c42c8466000340c10302604e030b00a0b64203000141041405d003d84c8881c00340b520580d01640382c00795551520388004044490802c040a07a80406020620001c0c2c00c0c0c80c4507060419040810340810348400d8178600c0101905035004080c54035200d10015000e41080c00745804200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 925347356 1250 925346106 925346119
    0x3030e0f0a080d0206010b0703050306061c02030a02071505090a170c01152303030a031a03060103141504031403270115080a170715020c01021804021c180b04080306 72
    0xe8440f0b47e00185d005d050401400720f5000c0c03000400c07500f014005006101d02c0004440304885000b1030000499200350b680d8030005400007049400c0c408107402c2081c881180300010841031600d40316180d200c0c10156401401d50060320340e0031140c0102d120903030b0082d0107110700030011903102c1c1501012041b1540b0454082e47d050b20b161f404144210045d034418400c02802842c502000e08100f140140641d04010341d00c41822400c4a0302d94504202d0180039510840090080e060942e030154580b032070ba020103d545a00c810200800a6808928013016001126003d6144d8607140c5407204030301301c00000c0000c03550290a4412150905410580043c80c1100c006031803103403030b05615911007000b0500a804c699007507500041e10104d62004000b002e001d101c15450408a00584c90181da0000c141202143e4020030841907039403a400c400e1b40c500c2c0b022101145042041c4089190b10343c050a803406110303076030388108035444a00885070745c84c16503c952110341900d460701d0803141c01d0304242c4005000b02e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 925348606 1250 925347356 925347359
    0x402010f0c3e100537030b09010609060309081908072c061e040f151715030f010f02270306010905060f04060902090f0f0a03030e0f0a080d020601 64
    0x1201d507040d80314000000d0300c4140c00c081283c078259456071004250001014640d684044c2c0440fa1800307404007250b1202d100801002200c03401000d5a40101c0214400d68070a4010007480f604041d61404944403403c010a1030215820300074418003034401203030403600d0807080220340564410038451180360280c455000c20380c0301d07910590301e1180c141c0134000000451303041c841c100c1c0341c10300180603040d21800c001517400f0020078961009400036808180408807941d07040c04005414200c004402d5607514080c0d402d8020050355041c800c0010f40090403021810000949a03101400085c1c00714078980024841408183c0481c0c00031b40c45401ca406900030380394150301150000480c001c0f00303001c00070001c1c00c0b03990911040c080144005054960310507869a0304030041e440c3c500409000b00012440140c403059201d0500009a030401c0c002841001003803078141d082c1e0742c0c8128500c00c0d03940501e09868003800480c0804c140302d06100d04c0c1613000c49039180016000700b0015512962000c075a00340c454a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 925349856 1250 925348606 925348703
    0xa0f020415080c07050f0a0506010e0c09060a030f0524060307021e07050307030b01080f061b090406091a030d0e010c0b060102031218070501020a02090402010f0c 71
    0x34000e501410108201906020000a1007030141c603800c69180d129a40ca81195507488625104c80340011310966003003001e4050902a041c0030050041000748007000251070711002e05890f500c079101005110350350226609032422300ca031303120001d880d000f4a810001c90920300b05510403070344910115680f02d00035401e12101800c010054900481ca150000c1481c854500303d0071000d8a841c1150241034841c1440009540c3d5007082150000c5000d688070720341c1541070070291070600d5601e19148178550301280610032aa0000c5220f03440d002c2c003944a01c0e407910f01003800100540840c0e482070000070300703001295030410820384401017240300440031240844c0b600c03581519182c401200190204074030079044d0021a00e101c01d0140e01c4101441980d15101d0404006403000300d003079503400340080310407000d81c4101804012200140030240006c0c00710f0305c85580060402140240000d0411100c0a0700d220794900038252850915802501f101c420303054601000706040c0c010540300d444250900006489 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 925351106 1250 925349856 925349861
    0x3090d03060e01050603040516091506020109210207090f0c030c14070807020d060504050705150f0d111318050f010803070b04050c0307080601050f01082a130b030a0f 73
    0x2100c03a0a01c032070b5070300e07840c08003003102d41d4000070000d43e418040c0300d22010103090b44259044c09010300e08400207078913080400c182a0394400390096400d582c580b030900e902055010215184c103841c0c620851503042d034004400c900700302c59548000942030a001000c0c0280460342c11011100c509030b0b0301003045c86100c180454907060700007407480d68038030100300c0386002c03c0303103500284451800580782c480954034580c0d511046410071113007602d407130b044100240070030b10f03095690106035120648900e0508003001c102c03542a1040300d5001460300e50b50300e11264942d940c1c006032228891201d00b10849103035035102043d450110161480c030140e20300701c00511414615240d190590342c645c0015070803c0c1056903181003285003d0000e0300d541c45000d1f80c0900991f400c100c940040d04103040501076651500b818090342c1902c6800c0309040c0015401008100c2c00b010300609403082ca01d24103d000c1c150f040c5a00503c6101d1881c50800101d004500440e106a0340b20046000f291090310400003110f81e034095104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 925352356 1250 925351106 925351109
    0x209060109050433120303020f07080307050318010b0105090904020d050f160509070e0f0a0e150405091207031809050709081908040b0f0412060623090403052a0303090d0306 76
    0x24070308081405e0010a10a90141101000c4522034501c3d1161a49804030301e504100e0302e0000003100002001282e01b00745283c042086107900089c003000c611038002030b000380074a6021300d0141e241d003c0000c00755612450b0600c04141c120003610f03d034441d0111000e450314040c12002103c00a00d01c400034041c20807040ca80e20840360303036860070b40c4028a40200440c01101e1445203a02180f080008606c1c104503150240c007402c2c40e40b040100080126040c0700548000400360300154011202c60104040c482040b14161a414609241d1380c1d511580e682180c0c0d0a030b13400c50700003540703401e0421101642081c44142550030a4007280c02100781d40b8401d0040311607100004020180501c030030403199407140d0142031b641361411041c60078140c4416030a000c0340309000303060361040e80716141048020030042d20100c2d0010010182c00d10148050041252000c02800080400a0000320a00e5900b0b0088112107103001107182e02680d00a2108100c0e038940083e0365506080c001d101028420038020b2040c0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 925353606 1250 925352356 925352369
    0xa09170d02030711070e07050a030f0608010213050a03080412080706050405030711240a12020d0902041d0613060b100f110a03020c040902010c020910030303140601020a0209060109050433 82
    0x3c1d403ea1f11000c0461b0242c0200c800d6100380b40d141c2480d1014407200d809400d01400c041d5000507101c2010b07004007404910b0590005000c1c0e014140103102040d02a070446044c1d490700d04810454503e00c0c94003660300d201d0403d010b415986044140001c0241c0440201100c9001e0b444e220811701d41c15080144200092440e240252020802c000c06120a840540007420b031030b0400c02400150000e41e074082c3d038800c030f101d101da15a95401060442c94184160700580703004640f6a01e842461400250b9a600b000d0b0090010203a0743c40480308000c2280c00c0250032050281908092071004c50020b4a60804107000601194151442180750b100001c1d82c2c05030140c066000f0316425070014140710080102c0c06041c1d04100c00c181410000d42c4078110013900420700003081500940c60b50a008084a103070841c102d144030307400ca042c441a44c0e800162400010340460340d0000341c0e107403c001690500290303486190403505040301c11212822044d08100d005140c1030b205400c4041c2d0707840481d0341403007600806 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 925354856 1250 925353606 925353629
    0x203040b280c021f0207060f06050120010204051302031009022502030a050109080c0f0304030c2303120d0e0715110102130f15020a0b0a09170d0203071107 68
    0x80010706010b07080680040400d0050325600b58004441c018040c000080d010503482c0c001503040200100d41c8034248100b54894000c0003407500b044002040243e4002c59020f40019803202070304038420a50403940203040081c035684c10f90a4400d50500a904100c9140310142d00c2c07235200040310080c134000c0701d03860302d003807840d4181c200e036820194100c03d03202c2001641c241c860b1a6007080040c0e0709114078040c41d4042d40f0520703212103204070000d281121072200307070105800070302c002c00000c3c03002d185580c140c8030a04d5640c002c980f0041c1c91242c9a80040c0c02e00d5526105884003a512855654014121015514410301808030403203001951200c030362003403103200004a2071000c0c209202d00000d100302c01d06940094030340b800441013140c02410035003004200e024048800c00a04e8071080d00516001c0c0503002910795000151a00800807100504100b00030791284034120400211541441c000d4008480181d01d540300e20a090000f50021a0000d012036400245180b1f1010b0000c0c101c0704071640b01042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 925356106 1250 925354856 925354921
    0x3050a09020a152132150301020c07030308070905040203040c12081902010605180403020d030c021908090f0d050d03020d090204052a040b07082203060203040b 70
    0x561030101c030710340f150300410003c1e88481984184160850250350b42e41030340800e0039040d882d00c0e0701c80f0510f24010f01d40b400c0e0610046240b41c40c290803d059016010f044615880b0f040940801d01901c2080980c11450084420100400d41c01c0307003145006809680e1500500ba45560a100492009660162141204080c108419165281051016840340e1000e6082c151004076102c40350840c0090a00580d4440780c06001e0750520f880174205ea0700504950100a0a054074007a40f03d80405402804050700d490803480014001c000c1c0003040740da0f8100c01424182542000811500701225403840303a02e112143d0480c074030700240701b002e1443c1c001020b803800041e030308810f400030b6000600c04c201c0780b078440d080c03000540d039030348100d0344503410381102c5039500103104042102d01c600c031301c522800c082010b0006114410003c02a038000d903a01c0750a0550f03403c851408481c28840c40251707e00842200c003804003c000d00354020b035015a2040404070040d884001c0c84200010021601241481c0d50303059 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 925357356 1250 925356106 925356119
    0x9160504230c0714060a0c031812051b01061a0703050412150c0f080601020303150d080c03041502010b0306280905030c240c0a0807092403050a09020a 66
    0x940390000490041189400f40039a80c41c440010003440c101c4864022004216201226000d001e08100346450104102c120011140c60b000d410f07a003000c0c15408160804080c514024400c0b1144444081582d00c404800102c1d901d02800c0d01e40501d00c2c0d162003912806540020000c10740d0066079040d12580d09240c10124071140c80d0f1108401510680759411104003100311a00c01c48903143c203244d40d00380c841000c0e8040030307004060140005046620810421004200002d0101781d03000040300c80e100d0003071b2315007007a600f580510044174015000004c1c0c00120180c41052000a901d81d54000b409440c00c02c03810140c403000100e0345030750b2100089040300d07180381ca58400c036540399808c03074000580d8101645550f80755030004418841c0c1da48c801746002108007a45c20030f5000d14001c90700240c1c4a0f01d090001c0d03800a0061640c003c050000035000705045a000c0c0d48035001070403486000c81d81ea80c150389180d04100410600340d40c0400d02e008040b070782d02c20650041c0500160007802d0304411914020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 925358606 1250 925357356 925357421
    0x30f1606080a09150b091003150b03031207031407030501150305071211040501030f06080d110a05060403210e061504091505041202212109160504 64
    0x404141c8415603c1d00d680d8002009060102401c10040d50001495408074042c0001e0000250040d4041c002000f0104001506020030388207110300e0001c0400e0004640000c2440e6003d0064070980d066a40010041c1d6030303030f15500c0000140784005080d404e031f8036000810b40c21154203000c0c8c051240c42d00742e0f8103000300c1d0103900f007150400c0d0385207005010318042c0e001c0e21080380c00c10a10017a5811002501704101e60b0726010b80d00d0709030b07840c904c100492403405000c6507464207000344040038801e10740e401d0f4069003000c0c0a2440b489800405640c0d0614080c64001c1051008050924086002c860204400c0f0420320801e090b0f082e0f1607000700750340e407248c403500d01400b241001e00c16441901c500400c40040c0ca03082600300080b40412001c01c242c2850300e4110080c0500c048030804541c411006c0d04241c3c00b80744150820210f8100604e81c1e03512041d0b100350010042004005070100380d810030f21000000010b050441203103402501c0150607101c004001c2a5402c0383c8103c3d94050301003814026881094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 925359712 1106 925358606 925358611
    0x2010b0114040320090403050d14090a030c02040e0d0e0a050907082a0a021501090515060315041805060903070b01090b0f040509010b030f160608 64
    0x1d45054240e4021840003820b04180f280d0240107801160941500b81d06001e003100c0040e01e8130703040280c115844075000b41c5010745000008804a01400c1c0d032103000707440c9000542180c41240d2011100c960034900e080c3d0307105580c4c0d020114510020400b1103d500781c43d440303120983d108241002040303000303684154002d8201c00c3c10488101c0e4444000d03a44a084079032b8175041028094045102c421040c824a89030501c009029075003c0e8001031001d08140c021202e02c41d20380e0701c1fa803c2400f910346c103858410200f0300f1196007000c43c1c6003020165070702140307000e90b62240e21240d20008040d101100380010740621182a0541030000c1402070706c2d4401c03451401549441415500e41508800500c10080f61a07540c3c004047c4513a1044050481600000c10902c030a05003050002c2c000d0a100c2042842449a074078404040100480d1262031596001c181800007440d02c00152501e43c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 925179856 925359712 := by
  have h0 := BRFrame.cov_init 925179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 925179856 ≤ n) (h2 : n < 925359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
