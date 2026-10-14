-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2256
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:09:23.446949+00:00
-- url     : https://prove2.me/submissions/133784a7-8c0a-42aa-bf6d-da15bce9533e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 405575539 ≤ n < 405755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 405576789 1250 405575539 405575543
    0x1180305100510060c03050c0a0f0b16020604080d0515090703090303060f080d110a0204110405030c011e140c24090c03030d0b19080f0f0307050d0c03020a080c0109 72
    0x1090400065401c05241c0350242a143c064a0710b20b00e0005c6510229455003100c0700c90380040c401e03100100003040c110342c202412940701e41c80c014024a011840e030803048080d00322280c15948440c1c180700c00202c0e0801500c2c040801071100181c1a516215800b00da01c03018221550424442414800403036410f070401d0302130314000d840511440350741c1c0004101c0030201e449581a940c100307181c801140c5101d00302d0b542c14840d1a80803101508591340000b0212020100c41d8019000002010842c0e810188000b0070200402d00381000c41000c1440d100d501c0280c40d411450400860b4014040311600c03400549481d4080c00084901d401e8291404200a450f01118645990381d01e4000480202000410261a080c060091800e0076465650301c00a005c1e0185250340c00380415030496150305011420380e009000b100c0040045020480e422810440d800b1036160300c58008114140c0411000a407210082c80fa601c2d00d00d01c1240242022410181294402085032000081c40c200c244815002002d00038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 405578039 1250 405576789 405576791
    0x3060406080a12050a0504090f0f0f02070c050f030f120a08100612020d0f09031701050411190c1e0209010f0303170c0f0409021c14150118030510 64
    0x241c0c03544011035507541d00c50320050010341007155614480e0302c100d01a00c1d98040030308201342407640341c0c640e03001512103103070142c1049540c40070f40143c0710a181c003800da81d1040000d4214a000c1c000c2c1c031059030095450040c54060f110900302d2420715101000075030401e40c004002d883c4103240094443d59158412a80c200005540b0f03004036003250a10f0501710111666501c0d5001c520307002441c408045d4020a20890078141d0f507803500304136250b80c0d000c0c0c5240d02e4442e9590701140b1071240c0043e541074030706070441400790b4a800c04070403401286000304c91a07007043c1500400c0c0807001d00c03002c680c3c1151f8403500a24059203080482080682d001c00d07100c80d14070031100000d43c1c4e0303201d5507140101e074103501c40a130004002240039800a4810300c1400d800c04529001149049805030050a01d82e1041d032102450a50025400c1c003c2d0400e40c854850300c054001040c482542418101042098003400c08011800e00343e404d80011b131702074028011903882c0303c01a805d4084d81ca04200740c0b60401000140d51072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 405579289 1250 405578039 405578051
    0x150506131505090303070326091f1503030806150f0a09050405101202010e120706030612020109060815030109060b0111160611030c0304080f162621030604 68
    0x40b03002e6010b4424403d0b01134011404c01c4640c0d2400c0301c3c90402140240c8041200c445840f80008502c41c10500c61200c040041090705945840300407090048a10192801c1c504000307140c5108041c255641129014500304940f82c582a00007500c9004044014a954000040c018030314845034011b0103c3e0400754a071200150350304d80501058400c1110b04c903403a02c00f500d000f0300c03c45c200d821941c000c0c54010314041d00714884240101d070700015059032244199014910810941d0f030b0601400c000b52203031100c050807140e680d9001034405005801f8450034030000303000150203c52107410900000b00c2c014001e001404c81800d0000081407600e90340f900003510710300300f01c8114500285003030b02c030303c84000707114141c45c50610102c07544544d07241e2a44840c0070801003642c401404101520103002040050f01d8682108030000b440c04060305000080019491810440180d1507924111300d18950f806090340300801502013824026000210607512030900040ca110142040103148a15000e890030061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 405580539 1250 405579289 405579329
    0x1060e13060503061f090605090103080d021b0606030f0a05120c1002160309090e0a020f060c01020c010b0f09070212030c0c03030403020c010e180406020a0219080a031b050a0315050613 81
    0x1f034400303a0094035042501800104000761840c0c0080010724401400107040400444501c20700c1c028500604840354840300511043e40b40c01d120350400005030900074000f42c145aa034080c0c6410000c101804c0ba0b0601003118002c0d280c040c800b42801c4041601c00b10340c2d800640e00c114010048888003900021900c0c7c201080c005560321500c001d20ba100d00c02070254056943c01c200f42014170754000b40d00038005100901d13502509001810325504240c0000c509055402e00707000e5120000c54642d486849a1000c0c0a901c58000c00c080034403150030307024075070b4070b68802c882e05089201d0700d4081c4030140b000100b0001419404510954000400da0310184200c40040800c40d10404070b08243d004c030102e80011500141107030b401031810b440d10b030041c0d40e4214840540700d104424115030580300040001025407403140e0501ca05003c001540715281034011503240000e14500a200f409028580d54800d0032074401c0354880460000c5c200200b50039910321202495007404066442070109850402c10b00d162 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 405581789 1250 405580539 405580541
    0xa11120a03060f030201170c0f040306020408060a090c060e0a0f031103010f06140405101703040608060406060c080304020411031602010f020705280602040303200601060e13060503061f09 82
    0x3c03c0744e40503500c0c0b20016008880081c0c401201414010f2400c50070042803560003140d20180000754080e0700c1c01600c982c6017003070072800c158004040d800b00c6403801310034000050145042105581151800c030a0300c040759800714800e901950880914140b1940c0c000040007558032080a650301d042c1c0c001e20525510310000015200d490040da4041c0220303400c0700d202820190700059101c211913003904d84459070f9400300752a944a0f6050710a11360070003d02448000d40226449030000720030350b0100001464424000d00b000100e24000382038603030000c0842e0540d903640e00000801400207105070764038188803101c1620701900540324000365081884002042b4141d1007079403c5160040080d0a21813a4031811b91035008685448040484061768500d0100c0c038180302920145219440f441c1169101700022250711500d0300a031002d5034440360041c0a481d42c052900244045c09407811410100c21600020203040e490b0002c2c1d8040c415081080990441c01c00382d03607030320545005c01000e40c0d03440c2d496602c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 405583039 1250 405581789 405581819
    0x30106241b060222050a180f14070f08040f0209040212010c0f0f09031115040f090c0806040203060307030308310b0f0c0313060e030d09050705040e120a11120a0306 72
    0x46d41c4200031a104214581c40000d81c0c10006401e1140024008000c0084004136031200001c0a02c80506c40200120035410414400b105425420300016a140a0341c45124a03a150382c8005d00800038800860304548030603c984607070f507080c94024004c1e80e40488008044108030248070000442c1c011503080340902462300101982d070001e4006500b241c5140510200c0348510f035840004210030000000c02c0c0030f103045104058100705602044104c800500200108406800a03100c3d601c100706100255900084910450f9410f05148985a8640941c61a5005030380314031b220070040b22818a071942c58141d40b82e10441d1040003440c105071580100861601411150103100032004c10105180083c644900c40c4118030456010412000380a0384504603000b40700003803000ca48901040c42000000e0201c040039103400d80b02003002101c2d002440f40e0741c101c03028018450090005c1c04031902803180e05200340d1411440122801c1d1031000d11110480d502505240e400079140c10310100303403501100054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 405584289 1250 405583039 405583049
    0xe0d0f05070b10050a08011b0908030a0c0809060c06010806071b03050c0a1a091203070504090f090b270a1203021803070f05030705030106241b060222 66
    0x10300709a03065a95100c840300c06408a00044508000001d140d9200ca1810000e00544c82c00420060808411001410b008221050a001c6007180510004100000f910942002403a2030001548982020051880307207a070069000180082c51000c601e0b030001e0344504a80141c022500700d035403090b0007103038044c03480e20100070365885140304040403038490405841c155408805403603050400e42e5903135803250020701590440c1c0d003458041020ba03540a100c8000e980050b220010300c1c500c1c0000c1d000703103544074038081c42480640e110b01000f8501202e520020f080c40c1e00044010690800d04101651903000c000130318008944a200500c180780c0104902c503200e580b000d0030402000c4100803c0c2d0103904250034910b6038103d119504040c558041010900a1420b007582e0300c503060400f800d050819042d41c110f14020787c1450760070004948000c03005629007820040303803021800b81980440d203c0740110885481c800030104418148450307640104a018001121030700c0302c03403546000b01c004840d10b120b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 405585539 1250 405584289 405584297
    0x609021c060812031801091109071e210f0204170a111507020a0311031213050111031e04090e0a020f04051509010305011401050a080307110604180e0d0f 67
    0xb040b140f00040400f079a04044600c048000d4141c0448030303070342150b01001082c0c880c0e42401000304c05504050781c0700358000c42c071850311980351003800a00120130910800060200120f0130f902c00c544c0721142e4030003006402c80c00028000d40d951102d035840a504240034030001c60322016881100e49000007500013105074003400c3d41603044149000c00012061088030703600310f86010010800166640c408000c007541c428001040391042c190223062a280c0c1801d0807041c07804d401c126908428950701d80550031a0400d02e04501904658003485056000d00110251141e00ca03000c4081d990f0341a5010340107a4400c54406c12802d201420441d80d00d030842000a034105007041c0740070110b410316800031030780860b08140c81e0b00314928080114805001c242e000380d800d6555280700320074a005440007640141000c0300c1651200781000c4002e500c91044e448020942d0f80000465006510307200d0944d4020b004a0401f4881440c0000c0548007419565115a040f802405480f070001d5000b52481d003400d13551555 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 405586789 1250 405585539 405585553
    0x120405030a1b05250503100507080a060f0b0d020403051603061404030f0c0c0803070f0204060801111b100912020607051c0203041e050d0f0503061e0a03060609021c0608 74
    0x2144c0282070285481042107200c001101040300d44041140150341c14540c040003903246003800d401000350802070446400941044006c100351301d00b080015050710f00d04800b0659440c076200c8804024821540002d0103806051619403c168502e1004412640994000e000b12040017200025001c2c0c2110000c0110380040c0030f180d42c09125010444a091180c050444200d48030000345180da0040801151007000d001400030460a203405094000e00000740280203540c42e41c048120180202e030302c070450304003080481400541040001c041781000b41e8504011004080c1031040148005601c6600940b0a400c00704018034410000c9075070070400c1240000580d452142440040d5201620030303035000e07101722404120070310640388034840148648020b201e8220624005445400e00c025288240402030003000850f0b10350b012080c1c1d50700880d000c02142c80025400140b1070b03040c070f5000506050326124011501c94003a50080650a411020990400194808520644000303000b010340c5a00140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 405588039 1250 405586789 405586813
    0xf0503010b0d060b03090a020a08120a14090d150510060905011803020a090608061501020c09091504080a0e04060803070b19090b01060e0d210203120405030a1b05 71
    0x200141401002085000c102c460b6507089040e501e0f007041d90b41c04007e07040161500210b1601d0710440000703010140150017001403050310300d041802580405814810440310b1004800d0307001089940842c401403140e030f812a298144040741c150134181881e80b052a103400b19516545900c51082250502e6582a00c2035051500440304150114078200f01d82c44058000b1005948002196010300b0f1441c00000304e651130152207a20700301c1c028003e0980c90300c80c200c0035601c590f40400c074091009004da94400041d00c034043ca180c900413034131600c084a00142401e11041002480040c4442401507464500500d0007004020807600b02c0c0c070601d12035500070022235000540400255178080c604900f5003009022900c5002d003600c01804c0204c42588840c801402103d420061300d03071803039000b99484e1040015603598011803201800d84000044010380c1c002180c60310810450701e003028040c8404980b4102403400a070703a82c002e4082480801da2015503c461041a403407410092500308004020b01071501c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 405589289 1250 405588039 405588059
    0x9010506090105040305070b07020f0604060507082107030c08010f0e0414030c06090d2a0b0429040507320a050406061e030b131802100c0b070f050301 66
    0x907448981031000a11000010503018801640281f84042c460756503442e1910400209409212105200745000c1c0001c0c010383e40e010050329074942d44a20500da80e0020403c0d20788480d1030421400e59205411020085103507415041203031468400c0d2500343c816601c0c0c0d6115450f2075010301a10b21201d40290004010034030110007003032050081400c2c0c91400020300c18003800c0802c1111006c0701c6602451060007100c2e4890340c01d604181520300945825542e814413142d490029142c041d0100c00420045414807075141c101841030400c5191042d07800815940e41183c0380411981910b0342e0055910000d855124130301103004d2504801800070158010301420800c0402c034442c2e00f03403c018101d00102d50780e225445041c01034202900c8e50500503c480450100312203104440c0c0c010035080049185040e10f400750301904000c040040030039040340300e0b1610215041652000b9501c01d80c2a079240c8605030b00003a400c4001c178041c0c0010382d416610300e44107880c031400c5003202e000000d104100402c2481e0724 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 405590539 1250 405589289 405589297
    0xe1f03110306240904091b0b090108040602070c051c02090f04020d020d0606050306250228060b19030c06031401050d02010e1207050102010e01110a032301091406060909010506 77
    0x400c40040d410201030030085012680c0e00c07034003100e5021600b011010340181c03c40d0107c0c0144521003c5615140016000806010016100800054000c5a881d08121032107003540058003024088501c1d25003415040e82d860050311030142e000b800c0e6078010507007050000314901e203c1d40d00506243d000354010350030b00202c0c1404220544040d0b0342c0b00b1002c1170b01d980c280f0071039005281989845c1031070200c0b040540c4903441000722110641d8800b10403558118034910600d84007004401e800c8404403090b05100e0083c10281c04250703808071000100151420108816a00b580e000b1842001f4a54480109400725407c0d02034192050008600400080c64000040d00540f4818540082005c400a000c60741940354151680c078550015501400300f564244900d00102403507a0080c0310400750500025510b224081c8c2480130981c03500949501c1c601e5003039100044030407084c413021041d070f0740e9066000203050094018100b102e04401040003494004142e440e499401000c8100c0d592820f01000f4690740 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 405591789 1250 405590539 405590599
    0x3020f0d06061211040c0f031d07120506010501090e0613020903060403080a20041401090b070605012112080a0e0a0b0414150a0207030e1f03110306 65
    0x12903034031400140702401110010406514100403651240c9462803407554003840d0b41d4051844d050f0301c41003180d809880d2001100306800c000420f0346180b21000148403900220718294400d481001401e10803503e15400010301400540d1020790720303400111800b00d040d03c5140203500000000c02c005207442104910750038460f1400610704001c410110303003842021201079010601c100c042211811542c002c94960003405002e051941d5000300b0b44241c50f00550252003c805c100540254880e4050a0030700e02030b100012100d40c5a285625004029010900440e060102545020714203550440c0c2000413865006035150380b4415480f0045480050007001002d44079118400307a89c4140e410b100441c091070050342000038030729003801e120102c0006e02100c4100e9074411802c0c408402c0c2d0310301c80707290000198180503a850b600703070804842000d0a2010a80d01840070010080c400000c3c80d411514001140c07004d102c1420b1588002826000071100180c2140c0c0d0072000b000c40031032215001492207 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 405593039 1250 405591789 405591799
    0xd03110414041404060902040606080603030a0815090c1308030301120b1e0c130803091008040302030c011508010e1b01050f070f030302040305100203070c290708060414040c03020f 79
    0x10f401d40f00003001284203407025901281d444043c17030154107042c06000040e054508001c001c40c1010004240e0324071810f6258070420404402044191154140305440c000b0000c01101c11420309180b07d40441e88965114146140800000250604003000f41da04859400700c0d8042401b10075140c1c2680644000c00d00202044107035000d035001040e42074503e005010a1b410703603880740003050901100f4011900321100c070368810702c502d42190b41c400d10300000c004450718002c08a626207241c140d140d4002e00d04e07220519420608a001c1400c50205c10b4000c60340424000e0110b0380d4201407080d11020802011250700c03002100101d400e500540061244401560340c00d40b0b0440c0c036171603880400c03000c40c40031400250009410414401e0400160f09a803048d26011480d6041c0900082c0000c146a04000d0840d03000c01d84c8500a403560f49905400d07019800c51920603450541c07002030039003404030b40c56071146180210f001003030801c0d00c2c85640701d02d90140403c2c00183c2541c007049240c030060a0010380c80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 405594289 1250 405593039 405593051
    0x6051f2111030f0309040b030c06090613170a11060c0d030203150406080309090711060a1a03160e090109032003041a0a091d04110103060f03030e030d0311041404 71
    0x70341c9003003006580010b12400a542c4460391036003040191a408581c040c0709501108407014039540c1c3c0c0007262340d0341d50b003241c05c03a90f01c8030340001070403500a80d540301e68120301110714075603101c600101d44004618420680d01240040000800041d80140480c2c408a90f10100a01e0f007428000da00a60b0000d900702c43c1c6815840c907000010b401d17038103150026181d54001140190440c1002c1007003c0d0820031508100181c0603030b42483d50740d5400001d07c00104903440300d00340b00380490308454420305120044c05441a0310354110b8421342c0e10900344034141042e181040040c19040040c03040303000541e49035840100340704800c8918203100800280c00e00b52400200400102c240c01c0407000b00c0c14801401e501038450340c070301c035001c0d0907040241c5c080f2003030b09500030405814184804440d94015840301c0400c810100c1c65004a000b0000c64008100341c00c00b800c00031003410303080964011052012400c45403010721044040f800e42e92802c2201c00002c00c10f00c0b040c002c0031580201e824044001802c00180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 405595539 1250 405594289 405594323
    0x7033504020d0521040e090c2b080301140a0b0a170628080d030b09011806170703021509090417070812011706040302070b160c0306051f21 61
    0x1858502500c2c8804c10040010208140040520383c1540300b240000900301da0380819021070044426207003401c0c499800c45102180b1450a0810f5404464100000607121340e103503500c02c101d0341da103844e82c1482401110800281e900100c4100c03015055595601026508040d030301188040000e001c1c1648200c030340780c0101c448202c1102004010090800d4005024074181c04942002c40e4250540708042c1820400a116110819824110f440e000c2c290680760b08126101c900402c6d01c3c1d04203121404000031028080c034030005d0400141d07802120703c25a41c402c40aa075040c0c9101c0d07603008680040034140001c003c6030782c9031034103422041d1785034072a441c04282ea56055581d038080c41c1c0d89002c0c07200c00001800041080319607801c40c004504000c18a13420240c4010f940c075429807040c1a1849400209900101040c0c118040d005034081300000c0482d0700c0380382c03002c05440101c50301003900c503110010803030345803c9071162011a0744003208086400000d1114066603462490191201c030913001e4040e82d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 405596789 1250 405595539 405595573
    0xf020903060a02072a230d111309051009050f060703050f0601020a110906040b0a030b0103020f060301030c060c0204020714071e140f01020a050307033504020d05 71
    0x4070940b410380005903100814500342c1269449141d45801c6601001001d080800c03203c0a445c041d02c0210003400d0b1012141c01c1681030020744032a401da0032240c0040104d08020192090700c0076403134100d8500c90b80922465002d01220813201e400340a603400143d200407100141c2d8041c0f0241d80c000e40649800c1c1d181c0300c0105142042c00d84125000a0780c1e4010041d0f19110280ca603900b00c0d5091010f0140d480320313034403515110032104428074861840e22000c40c2c50361741d49520098084501400c0320060035500d050040420b502403206900401403228040505d20f82201140d040e0b0340c0c003d0309040c0541c00d0400440355011101c0003241c01c543c1c2001904c01142d040040b00d00b00d15010130040100034103280301c40d078003100c1c56501092414484042400b02c01e01c078441c0c0c0d031b10300e00c025107403140801d000c2e5004130f103012089107015000d8080014000181a4440300441560991201c10761001030b024000c2d000582451018285080100000c50018600280c1c5655468020001c9030440030541c01444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 405598039 1250 405596789 405596791
    0xf0212160b030907060305070215060a090e010f0c030b2d04181101031b0c0f0b01081b0603040206220513020a1706010e010c05030d021c24090f02090306 67
    0xc1039901c804410082c0d0080304210b0311000c4c102c10320341400107003041c00b001303941c2c0c5140c500a00e04034000d840c001401610ba87c14458000d1525002c01c0c00280189084940200300c001009608181032442d0681c5043c0603000e01c91b024000603003840900d2040035000924071355138007020085c0c0c2c600d240c81d1080541d140d000380359120840e0303d0b000c1c400e4162442d0403402e00c8401ca80300350505003070102c0d140e940f42d03c00c40e0b10300b101d119604114801600618008007840c1034100c1c000d000304864030001c0b50348240081c600f0704002181514826510081d0100080341c001110000d5010008204480130b14541408821000d0b0801e518000d800b81c54000051140860b46040e040080d4017003000c540c5d441c0d000b10400300c83d04c0e0442c0d50110318101140000c0040d0400c600807418000010f4011003005800c1045070b51300d80b80b0304002c644440caa5072115800c100c0000c0401041c6041c03503498000d0b03012140c140142401e142815030101c924203c0400c3c0580f0b000c0c80541c2400b50300380084103440d28140420b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 405599289 1250 405598039 405598049
    0x100306020a0e010e0a0b09060a0e120a021c0c1406070b0114040b0409080706050903071712090105090c010f2a05070605030705030a0b0d140d110a0f021216 68
    0xd440c141c4050000101301c209000e0900b881285003000822842c09010304440c00001c0560f01c40d0b0360b0f42d04549050b10036901d01a403140d004a007070184074080c242c02040482c0710354402c841401c08120fa034500074280d186c43c0d070380c040c210034003501d81001030061401511300081c1300684100e0501c0101e858400c4d0f0500c00f41d00614804150701c5100071280313040d1140b404000800c80e010000500c20340c89420007406242d030003c0c54103039502c02207208640c00300180c4444a51003036060050405440080e601c58115480d04803602c40004e001c10703c16501030003141c0c41840d10318002c0c501000180011900622240c0c804001d1104000007544100c4140005a807840c0c0303252125001000685409072910240344d116008108043c020301c13246651203000c40780c100c00544000f10324004203000140d01c1e9078404100600b500021034000c40100808581208031103010745440c1e40c0c244210f0034075501e6202260008240c1100044038200510340003032802903401040c01180c1590451191500100c0782e29080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 405600539 1250 405599289 405599297
    0x1909030f030f0201050c040e04020402031003080a0329011d01140a0305040c050102011506050d180b09010509010509070326070c0e0c04061205060d060213030524040b100306020a 78
    0x840b000007602402815041200305035410316062600e042ca92052001604c020321481e00000803800301030000142c2c0000c0c50b00300e2903081e65110441c802500401484903c0031541102c1c00107030800d220030501d036240504068685120950080e4402a400c0721800c8905060000d01e210b038bc1290b09011010f800d2118140d20002200d08080c18034420515081d44024116811700c840c0c0d00400f112420510200c4d4400d00b0241d8880a400b00c1c48006409031848008102003004082070a00686500e254001d080440081180381c03282881c40e030036038100f111801042c1d0722001c4c0400002e00704c9034050b103004813008440c00f00305141141e90f6049900608058408075039aa80500408407071540300c81c8c10540482d0800d191078649000034050f40d0070540c4688030507079142c00103540c54071144030075005554003210440d900c03c0d400c81d440c100807184e40001e444034407513444042a90020803195068104440524007516900d50b40c41b1070110348002c00d0b00c07804000d683c0300080001c5650010b80811406030315 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 405601789 1250 405600539 405600557
    0x715020301090e1e19260306040f0b03060c071103250806070f05180a03081b120f03060a0e090a12032a0302071401090c060f051909030f03 61
    0x380707052515000c05a81c5401000011401904141c005201064038801d910303c9402c02e1728500706007002070004154404100d151041c400079100091008510404003110f040140343c203402c5100c4112810042c20396050303440301e00420b0100362440302901782c40d8801e1845407180b0103290040b03401d20741d07420301128480003800c009480043c0c204001d0f6029110a9008040030b2401e40c400500040c0f02d4001c0c0e4007404800200403000b009400c6451400303141c084c1000c0040ca95038501012903920030200760141c2400c150f41e1803e0200e0200d0460800011070030f00c2414503414090031080e581c03010b08900d0f84501c815100080315400003c40758401e0200101034208443c05080080080700840f040c00101898551144400010401500c09440c4120444440c200f041001a0001d22800b1400b0f01090400010810500c00540003c4039003407140300d20b00a0180c0d2200c054a007002844c400c2004150240a01040c6004e078940e00c000424580c87d1545945a6075240c1c0d43e042d8101280070307000160005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 405603039 1250 405601789 405601811
    0x60a06180605030a0902270c1e070201120212010503010f230c0405130b0f01030b22240306110f0d050712020d0504050c1c1401020d0e10050601050f0a05071502030109 73
    0x281f11075408408030100c54070b4000c1000b1a20f0361403a011016820052001c1042019644290107a44402c00b10708002c40d52a1500d07980007030065001d01c10387d4842e41c24003103008210b6895005d050704007080003e00b406121410024003501940081484d030b42c155040c440045d5590325008030ba11901411100080c0da4584041400319200300720600e9418103007040080300c45a203445014074007044c44000b0344032034940b03400e5080001e0031070001c1c0b0110700700581c1d842180000c050700c000e804070307031050790101304480d40d1051048030380c06012101e080c40b03181800b07130004894641c1c0000341d020340280b51110a41184142543c104e8009000d0400d040395684100010040b003003014400703100007210304009000071f0b41c50151100001040050054406e0100d0300c0600b0425015503400c07641594041c0600740484000550302c01c0e0300700b1101500c40c01d1601107640c55024008981141461103c0c0d186030290102c4152100d5010002c00c8a403801000c0348400308000b070b8400b56010b06544003002c24040480e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 405604289 1250 405603039 405603109
    0x24070306080601120615030209100501180807030f05030903070906170705060d020c010b030307050d021504050d0305090a060906150614070f0503160803060a06180605030a0902 77
    0xd900290803660000006003c0300c3e44100c140e00d04144c4c01940032440c0494520b03584000c25042d48000d4011090400340100161042c412200750f41007a0b80300d032005494042d41c00b511a600d40320b81c90064020702e4045c030104200e0402c0b01c100a0044040343c1c64103041e1000b003841d081c420352144c0c2e0003965440040c00101c0c030404c40c654500640c000100485801c0a0002d0300e10b01c0f03408500750700a9400117088481c440f00390043c4443d44001000e4985840d21403e10039110204000f00c0001400382c0c40703c1512100f04100d6050140350410028100c9400310802070b802004040e14540142c814018040006800d81c05082c807114481c00022a803528442c81551920304640c1040c4188042c940601f81c00000002c1a40c0c0c038a50450002d1603001000d003020760441c0305120700041c260341405a10b9050110031001540508800d4508458055803840b0031104a1501c030303965428203111010030004248914003640e0840801e1070005034038040c42d4002080f90308000003d9041c1e1819041102e503014407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 405605539 1250 405604289 405604301
    0x301090912050c06010e090c030a05060f070914061309050901090516030b0c0f0712020a17040503031e0d021204061a060a08130803040605060a0501140912240703 71
    0x140d09156040000d00f01001e9110101409200070f205070300000906030b068200091030145102030161006560715092140c1c0b600c02c11500c400c1d1810946002c9002d80744100440c1c0c2c201c484268401904140100401c10301b640710b8803020314040c00309680030481143c54443d00b40191500000000c651810b840c1c96405c01a0381813035a110b4031002c41080000c0340042da02ca90b8041060800160b54009402044c0d0241c02014000741c0180e40b4050100340d446d4001a016000502610f10084400032801800003580324034040c40707425400c1400f9a108103420110f00e0340000742582409803d0445c400c10060490b0801003200c0d00258040c3c040c001408054810a2540034441c20048145000c410100c0c0b01445100300d01800c028174480003c00d000c80d00402074444541c05140240c1e68181810650081e0205984c0d20744500012200001c8541c05240000900c00017155010706240c0d65804010a40048100d02d040a0007141904039080fa04103d9000741e40c0ca034480b4005030380c1001c2e4801001c030f1349 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 405606789 1250 405605539 405605573
    0x1706090f030310050f0d0f0312050906190f06080d09030c150215040c050a0b1b1501050411090604030303150b0c072c0103030306470403050303010909 66
    0x4200203101600c15040a0303c801e680044d1280c8a030440e1580104250307001060001d020782001d074034000c0070198001d80c0c2c01991841054140f1194030380d18101d0751900000e444040c820384d846040da0040d8502c9401c42015940c10420002e42940e84041c03107800c4c035100c2984400000d221450510401c040c101210025211004030440320586800f000384d59007229440586141c00c4c0c12000030f040115140b58400506400303043c0d80c01703095480048061f9038100c51100000e1014204c40c42c0750554001503403120a2080c000f80902a074601018400141812460b8012a2600700b100c0117070390b1582e40c0208000c502c650340c0040c0e001036516802d811f4400700d40040148000802c800c1181102c0064000c05440700d0410102041d41c1420481030070003150b40290a6a00040d0000800d00d074140c1e00080c01c40c0d200317031030500d403600c11001000300c0381075120750940032102c0c403054064500000c1448407469400340141d80340781c01d4580d00e902d480c6800913448450781548680c1e003542080035030054201002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 405608039 1250 405606789 405606793
    0xe040b13050901050a0c03140720011509050a091a07050405040e0f0f1501030b06120d090602070b210703020c07080c0307060302030705090f01091208030109200a030906061706090f 79
    0x1c00603103500042c1c230001a0015041200541da000725800c0080460402152440c008002d40030310361803501c401401c641715085482e40b4000000c0c0c5112a24001c41c1d035100d6000481d800940031b4000c641091400251034401002024800443d2945482c41601c0308201300000034640868901044d616080f00f03405130001e5500400c03c05041b030f506400995041d25442640710341c0641c0d5110115500342c00c000000c3ca0300b442105114aa041c3d0480d080d9400d58000303038251461240c403030704006c0661003100200600040815200c1e610020300354860f1360400c101d0314015140c151300c0050b4514008d01a002900f031604600b20741a050311b010004880204100d06080d415032414800c0034095004040c8803e005070a00f1081d02c4c8103a05c2030191a0280c02ca0b0301e22950011614189400c0d103410901a52490034905607103d56103102480384005030101585e0b215242c0303188010100c0107005910003c0312010740b15030010502c00b41404610741c04560840c000c0541c2d103003c113000c42c0342400081c413040240d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 405609289 1250 405608039 405608051
    0x709030209070815091e0a0b010e040b060f130807060315050d0311010f020919210303150e09010b0925020703050d0203091206070e040b13050901050a0c03 68
    0x6031110a20a0340c000e20504191581d0b503660310210140c3c0f100b6044c100c0d4000ea00d07400b008110040d545401a40301c151210200750340d5503007818a0115140f20304924007003070f0307070051046003450f080d0810125624003034952810302c0d1051702c41e0502d940010801003008a003004007484000d4040004200801c0d5a10703003400808241c0381700c11035822840c0a210702661006c2082c41c1410701503c4c1c40c64203150002c4c000c02000342c8400e103900094210740101845035290b8103070300032003c50480c807440940c0d8100b015204440005890300302046142d000480905450324002d01c0c4444611030010018400010510400d1034800c03581403c4035600c01c200d41c400c480d2071003401625507680c144d01c80c907004003990080d10b0303208000090345448030a9000a01c03600c1030a0605800c40d60200250032002c0c01517400400c0e0350024200541c40362400c80c2c0c00000951914020769403880e050b080b4946000c2c0c050030103010b4030400810f2000380c50085404924980d142e0341405030002c0316100e0f10303900300450b03e010490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 405610539 1250 405609289 405609293
    0x907020a030e040b012714010207050a09200c030403060b0d0b0103030e0f0a080d17070e060315040e06041403070203060f0a0b0a14030105010902040e061003020408190b070903 77
    0x2881d58071460b0710f02607a0780d0f064078100d590196120341624501003400b03d0320428120400e1024015a00540c0748160f00d925003402d079540009000030130390310000c082c068007d08020744030700280340c40d00078841c2e031362800131000349801840c0c0c00810f04128a04003465a59085042003c191540070b078289014a600c1300e090b501250001e190b49064903894a0443d543d070606900040844101d820b0480e48003280582c002444d40700010b090b0104c49450712041081907501e400104d62500886041c07010403101645c0300c0c1d4914180d8015503000954410f2000000043c2020400b180c1201d2860240c07031740060141f2051104070500c1001035600c0d1001149031403102e40c0400d031182d070003a1400552078515000b01c0c803004081e0700072400f01b00c40900000a900e17039a51061510b460025a414065441c001c0040381500443c000c940c140d485105c5129801d03114402030181c024407036000704040503400d05c00810104020b20030340c5c8801f0803e0880304919449801d084511800107080041402401c4d842000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 405611789 1250 405610539 405610547
    0xc01050610020c09090102130807050f0609030a0f080f121f08150406020d0903020322051e01020111030c0a170106170c161202210d150b0f04050907020a03 68
    0x1001c0c0c4800e94000b41309807200c90981d4003902840c80d003800a04202e20010a05410000e03541003162400c8400700c030b00803480ca051290074031800399500c0d099000100014040780c00e02a805c50741a2044100610700b040310102821650401e8110b00c40c014128800c1c028124446580b8168820881141d80021441c10700e0065032a10464a030100b89096000080d0920207594182d034202c40d0f8880d0144159515854001d440307034400d10048194815044416031090000d1820509a0784050b0048142d548540511180c0c0724810071441c0c1150f40710480b0103159038000001d113000302c48590401d51200b2200b0b030085c05c5005908400c3c2a0341441c00c00401c00d0dd54441840146110250000d40742600d501508610610615004030404031030200030a0801143c02c4149031040e405070300361261000e4000d184050b80c200000c900c08017500c2440754002ca00c034164000145088940348200780c040e510710800c0321b282c001401c20403240c0d002042c00c00c4030741854031845a20420328405080650240e45d0050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 405613039 1250 405611789 405611803
    0x30705091503030d0c02010e07230d05010f09240e1e030f070b0f250e0414090a0204061502060a0f02160c150c080906070309050907050c0105061002 65
    0xd1041c5200d40e40040e940c0301401200d91004504406001c0d4640d403c2010340600343d080310b0884903100300ca800180d402803c4c8420080c0d042ca0501d41070f41201c643c0f00f005902c1403403d40c02e580b155642c0a070b06c203149401d48070b140c80061203100980d81d1002441d601c1108036110305c03001403807a400c01c40e0301c2960003008110b042d240c1052110155003601001c0c1d06c03603e14040d100c0c15011201c1c00060f49030a008140310845c0c4a600403e80b031600300c1da929080000c9048101c0c20b4101c020480032901560709014401d400c51180001e1b000003104c040300c41041d142d06509030b4020700b207078005107016000e500303003401040c020f8205440f50390a046a1190300070f5946038001d1007032800381d5680513609030f4014aa012903400c10b1340b0000310f0444501600b040c0c0c1510307007036100f114165840d018003800810b01440c06c42c41203079000301c4040d04090410080c41415400301700d0880c00c1152229010031555a0712940034050071040d501c4c0c0d6140c03484043c04508617940a000035201d8031000e00d40d198520390004440d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 405614289 1250 405613039 405613051
    0x4021c0b040b010c380c1201050d050d0c06180c08151b07150e030307020f12040905040227040b060d120c03090e0117190f0b040507030204020d091103070509 69
    0x680f951761401e2458048590a008203d00f0300c85e41106110303540f190305001c1c0008045440e4907031f0b42a681c820400120443c4404014219040813696604080c0142084441107025004c04a40307130f03103001c101c11403a2030780e15402c80302040e03800c10030300075600d08005003401148926201141c60520340c01d18203036110f05074806412890005140010070110100c03148030072055407414000b01030345420140e201d800c12525100180b00d034804041d2071800006030302d545145204200303840d060a01103c1405841300400585e00b11048a8052611201403510011400142c0e40d00c4050b07410f05142003050f0a001501c60391080c1c0340422820007091103542c9204410400f0f003003680c8004418942994008502d9004540100c1010000543c80c614209101c8a2a81040945d0074007070418000000c403070f840c0c0d140a050012880604800a8160307010660014020030880380e41981d81c0cbd0002c3d01b42c0c0e02080c415924240c55120f881e0401c0035544590300b4031201103014000d41401c04005c540e031028001e01c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 405615539 1250 405614289 405614333
    0x506040e04030215010e070e22090512030a050414030307020304050d15050c03070f03050c0403020d080d020a0507150207020f19030212030c06060a080a0308040204021c0b040b010c 79
    0x2040070103008025103800741011070800d403041d6030f4031076800d8080070b0100e40170b502285881d02c602042e45480101d00d40013401000501070f100140a140000400c0148ac0c111038a100b0b11960203825500c0d0005540b0031500744402003030381c0c41c25280c0400030040c600102d2146510030700611803425008001c0c3d4060b640142c2e1514103021050402c0c0601140c1800d0003034012b072600d010b01c45694103d40056110350b903561198180aa0071100450880700300311100390303001d0414441840185088101c1042442c09030b900d403400d00461040c6002241d01030764085020410000c0d11100300501c8000f26190303101c0100c0c04600b00709160300421094298028032520030f04054485800820351908203c004e5600905031007031200c0c800810f607950303a200344c0002e4200c1c0304200014600e860681100420f84609801401d412a4a69015641000c0141c01242c2c81a001d002c2c0344011a50307080004d141015030040405d4111480c42444102ca0074940c01d181004105e50000010407103426810280c4801a04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 405616789 1250 405615539 405615541
    0x10c020d02040e07090b0105090109030206160c06050a090603050402090a050c1e1c060803070326070203120a02040f03260a18080d141b01330506040e 66
    0x40000e400c540c0c100c000a5125140001d81044200006200c4081d03807142d134810003425041200640c1c19016102e20740b03000564850040c001424607034050701100b003180000890b00b041c01d41e41c913007001c00d464202c2e00c0011004035002c5c45880e4424607142c000c040b1810700708614285034011510700d10340282100ba9051b1204041001b41304c16404450501050413802100c02c0c10107016807407140d101d02c1e0710788000782c400c06c40b00b00d80321300c944603140490300840003e6240250940c0c0645228080c0100f000e41da0a178550080b003946000c1241d2486101c49a006e0340d51000322401c2d89002200280c07804008610500003404040071804613a01584e400c4101c010111718840d25100386402c0c454815946008040b40c150003458000020b9121081301c00640035a00d5110352103103503103000c24040c02001801c0703005406440b059080041000712020100d01142c81088902e080c2134030410905030a108602d0389a02030340304002020f18010200503940c15a51780e24010010701c10380654001d10300119840b070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 405618039 1250 405616789 405616793
    0x3031706060a08013c09050f0603060402221b031b050901050903010e0a0807140a0201140a020a0b2d2401020313080303060f03150106031802030106182306010c 70
    0x5060b00310541149503581c881043c07400005e00301440c492030a040d81400003140c2d8414060a2403846041c014000f08500e540b035800b01320303c03094000b01141c01003050610240303400120b03000d04200700395a03503109000c41f501d8100c01011981390b24400000c411803041c44c801035950010448281e00c009103070046d22110b1880c0041c0c0140001c288035290303842194102d804108206c3c1c0581411030061003416000a1010900e640351501d01c08020f000135120304100c0d0042e25000003410711941c40d0f20454081c4525907442212011007665050128504603511680d009502090480c6100c0513a03910f006500f00144019401c6c078101d14464009c00c6120080303207850348208296040b416044070301032442c56807401150b48036442507513250301070240361042c4001401c00051916610200081c0c6000607031802c5000c900902c8402c3d0311011030404201018007680e424010800980700498000c0f21046900f90f038403080380c5200106010100c00f03030181e00070206038007036459884032007828018510352a034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 405619289 1250 405618039 405618089
    0x1030b0606040e0a05060a08070e0c03040c26070906050108060d0303151206060e0f0a0e030d110408010e16180b040c0807020c061303030302160b0103031706060a0801 73
    0x80d0403c0b4160741c0c034a020400200041d401250181000b5070b00061a0ba072110b05003919400c4a004a044400d400d07000f01d655010400001c6500074021482003280b40c3e10b420301309152800308041720f0b1001c0310fa038480800c407000921244004101d5500108150b1385454006840d0307106c000d08481c0b00d00408104c40c818540079400c1102100d08003105001c100380c81d000c6081130b0750103d000c10340b0a01e240c04d20108510701080c1c86103000781d80b80780d00318a9035030310b0501c008040c1000c8944e8070124041400294034042c1c590107200868414040902d8445003000f40050840f43c2c940c0b0b802e21150700044030342c0501c090030388001090740d00f04a4416404024480500040e00208070456049481c140b10702d02144d03488941c05005440580c295101d02c0c0c00041000a2805103040035a048102400208002400b907802805c9a040c0c0b0038104500401584528101c648240d00c00c5c0d0100c2c161100060fa1442c091210b02d912560880d01035080c80e10421000f840f612050080310031107807441d800e4940c52030030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 405620539 1250 405619289 405619297
    0x111070302030a080304050f12031515030709050306061e241306020606030703030f18030f0f05060c0705070e070e03010f06061d0d08070c08010525020a03020601030b0606 75
    0x2d4201d4400c08890b02d0f0410441d030003110b0a03161400740050070007144002040310b80c0e40469900040b41180c4030345500301104540c807420254000a106441d92400c1030b18000b0b188101100d40321b29005900c2c142c10301d803c1c03103030043c4040c0c4982c035504842e90304420f68809030002c400c01901e0034400c1c003403590403240c0c0140da5044990b40311400800e440300e82c004241201c8054425031b500380c0f40c0300c1c1c4600e400c0c1aa2603241c1d01000b00800d43c803905d20704481d80709110b190803042d50300211a03c029541e44070040c603004400d0043e2840e00700c020703515090160800a1540085c0240c40f20f6103013060544864bd00c4031403034010070021041a8004c18072003449140c1c41080904020000c000c000790301180100103041612410000c81c3c08813070042500c80d00da2000810310701c40580495039900c1103030f079100f0490f4008103007118101103032180440c0c0b003e801d00ca0340c0d01c50204054414040d40441e0202d01a8071a0a00000215404a240b240001e6408520301d07044a901c0030001450780c40d5200029a1402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405621789 1250 405620539 405620543
    0xd03020906070c240806010f030f021204050705010f1812020105040302130507090b0a1403060105040b0c01090b010b07020d030309050f030a1d09220f080f090117010f0501110703 78
    0x1080c00c0f408502e041c4000340d0440f80060544108009411881040d07420b41c008584c0c0c140864060046100b07001d01a800088150708081d03001450b00c0c0e802000301c408660140c0c0c1c1601d4503481400140100d580201d6846001995030910040c1d14007100007024050400e0b000f4a2070b51400c0d02416021a4060010740d006580d004000d540182e10820056006090454803603000030702841c40010b04441e00411996a48481e649151218a411640c1c05007030780083e20f0681040010040007414150100141010911001c0007280c180c1040c280013003800300c1a00009034640301045800300680da10328454030180da142c1400b060352052030074040d0504403903198501c0c06000c001484440c1c0d90b80b020040080d03000d403062254080c03108800b4040c0081c0111555800d10300000300600014500b8845031901c18030829420b03000350a00d030385256071a00142e072011908400460404620b6030421200c3c1152420068600059031408208a6840c0100e01c5058103101614180004c40038090200d075000d99 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 405623039 1250 405621789 405621803
    0x30a110a0e0711070f06022503351c0903020c19090509030a02210c031206091302090a0b0109080106060203040320031c110d020105090706030203090d0302090607 71
    0x1ca0060300c0a000e20090409840113030007100804107a803020f20820006071000e56004007001c2c00000d01404000b1002110240c40341c000c20000000100707031448440d00ca20070316000307002022a02a00c103160406400c40700c07086800c1400031000000c408804440281500300010440690a0406034204080200d070740c0c0c0c0240890302140900c0820319100022515500300810481e80d8074150280c0b240108014880140c120070619204121003103c100703000d40c0540700745494072405022181c40c5038001040c00001e00c0001080100a252074a03515601c24611003c0c4001158144c0c00140c152100600c001e004960701e030322551099100e9840003002c2c00054008010742034858401940d40d4000344022101e50b484071500b800c2d04070451170000301d40310003c0c0003004120004074200040da040100c044041191126603035800301410440aa0551000d800024941c00c103000e0301c0d810316145810030f0050500404c00e2150260300000c80140011151a0045c2c45802c01d6000424510070004090281 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 405624289 1250 405623039 405623041
    0x180308120c0c011505030d0914040504020303120f06180708010e0c211b13030605071704231b0405040201020c0a0e0f010f05060702010c02060c0708031b0c030a110a0e 73
    0x403100202c0c201d8180c03001242110089031f0098421620400940220380421451480c2c02e182420980c00c0340781c12a20003000d032824180040c2520040da10100c54290b113041c8803e0a105081c01c12443c001c2c280001800901c1c080e15204201500341d10040c4250b00c01009004005290340c0e03c0402640c005105111111119401405c0b17821103404083d18403400b654203c41040118501d1107040b101d800f00c8802c0d813140d01c0c44c1355444010060800401e41c509005c7d21500c03114440032030201d414401c81c801d440002d01c094840c9292900f030451020070f40c9499100c038501c050081d035440705442c0b028400715000708076542d4502c0100d007840321b00e60300302d600141e64690120303980300502e9600344103009103191080716aa98550411107d41c0902c24143c1000e010404c0318050b51188091161042c0090115450300c0180400a0701d08041d0f0317841942c5a82021606c0c0f00c98007910400d56100301e2214004209125520340041c2e16002040d5000304100da908035031003800d440f202d19610042004066a03522 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 405625539 1250 405624289 405624311
    0x10e03070501020c01060b2809030605090a060b09060a030f050f0a03110606060901050a08040611160204050603010501050f0909010f0507030203160927140106020d180308120c0c01 79
    0x103034004c40341021455091240204046281700f05450802070100d1f4401d000300d41c46180c401a00d0750301c50501041142d040c0d0040085000c1d801081d000f640d07480002c050b01d80ba20304000040b03680c4442c5049c440d600e5402400384c2640c80c0d0440d030041d00c0d00a200c0e24054009460103d1801400ca012520309005d8102d0840a05d9040b00d0166010121881690340c0d41d555542048000e106000c2c6140c082031040c000d42880358070450110f88d0061080c01c0c009000362030700f8580c40060308103002d4409800315a01c071100071414107025140c1c0100e402d800a20581d4100400501c004400c00d542d1070148140100003020030100b50843c240040d82d150080065081501004010b580212026500d90501da400925000c0c450510242258000310316072846040c0c01d407140031002501c40d11012000d4907250a914031007100d980e03803402000c1a400410b250842d0703400190040007101d41d403103030f816490803003080450305010488070060f41c410b050302059910502154924042d00f040d560580d0720301080d0200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 405626789 1250 405625539 405625541
    0xc0709091a10050d11010309020a1413050915040f0b01090522050601090e150c0a0305010e070203032d09161703040306091a0c0d0f0204060f0e03010e03070501 70
    0x1a5900302026a16080d6030b03460441c0828010521509070410101c42148020601c0103c0c00700d0300100514000c40c0c4001c0c1c5800103041d000d480e8000b0360180c00540d07100019464000c03004608003078205c0b818445454042040c5483d01c0481e1a00101d0b10051400074041046842001d0300b031a0380321a0504865849603690f50041c0022140b20030614282da082400c0d00188100c05291190700c41d0050a00b68240040c54003c2c00394034004901031b100704500c1303c409402040405200d9031701d2247c000d4035070281140003800c4e2001030b40b1802c0a45040313402d010b07025074040102c2303502201c1d680e035003811131250300120600341104500d41742803c0d0154050184010000c55000d403540c0844c45c000c40220384505004000409202c0e10703d9095004000800c00102250003010040740580b0290f038006103001044008a04110b4507000700350000200280484030790300c94100c04a000715011400c0504010b805031001c041900002c00380b00214500b40c2144c0c2d400d40005d001d1110307a00c00d40ea161015840d1081c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 405628039 1250 405626789 405626813
    0x2090c040302090f2203120e060a0b0a060c0b100302090a050f07090f030b040c0f0b030a15050a0902090307081207030e1206070804141902100903080f0c070909 70
    0xd01c0b071842d800110300c8000007461821300501790890f841c00120b64002841300c40c09410700c400c80500050007510b2441c034451b48155152141c0740307800352007140303046110070701114403c1d40b01503c203030140d500900015500001071002d480e44401040e015407141080b0300b504076680c1c0e1000758000e05001c10030403c2c4940b0741240e80240d003a2040401a07841e005015140189580924401106a100704201180600d40402c1d082806103103141141c83d280e4441c0202c040a40d0400c402e94203000040c04481d041c913129200c04420702002d6000b0150030000020110641c500c10f005c0556000720f41035409640500a0100a01300402140c404145504880c19940c001440c1074011604c80803040c0c4050902c10104074400ca800c2d8054115580c550318140c40030040940140c03890352101c890b089100d4000c00c0440000c46845801d03c0c4404954410031041c91600c83d8400308124040c6000c01c0080c44080035210114081c04a95440f51643c401e20b43c544041907022600c0c813403c1401c5582030018544440b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 405629289 1250 405628039 405628043
    0x190612022808071409040b04020708030a0504051504110d060b040f0614041509091b060c0b0702030a02101d12070b01060804051c1419020106150c1e02090c0403 70
    0x44015900c007401030703034081d00044100101c000100030000051500d58006080e47e64010401410034215031104140381d0422101c502015540e1818042400b40812006000b000c02c8a00c0d58400e240a0b5255991061200c003c5401542d0900d04401000001c0d0440c1029030340c042c0040010b101e0000c5580d01604d0716102d8611a2894140340499a0034940183c0301c1e440507041c4941545440c0c185030400500682c502a01c25040001410000c000105a00401003841c0d0717a0300d419160381420306c01c80740507003d4031040556100f00005103500f5004150202104050000060340400040c50340300b840ca50001403000902641c00300fa8206070904000e810901d0054a03d424940c1c3c80d0070f029a6802001e030780103080c6a103c6084004008030104446510900519000d00041f409003401485a0400780c0548904e400414240c1c0349240e091040000a1846a036180c00c40c1c060680050a02118003c014010200041d001c95a090203c584000c040303a0241c40641d2a03d000d0160f250550858007007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 405630539 1250 405629289 405629297
    0x12190c030f1109030c0603070311180405070807080411130c0c06060504050106020601120206120702010b1212091302042c0f010b120702100f1a1906120228 68
    0x40c40c10590b940107440301000302034000c1c5250361801c1d08102194100030050b41c201500c0d401200e02c01c0b002070001e07148100071828444074842d1103e003080b041d64001001001040100301c01c0055040d8032071059604940c002c1e810a02c14080480031510362100110107607400d030b05080307808004035840480e00900700e024200800000c1e84400c104026a0401e10400b00103a2045005010b141e1510544030151403005240c0c03880d01e01c0401c91014a481c00302e0700003003d07075543e140c61500b50800585610f030070402d0380094451044100c101a80c540078500e042809007101c2c44294521000c1c5504450190648201031058606202800741e000f05959020104161034440801c0c0000c1d0b0041249060f2025020401e05080d001d000c100c4400300001c05240861160381a000741c0548148580300856141520100307240000e01d12aa07102c0c1c258038042070095141c4a07150300545036000d000c10a540700e620703044008449101d05040680030700a95170302c00c2290300c841031001c43d400c50301c2c030040005507440d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 405631789 1250 405630539 405630551
    0xe060301062a0c0b0a0302070203011a1311040b0702010207050d080c070b0418020702180103060b040c050301050f010c02150a080a0f0207020d12022401170604050312190c030f 77
    0x1004088003004000c000384050110f90703040c4400c00000c4081d01201e001842e005003003c40540000742500c0c81030a40c000c5080c00c080c3c250003a420013540a03402414200400d0040c003000c010844040d1280c0e1180248401c00800c0300d0045a10900c1014000c000003031101200c400c0c80d09140b00c0302c1e40251000f0304039118550000407a0078115082d10115200e0000b0b40300380120a41400000c1e5010300001c81c4d1001c4ca8800318040f8240c02d1031054065400f41c4000924802c13400c1c244011144034014807011b001e02031004101c1d59850a000a0526800303183c1071601e011248085800100f080b000c1380303c9610082226030780c1552041c1c483c1d12070101d5050901420200d210088202c4c45101d002941154075002d903003012400002402d42800702030300c1140d41c2d50342e00072841c10180e0958002007003d40103c00042060000650701d02d85151000806005d080c1810b41c1c4a40c1e0380c2c8a1003181907032404c0341900040481c50444030074030110791062000c0c0510f4209040c002c000340b090700007000301c0d11303c1d20b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 405633039 1250 405631789 405631847
    0x3020d2901080706050702220e0d0e09190e0307061b110c0103200d1d01020f0d050403032c150c12090106050d080a0206011208120402010e06030106 65
    0xc80c101c50000d00509803140c02c010040300c01e5400341c070b402c0c0d0300554115036141c4603400b221049038000c03468480000b140d228481e01e044c00c080450101c002049a0802e400a885e9034108a05410800e1101d0700c10b006082e000512019000b100417248590101041c8202848100c1d003021035415825215600c1601041e0820b6801d40d845448041e400d40c810000c042c1e40f5402548208881c0b18403226442c4012005201c07403400d82d10191560382d03100e440d4440c058400c1400c4400e02e00c00840c4100a509044001164042c03d0003510400b022164032180801e05240c0251f101c017601490b002100036038144c1d0b004c003100220071030b140701d42c00b41d1103498041541c51410820050003003103141c1c0304a140a2018411a012101c080c1020106550b0350340000b0b6103580b1414a070980920800d0600e85410205a0107401c041050744140840c051010000d0001408181203500c0100c070714905612940b91400126001c0d00c2004036076800150010010030b1301e507009040f80991400451181c001c0b80d61300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 405634289 1250 405633039 405633113
    0x10f06030f0323072009090a02150f030415060503070b040503060f33030a05010c021006051c032c03120f030a1e110d06051008060907050403020d 64
    0x140d1605040b03001c01d01c484800178111021016013924150a40001c0791480e40c0052500481590b071551294450200701d811410031044144007000d80040050400c0b840002007200b621008000030455034422003030040c00f10056002c01d0103028050201d0340d20503203461075156a607000ccc0c09042c0c400c0c0303c2c03a400101004240d401c0d081c4a43e85a400d4400542d00009807a241003d41c42000700110540d040302e50796981b010406c80020b54045c50000c0f9038001c0850010b42441e5070314007541d1074203040ca0f0b000e11058581880c000890b500c0301d07094070310040072401d00b00c0c0d841c48050105007164a580c202180e0065070845684140d10044098494852165000441d2442031100c4e520341100d0900018481c103400d0740c01810401c0c01ea01c00d4620180b0036945900441c1c013201703450010b019020078072010040c070a21411002d4072054440c032138200d200c036501a107494001041d01388108000000184400e00c21400c0e80c0007181e011b40181140d00b041d00c0d00318030288980070381e20407668403c8443c0c0c4152100c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 405635539 1250 405634289 405634337
    0x71103040e06010e030c010c060b04020412050303070306060908060f0a0e0307060905010b0f1825030203091509030d110c0d12050606120a09050a0f0b150121020903010f06030f03 78
    0x161282e05c8c0030b1003241c0d0758101521a100c41c40c0d5015a00380304c0002c84440060500300e40900c00d2014503a280380044010701140e41d1904204200480780d0828801d1031b400048080c0c01070b121603000c2000ea9030708003400303018140f103030980c0721b03e80808503500d01000346071781140030014481c00c000c0c404001d0403018440c1c0e074070b01c0500b2586d00414402450340d03406902e0b1000c5801c106c9280d03c512210000d03008071100d504002e4084000280e0000800010362001e00074403a180c2840f5035520725604164071410358078060303804003426069450740015180c4c5100350403500a9640b0400380e4229510075a07002e002002002103403081c0c01c1c00c10000540c1450603908544142c10345030b09816094840c00380c203800030f21078800c040b034591280e145c5404c003040a001c00d40203001d1040c03c4900092400e81c2e0303200e0b0a110b42c5030986042c441c02250030082c450800d04820a0403124000058075207603d540000d002d0a07101d0021941c141c43d0003800300c1401011001104154042d481d600000c5466a01800c2c1c0a02e1f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 405636789 1250 405635539 405635563
    0x609230c031302130207020406031b0506090d12090f15031a2805190302031506030c0409020a0b0a021e0f030a050d0209031b151908071103040e06010e03 67
    0x403041d0302e844014589030320b11030389244000700010304006596010070111a420b40040e07400a91000d0344020500f076100c0c01c500604000d460507800c19800c071340030900122035030000034648442009507424491140c90442c1c000c081c00c1e51201d900a5840d8500e0701640319a0904030002414650074002000340d140d11201a2580a40005030b4a002e85001811021100c21580020114a0800201d50760b4103046220126004541941d1441c51841054603009035811150102110002040f48030380e4040b412026215007a82c01042c191210b02c000f13418141650410b1202c04408103465800c950f00051400042110038508610740001c00001940c44451550310b070f205502c100141c0f04070603c0350700035141550800c0d10140c1054841c40000e403c01924054070312411890104035815451f05108002c2c030f000613544420329104054081e050781e01250100305003405541c0700411803d03032140080541d000d941e581540e40b607903282c8010304020802030300c0013400140c126440003001d280210310428201c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 405638039 1250 405636789 405636811
    0x1309090b0601050a050d050717330409060504080409060605070503071101030e03070b100617160e0a08010b0102070603022803021b2103040203030d020d0609230c03 72
    0x19441c140112000c1c0d002c003155004000c024080100450454041c0602814082d192225400004ca6864a140c3d10041c075499402c02210145114046008014902c024a1002c07a081e0480c414001c14040c0c01500c80081c1114501030401040c0003955014000303840d034003002802283d0343c0781d40441d1315000d29040038250750020030402002076001c0582d00701561060501040910200f003001e8190340000f101580e400342da0070f0400000e407005ca000b0102402490620241c43c010008004080510040c0f105901201242c5108030183c0210b0015298040c000c03c840b503010340b03603c540b90180201d16101409032007110030115019002e8001e5a0300d9145002100f41c0c40b106504048042c1912100b8480615a0800203484411074211450081c091160f0060003402c0d000e44010000c2d0054400c00040c0c0c80e8180103010041c0d6001c4200c0c1c606903880d0001603151600543c0150007413000398842423041d442d01a448c28101c0b0030940101d01c1881d01c0780340d544c440d960006540c04038030045030a40c480b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 405639289 1250 405638039 405638041
    0x210b010512030a0f0e060409050a0b010305011a090f0d08041a03160c14011d0f1212100518090d0c0309062d20010209012319051309090b 60
    0x7480364079441c4c000138891134102c0e1140200c00201c0c0d5a03500ca504034010040e100d0081084180d01401140c1c42803400f03207410010740d850315052112840c0381451301e0040600c00500e0184641d503849068200040c000c15207004281c443ca80420307541d000b84a5107070322201082c10052003205842c00e0340e10500300710400b400f4408000750200da01e039018150881e240d00040c5c00207086074000340700714913440c1515400000600c240d44501e52803d45440b03a080030130752050035207407030900821003910708000b40300d001c080b20f5894281540b43b10552941040d0381003480d01203917407900c0c00906546e40c014034500f0250313440f0940780002192024000c210180c0450030081c0b0420440c9d203d0800b880550120000c0d01c40c5031442c05551003001000a10f40900140ca030099010003000031a429120382000f0138000c5141140c0c040000c0d14000d4181c1d618051003900b0b0690300c1d40b40b5080c204807944e5029003482e88a01c4040300034040c203660804034982d0100c1e420840c020400300d01c54400c0700c1255070013043c00c1d191 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 405640539 1250 405639289 405639307
    0x5010906080f13050f0f0601090e070b07030f05210402040c0305091c0c0b180d020303091c0909091a01080c060d0b01020115030c030201080a18140304210b01051203 72
    0x1c070455018081321180704610229201c1c4000348403814640c10303084003500c01940b4200a9000303442a00550b42c24a03008907804101e1080d00408070b90086230f02d03051203c5621001002030710540540580321004041c2261102c205c1a110422603102d2442154100400380310803a04808403030080340c00000700d0b88040a0401c4034240d4105641c07450b68145851080c12141d90b031410a03619050782c040315100818911580b030490280107118160410344001c504526100905030b80d140e800c0c0c1080c00000661040c02c0702640d100715a400c0c080c01c401c8005020b0b4009600c3d00001c3c00c0d08000c400d05602c55050b00204060b00042007440c035007000140f0729400d110010030000700414504913894195940c4480761040004645c01c2a40118003c0c640c07055858a10f00001d000b0000c01001c014072076151400b0140071100a541034652035802c110742800d200d0f03a8814462941c440c03504912070089100366001160405d0000c4051400e114400c0078205907070350740038400c00c09076502010310960001e01003154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 405641789 1250 405640539 405640561
    0xc0c020d0b0402040b0d05280305030117030708070506420a03020a060507061a100c03021f0608070b0901210603020603010b0c010b010903030206012606090705010906080f 75
    0x280043c002040040c0786441040064820444000f0440d415040070700000000ca402c83d90001c24107148510076804100c156600500720302c41401000441448023041480c03041081040d26500d0758444010b50f9201c03824203060303035544404ca0307412801200495501104c0300251400b40b860401e881c0d80c014610400c811035101c610f5003552141d800420702d10700080541d49422141c0018030710b98440a030384d8a160b040603420b50360301c11602c25046504055905040d142c0d0010341011443c1e92034810400078081ca812400d1003014a410411180304e2800c10400e040309600100480322020222064640d4a080601c4103008000045020894103038002020400c405500403000d0a01040059042c0c0c999001800b260800e0300002e09000012400f4051442e00744600c040003c004d0900000440c91643c00030b503103040502070f100c500f088084003a00342e8060030f103400300a007604405540c160b1500d401c003250740764031602c18980024412400020020700805071140582c0380c0c1c410305c149503560402800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 405643039 1250 405641789 405641791
    0xb040c090e1801090203030711090a150b0d0e0a11030d0306031109070908100b120c0f01050a020f010915061a0d1808120414010e0a0f0c0e01060801090c0c020d0b 71
    0xb90b2a9502c0c0c42e2a0300060b58140000c140003031080b20110a880b04c01c0381440340c026030090124540e1840c081d80b601c1102106914401154074144409640f116824000e03800741c5031021404600d4400d81100d8020842e40340c1c000c040790f240c01d4044a01c03440d24808102e05031801c0d488040c00c5406140341003004c41c20b2102c0407036030040e0b603400d2402d0328075583d070030f25490f200050005240c50b0755221655221450142c0268203031340e407000c0c010040d48404200040803102e22200e5141840000200e101c185d5000f13104c200c0f50300d100c40d0002c0102032030030709000c40e040800304403800c5c0503460200d0203d0140c2c0d5400d4165110f012402106003400050f20009008141202c2034017600400510703448002031446004004c0203000d9861402d03070381418501107503a6403030400132186c1c0780d043c82c45000d40d0080005081e9589600459222039100c124208800e1000e119007001c040c601c0c0700300000c628141c0201000717040741c000500802c000303842d6020465000c42145030003035012840324107200118035640841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 405644289 1250 405643039 405643081
    0x2010504030c06030203100609060813110402041217030403081504060f08030d0b0102070812090d05010c021f090c050111071e0801150f0515070b07030b040c090e 71
    0x1040c40d1a49a8a80d0419540b0940c0901d0000c1d070000700300106020b001e40801c0c000c0005081168210f41043d6004d00450f200401c101322820b06940da4009003d0110140391681c1405072086654a032610b01010b0103520050066401c0a07103291006170b1002a1360499124580682e99420280c4524940088045100440c550b00c0b6032035001c0412104d4a5400100052800c0310003540c0c3c90035000902c0c82540d60799500b041c15900600d074104426040420842c0d84881c125051315a01c15224001900c240d481030000b800640c40d1005052910b50002074542c0550305252444059030a40e00d02c04041e1524034030300900491318a00304005550180b00ca100048079648150b83d01280c55488000d4a500081400440c0126000040018041c00e2103200e601d00490364059107120b0030a0240210385820344581801204c0c01041441e150303a92006503135040d0350141c1030031150700b000c20000b4060708201c1700d900d01c60b13441d001240700214041c0c4108000c03a00080341d00c1800d507440e032848850314001c003c0d071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 405645539 1250 405644289 405644297
    0x309030f18130e0d0f090603111603020607140a0f0302250305090a060e060702120a0503070c0504230403030c11030d0c030e060403090308030703090212150c13030f0201 74
    0x4080594a0000c0b0b95039051944000290410b03808201c02d1400080000d14024800400d005403c117590010380002a01c60b20704001c500311412100c0e24403d445110800c002d01c1c010800c82030101a40801c02034080c01d81c680e43c03403800d03841003034000303000344a02f100d00804249010303039810481d40203801030b000901426816003c1a030402442d100034100c40042240090700c000740c1865140b40c400e5015014040314035000d16030410200114500d403260b4840a40702c4d00850060a000000030803000c5080d40c0d011058927180c85080c03505060404480c0030707c0340b24a0030607100694481e456a8220407a0541075a60f0105450b151002c1d001801c29030307400c0040040c4904101600102000286004403110b0350000d0500d8802c140101100c40361b500e5280f580c1c108509010102c0d40c48008030b410390313810000362680c03506c0305074040d4001c00b0108170080d0450180c6001000b071b50b00224501c0620081c0c000c038081566110780c1c0030754a91241000700b200c615140c0c682480415070700c0841c0070b61a807043c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 405646789 1250 405645539 405645577
    0xa060924050f0607051c08070f02120f0705070807080c0d0308040b100b1210093c1107021f0c1104020f13030311150c0306040b0604090b0a0b0309030f 66
    0x60340e40c10905d22030406c40c1c3c1c259414903404122548903012942c40682c42c6000103485004030320094840712210300ba2402c4042c0450712101025004c0c0803604a15840030880300c1c03980e40c90701440d0b00c9a00c41d111300e040a000b0004001864141814040c4049502d95a5500c6a540d96500c0c20140fa40244c00899582440040818600c0420000744100441e8841e4069540740c03418907082c2c480142d82140034928140380b144452520b03e01074010200d58104200142c60480284138540107005100c4603440328104200380d842d1082c0480104a6207009540a103564410040c800041b030714900200000104121072520100e41510000394450f0b1005101625004103c000a03d1030f0300404001245920341c6c0300c041080640101003170b40e440761220050007100010401b110031407000201260001d80300040065491307500c1368040c0911030320003803c417511181c036030140c0002442407100450040c034023410040740d50181101500d100302042e9005503e4490b41d001c0c000c5141c0c12040d894002052044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 405648039 1250 405646789 405646793
    0xd090204050a020711032b030b0d0b01091d030906160b0429070804080306033901020f120906040902030a020307030b010e130b010c06050a060924050f0607 68
    0x8081c1c2402003522000150303c50303405003081c821001210524900c2a803240604048001402d0b00d03d0300c9174895440c4c48a65488401800c1e4084c2211000d0180c1c40285010194100040100d17280e050322440b0b00104883c040c803142c256100d00920324101d40740c3e40305104c0400075160100007042c1603085150403100c1c102c050f58421300c0d10201a41e0443d08420010782449408040c1c501d02c103440804100500428209824050007070f080141004d80303400d800200052a0792000c1200c0604000e900c10001280e5000248840c0c400d18514008a0052801d171201d06d49503100288000c19440703900040c000d608107104400c0e00c95444081b186400c0031060000040b4510300d803004e10310a01c0c01c0e0001696905e084400141207074450060141402042d200d00c084903202c0f45d85d07809103500d8040c400914411040d005a03920300c076440d0003d022500380f0007000702c000c001d500320104a0398000c07400d11103020101d0208094102c400125018403070500c004000a2410903802d4010401c0075000c2d03480d041d03441e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 405649289 1250 405648039 405648041
    0x140105090c0418020304050c030a0f0206031005090a05090d03060f0e04050c0d050c01030f020f19020f032208070303020d1805130b090106050c0307060b12010e07080f0111030c0d090204 81
    0xf0f904100485a40032040105112040c0aa406504012400b03400040400ea660b15842040d00401030700540003c00060a83d81503402100090003008100825034900302244502818048601584a0040440c82110305000b8011a02501ea480d071800d4541c5080c0903d021140100134000c0e41c1500c1030140303000150321403c0da00c45409000e02c020303001c0700c260031001509503103102425140c80b6104110000d6280c2c101c2040d2064800542588030502d40c001c070007207117000040085050f00d400001809000110142e0f00c00c420f40034841154041d80d5603601995407254141d01c07024015800442540c46a58400c829132045503010f0341d145041e058031070300070030035403a0b4030901c00c492999240a1300d0315600c0d00c2200c244c014079251410034a040200381e071407600c0f400f8203040107185d01d4482c080d041c0d080d034980b64107601034080d41001308001c680200b40305036078508510411003107001d05440e51600311010700840d9a000306004a0310314540310360304c4801481c2e01214010580d26690405180181d0392 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 405650539 1250 405649289 405649319
    0x307050d0b25050a0801230f0d120306082803051e0d05071b080d2d020306011b02030c0d0809030a03020304060f05040e070804171912140105090c04 65
    0x580d440701d85880d904d01d0080c4c400301c0e040e049001300d0400d0f950039145900c1c100d20309041c8048180c520148842c4d104002c1a20010540c00040581521100c44219141c1c15848034084942800450b900f410341000b94004991500080d03210103482c841303070180460302440040c52008119100d895041c40402c051f10800d80001c1300c0c0107805904ca40910451542c04010508100503030000d40f403044000341d56500c030902c111042c2c4c514464494070001114143c03610340d407080300302c24086581c039020819440c5000790700865440780452003001448840100321124103582d2030b0b0150080c040c0000c034001300107010303110324401c80d281101040a034440d0344081c40b0040b6028401e80085881d541014805880d07003004603041020090140010000110402111742e0015020304254080f40c50702d00b4046109000031400e400c5290000a4144181c0152451400c0d403d100b41d43e141002c81d410013908040d0f4140142a1014883c03503030040c007061030315840c1940c00003151440d071352a185d1307689442100c1c40c03e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 405651789 1250 405650539 405650611
    0x31801091401110f03070819110c0111010621050d1803111302120405120903061801090c030804030203010c210f0e1b0f0402040315090221030304110307050d0b 70
    0x20020034075181411001051a0300400a030420030301a59202701401c1d80d441081d000d16041040450a08094050a50001d4040e0640e46001c0354000000240e5190740c2c01c1c1c05504a50900c5082c0c010003400340309040702203901c410310f107034106d0003469a154101c41d031100e0400c5a51001d01140928002403a0348010683c1e10300c02ca00e20b0603140390608045003003001108142c0781c600d508101e03032000c0b5640807800f02d620480307501401ca0324910310780f040343c018184004024031403551036801000f80003d80029200b02c0c3d1080b0020300101000312006c4804061415650301440f000107080006941c442d0130290b03c50803420f0340018080103c5009a103000030f2084043c00525030010b054a803130404250801760301c1c45c203541c25071a051960340c82d80009007609540c800c160741d444103d601150340364003010345200e800c1001c0b200010404442d527510380d8806c0ea002c59003c02d80c201d044c0c0007800e010030100d00700d0304004c0001c0751070100c0343c4580710079240090606000482005041805041c0e852036004882 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 405653039 1250 405651789 405651803
    0xd0204090e100204050f0415050316030c0b0a0c030e01170c07061409071e030807030e031b060306060918070e090a06052209060e031801091401110f0307 67
    0x5640100302410701002c0c000c0c40404900400c0103100d903488920300a00040c1c802c0d070703000880e8607a814503d99055620341000d603150042c500c0703824503c80c5260310f00081d240102c0c0c0c40811290b49041400170380c400da4035108003050041d2000c0011034003074543c0c4440e554040c1044403885007031902c2c3c40034403d0b045854410594010411405001d510700c201c0808844024600307015003050305130282d43d08014801c021588000c0c2e4481422414506400d900940c0e000d0b113583d846100c0d516014101560115000b8040d102e00400c0313000c494001c030001016908c02800851864848070240b04031680520111500701c5001d1019241d180001031046201d82625034801d18251012000c204007260040c00b0303403801608003007090005940b45406051918651240c0814560103021410060040000041c000a14020320030b01a0b410110051680c1004407103c1311486541500654200c482c80c02a503c42499010340d84641e54003c8a803486005801401c4a1410210900c11480c3d51300c84c0384103d98076 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 405654289 1250 405653039 405653051
    0x5040c02030d0c09090b09190e03040e1e0c0313030f020f0708030a0e0108090601060e1512070915050d02030a02090d12080a0207211e0816020c011b03050d020409 71
    0x62103203109a48006c80308490198007070410031041c588120700c0340d029500e115646c40c6c1c1c001c100007003002117400415002001607020314004d56400f580700c0300e4404030a03880786083e0024510211200c1200c4c402c3c0dd01d840c648840b0060fa03102110b088102c00c40041c258400c04446c83e4041d04200410802480d07160001e40d962411448010641c40c4806d40240c103120410040c01544107020951754192206440c04082d10607010780043c621040c0450b5003d400e00c000600f54804640b201d42251160403251580201c2540e2042c1c81560742800e00320400c0040c000340111071001c806500196004000920050b081044002c00030303c05940c1041c003110460b0303450b96081c4100703410401c0d482d441a0451011800d1107000d48a00c100e428044808020324204d62050403100c5000395401c4540c8e0820015068500329906000707042c168041e5402e58000159140301c841107480000c84c1c03400c0c4c00060b901c01d82480c0d05001e0007149400440004c4040c003005020b842c20060062016200070a00c1d0076010800b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 405655539 1250 405654289 405654299
    0x50115080c0a0e040b0613140a05010504150c060f020327070608040f080408100e0c0a031506081902040b0d020f0108040305071a0612072105030c010f0516110705040c02030d0c09 78
    0x502ca8a0044c0107014002c49c580402080c2e0b080310a07901180c08a0004100c8014022421100403031402c100030050741c904959540304011a9000d14031408141100c034000c421180c0000c550a04000c02e441503580c0000810300c10076115042040c0c0040c4101c0c0e14101c400d03c40d43d030304415a007181d001115158442180c040130607040b4007903078404c2c048400242103000d2844d00803414003901800060607075041003d2158605146038402001072002d0000c3d200161005001524035140b0490140e11960810320125800e150107040701c24005c2e801402e072144183c0d0440190b41d8010028030590900100f4400540800e450b950001410500d0303240d05401868040e04001c400b10b101480040c45134050710742031111280d18040c00c40c004500c003c40146411540c03500503d54820340e20003480550a020360840520380581119001e04c031501940c00c0b03403500c0190104c9860311703c400201010303488038000b0403090919a015012900d49031050328502040c1c10740d035105507810300c5a150001b641109041007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 405656789 1250 405655539 405655559
    0x816020f10020114390d060801060f0b030f010512031b070e07030e070b090a08150402010e03061b0d020d0c020c0109091104140105071203050115080c0a0e040b0613 72
    0x2d800005007140d80c582c807101c58202c25061030703054280726a1141740b409580d031840000b4181c6481440b040800e2105d1901c0380c0710320340a8400391050444480d0a81004143d40e040402503921a0504035801a25a86070000300441010544e80c0800c035804100101c1d41800148114421201c1040000300740082c9802021000381000408000800d4075249401540d2100841e0200c1107a01c19054a6202c500100c0040c401c140940d00403401c0344104944603814000300079a00c5c1c0f01d28001d0b03c0c0c0c103d17691084410f0544034801180c0f0032120503126004107200340002c9001c0e103071180d81c0704001414215410040d200b254202c295020140e0b0002c03c00701d0203580d00c404128050a01c40308144550715207200c140c442d900980c081c4050f00f0b04c103055103100c280d00c1703002070f186900d8000d06070744100c1086e550050005d0100780a140c510400e546102d012040c00741c1200d60007041900b034481c1c500301900030210b9954900d000910351090b111003840c1c00d41c0d0b03149006080d480c00d028041c01c40751403500307072122 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 405658039 1250 405656789 405656791
    0x602010c09231c0f0b060f0f0d02010917060f090a030807030c051b030d0c0516081e041205070501050f0d0b041b030b0a05030a02010903080d020906040f0815040816020f10020114 78
    0x1ba01c0303002010140019502d0300c030100283c1c1d8000b6180b4605030405840140c5450500750001d61032515028044460400b00181848c05103903111810a155128640301c1d60b1548900c10700680443e500c2d0000c01d8005210790700c890b11040b45841d15505203044000b85c414003840c5e0409003600c513800440c00801140c00c07881240c400403c107050852800d103400c03104c0a00b9001c90316000d00084008140a001740140c20101c840c2c05000e80040e503500c0e0b1b02c0703810b0070900101c0c10805031414482e103440460994010b00488000c3c1e440106c5a5051910004412010b001003150054100361501e00e14001030f043c00028203243c03051038402251100e00383c03040c44000e090070350105100e544007040400150b60803107410070941ea001400140d90318280c4503500068071445480f290000000103000403410b0320881107500b59845041075801d241201c1003040030504040d80e01034202101004481c070968a049030340300006202901c81815061184000303007050002d00f241d140581d450313594404181e60300051403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 405659289 1250 405658039 405658051
    0x30507022b110c0402040602060405071502190242070209070809070e04030c030305161d0f03010207060501080c12151e040c0602010c09231c0f0b 64
    0x1e68504800d18403622514510080c0c800103000d450003400c00428024408402d56034006002955155070300c00009584d070310704803419034130b600800d10302054407114010740090f4040b40c0e90082c1800741440400318189031594001300d9000b42101010700840c1202ea00f0b01002502182c9585041c44986162030f4041c1209003507219845000c00143c03005980b84074009820031030614040d6505d0392603d041d00c1c600384035a0084602c0c1d8400c00108820907a00003130482c81e03640701342d5042c401a220803602c541e040071401d001001107040c103000c1084110b04a0070b9a92414001054119144808804642241e020503416190340380c80b41d0050024500c20805500000d80983d0742c615561454100310b0b440d5040026910000c46c0000c1c0030880842640306460009604000b1000e6181400d2900200c11100c40c880c09025500340f40d1800d100c0c0d400380d02940c0c00c40d01c40c4c68401e16804100303c1d140028021066200d81e100e4041102d900c500710761a03070a02c0d110740c03080d014180480304a0034840d086c18001400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 405660539 1250 405659289 405659323
    0x30314070e030307061116060504031805030604020108040312060f090b090c0708030622150503071214070807120b0901050c0904052701091704030201080f07091503050702 75
    0x180d84010b441c004100d60185800410000c0c0303003407054038980130606c034804140b0460000b8450b06400d0140390307030101d030289103c0d885940c00001400c40500094009114542d0326400c06000600594020030312560302c07520034501300e4807088414128030106c0788150012003004184171414002200e031b51280c240c810a044524220600e800900304a66101e0264000d1a942c000b0012400f55282c451074512552160881301d24061914031006006000c0c00201d00d0800220802c00500e82c100030880c081510601b00345e00d03c07400d100d0f8581f041041c001019189551252040020707904006100c0c49001d0300d05810310906610341800c100030505030142154800e0b034904020700c40190403e0040700c07c903001c29200440c40355500e4003180207004900510b220308002c0500c107042103110640c80030300924402d8074014040c2d480035522500e18015400003d001c6510400810209252600c00b0344c0d01a0543c0b41240c0060380b91204944080403c402203c00720b601c906c2032000c06501403116000100b05001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 405661789 1250 405660539 405660557
    0xa0c230703050717030306131413150902031b010909051303090f2909030604150c03140a05180d05070b0601052a0a1b030218070e010f0e0301050403031407 68
    0x861303544a100c050700c410710801450741c0040d900801c9400500341d20f02004100000ba1134088a8500b00c40d0780c10404640f5a402c44180d110600302912500100c1500940241110a0301c1c42c0c81000d00e0600b00109414040711240009510455001d45885085000086c003111201450054241d1601e0b400a00c625144110144409803203001034541c032034244880c0b1100068803030070340e0100748100400540c25004030307410003007405620341c0d042060522480d010446044440012401c9949942d00f0740e0350021400c0c085206580765802494000e00d15061a40c4a4041281c85038030300080011400081400815080288a000100140c0c0903031300b0b00b0b1041c40d01107000d80d811050744855048118810101041c041e8801e010407000210326070003480900b4618940b82801401442d40c44100d1080743d0900b0058010381c1a205414002c070103640703880030710030940c2c07005480fa80c049a14081c2003208050850306299400d02580740150701980b000605051902c0d60070240d00401025141482140c032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 405663039 1250 405661789 405661829
    0x1080705030d020706020a12120e1f060303020a080309011b0c0c05010e0d0212100624030b09130f060c081503030306060706050c0c030712090e0105060a0c2307030507 73
    0xc564500f034680e00400d2030404d000c43c020127588003110050300030782356858541400e25100d40010b619004960f4151101c0103940d01641c00401c2d540d282c0001401a08240c0e44031000035406ca0286410109800021030800c00499280e69000c00c0e455112002481030212001445071500c03580d40500800c0c6040010008540080340828607041402030007002001c1c08041e4018050101d400801b00e007110921149507209134004002a0301c6440120714900c5e0001104068081d01c6a580d418401034000680c9580d840113641801c4400c00c42070f60705100c2680c01c04006242d500c555600005603480d1501142460102c496a100005000e14041d5208109005850380e820381916016076121101003855910f0b15000320050007950329201c914400490f20f50208080080d904819038203507a1145109940c0d07440c6180410b50038407a40f0f401140c02c2044d0321740e5604c9004004102070085410218118030803c07116000a142c0c0340e501a9604044001d104209003440414010100d080301d03400998020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 405664289 1250 405663039 405663043
    0x10806060d0f020109050405070f11010b0d021002070b0d09120f081503011b0809120f040e0601030b0a1410170708070c0b0f070e0102030c07030602030606090901080705030d02070602 80
    0x91405400d542c011000c0d0b000710ba01c00d040b050050800600180300038144014003401184020200502290b568070350107840b50f60521403240103000040c45450b0705c3ea11034003804544c0030500001d02c114040c50070003003007440e0304d440249183da4802000048240144c01c00c0031508000c8002e91040011407040c24403540c0d40140c400c0d41100c6c90a410300c0c200b920000c0064010000340840d040006d01d03d2400264040e007100703800e4450700c10b4009448050110381036070b07070603442540d041c01030284080c0003c1c80601403483d43c11390700600604000803441311200004a024211360310030b00e400500300190403031504003500003c034400414140b1503035014400f03d0003004148010000740401100300000b6001500c5030f8000528250086a124040e0512002400310b0000480d4040e011441d002c1580c51594270000031502c0d441824005000c90303d007580d941c84003035400034265a51205090000070340301d0351110b0016000780f00ba4001001018502010301d41883d60141c03640003550000b2008200c0c20b900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 405665539 1250 405664289 405664309
    0xe04050c0402130e010b1b0a2a05090a09060c0201061202060901140c070602060c03060d06050613020d1e02040b0a230c1f0501081e07031a0a0501080606 67
    0x4100d6002d03072201c00381d06903100f15030714030b074001200103401900015038020144000c0402c555400f42c0c030000c0c015002003050307844030130003c000c0000d01c1164a03942c00da002c61511103281c0d1030395105046525990000101a007800b900d1300c0c45400d40d0b4807000c0c420444184129602124a80000c0c000d2500c0c10100140c0e80d107042c00c000e80a000000b4014034140e00c140d207a4140305c0c0321000c60035141c4040c0e140040e602c0282d4000c000140c41400b004c520010424400e491090328000e000690707521140e07840074040c02c40500300b50b8122103208614551201750b80003422508110640000310500980e2848030b942284448400f26544104400d0249042000480e2081c2043d41014650040e00300301c480504c188001b0009a510008181c168181c64045044086c440c82c1c0001030007a4036056150b0000c0303680a2280c0200f80d8468503148400c080d00d075200d034054945000640303a225a40380c49c1e8900300d0305554a88204414103000f0015110900e00c101703409000d01d180288220314201c008940c003916 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 405666789 1250 405665539 405665563
    0x30c0e0103020c07030c0b0705060c04030f08090301151e050a06140a1205010b0403051b031b0109082e090209060625060c0f0806280305010e06040c0e0405 68
    0x6000194211960340401203d0002c41d40301b240c4001c807564441600025400c4101d045489005d0b0390040f42c1030180c01c1b000c0d2400d0b04c1e00070000940c04042c070760b908811580f00038940c40c2c0554131102030354840e1078991401002003201c1c003904400d02000c034101596044081d00594812072031104140503007036000c12003151102140b94040d0342e41c0d441c8002504c1c0d47c01a4041c1200046c10080017094800c41e16000d0811240b0910890b80042541844032104800c08070b1425096807000105c208101d01d01d202082e03104006040100c08a5201c0c942513040405211400c6004181d00b8128019541c10b80c4028541ea050f5550402c20b10a441c0c2c009808210080d0081e4455180412344000c01c940075042d07d1a007034120b00d21025184c0c21860240007078400031880d807001c918040d048542250060003110b1203104010869403a1680030008080307618401741c2c020b80510304e01c0c0300100001d5024411500300c82c00500043c0000d01c1c191408410325080c0750005412024650180300000f103000548103440c0e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 405668039 1250 405666789 405666791
    0x20c0c090f13080f180109050414060f04060e100305060606270609061617070515131a011a0f090f0609040606030b0f0a08030304030806031009120807030c0e0103 71
    0x11401c0143c0280602007800d01020400107448811070100c540307104411000fa01d03001070060f9140300304070455801044602000001c01d0008072503240c0501140c1d01340d1002407001810a8442c0b4030b5480000c0c048448a805451035182402401410071149901400494541e4980080041000021404030788000204000c501c561200d40d0f460030b09996000002601c0192030b40075002140300040c00410302a109aa41c403c282c1548903c00c00443e103040c1c2e0810000e10522406140220b22400000c1c11461ba24080c411103c0c00640244190782c508006c40e11b200c007895041c1040c2e8550820139001a030800d40041141284100d0f556040c0c1d042483c0840c3e410054242c15404160944103100b02d0790303030007480d003400400e80e2505540603030154402907500101e210311203c14003681c1c07005800340601075131043c800130300047c1c818141243d014501800b625168000c4003400019100c60034012500000030224548107554000c561590000e51490140852810740002800303e0016101c118101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 405669289 1250 405668039 405668071
    0xf0f090212070515160209240102010218010503040f06020c061504050402010c0b060f0604081513030503011809051f14040b0613060e0901090c140a061b050709020c0c090f 75
    0x400c017190740000b00d154010304903040301c1c80c003055080641d910301410340343c0581e0301c1e50807114254414070030344284042c485000a00c4d819100019210341c0c2000b031044500d41c0480f0159000109140003406041d40a40010080c2e07052140c07a280341c151248070683d0060b89800200400341c0e07072000000024a4021081d03c2e0141c5501011403060503900619a030061400100000d603040000368045200c0d9003446107841c19181c07500c40002940c0c0300380010317000034000c1c030040c0310b000030266084244600c0500c1c0091200f1265984900344841a040b60180288410b5095200e05207402107549001c1e10000e070028903d899a94941601000f40a5901404030240c012028600c6544540054081e5a403021045c0c90a00e0540d406403644010440b48202c00200000b10300c000c50348150586c01008080d500450309206007140c84003111823841c00c2088140082c100810001d000c0c0002510002d45d0160740c6180020f10380d45490390a041c901d015591080c1081401900419036a07000041c0129000300c0e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 405670539 1250 405669289 405669307
    0x10f0c0803060402091309050c030c09040b0a052d19140109020306060705060114010215090319030b0904030e0a05060c120702040902150405030706050301060e010f030f0f090212070515 81
    0xa0509050003601b039480c0750081102c1030150011340c0d41d22281d01142102c1c3c1258151050001c1c802c0180c0d401000e9084080101da0500701729000302d41d2103402405240c1d200c01004040c10400c41e02030080c110ba05420409010b0702110340c68543d0050b141c0403106204100160300760103504c040c144103582d10b40e9804800704840b03956020031aa041c1350080704456803540c5615214512000444256000d8030841e0801600e00e113005280d184165001c8024504004035080460011f4021074444000c01d50340b0305500c000340c1c0d242c111650045000703035602c005039140b003014098003001c6904424400c80c810b00c05804510000159008910080c41e03603a80c9901c07440c40450007605920300000d5200c000d1883c1d4121540c2c0d018042c2003250011000c54940301c1d034810080c0c8151200b8094207001900d140100f0b4a5940104640d80c2007822628001500060780c0314900d048a05a456a0006d0b5860383c0c100000d6213080d0100d0b03c2101d04140180a000c0c2c982400100a10b02d9402401e103203540100e04808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 405671789 1250 405670539 405670549
    0xc0307030c0c0504020c01062402100b0607021806152502060405031f05450d0c03030b0a0501020a020d1104090305031f03030905130e0f0c010f0c080306040209 70
    0x400001c2d100751340306d0408500c9a8040d00d840d0040d02030300e5100c5c14000c2c003594002c030507030501e070900382d00540103c0c1040803081002d407018403512500450304101100060f200c0481b0007580d4845600c02e0310f444d051443c100070802046407605900d02034140b14098803c00c0781301324208151640110240c901080b44041a40303030149902c1141d01d0300601c8801c001c03008106500c40c3c1d4210310500c007040303a40c2e40c5000050b8025030b0132140340035001041648038030f040b1402c0e1115900c8002d040140c201c440628500d24580b03102800d0820010706500488030400d42c0502820560320000c56000e100c01e41080d0000355104240280a880f40c0d800d03984c003609124118980368031803800a0000d1040c0080c90501030100d90040d9110140c401c441a4004a4503000031040c0301643e905540703c20310f81e850042000309100c4107041c488a501e549500c00d00f45400200000440003240348040c0044101c0d0000242180c0301d841c14900602204030b04110008180004896000c94100d40060311030001c074000c24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 405673039 1250 405671789 405671813
    0x7050a0306081509061311041802030d090609080f1c121419020c0c011101060e01030b0406050c0319112a0106050d02030c0423040303200c0307030c 65
    0x142c45400f46442c1400b007540090b800034818081c660481d24140c886880c00f0040740d1408401501140b0924100d000d1490f140d00054100680e481111600e04096000681031080e480070020120b1031505040080c241c215420b031009203240390281c003001d235458041980310038030400c03000c95080f000452a44254003510a81c1c101d000d006400300a952002d040d911504481030b00c2030301c840102000e2180c03101c04240201c0d580c0d403012401074540b03031906000541d85e04610101003601c40d52610340210307075818070300b19450017035001d075044440c0e07402d00782410004c445001d844142250020000c022618041801410700090501c40c0090080e0120003000c100d40607170100070414528020b2206990348408940305028040700000300152035882040000507088840029015000940b001c7d1a0345420391002541c1c2d10b041e40c230280d0104510300c070760084080466084010070b0b0380c2c0c2c0700040804501c4204000031400d00312941e2500e280f40513407030350f2400740e05001010800100004401c2180142d046 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 405674289 1250 405673039 405673049
    0xa020112180507090203060316031e08090d030302180609030a140312070804140c010c0803060a0e01080303100906030209062709011a04020708040b070f29090705060307050a0306 78
    0xc0c98030144c03907401c0c0c00c000e90b10503680c5602c28450305070a03011100420000404036944007500d90f0204251400e0340b40d4100c2208070580d41e0f440284802042911050701c003212061007582c005903a80c00306040e070354207140c00600702c5000e03100a1001007040d4030002484004190440d400c88407641d5a09074440c6184502006403c07668603140034804241c0e000901180100d11031401503c19582d07000c0a20358401407852144c1c0001d012000e0704002c68a408011a0040005801490419281c800d500c246880c20ba0241d80207034400070403c114052104420360245c42c0d4035805204592460700010384004024040300e10a581008422000f10b060034006506c02c1c0c0c1052207000c180c178020181600815002a06170792100d2040084a1585443d20841d1081c40d8040030460030f00e400c0040b6000d040d00458002c40c0c149103020303012804504200d00030300e21001c038481e22500104202d241404201d50181c01a8000d900491317060041d81d45080640341d221109290203521420600e00c01c07800303000301e0b03400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 405675539 1250 405674289 405674293
    0x9230a14010f0906060501110f030307030f0204030501020406051e0f070809042a020d1e0507051207060f0b010305070f08070201060f030506040c0501080103030903020927010e0105090a0201121805 86
    0x1c200802007283c214004a4400740c941c0000286c0c6400300c4ca0700c270190000c000307520390403c00000e66080c1c02030380152035014409000506280c0c6944e104c9023242e11a03000000800c1c800f0030410340403110542e08244030049038440600781545101320b01018080c190008210110226036000f860b1916400070000041c0c0f480f00c45c07074003843d03c08008040c0d19100001c0c0018000d045240509d9400782c1e03850b400650180000d0704201c054404102c800307401695045419009a1042c4981010460041c2050901404002408031640720400003141d501c9800d00d07061600f000100000a40c115040d000a80b0b8142841e03282c07640d801104038018001e6810100d0121600340011062110008181d4411841042941c03451910b4030015506210b09200080000c1d803c03180500c01814078948040d08121440368031400486443e0002c01603809941900086a56407000c900170902c1c00d000e001c0e00f0810080180c0161240c80d00001c20ba0003580c10410780040d140c2c081000c01107800034500401c0c5800000b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 405676789 1250 405675539 405675551
    0x1a0f06010c0809010302390609030403110f0411041e06080411131b0804050d020c0a090c030209091602010c080105130e0c090921031017010609060909230a14010f 71
    0x103407600161521081f690018800c5200042c0c1c2020b000080350103580e0402e03001a503441e0b80d030003007020f4240d144055540042c1c40b10003600c1280f2902d000f803c013a118100d204040200b0040b0100d8a251103075100508001c031003014000800c11018200c50300302c3d01a16030303040403100580c01c0c001138103d41c14542122004c2e01c4418140641c07240106009601c80c001365804007136106000c0b651382030b0070403040e544010184401c100300d44595000e100311450a0138050300300301144000038501c0400720740b5400c10801c0e41a0380007050f5428425556441458288040c0c01c1d410100499080340302a07494421003952903c1c030b28042c9004000b01e41c02da4034000c001c908140b03841c6115985441c0c407000640c03a980c100781d040c241103690700c200783c078415801040303d04586031612040061480b130000481110f9541c0d00b034046544455030040350040c060700c1c900803c03814111b00c0d03d01c20750181c40d140e00c801c2903030405440400c01c0000c6400c00c600e03504085040058401c40f035080c0c0c0101103031901d0140c030318604a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 405678039 1250 405676789 405676867
    0x70f1106090705040b0303030106080105060c0c0a03080c01050702010e250306050a200703050313020d0233180f0a0924091505040510031a0f06010c0809010302 70
    0x20034800f51003058805020400485d07091669a01003802080c000c210018010b1015041020140c0b1045034034400300c8070140070940108a44080c1e6070429100c0450020720076001c41e5003400f5940e00001c0300d1000704412420b510001c3c2e100c01d006812080c01109440035034140d0400c22070b101000d980c00010811041c1070615a4900606a80b815401c09400380444640904001c01c10346031030350740640310907145a507141061400882c1e0520102e074030004072142000940c40304102081d20040c0c1c9010510142480450354600040c0745268141e00b0b03070100600019001004140350183c5001d407410f144500d1044c0000b92100c040350041c5c100030346080781951f800000000301120304a051a007400000b5120250311003500c01c0202e00300c81d440710024041143d400c01d40e1100703502410f0014a0050240c4070ba49000035943c1d6080c48008040501e001e0200c0e040e1304001d540d0b0450b8090806c0e112204003a41c4000e6640241241d850606902040c002c0c4980903d05a1006407a0903000c09210b0384201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 405679289 1250 405678039 405678043
    0x5060a0c03060f06080402010c06110c06040c05030f0309060304050c090420010f0c30080103020a08030307091401032a08070801140402031906030c1418070f110609 72
    0x500390080000e0401c400040c107403541d80c10b8a001c1d0b610680e00d01e18180d07210380054688484c0c40030304441c25036a65000300b10b0050a50040e2800030150b50140c8460b082c0f60905510440c502d41000340701e074104168072403540b40000220b40e21042c1c1555144e4590352541407041c2001c60481805070440b06d075604010412491807261703a0349500c2002d0f4170680c144104011680d01000007003030b1011800c46120400410050015100ca0b0144500500046003034413110400c3c8840e10780c0240302003003020700184218588043e8420181c0303011801503095181c420f0005000d1803481c49601049a00311010941c2a48242c10038852043c625815842d484c60079041100d02221006400c00028402000301c1e00c0e941c4203141c951f040302e101055000030040d0b440100002980061b110312000084466404c44c8080c4501444004601a110b030912079440c00b241407508150a4103011722403603a40c004102508a01d1101c2500301903030740342503089900c03610b500759924080d45503015034a00c10070003000304c01c03c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 405680539 1250 405679289 405679301
    0x10e1201110d1a2d030717060921030928050d0e220b0d0b042303160f0c080304090b0301020717130306090c06030b0603070801031101020a05060a 64
    0x281601007040002003d40d103140c5000b1080c40329400102d610308140d211161059455411032a00803a940c3c0342c1385240060f262903501e074491807156182c064421402881446a10790080b20302c4c0c0a054110a00140c40c0742d4041607500301e4004907000b04c049074115a04024000d688000c44038595003407420304441281d00c5510060403a07c51040c4a04075101c0c1307201c0d6000710102107000d45100a9a000070042034440360b089034851210603520100c0303181340d43e58428201a624010f810301070090600e4100451075460301c180349141d608081415030074800d0300108840704403031400d403604503102c0f40d03180a881c1312401d40006008000d50441c04200c20402000030800c50f20420000c2140d46050414103080c0c0c000d0340c4010f00717110f1510f00c240a541c880f40b0001c041c4c0d118441c0b13840748003036140d60703620f400c84509420035506080840c10134400c0301d03054030038505084000c0380e41c10b040d4905580024203038441400300404294001070078095030b900800c15003429691040c151446c1d89408981c01004000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 405681789 1250 405680539 405680557
    0x90309120718051816050603070e090411010801080a030c260d0501050301050108150c03090a33020304110424170712030210020309100f0b0f1e010e120111 68
    0x10110b680e070f8030700c800008002a41078174002000725824607210400c441307a080109040c0a100c2030008044150b1b80d6803034681d1040b4880c0421480b0100d4400005020810580202c6030b143d01800c404404240c01003500c410169000c1c0d0001c02c0c0c030704040040300105030717044214207500c840400d21900748085504072130b05848087d0002c010326a603d2504982d244824000d400c400101c140c08540c0005c208001507500005500c100c0e030030800c0710f55548400c40c0211400020101e4011850b07041a402600e505c2c29900d11403d00354114105600c4e66881241c0007580c16204990700d20610030f4a103080004a80e01d80410703001e403140e01365101c4481081155840c0541c2140c000d42c038000c201d0b500010407040d842c40c0c256000300100354140140303100a5002801e840079510410f8402c0c40f5100720340c064100b18801200c4042401c2c42110b003480012a000294244034500f49000b41581352420001c5403047c18091808804208038140460700324042c0c80640c00c0c0ca03500f480d540c1d120380d68101d0010070642d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 405683039 1250 405681789 405681811
    0x9020f030a0f1b030b04060509070203031603111602010c080f04050108090f061f03050706050903160e0c07020f0303040e0601110a020306040b18100c140309030912071805 75
    0x8101440148121200c2c08400c0f0481d084406000503030f94400d03800f20b442c040e800f9200203661611000010710a81041301ca078401039000204008405410b00071007002402c0c02d003003d003c407203504000d480c0035001c0c00c40c1221221180c15860f405680c8101d219400303058004148a946010041d40a0b0300c0361b00c14060503000c29506804118030000020703c0d18801c54405006d0140b0b51030b6100d000350500c049600c03458001c96102000310100e041400040b0040071785490382a5118000d000741824408002520020309150f91070400103500800003203544181d4404020303588a103248001202060b007854010b415120104000c90300901054010740600401d2701c610980301c14a01c00a40e07120440d81c0d00a4053300010085400a5a840000c40d04026010308001c11406005034291400a00d440c1d500d10035915034209000e040d410140f03c0c1042e10700c0441c001c0c03461410341d01c0c003030b0f913441042040d0f8011105203484004404040c02141c1c003922000220b9107101d07558103240801340c0f5007a1402e401756 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 405684289 1250 405683039 405683051
    0x718091a09010b040311030a0b070206040209060f01081f030f050303010602010641100201090b0105060f0423130f1103070206060d03110106030302030c06070905030a0f020a09020f030a 81
    0x518094945904032000982c203c0e2510f400d42d50358419100755052402d4043c0708880c0d2082c0010700f40060107100380c080c2c0d40144002d18060040000f4050b005d88158051450450a140f03240d078880d12090307010914030001c04050307105100624212400c0d034006003612100c586070208012020000318102c0d2000d031300901941303480d0b50100e40022984007031665465040c29900c2c8000302c508091a0804262009100452004201103449400c61128100060355a8240402000298044640504070980e0528107001100007002000e10030390041068034035805800264924481c0b488811600c00500000078401241f50510082c00070110742c0e60905050000c0045c0300032249080d0781c440c60082e402040d50b51205000d100402c0c0d80440c0070b07820042511401725100100340142d5000750710a5000703540d107580c154040ca040c610089c1450b002c210100c60704006a99000030101301c45604250a080502d02c0303840000e0f4081980e51148107001c1c000f0603004843c2e455000a0b41c401e40d01120107000c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 405685539 1250 405684289 405684341
    0xd26070606170a0f020301060b0c0d0201050c0a0f0c08070c03030206101e05190504020a090e0a020a09051908070b070510050702070603090204020d05040b04030f090302010c0b071809 80
    0x49140e42c80080c1543e0b010740880000b1420010b500800d450000d400018802e89421b01c14a056001c10906a410b502104012401590910503507a204002080f024107064980174010148106000b034941000312200300c480038000450b0454454079800098110791075174074540a901c52004031011000800c4c0241e00081803500960040c861030b42009820850714240380c1049821110405c92814540b01a5401708168841d4402040501410f40301c500116107454111900d02c04002c00001881e401800803401058005480b101515001c03210b1001a4114030300c1d50000c03249650050a45205129001403030754007030802405c0c0d030342c01501a42d10440702d0110b0401a074105030799810040c0d000e64010045144030ba03000d038224901c001c0000d841d10351008000000c1d241c054a0a65582200380248001c160700f2005c0148555400e050040b55032703143da00041c24044507204041c0000400e04000703090540f041406070366a82900341686040b603200d843c01d0008240d44680c4c81e022102c0c1c910301a0f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 405686789 1250 405685539 405685559
    0x3061003170909040308130501111309090b041202030c01240b030709170f1221040b0114010903020907351b040509150301050708060d020d26070606 65
    0x100b004400b5152414684030395404844400300240841e040c0392a40c0900c0c80003c4080c01000e4006a4400704c070380d107032004001d01d20b0003440564420640c0915010b40180040e18003858154001d0304014400d00408a6603016800d41c450b003007001c0c4055103810402600223504c1c46005540001074682d181c2a030340c607400141210311007036441101061500c242003004c1e1103401e03440c40e4110345080070348280480f100c82040ca04080114455030f8014003180d00354159003070407034170791a0b0079801d51000c02c2410103440d0408560018001c000c0c2c042c400c0100c510060b405114460021a0301402e20081c924242c20020f0118045c21201c1054407034600300f80a40c4184000360f4101840710380080010340d102e00182c45020b03490201c1c1d12440d85401c0c4000121030783c07540e8140c0e20031600072000c50110301c0d01204240c02c4070700081005052044540501805031603040c1c01e104007950680310042c1910340381c1002c00b010441002d0201403080521095200f02c00040c01500036644514000d101c0303d600d07000404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 405688039 1250 405686789 405686797
    0x91504060e040e0616092606220b060a05060a0302091e100e030f011e0e15010308030603070e090a030e03150c0a031103010b0703020d0801320306100317 67
    0x10781c07130741c0000701241c24100c03903100700851074000d42805510b240da1804c4060900c80b401d144441e00782040002c80c1402d240501c41140d00400401c0149804000141c0b005011200500301070b00c20364a90000400c20307200c4006503000340c080106519180c0c240e15500030302940c4080125400740c400d01058000010a90028031900b08006154414100d039044c000c9410000d080301c106d45c140b10704202d10100c1d050070320a80c5001200304541c03105200c00c4034044420381c3c450209000442d40330a82c52851180324022490649a1040002d40d0b40c0d1101e0340081d180642c103400006c1c01d40000403d0201d40300b400114241454401d80b28002300d84c284000b05a1140c1c0c4a0341140c603400741640028500d03c03009001084001100d007000103d9840301140020250400d07080fa15142d040040c00348141901080000001600740c07034110360070740c100700011216560f020000044000d252126201d1803400b01c0d62030740074580c06021248949041108902c501d1105d01c0151004014540790700b01d003000c441c1c115 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 405689289 1250 405688039 405688061
    0x403020c011409040218090412140f0d0f0b031203011e18180605010807050405010b090f10020a020319020901081506210a0506090105180c040f02091504060e04 70
    0x2140c2412003483c01d01010350b0182c90f0209074200340c020806420380c1c810b10a2030041e4001c2403081360079119140013a001c4000307118004401007052100d48840c203692000c86220341c00040010a01c406602414009840075145159140c012162880c0041010002440c100d17005a070700007903c02b06880c82500c001c416801401d100c06c4400c100d040c1881080e41081c1000b007200c0c22102000001c42d00c1d42003c440f401c2e04948545d401c418400c00c058982070040c1405071200700702d8140340860348800100401d02454019003d00c0c2d0348107000d008240203001c107c0d040368010b41a20741c04119403828406c80c81d54030038101d1084c1d450724004500c644002844646000408440311084e45503041080300c5524950401060b0008881c0000a458814450301000d248150700074087c03402d0062400e401d45070010400025030300e02c81408280000300042d013040032001500d00080d1114050302100c0a442490504c0d41c1111102c009091581025001801110029600c0b103002c040581c0801060f126043c1c41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 405690539 1250 405689289 405689327
    0xb010309021c290a0c030b01020c0f010201020c0304180c03020307020a030c0c050a090e060a0e0d0c0c120c08010b01080c0319140705040303080f06030a12090b040e0403020c01 77
    0x8044010b0b400c51088161900442002c00b0605124070150103e02a841c9281038040d1a81d00b030001214060241c8070118003141006d000d06075900f00002d58071001401024410030420030701e1202039000b035044400322014001076130b640c3c0f92103c000600c8003801030352000f0450320b42131601449521074030170799025100a5014140c4454a600d044035415413104080d102032001e154001810781e11821200e00500c1501d50100f100300900101c0d070b08110000341128940350425a2038180c5000c0410340381704c10b50150415002d45595401e241c070380c0081940000c070011100300e070010107202e026120001114131140003072180d03810300d1004591090050b11404601c14051001c80c4a000d04d00034505252203020700002940300d00083c3e2200c1c54801914241d0225000050500a05a00c041a26407004104442c1170349809c0c400c010955170401c1080140441000550740400e0902c51250f0a00078422600829261034807400c4100360351000340c1d41140540b0512500d00b0703555018010310703d07050000d008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 405691789 1250 405690539 405690559
    0x2060c041406071a0708062e050a0c0605091c0e03060106030c0c0b0f0108070501050309061f080307060c090918020f0121020a08060114030604090c0e1501030b01030902 74
    0x1090285a030031009040311581310324516041607592681500340310703004968459a1505159042c0030262280d00049003044442c003011052000174488480b220840e0303880c2c00d0f5601c0388401001c58407a220b9001c003d10150400f418445504c10009003907203d05502c0c40325401d551f070450825101c0c000fa0098582d0560006401001f5442c080d5004402c00140ccd4100350070841d00ea641c0f10311120700110b1702c022004070010b00520204a00300704103030180c2400e08201c0d207076090032410181e40b0040101702e00506102420703070f038510820300440d0382e0017405c2002c01c42e5180c40366864104040c003e100c0b454000111800381c0002c1419050080400803040d0a9250f0ba050440d034082c80703800f0000b0f43c180c074180088460a0080320b890f002175140300600b440c60040e00e40d002414010801d01c405400c40d8100403c14600341203c41c0c44004483d0402e01c210350004242c2d82a103425032103a0895400101d0700502c00d0100100c1c05990040c6c10745284090b03070f04012a00580740150116580c40c40c010b034000300120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 405693039 1250 405691789 405691829
    0xe011d031e07020604030b0a0522020307140d150b040b100c030807020309030a03120c0806090c18100206060414010f0e0603070b040f0f050d0803040305070201180f0602060c04 77
    0x2008080c2d90740041c0a01c0d10b041c0d00c0783c540048034081030358807640807070b5a0000c005800100c40960400a8113108001e00d00381303c41c0e00000e030340d03400d58000c80500010881c1c20a03078603903c3c003004034817060740402c41e22028202d082c01c2100624a4003425400b40d82480c0001006240400010404071440c2d2507001e009551900d0454484400903c548150b100c104012049075404000c01081103109503200761078030b9524680c880a48076800d40241c00d00c1034010900041e5076a40c036015900c86403181802d41c65000001c0030000e0061220b458a4101c0040c45050058a501280162082009880921422003a4420004804024411586406e41526050102c10a035501c440d40184004084840003a1207a9100b8003540c400da0101840d0001250104036401c200e880c007100629003241e80910301c0340540c548000c60300c0014801401c02100041c09002c40e03028200b0141c0c40e0302510030900441d0745620303203206420414060b40000d44180c6000a5003501002e040700c0644004c403280e80f502d05019 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 405694289 1250 405693039 405693097
    0x15031502070c050913020111061605221202031b061c230106140f090402090d0c0f080f010203190c142805090a050f01120e011d03 57
    0x10440032103030b62034100000180c2c1d5440701c0e0036501036641c454292442202a1002400f4280d1150038141c142d00204104000d686024034103034100f2445041480d03403000f0b00c070741c10080b080c0c840c0c280d000000d0404c1404500c1c09914440501124401d41c1160740100c01810089070350292003440584c0400d04000b00c0c080d0944c8800d01c203140340d0800030007182603030000042a6007009580110400d042c86140100101584245692300140a0b0000c481c500f80714000b8089841c801c1d00751160141d900003400a1142e103a000f9420b690942008901d5001c90300c4060108031f00301c0a1094031810b2140701c024902209061003101c3c0201503003044496030b19001d54004029003848202e480c2484200400001441003420003400107614805140b840d10129031a0104200c0100030b81c80d00300001480500c80d42d4699161a0050310740455080400004d00301c0102c89940001c1e245d807010034100000140d15683c15000040c1040018a54801901c261880c0964038043c1404c0340780b141c0418038141340c070a510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 405695539 1250 405694289 405694297
    0x4060804020f12072714060130020715150e061509040e030708130609060e0108190b060a0206010302042406081b03091c0201020406052506060305060a15031502 70
    0xc564805c013a0000c4111172601114244e0007500113241400b010007a0702e40e845820039401c01e000490304000a04205d40e00030080003140c08030390881d54001404002d009008086d845141140c08080c08607004028a0b266600c100740300306240750754a080401c180f0b14181c401d046c00c1740f940c814401e00302900a410070014002280d004d51490100b000a030000c182c640707009040400c201070558000c2481c026004000f14901e0b40305108014082041e0782003aa40028215086207039200759021401c0d4040e1508002c010600641d64000d40004d1401c802d03c0c0c0100d0f607607049034003c0324100020410f11844500c800b4084020308001c100b59481030046a014200c074503003150400c050314424110a107140740c001d900c02d1f1042140c41c3d000400002c0039038031810401610b440c0358802541003505d412400f414038010700c1c9000250134000c034150b00600d000ca684c14500c3c035401c0402484213035035030b0410a403a010300b41e5407031410905141c04040103072000030b160700807a40d100c4050740722000b441a4080080d04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 405696789 1250 405695539 405695579
    0xc05100c0f0f140c18011203050d0f050403090312030b010507030e040e07181b05040312020106180516020a05030d0b120105010f0611070302011205061c0302030c0c031614060f04060804020f1207 85
    0x303079a001c070022465161041174460752207913f51300d850f41c2c03c40c00c18421040fa1030700f1000406060041c414040d9a0200689a000d641800c01a03d4068000c2c000350152110140203003041c4209407000507403c403668111000d01e20246010413000503509031078000b107644009d03002c0200c0d904000420018403484041d285000315440005522600c440403c043d0782501e030b428000a544038010b02620b80065814004500800d0006246a401c140d54403a140d0180207250f010459440c42c082982d40c8a480d0341c4a0042e0484001708115070719084a580384404a024620003d8001303521100000e800142d07540c20390b80c05071500702803038000001c5030010300001400d40382c00181c0021091307880f02d04a03a50386c61040c401d402554030b07030600c0c00d800d23480e25466a15480c441d5000120407001c514000f90000709581801c1c92418a4100040100300d1501c0340f4076040c00d80c5000064001038580d4080c0e02640150f10845c5c150f130002e4034580400491800d030b15000c445980040700100000d0a051200b250655 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 405698039 1250 405696789 405696791
    0x50403030b01123e04060f14033603070501021902030703020709020d09061a010206071b0602090303120127020c25090f02070c05100c0f0f140c18011203050d 69
    0x4661211203d150308194014004207d5140c00315012541100b043c0d980e215058441d6410b610345100312455403280d0b60b00c07030f1100105101455180094000c43c4410503005d1341c040720b130345003101d04d0014000d621481d411220038910710303c1c1c1d00030184007208488182d90980d0051103c61704203104c1c44004e500c01400c41c000780e60385030008000585140034a0f800711398078400c0f000c040e542c02c0c400a420030350007c140c0340402c200c02c240c6145030303070ba2500070400c656000080142c580c060000443c5c5180300c0e00a003010440890000002d9165200081d50079a46100000d0041032861005683c2a07010f0805c140200790880c80350119400100c41d44031502000c0c0e1034800540300d80e6121004212000a40420149038002403d40140182440401c0050005444503a01c1040011004200d031a4450700202084600815142441500040031a400d40c100c800324108520b18030140e980c03004556000c074010074140d5079400403910786500142c100d4500c0c102141070642c9594044600d507008040c1d0300b90003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 405699289 1250 405698039 405698141
    0x904080c0a120309060c050f04030602030c0d11031501142215050d06050d020303120a0f06060f0e180c090a0305011a0a0b030910050604020c01050403030b0112 70
    0x490b511140c500c07818900780c0c400051001c1c041c00d060381074541481c40c0d0020300c03800b0414940d46141c9041100d0840f9048000103841e91208185402c05102e40c3c4920700645040c50481003590240700c0c0114014401c3e138218500404180d00199000d1002e111100001c2100b41718941c050a80050403402d820001110705070200c5d21841c0d44030036003110444500000342c01040324440e600c128440d04c0094401181c110148a001e0360000355a4801c00440c10b02d900003140110b0071101c0560042096030654500a0000544032100180a08030071071880002544d580417586a5046c14100154000c0038124031a800b03985010410300140d000d0803486800c10108240040400d10a1045100020f01480044250482c44042001806891300000d00001e030070000d00c1524030002840e82c00c0c1201100c0c02040941e0748200103002801404001807865003003c040104140d4994444505c40c1c20988508030812902c503541c2c070890b00f054201000c01e20601840e01c81c00b0608140280c0e0050482d4803234898 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 405700539 1250 405699289 405699293
    0x10317070501140703061e090c020f120a0e01031506230d0e07060206150409020a0e070e0922020d0206130b07020933040f1404050105090601050904080c0a 68
    0x2101c01c00040300b621000300c1818480202e505000f1b40c0e00a041e4a00341e90800b40094030907a178198818030078000075981d62021030071020300034001c01c00b0400c090700a6405140e1803845403d981d510400001c00007a8034685185115806480703454108201120310399555803c0190545a01d5141d0f0046030140b8100d0513105240c951000091501d145000808204204103401180c50050650050740543d04140104076854003c4001040442c000b1207012448a00d50300228554000b590003224030b912802040104942c0c00006541c400310003038582480d696074a0a181044008801e13400348004011740c1c00c04054a007000803443c449000034060352901611042084004502d176010744c1c0a03900106001084d0b01e0116142c5912400c0005c004102100b46c80c084045c0c000a00d42d5483c01200c00f05451074075448980c00000215800d0008100b0602150300c01c88002c0b508a80854a0b0760030701000405040300440c8144c1200e6015111031201d4540e5610741e22203403c0031001c2c10300380c8583710359000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 405701789 1250 405700539 405700541
    0x35280908071103030d020c010212010801140718050a0608190606050409110c030c0714010e100f02012d0e010908160501020717030f070207030305032403030307020f060109050f010317070501 83
    0x47c6a2228400180e031120442d030b1240e02a441603108060a9140444403403160f543c03081c2a560000c0c652411182c0c85074030182418408650ba0882c42e007003440b01c3e80120300c0701d8201003900d00550301d090368007004420107111081500c40300d0082c500042c00900040103011180d13001184141c0d0103004c29814010350040151a542001610f07506540c42410100700f20848500740200e40e00b800e02e00342c000c8401c500702103900d0403032654070780381004226810301140038401e62105004007412584e0500003000c4c200c1d81c1c1400d481030610344540519000001500380d80501c07450510546c4085800e003083c0406082c4141400554004d0320039540030003a10001411482c00280351244049040303480e820a4060140540700007014541507500011040c17000c03d41140c00d407036001400124200e040368008180710074034004040043d802d4031000c01030015030307500804d031201d80c2c40c141c60440c0e01503aa034105003801e480e815180382d041111203200500104503002240e104c802007080314649010b40d01d6031106c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 405703039 1250 405701789 405701797
    0x306100b0c0f011419150605030a0e0a050601080d03051501030203060d060c020d030b03061009110724272306040f12030c35280908071103030d02 64
    0x2540c40c807811320800c0741034a41e540c195407662494140401070b0514000a4004000c0d19001d100d040c0403011000428010341764001c0c03952400700c00240e411995103464071a035198800c0c00740383c0c414003606407005246403182c0319003031190040c1251030a281d044500198029840a03240c15007014114404c0b00105810740034200f082c464560041a0134400320380028115018094110301c20b40040d07041c8200001c180e4890005d83c0c10740e000006007040c1000c805032540c810385600074005030a441c8490006142c1400c1d650400c2a001810300044103820702c150f691101c9401d03601150b034281c1280c507002c218000c3c58022250503080c201402614048080c900c0d2180c2203500f220756107441c05001081150040b10803800450606040c40026044000580408842602e24170001100046400c0d00c50b14041c0c00c544903400c0c02c0c0305800c5070618805000d00c0c4070400c00313170a00030070903c543c0309294050742c8110a0141d41100b20503040a89079075030041006100744803954036200901c11503a80b510244010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 405704289 1250 405703039 405703061
    0x71407030803091f0204050622090f0204090e010b0d0b0916180b030601080a0311070302122a0d0201260106030603030314060a12030525060b0306100b0c0f01 69
    0x10032044808207503e52020001802c02c44c641c41c0140810000b60b1142c0c001c0c1c0d5213280ca048e02c404000803200d0041c80a901d550782c080e42545003044800c00610f2101d5008105859420304240100300c48042110300303030344044003d5074100c1404540d101c04038060401454101040f0700544125003071184210f504480b0039001680804400c4141c0c41c0702c03a81e10711541c1d00003d4240c000d4015176140480c1c9a480e810303c1c8801905000031140340c4012031000b413001c0360141d64001c0401d2180c1e07a81e100c00c5c5955903e59070b1851141c0c104240d03041d00000c5802000c095002e4000d10410305107810354011140340d80c085459180011401c941003080050341d0300f03414040e02040c0e40015503d4614103004056515000c52841e100b4044424842c06e0f480b60b60961003a107208510b4092140400d107021582446008280030b031480320020001d1402001e54200400d6601400f01440f4040d600402c01d5250032055824ac43c2c0400490741c02c20058042c1d1300070700b946840c444107681d450030f48800c80909550400d148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 405705539 1250 405704289 405704293
    0x62b030324051f08060d0f0206040902040512010e0304060c0203010b10020c100801050d1b0902040609030c052205100515120c0301030305091c140d09170307140703080309 75
    0x140b00b181410115002c4004444078000f152100c0c4090250031154050106800b656243c22940c06110014032842c540c41d60280c0300301e80d61556a40c920b4000c0d0040d0103128428501502400080041401422101043c40e40070b18507040c64a0400d95103081801e07000c903090754a070200d1340c890741d681d00d000003010109a0084c050503c01d15081040c000c80908040c0107110a1000502590301c07030a529145203903028151803401c03050b5041c01240590558002440c2900000740401c45503031100c0c00004903886198003d03400c40d110020401003055001d008981086000b41141b410b6659401543d000015801150255520340000c00d015000034030102a401d00d0009a80b10700150901c034003a400070a0f610410b0465045580c0103100b445071490701c500c0740140f8003001803200350080395082c529501600c070444c1c81c003c8110036500e0324601494000441c604c2c2c0310008501d80a40701c9418045c4100024615050356070761400e030f00301e804288d030429500c6540008030010704403c0095008030030000c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 405706789 1250 405705539 405705611
    0x201090e070e0f0607032a21030f06030f0f06020c0304031a07080712360302010b010201020a0504090e07030807080c01050603070303080c1c06090212062b0303 70
    0x2030090f20b841003c29140154000c00071000031aa2103801625002640042040300341400d100c0b0420903172415001600392880c0c40b00002121000d0b084030a080800758805011400e040c5c0401c0c421035180d0302c006010000044400c070b00103407011a50803616842042c0060921405402a0703246822a0b00125001002c81d804445610b24000c1016400380700740c90100c0d003602e090b80d80180b6026181c00151450740e11185928800f4800c100350000d000d204079500d40340c40f40021044d200b9074100302c1c02a00036500c2d05105900c594418000c0b07564011103600c410b45020320304001e4000034500810300396030600032140c0200014496800400362640030314011925030803220a441c5c00c660001e44031520907031017034104000183e0090015513100104400c52901c1c1e10740b4040484041400d421502c000520388040491009034560280c003460302418034080c5103682d401c0501829030010031101740c05a800e1041350610341080e128825030948a03103004100320700520341e650051440851504030044240c2c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 405708039 1250 405706789 405706817
    0x14160608060f030d050a0903061e0e06010f0614121e01060c050a02040c17040606060f0e061902160801050703050c0712080702160e060f01020d020304120201090e07 72
    0x3800e8000d5411a2000e10384510000042e42e03400303910401300184040412030b26186030140d60078100458000d035060000304440020b00c64006c0319019200507140c0b82a001420409001404506941844102700c2000341444c80c191562010303100740141940d0104030744400100d221105038003546000da04802155142031100c3d8107008160003d00c10000c1d444440c0002c94400501d40410940555000501c400a010211382101103090b15a8002a80c1003d00003046001d62002c02240d41c941c3d00c020a11520000440348000c8412020b82c0c040d00c10301c0500304841e5a02650013052440303004031030f0070201c0c0c102e414a03095019400030055075921403c2207425a05030207440e0f84048500d0a03603142001c04e070388010000701c0c8841c2d44c0e0204000d110016201074003c104201654488250844001d40e03219510452510308036038850041d41840c5012409500019803000e0303400d031540140d0b06107400c00210212520440506a041003240b8000040c2c902e40707426000c2c001d8819598100f503450070b20f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 405709289 1250 405708039 405708047
    0x7051303051e0c030f12030c07060c080405010c0f09030623150108070e180a0e03070f020415030804150318050102070210090807050904060902030708150f0c030c07141606 75
    0x1003070f190083d000b42d20f00814180001c01c110203000030302c000c0c1c2a1a1340300c200c4648501d0113240001048540391149003c1c0d01a04500070380d110310b00c904024456010242c03812900002107041c1c0c40d0224852900503c002485504901d001e90600b1104035103d0115900c0110300c000e040ea000014010b408450b00c5036542d100700341c1a803045070b9040c045040200d10000c542c1940203505140c01d41d0502902040d00e80c02c09030002402c140805040780d81350101410006003454801c081240700d107103801840d1100f5503000d01b81e101229013110a45043c6843d10f107101c003000c400d2442d154105942c4540c440e42c2013154120402d81940140001601e1300001d00c10b00c41200c62880610080c0000c03004208900c040000300d000035941c0580760803500f51107900d4044050080350200a601d4080c030700f00400c5444001031100e4040b40c1443c003c1c034094440c290b000149035000d42d15a10104030810020740c80300d10b62001401038034030941501e04208654030302c15007449105075070421007040c4a0000c01c101948 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 405710539 1250 405709289 405709303
    0xe0d091805010b070602090307091a0a0807060e0618060d050a0b09060616030e0a030609051e060412020327040c140702040915060e0103120c0b07051303051e 69
    0x19a10080007154104100c80c03503103004000703004003403c2c2c00082585c9151000d001100c004c0180b510140040c41e8100e9801d004104d100000c2e501400c1145000215204001070b0b0104840b00781d00c99030340700c18200041c0072940d8418900010780f60103903201c0341803607214000140703882c005220001800382441c0b200501074074004007000740704070141818010942e550404859100000b01c0d04107020414030f24064038a0700e078102d481607005c81c0c1c0345000802e001c010703000100c0d0540b0540c00e4507424101c00c0f100c00d1041c410507a0f0030b03e01e60300c8400050000703406505081c00c00b489071f00447e402c02811115504503c20b42800080c1c103185c3c00300703141c1ca007403c0601804940c5581c9080c12a00341038a100804500e014052020707201c0c075161316101c0188010034191003019036201c0c1090125a0f212802007600c17100a101c21960005803041008020748194014441560f12240758a2a500c0e400e0085816800101500030090446140040021020052400709a8116504a50030a000d240b82410040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 405711789 1250 405710539 405710579
    0x30106020a0b060d12080916090f0e0714150c030d06080607050f0d0f06030f03020609060c120a0504080906070c0302031c200a0b0915240409060e0d09 66
    0xc64020400051001509517114101c80d107026102507456025091900c45102d42400d0712541e01900420019001c1d0004010b12039146014418102d034100610b5548a480c803846038130300b03009001031140f49020300e0410440340d9014000e500308207050041c14110303032000d0070814400342c3c2d070301041052000910485500c071519003401801c0c211694800105481228003142d03840c0d503a01c0c0c00b01010a4554441000703035400810301100d940d500c0c50069650f010a46140c01144611030000c3d44c9009480c00b1517088204078950700d400e035200d107800c0384041c2c00060801c5520003024005035605480d400302a10409020f20b80c00d0104600e140145801c0824607200d5590615041c000c00300300c281c1044640468a05590400701440000c010540c2410030f65200104809049030502141c0c0a0000e508403401d00700e800454002d80381c002040740c002c0e00c01d5000261002e160340740c10041d03241a40c0100c0c406802410f010889801c2c8000190400142c00550404504600c00622201d1040b03080c3c01c0c4050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 405713039 1250 405711789 405711799
    0x1e150a030b132d0b10030804060906080906010315050a0b090903120a020304020904020904110a060807030f0605010806011b02030f1510081b01030f06080c041401031a1308030106020a0b06 82
    0x1c0e02c180d81c104020f5090810280280e90104041041a20340d03003480c80065401401080c0c50b20340b901d80003400c0d0400c510441000511880100340e1002010034802e040700d80c0201c4291440300c80007506805085c004004104640d62210030841c2c0e511144956489020400091a0b994165004003005045c018000c2889944140208401603c0740050182c00c1a0101d940d0340f01a690342c98028040d00d00981110b80040560b000040c5540d00b040e41540034bd00161424030891540c01040c000301c03602c03445a04e001071100804110154003400c403c1c8a02c00b400315010f4500c0000b07030042451b1001c10a944c441ca94410020800214a0703911165080780050304071650080c900b0682c01d64442d40340054002c00245540c4003c802c0e0b00a0303000602c0c0c1800081c0034460b40ea0307940c81d0300d505c41500019413400780e4140038680021f01407044900707060300d6101240c061805030024485452150040500115080d4240303803401060038540514001c02d02507009003000031892078000010040030b00000e01079 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 405714289 1250 405713039 405713093
    0x1e070501030c05030f01090e1f050703050705030610030c1202040803030a1508060c0f121f05101b0323071704240e04090c030b1e150a030b13 62
    0xc3c1d4030711a1701c58111070401501040012003002000c3c2844402040c44010352803164110b010f10110b5000580300c1c00302510100016618014240c0d0f0a02c0222001c645c000e10780c0c4040c204141c000d07130003a003a1041a1503c455005500200c00040f030340503800c950300c170ba4800f108104128120703000d00f103a080c016031308403810103140c202c2041d620a005040e14034020b802040411074010303000b040c0c82100300310090150320750502c071100a01e0030f084103d04041000000c0004501c90801c80e02860a81c422903803881c401c56000aa446102000031400702c0802c500481c084000c0450700b850b42c0c0c911701d501055103a60b0f03892481c00f03034800d031250b03000420f81d030320284810000030003180709150a4a007506a20481c42c100508101c030307407030180640c0580c86458003c5130401d101200301e43c0002c3d01e10401c000c1d1825101e414081164411180303038020b8000302000012010542c68006184141010b440600d1954680d502d1508031802100d04c0001102100c960005004004180d2411201400c002c1044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 405715539 1250 405714289 405714301
    0x403150e010207121115040f060b010509010215180321070e010e040c03140a0204230a030f0501091203050610110c0402070f050a030c0c0905090304030f051e070501030c0503 76
    0xd25190055010300101084000390117206210050f1200140c20046010b0300d042c0c034090f248140901c0040c0d0303215291600002c00d075402402290000c6205030000d1144a94001110016100003050b03048810751580821003642d800b040501103042440794500b003514100351101e007100100800507010848000d90400407642c00100e45450b02200365000310390790003403280036005800c0400e00085031401e2a410800da0230107560140c4192911544072500e0031203160743d40081910791008140d848402000c08000154080f1481c4292503c1000003140b41515607c500440c001c00f6000d08000ca40c99600b0050980340c40803000905c0085400c265410392900381d4201c0d03070f504c07001455a000c3d1341e0004120060051a104010000f5801001c4510780c070078514000301000104041110400b08511011950f5072542c0101480341a194000318106840c503100d07441415011030007a01c0e81c0c02401c2404511483d00042c0b60300c0c9048000082503001c1c81c00e4001401c440300c03502c2403000c000007401071041e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 405716789 1250 405715539 405715553
    0x10516020613031b0f060c0e0d0507051c0b0103050106052e05030717090c1804080703030507030204030b0906101a0711270a1808070213060b0403150e010207 69
    0x10241e00b510b031082c1d0740710100c1000c1e0308040c6042c1021785110340d03188190041040c0340d0070800c05034069640321001011a1002c2c44203001c5000402801600300d43c205000e18200111107078529070207910591113000d46901c070042088403c1e00261143e9464142c05d00660522120300d200000d0051181d041102032222040c00044200c034404041000010204400034420400c40d966491050100d10407820116140c5e992039081c00120303400394040100361502d8405098180f4800c1c0d40000c0034614240782d5940c11002804020009000e1642c01e00c80400070641c1064a00d03c110350010050101d030400c080c0c001d40002c0e20b035004c640c46030721141c140c441102907802501e410b83c2d482005d80354070150b044c002030520207001d154582141400a8210440c0c0b0050016600951104400300100100c15800600e080700900015004500801010740107060602442c800102921400a2440d0700c0e5503071403040b03a221b80d10642d032081004281c0b500e00041403080d00e4041d1491230086140480e6661110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 405718039 1250 405716789 405716821
    0x1002030307140c160e0604020f0a030c031407030207110603070e060904020d020c030a0f050403030f080406090506010803090108060301090c05060a090503010c050d0f092a170105160206 81
    0x1c1c00b0800c1800052500d01480419584045050b00a07180c03c0d0102841000604940d8461411440528804950b03107003014421500030903e41c0d080030b40b0701501c1400560203800800103050815640c0d810b5070a007031000340b6010303020b5041070354003513612112410320501002d400710300d00388919001c0003400711035038000c500030441c00419503043da115034010000500a000b14030500102da0300010701255880320100c02449405080d480705d40c001c1414840c00c81e010300450000030041940309550030317200c5001d0b41da2075a106110b540045000b003110b5503440d003002e00aa00c003010725403020031103400540e0440000d5900c40310550080022180c00d484c1c028000b51071340b0840d4050b1070005801c480c41c0d489080480080e000c050300030702c20700050301c000030b129078009610010170ba8039000ca110403541c510700650703038140c0c2c05c030031196031505207961030b86945241e0060070078107904000000140a01007078000c5400b04a000000207051500444030425200d24004a00031500000c0402245800c59180b02e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 405719289 1250 405718039 405718051
    0x61d0a050f10030b090702160b12180a060c200309060304030807020703060e030418150303031d060f0a05010e012d080313090e07080c0d020a0b0417070510020303 71
    0x1000c112070340040a40003001032601c1345402111003000c010486400040d011007110179450039129699890b48039401030b000f6507400301d11181e0410040b920700d804500710300d00c00810943c191004042555901003c50700280d5004012540001807c601e0030a810035006a80c3c0301a4051440d007200c1f80d0024801c4d2100601c024144108140866070b01d030b03c2005800080c591102007080326000c43d203035650b540d0704603105030741203683c0c0b842000002d00e0641c020140a240f030808002c00c02c1f42181d805801601c084184003690741d640c0c1600c11180c03a420003e180c003881305010340c280700781400e40500b03080d210160071130981c522295004100700098030548104044082840b040303004400c00244483c0307030345907110300c90034070001c52403002c070f000104800c50807034064000420203a03c1d5001076507129012803180701c4964000d040c0010441c01d00c0c0c01048802d9100401e201025a121046503041e50802d0304451803000020011480c12a01013002c04050301084a066503100081030000796688002001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 405720539 1250 405719289 405719299
    0x20a0b0c0c0a09140604092306010e0601030204030506071101020f04060c05070909050a031101021b06070207090e0d050d0f02030c0414010306030b060d1110020312150d031b060204061d0a050f 84
    0x8280501c589400c03007078040e5042c65440030041111008d070507902d98081c0504183d64022a0100e2a2507000c0c0c801c5034102c1350711070007418032661003500950f40748010721081482d5540801c0900003d030350700d0008001403c4141c448942c07014403403c00300e00c0e1500319040440d4607450701440a020031800a070320b40c02c80368945422070100413107d44260181c001c1040500910500f60300c3c0002c104004a005032090849508640010340d03154000b500366851041c141c201604442e6141e13030038601c540001d01c16406068400300e00c800c0b803d0403c400f00ea201300c034060398400d40898144403050829000c0c4c108400300f446c0600100d410b54a9403000c260780507160707520030944500098200101d54000710740c81c0000814080c01a816040041e4807a40142c100c0c082d28010a80040c0561140255284904d54050040700761116666000c0d42c0c0ca0b01c1400385c0341d0010303043c04e400ba03001030107078002440030304100c2c1e942403694501400b014401012041d2214031520090000b40595124861003051582c005c4036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 405721789 1250 405720539 405720551
    0xd05071211030105010f0302090f0f070315120f050f010c0914011106040605100b0c030f03040219090912020a0f060b04020906070809011128020a0b0c0c0a09140604 72
    0x585401605000031050b078040d4201400018440c0458100740d00701e0b40280c9107400aa510500404280e00d8215544d4200c840c103100800d0401d84280d00c24011440034285030707119151580c031312b072029152002c0101c480d0125400c4400c20010305008402070103070800700030302c034203403d1020207403020490f8020041f04078218481420140c3c13190f0800c101c00c40415042e1801424603080c002c02408003290711803e5116184400a100c000c1c0004076861310907483e02031810a4082c80c1c2100d070951014209a038062140a60b02c061100002c030301c00020500f050300064690b0051500c0c0e030501c0f40032140c00c4195005055084007040500040024171903003e00c00041410508000900070f0144040068002030041054803c0041000080010b401c00362503100c071112035801c0c0251f0395140342c502c1441841613019405030a0000c0f103650442030744010807410711281c555100b2400d0f038020706465409544585019109428010200005030a80070014041c40101003515130341c801020b0009402140d07a40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 405723039 1250 405721789 405721793
    0x60e12030f0f0709030b0f090c030f12070c05220b01030b0916051605070305070807230103180b242419050403060c0c020a060e0d1401090b060d050712 66
    0x408040c000d07581c041b10414490a0890fa25006143c0c00c4a02d1801740c4140200300c080c5181c00140d80b229526403030010540e213410034128521b20740101000301d4807406003400110320b9503201d8001810040310144450070f44403205510748151420140014141440d00070700840390307190007192961000705034400c48d040c1550b00c1c07000c5035244074a0062588030300300c8012040420001144142c100d9006504440c413590311440215203800309482107003090494074000f000c083c1c01d00136078000d41700014100001c0c038030304038030350180507180c6c40d1802c07070f1208514401c00a502c02000c2e510400001d044200d080b40c42c410300e01090300000c0008042800d03407810448020703000840401c9036090340d92604246028015286c018005070404e0004540711070902c4000d60710181310751151025a0340060020900d9417810400782c55452076210b03456048101032001001041c040000b48410130681d00002803034181900305002c41c008043c15079841500004800c0003c80e1001031890b05a1f4881980104503284038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 405724289 1250 405723039 405723047
    0x20405090705030715020601080f031626041d0708070c0c1503060303080109021602120a0f140705030105091507050d050106031e021306180f03060e12030f0f07 70
    0x303501c0310f03606105681020600780022200b2002d040c0441d022124035980f0f8004082c1c6a0540701c0e05102c00764000d0046490907d1181010000140030ba60016400464440b41c00300000500b0300340c41c105075001804101c9000b5489882031618400460b038820350402c81c50003442144050551801c01031040e40e40000d01c82030030380c540002d01020303800b04121440c00d400036003d0b020310f11050f03001c2502c64000103076120145c000c442d102c0700c0300491540c42c013981c1c0d400c1000c0c00d40012590007080c880d4084030800182c0c5c001c21000024018900c8807154070b801107041d40342038a035400181c041d074140018010b4030746002611030b6001d889401e00500030f0340c42c00c8003111107025886142c0c20850911000203840d6030180c2c00580b14010205020302d0403040820400240d12405008103c08112020304020817071003a0000014000c03090340c901c00c80c0e41d4440340ba1242840076082901c8030390703641d500c254810100b084100d02c07040403008500d046145c1000102d0400704014260144d09020b0800900c42e03c0c81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 405725539 1250 405724289 405724303
    0x1e120402040506060f2a0613120302090301021602040c020304060801090507020f251a070b0603070801150f090605030a030309051501031b0f14010c05010207020a06021b0f0105040302040509 83
    0x7003c0e00454544045505041c80b00c2010700111b507041c4502e070002c2d84100c2d008549540302d07800c216080124440a56901100300c2e400343e05034410140c1c2072081d102541d50030300041c2918039540456203c04010f6004120882d03001034025000d550003000308108440e00710b4001c0381110110480003a9607a03981c6802c0e828030102d280502464007403002c18803290b01c1c0f1000d00c1c200e5072001c000c2410311140c46551b102d1121300101003543ca29801408140b0001d101440c0c895800000a800e80d00304980c3c0d541094251340c900d05400500d1401c0744000c0c468821041c511000030218508248025031410011a4903106100d0000e0308154803140380c2420312100300100c000c1848106850941580d481c20a012800c1e6100c1280c10360050112001411600c5032840c401910408104410f0380c9421700010340d2140c1181030102d4455409004640159842905110050480380c0180200b424070b070b284000340c0325900e074800d807140b811200030681d2031f41c0c4441078034140c0e035068800041640311203038003500d4191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 405726789 1250 405725539 405725557
    0x10050112021c080a050301230906060306150415120204050f0d110a030c051305040b0106030e07030c030b0708220305071b18110304020906010c021201050c1e12040204050606 76
    0x780044d08444642e84200118100c810a805ca14890000c000040c2180d0303103254003090f40600003801083e128602070f40156049200107200c02c481d20070720040c0c1c0300182c209502060300301807000d84030005140c01424108400302c10034011403806080000140180004800710b5009109140e0100100400407032001003440c030090540c4603d070f03520300c2c050001400a008180c081c2c482e2294041400c0c050340640d03070086910a0000700542e0911400718014080c00500006a00c10300b800007020070082c80c80c14000d14080e10f0140c0485ca0501000f808010000c1d02034140b030090031b9000305444031080d06803615280d1501e8040e607034200b1410044400c02040c0307008035218131010b50020f42c00b003e03400700d0101c0a01c054400d002d0046010458080c60200300c9005e500000b82d0400034800e9032207500f280807500c1c802480f00310b9411803180c2c0c10342190340c1150f44411944000031280c4010a0040c61080e48c100a83d10b0f1600d03041040c4001100c0001c060002802184c031031001c101d1682d2040142e134074643c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 405728039 1250 405726789 405726803
    0x3080c1515041b0e040e0106033f020d050f070501290a03020d060f09080d0c2003090906041e0212090d05070305340510050112021c 58
    0x20401c4100d40580c00035201d00c03503104030b142100e02c1040c01c0c0c20582e01105814030f40c94640100030001d0501000c3e00c042d042c1050555a922000b0001a50340004512604070f002d00d5240c6920441403c4801c04418400c0351001d03c809070441da181550004568500749803501e066911880c3c032128000710350140c01c40083c2954206108140c000c140d407d040d050390310321013844200d08e4844070309100e00b0720200d00002e1b42000d2007180281c0030443d1350b00019400c01d0050b80004107003581c0d403900700d0703981c024940c610319460f1200c040d40c01869212030180ea22888407480c1d54060700c00240810380c1c038410945224081c004550004005a40b16802129440e2a0413001ca05010604801c1ca00a500c601840c50103201c880020921030346c80002c01c50082c020030345810307240c05203c0e20103030307007540010a110f02010704a0480c00540d00d028003080e80c1c864002c002410300c0c031440b840c0c01420201824030030781c2003610300b000400080041a51302c03511150107454540c0e007100d00e810f803407488048501000e0188 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 405729289 1250 405728039 405728041
    0x8030c09010c02090c280f210912030f050f0609060a090c050417010c0203030c030c190c030806040c09141302120610020604020a0504020f130315060806090703080c15 73
    0x54607003000030191b402a03194080300e00700c41c4100c00140c0d8810003c60000082c0c4904649410a01403440c2c0c0b480b8000700388a42c07035106a0a1090f105a40310f05004a170450505403104003060340501510b0003000c60700c0c006011516004d01c43c0b03e021403008005601c180480c40102d4a00d46858164802410440009210081c02584050a0360748188a030007421449415002c00c040c3d03040c45100060b01d9154081c41c999200d04d80640340e5908068040d04842204008840050f840158130340500c42d001c0d240c00c084049507007401b91481000824060140b410000012040d560140d81281035a003488000b881c00d903010408116020721204218000b0751002650f21000381c0c8003c100c43c400c040413503480081c2042c0c0340c001c9840700030030740e0000d4121075034242c240520301e450b80203401400602202c1e241800725440c0c503c0454038182d80f007500d00001c2416248100308150182401500c0d4420062840b828900406540c9600c2407201512803480864819900c1c01e00340302c2040c000176205045455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 405730539 1250 405729289 405729301
    0x9081204020120030c1e030409020901090b04030b1e04050d110a0f0609170a0203190e030105160908031c0e010b1f0306090b01020a120e03070b040f090908030c09010c0209 75
    0x645e51180c2001801c611807000180c58148000c40220754103290386001d1801d181c9002100c1010b500115843c50502010010205100d520400540003e602400006055080c0001550000903840503400c1c0c0c83c064440c200408698009900c1d0140181450f02110a0001050180c144080703030314020701d20a180641d810a01180e07810044602d80500c460130401c40d101031002d80207108100840b4050303001445484800d0046841c2c103141c0c20001c0c104220340840351000070b802c440040340d0540401512010032a40d89600414100145c8040c500840c41c00403960100340000c143e50040c040034036205c001227405004e003900541403c0384050850b00008800c0e8480100401040860000103071400500007058102d42c00790300b140f840107030041c000680407600c8803a40c00e00d41408041c24009000004013071500c04003d8100240074604035540c4803030134440c09050203100381c0c1c40340c4000303414000c0709408500d80c4003c4a0b0041e10440d0f03455035030741410b00103840740f1401007006980f000f403180401207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 405731789 1250 405730539 405730543
    0x20d060b0c010b101d01020a0204060b030f060a1404051b07030f0201050702061e0402011815180b0f0d090816050f0d0210150902070807020a0909081204020120 70
    0x1d81940034028480154404103104900c1110600c41e40003800350040c6010b55000701c0208a902e0340c0610644680c3c0465070085000d80c2c1c050303030040d0600b00e000000c1040d0901000303042c542000303003111040215840e181d01d80440f10140741075103100341e42d2140407448607039864080e41888140d0585507901c6150f02d00300540020354a50011002d0350804c1c5c005400b55101050030381c440c1483d01006068020045d40360342c50400000c0049042c0106401c041d02403451102d0007c0040c10404d40640d54040701c0b142c02070101e6460b1004400805040f030050181c0802442510000380c01c41c0c59040c3c462169190040140c00d8014000d04884800583d02c40c012034902402400c1d03601071421503e0124a11801c5a84c802070203c80c00d0040c0c03c05011420140d0440e00407200008064032341c0000d9640707039440207040340c0c096541180d1080c0c2c0010107a0460030050980401801404000c22200c0c0076611828003521600040c280c64116030800141160f0041c1c5040c441d100741d81718284c15206440c49100c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 405733039 1250 405731789 405731797
    0x70503100c231c1401032003060a0507180e0106080c0403060903030f06050306060a06080702152502031903020a110604031706030c0d02060304390909020d0b040303020d060b 76
    0x20b240f10f503000910600809090041d092410340030306924000780c0c615103410071003085268058503580c0e20526181c00d969010452580182024640000c8509043c20b000d046244480315105e209031f1010b100b0003412821084541c112081414540b0b4290b6940d080b003511446180c100411071450900707488103065059200d41c21060345070008000858896007010381d191780441d205540514407400a016040c4a0201d03d50810054012100f00c08a0140d4000a2100c11142c000054400002001d0340755000004c20321700a1303490000c1c618103614940344580c68103c4440510a042d00001d10344052803284010011b5000c403401982d843e801d040c54000c0240041c80700498040380303040e000c82c51501d004180809252401404040346025030f03420b0041ca60002007050303c5640d1026061041c2201400702c80b104400c1851200044c05881c4221b0100d84415030041d046151034000f20070010388035082d80700c46442c0c01c030042002da90350301c1c5402c501034881c1040b080601401e2a4002601c1507282c0064 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 405734289 1250 405733039 405733057
    0x2a07030624030f12030204050303070f05160806150607060f050603100b01050a180503010516091508060d140f030904140717130506101403070503100c23 67
    0xa0250060000500690301c07a0780405084944403c90803c00034a801d8180f054840180c100982411740e1080024210b4004950503142c00e507003902024100030b414030503483d90074031058110308102e0422241c1642e07020300a00107901f140300c017001a45203566040035229840c1d4007107802d0051030380040c80040a08400c7c0d030203502074420032840c0f04507c2c0181c001c10f84045d806035078150401016460880b4030203002502c520a9400d200e1021501d602c0a01499108000c00000000442d0030020010f16000b900c2d0300642c3c008606100b1140030b41d600114441d000081101e4400000702c2c41d080259001c09080c14112140c41003480b202001d01010000c0c104059003102c0c2003183e1004d44100c20f401c1c8504031440000140340101c0c41ca00003110340001900322824142030810040319540b41880c11100390b5040e0341c1081054810001134880034441803070044181c020f01680c2c0c2c500400700360740c0c200c002c1c0c611100c1501ca03005400c8440c440c401078407082c2400c1000a568039402d5062004c1944203c900d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 405735539 1250 405734289 405734321
    0x30c050c010c2004061701060e0c0703092c04030206010602012703030e0a0f08030109060b0a020a0201081503060a05070e010908070b0f0d05040b0106080a0902062a070306 75
    0x254503000d41c060a8048062604540d0b850310f00030380180c01c1c0c00342c01c605403a6140c1c00360b641d43e008101c1c0340303072800c9203240f03180c040000203503203400c00ea00d0000340c00c070040504c618600d01308110030004c1d501443e000704442c0746069029001d2140030940940c5071800c07184183c198182c40420051642c0041c0c0c40b8100d0300b043e0020058416109103882c812040401507003011680320402400187c400ea100c40400520942501c1980c4519603072a510140c3c001c1050f110044003000502401c495442941c0c018040b00302c0340361900c1c225101c0651158107603c4080d05010b0300800180c110000c00c139411351381103401020780c0c4c1c41c2c1c582410134070700410058861600151319144c0302c0c606c550180c450b800070365400e000207042842c81c05041408a9100f1001e11301415018003070b407008049103000b006c0c046c600c919509000d03581005001811800000c00c008256801c0c541003102503280c80302105d4000c0881018030b0400200903d100300254010701d04e8200030300c100c1c8000002d00c04298803003040001c1102d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 405736789 1250 405735539 405735553
    0x190209060a031709030f10090201301a060a0203030a0e06010b03040609080f030c0c15010f050609040b03160303021b090f06280501020606040e06040b0c0c0109030c05 73
    0xc1c48400345080c04010300e052400f1034081051000d40002d4240700d4070007002c42d607404900000980c04c2211050803045881d4442091804647c0c0010510300d0481034642d4140061126203c400b149080410450340369990b030b07004c00c450b29186c1118818840c44040e02040c1d40d8546100d000b940c07a801112a91401407800310500e403070300c5c4003042140c1200c103400d12060131a201c1da19403400400003500c04480b0b0b0901044800007c81c0700c0400740d44220404041c09446601e00f4000c90b0a00b8031951000e09059070240c0140002407070088002d080e180d007aa03840ba111882c2e48081401080300b41c0c2c0c06981445100714403126a44078418950949100383c0c2903d02000d00742c40c0c0e5a500044c903d003500d07404000a00019405c0b8280d00d15603a000a00074000c40601d0748041c002202c0391481d48510b900c4c00d031124406d006558041101541020701918204203a1f1841c407485030302c40310702034401081010500046044c00007a01d041c0c2d00308001e41f90082016089924024103880d80405048a43c3e003d500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 405738039 1250 405736789 405736801
    0x9060604060503040318080d09031a0f070f0201111305030706030504050c33270a140a0b0c0a0b010b0a08151801090b03120f0a120e190209 61
    0x1100392030469915440711800d60719070366015940b40c082880a5403c0a040b4940054608020054060014090b031600c0c980b10b800c42c10300b00d003098058128407070030015810601100e10300c6035815540c02211803030105c0031802500c008a015010120810f84682c0010440c07400c8030640c240c0e00421035904034101e81901c1c0d901c407819801d0380c5040303030094480d801c400010045030501c0041101185014111035000720106600300c142140b016807420110b10021406901036840c6440508814a24000b803085450745080010401007003801804104c030510903041d405901d83d056224080d110540509480c0c60f00000019600e0300701200540720500c114000003130781c001d51412120000b5055444440c00d40d83c480e02c040c0c1023090800d20350303003144036031100105150318000c0403806030036070b0000132a41107007103010540342c01c0c0e994400f600340719410001381c03080040340c4c0b0844620790740e035051140c589802801014018a0317818040742c60b50055070030084100b000c0c0300018107098400c070b40302d000f00c0c1c07246 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 405739289 1250 405738039 405738049
    0x31203181509030906030a020f1204030221040902130509010303030b0f0a06120e19030306091b080f0a0207060e0c04050714090f1f020f0c06130603050915010b090906 73
    0xb61400003080d007007088408001d00301a4002e541c0b01e01420409464031070380c1c0202425a504c040a00300c141802441404101a4180a0f008416034240b40102205940c1c20415441d44240d104090101e0360024405040d207d034424440c1c0200b200038811020303982d5908000c0c020301202200d1300e10800e0540c1c4210303050300e00030190304d003a01c1c160707600d880c131640e004580a0001d02a140e1101c1442c4215250810b030f604808200d204a81d101b690003040b0a450800030300251056902ca01d805000b04100c0c07140c5881e8000c19560b03200782c880d81d0781c659a8444880000092041000160005007401c0d642800d40c2d0b000200284132610a50702000640c1e40c8810441c5c1818074515600c10143c8100f1001086103007a000c0d544031013600070060100c28901d580540c5d0301e40d218001d26005a04804204d44590909203e080305403e4181d40c101c1c500031510b889401201c40d0350081d00141a40c03034000c41c01180c010003524005840c0000b142115507141d91190344036030800741040c0c1c8102d2010780050303000d00300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 405740539 1250 405739289 405739291
    0x40c050a081e2b11070605120603030711010c030c02130515010c15090303020d0509070f17030703030e1504060203090c030a17091203070c090509030c0a110312031815 73
    0x4020b0180310350f40c0b008a6481c612001480003080224840701d04c50f5011041c002680208510f4503800d41c0c940d0030f042d031801d51034401400703203109130018000e040108003030104080b5441c01c240b034450340940303da1409460100c030340e01020303400045561042c280117440d50302c00d5002d4100c001e00c41603032518001c011107103100302010085c561540c40c504000110500e41103801028441d04002d810119010300c0001254012074280181c0d5019020401962548400c0a8040c00800506c40941e02a000b03081d6941c3c03064000050030540d503200c12480103102849a44074132109021030f44400e003801e081c06800b940003500c4001c10380c0200011000a4036000070451b51103640044c3c40840300f50800c0d121556030300201d04094001002d0320040004030310034001404540c1c400c02c2114510340c00d11400d9401c80d4001443e00407182c0c4200308921082000013104241c155100390096041030b00b03400424102410007810200c10900801031042e40d542d44150b0711641d00941c4111412150028110007203080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 405741789 1250 405740539 405740563
    0x6140a0c0e01050d1413020909190b0a090f050105010303112a0411120a06050d02060d110d0f05061002030304030503011701181109101d040c050a081e 66
    0x8140c1d8112591940904058910058001d000141e25512042201da002d40b040f80c440d085441400b0100e021850010070554100c02c1000c0100b0610445c0041e5454211904201811503030000e4001002d10410f034015201d41c50f03000c14503400c42045440d046020708400c1c0012004200c10f5140120000400121000c3c0c0c0c045801d0401ca440615000c041c91241c0c64840340c907042038903000c4c00c507401d44440340182404110318400048a02c3c200307034842c00326075050b04103a2140041d89401c401581c2c0d490161b82070034135644400145a6131a1081d800d40c1e10451402c14546070410040c030310021420f5020300d125600c296182202c6028152080b40c4034881102c00401280080c001031003030032107010b25107140151000002505015000c0d1043c808440b142e01240c055914007084c03110750030f0211655810120f10101341d1507850900c4440600d1041d4403900c42096500c180000e41442a0620000001c0030302030a5103100ca80c482000c5a00e03404040301050464078500500b211041000403c0c000180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 405743039 1250 405741789 405741797
    0xf070f05060106050f16051e0d110313050910180608071202100c0311062401090608010b0715020c010b0909060f011a0705150603011409060f040218010306140a0c 71
    0x1c083d540c1d50303080346c198000c025541c6120b401003200000091481c034001c0049900001c00c40181c81110041ca81503c480310304506d40c205202c410f40d45450b24220f4001d440040b280e5445550b01c42c6001e02400c10980c2c081003c0c0490301040e5486c9048035441402603941f03e800380c454082d01c0c0d03079403207240604211009403c91070440c9066900d611500785501c81501c40e261200c0c0c02414200700a15000c82681d07001c10300343c5440041071040010708030740c0c40342c03210a0907c4400344d4078007171001c5c10340a014884c094541600080d04802c11501c007050704100e4150079011500d0345010542180240300b250410341c0a250500c010a041ca500010000c1c41103495828102c160703800c25580d0b420480c859018040f0342007080c0000720004070240200c88504c400302c44100140c0c6461000c042c255628113203580c86e00e0001d04280441001c02007851940101303451110501510360384045201c05902d0050322800340d000c0000071003080115002141d1151051807030360704e00e45a280059040b21815a0300c1c00c041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 405744289 1250 405743039 405743047
    0x1902070e0606030c0f030907060f2102030702010603020301020408060709050a0e040201030209060d02190e0a03051c0c0206040b1c06082a030f0a021002011803030b04020f070f05060106050f 83
    0x203403500c00011613000d5454004c150520014403074402d160380040d1138101d51600518010300009911145143d840030282c41c2010b00130320415a20b080c580c051800030020141c00100054006000b500314600466018008655803999600d03a01d440e24419102c0c000003601503a400102d51500110180544600407a12095074460f5801500254006e0a4554200005001d0460485103d1002d4041d0180103841c0b41c0d00c15005520081c0307460040c8150030700c107081d03203902032010400000b8003034030768051050004007011003030400740c88000161500941c0310138001008205c111065016004c00902c0841040350f0503d070071000c00944106000300f140c0c0b50320446411714504071001c02841800080440d80300c140302d204012a007000c28401c00c810650f402000f0840441c14a40c0440d62150140c0c402000070800e4444d00340544480a803001d81050380311485101c841d03583e98119414080208045d0399101c042c1d2401c180c4680c0114015140750240d01c00002e40d590084044130203203028171811a01d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 405745539 1250 405744289 405744301
    0x140909030412020a03060609090203011d0304090e0709050103080c060a0b06030f070c1e0201120603230f010c08010510080402010813050c0306010b09030613030e0d051603081902070e 80
    0x1c2d80d184203070203a910407030700755001000c640c1a04c903031400b50441d400042600c81c1103005050070f40d40045551981d200c545694080c6c0c0d2038011096505403440d0034008600d1285440c9003a24048680c0c00042c00300b8a4500000104a800001801c2c6080c0d0301c000c2d40d01070742c0c890440c0360444412a000a80001040002500c100102e010136548102c181c01c058524142a442e2512404900e0107180d4114248500e034800350b60700802c1c03281c60740402c6101841203a04590310f50391a407144c84481e44409060140c0b2400c9102c0600c0858224a1204020010b07405083c0009007440f07420b11a55024078040b540244c3c0c6584980b01180c452501a181c40c00240c440309111720610012030b1080e200ca005034103650f042554140310040c020503019008984548500042508150707018140e00307010794a51003c48002a0809074005030007204888a403a110340b682805070a008503034101c2060364a0003503002c0200102103016104041541e03503054840300901400b40d0b43e940d118040c40c01000c041e900081d030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 405746789 1250 405745539 405745559
    0x6010b030601120e0c0310020c10020a05070503030f061203130506030a060b071209050604060e0603070504050306070c03080c1c0b15040b070204140606180118030303061409090304 79
    0x60401010703d0038a00680c101e03008041220304100e10006507030088903042c002840e0801a505519101c80d8046290400103400c0342d0341c1d440340780540c0002c29004074031845101d00075815a0052074000f42525540d180c0640c0c0c9090141e41224000c0c0702e0b05c42c25548124081c00003080e50b603000d54440010b200c0c20301b4101042410741009100034020b030f441d2500401d010151201504509208500001c2c41e840035075000b601c0c0c50319942140307000e104103200400c4404e84c0440300c9001c01c0c5095030305d203071b5039195100d04880911441e040380360180700e0300341440b1009906c010030440700382c0070796114052034452034214404c6100c1c00140c0510a010081000224644c503484040650001000002901014118081181c2003580141440003000c550a01036082c58044d503186c00c422800301002038034000c40003a4413030061850040680003150504032403640906180c2064130002c01c05000456540c0c074004010340768501a001107001c90007003d1103941404000d05010304018000b43d401d2031300f0b1003031040e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 405748039 1250 405746789 405746791
    0x20d03110901230a02010b0a0501030c0518210a02011107060207051302072a090207020d060e070b0309012702010c12030209041514030a0b1602010603061503030f0206010806010b03 79
    0x40083c02030810188000707000b14001d00c00c03c1200e03000403c0b1320035110200a542d0311035510250500d420712016804070b50b401000c030303603102009007138086d0a4070b00300e4003107520030b050044513400b04c1c40b410350207040c0302c0c0c800907424181c5e500c05d80c0d40e54208040c000c0000c0e19038241c0c1c410700004d80d0150605100914000704038821244141400504240e42a1180c0b084591740c680003000e0340000411034ac0d6460904900b02c000340100103025031030a40c05a02041070308040300400b410450790b6800c1e21348222003d2001c03500503c03400404544030305041e00c0b000e00824481c1b420392282210300e4265141d000501c80710030380305501610350111600b095101c800c41c516a29801008250342000b0b03200079503907207201e40c0080b5070401c40082201401c04021140c4003072004405031096001149003c0040c099500c103d03400300304400031240303e5640714030990140c5495000204414288844001c10045448031801100e01039514500840c1e45010300742d89a54080c0034019807504281e00500030361206070019 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 405749289 1250 405748039 405748067
    0xd0f1b350a05160c1401180b040e04030216090b0f091302010e1908030415020c13020c0f0106141c0b04060b15070303090b0109231003020909060601020d03110901 71
    0x2034443c044140e03200114036005411800d1140802055030030b180d68005486a14404a40404c010b03580c10091052003074000c5109001502c50f00c8030002d81018400d02010007000c140b17000d02250240c881c400c10004d44040400c00c0d014011801340e02c4024036042c03c0b0745000d0040404800213890f00c80c1c00445a522040005d2138007e031880d000d03100034410989081d40107042d4000910384607420100c1d202c0100440000c80d0085510074480480780f681c66100c0d941107007030300100c016030b83d1f60307414041ca003000c02c0901440d030385529111000541403502110303050251400c90f0036141c4070404124424210300c41d104040c202c25500000180000c00a41c1f041c059228001c100c1410602c000419050581c0240000c6000030f890310703155400c2007040c4c1455400341c40284418401015605400d200440e543c11302c9050244441022501000c409034200024603000b81c0080098031b0031040341551441d003074880351300611440c1d84050034a48a4401d03c1126108404124a050511001150380c41191050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 405750539 1250 405749289 405749317
    0x601090c17090d120c052d030403050c010c0801050f0d020112020a0e0a15140310050603010611060f0c0f0310080703031107140d08070201032406030b090402030d0f1b350a05 76
    0x2d0240187c00d44000b562003584295100ba6540166404803403d4038800090300040c4803032140180030982c3c2d02e414694620718203907814405c4540d5400125901028010104850351000680b0071002e5800441e1001c2c4400507a42107000941d641c00503982d040803480c54100041030031014141c9080290000c641000e17000b0011821140c403000052000e500a0740501c0c04601c189605900290341400072a034403a220f00c86184e10b034584651000014802d1034041c0410300000000202203001d03810185001c1d04c0740c1811600c00c1c0303441e4a405030403502d06080088040c0310300340c4001000102002c03110301400014002c070000300c41c00c5e0348540180c2c009150882c10b05440b0b42c90080401604410340d036640600348401000702d031a081014003200c141c1c14505006007492004c100158034002490042c1003541e20b00500e807180000c1003218055182004801801504503e038000d200c212005a00ba000b0b00d50340702070701c43e0015080d158010026032000d014064042c4603201010380104050a01d02d248281 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 405751789 1250 405750539 405750607
    0x6100507060c03020a17100b09011b05030c100209030a0213090506150f030a081603021c0903060e031903021c02030f0115110601090c17090d120c05 65
    0x29650301a910101040c1d400070340d0210354100c038258000c003401905034440143d0386c01401c1550307045482007414001c5518811002411342e00da6403041552012204240d07a149516007003601d88903880350310440601640f4800c03818941480c00c0300f882214000c500090050003d40b142d41c1c240510f0000c895403d007201c03940d440090300400d200b449141d11070442c401c100c21841041c4405c04c0b0a440b41480c0d041e0003a40180e02c0c3c0c4000809200846176000349640c0e80001e000000e02e0100c0c5480500d5054400014a40d00e203030381c80d0b03a08a518502924400c0105010041d0610016552405103603007104001503080402c0050602a500a280314040300250100071840c0c90702100c10303039009a8548185c0b1800d240100300044100301c000241040b50f250600d90b80000281c419074410f0103000c0c0e5100695242003900380a805040c0c84034604240b117a21618038030701140380e03d407130b40005803918010402d040741340c2525110300d1040040da00c0e0f00e074588230700704800da00710705283d41541ca5100c02c0c10241c4613 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 405753039 1250 405751789 405751793
    0x1b0a0807051020010903020708070f1806120b040c0e04111908011503050c0a0501170606120403120c05040f1e0f0f0f091413050a061a19060806100507 66
    0x601043c242c04400300000c528452a8a4000d00d0305603207500c9000036400c110024804c60070f00c0350942c03007120600082242036100c400d09640080c0050b520603140030b03160402c200100300786414131038400e9010f1007958080316901c42601f8640e442c202c41c01000d01b1a080880e944c2071400c41c24951010700c030701c039a00c3c1c0c0b05030302d03402002c1c03c5071091600301024050300d0070200100f04e0200300004007013805076803440c50300e458038001034130540072168000003600500000441a0320750009032202d040050601c10618105820045d0841e01c01c03490031000c0034103001440c2d03c00c0d03004030229404c4520001d160312540d40780000000d860f141542d00481c1e00402e000001a1459a05071608007801e4500c80d01c1560794035000c210120558103030b01450000c0c4c1000c110b04a0070072070090040d03210000f003010000211031464607a05090100b40000c00031468500500340c2c1c22010b06d4010006441911554020803041c14044c10001d10791017031000003205040007410718208040001d59007045070034141d003080159 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 405754289 1250 405753039 405753077
    0x1804020c010e2d150105150c0a0f02090901051909020a180c0809010e07121a040b0702070b03040c031115181e0d03050f0c010203091b0a08070510 64
    0x402d120543c00c031005100d10410036019800c0e4003903948100c001c01c60341c0c0d00c0b0500006110b005102c0e4501c0b60442d204c2a29001c40084100c0b10310b6000007007600e200e112249000e0000500d194000e03030082c42c6500000c2c0003800140301d154001d07818103d010145003032014050024068a04040381c100e80119800034034040c0ca50890b001140a510010846a801600017002402c004240d100359a04200582080704004111401510a560241c0c41510b0705401c00790030a50740d1030300340c0524003d03240420042c44402c501c04c84c010032031030307003034074070990390f600c000c001c140819a40070345000c06190041000901020640c01122805030010f1003146105c0a012543d03002600c102070101149500100302d803414680100382030700602546081100c40b200030942d0040e00c024002c05222001400f03603071842141d8184c0700446071020003550b59107080c000340344d29005164018507580e615022546d41703c2c9813100c000c00546203142c00501410340b40c03030100308603440c1404080c0c042c0400308140e82040804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 405755395 1106 405754289 405754303
    0x60906010f14130e100503060a0b150a02070b0705010203150d05060415020d060807360c120905150f09030a0e3606061804020c010e 58
    0x2145816481c000c050341c000d030b0240703148181040008041101d1480940f001039048d240940c903110715031010341b81651449540403206402188462036450050a0800344d1881103d40c55561400c0303454056100240a581c80e035000010001000c4403140d0510800b001500c070110003070703d69202c154036900040d000a01c0f05c0201d40d85c80d2200f101c40d0301500d45500c1014001c120312681c0741606c644d40c50191252068610b0340489442405003585450600a52061001040720a40d50200e1000300034071388450b010300610071410002e0351a079114040c0d00502c140c00620329000302c83c0002e14040310080049182c92460b4040100036880030040c0e407034118075030420001290001002651094502c451203404407055800900e59100030419030702c001682c05c00030300031516048140002c0d0b01c1000b40a411007841c0c40c0303840d41d55040030350007407030080d840300c0002a80345803a030521820840 = true := by decide +kernel

theorem cover : BRFrame.Cov 405575539 405755395 := by
  have h0 := BRFrame.cov_init 405575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 405575539 ≤ n) (h2 : n < 405755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
