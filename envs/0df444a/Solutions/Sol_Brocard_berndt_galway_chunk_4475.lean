-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4475
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:44:07.941778+00:00
-- url     : https://prove2.me/submissions/25772c3a-4e8b-4b12-9e58-ea46090c805b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 804676258 ≤ n < 804856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 804677508 1250 804676258 804676267
    0x30f130206040e042406090f02090609190320120d0e0f03071d04021509060a0c02040e0106150f0206012919030b01080c1201031403040302090c0406090b040b 69
    0x24103220102d00038200f5900e2102021740c20038002d40207441850031050310000030505903d020040020f130381509180d040f0007030041c0701555a94464800303031030030482e00302c4060304150541c500d00d100c00714940e040603021180188411401000030407079014409001d854155002180220a81d2620002d0340c1070800038620507040c28142c50140c0103402e43e82c1000301070b1880030303584072007085844c1202c039904001c814051003048194a070261a401140e005500c1207460701002c60005001c0b485200b1210f000e0011400d8104159182d9031302011401401d04000c011054444140803180c18482c2c65410018030841c8012403103900c0800c040713048900c28503004030036100e00d000c10071060303a5000762000f0700007052040c4076540410043c1c0c03d100c00340c02d440c001020400c100005100c00402000070411b1407080020f504181c2c68160054112a00100280014045e42c454641107200301d900180d445007141c0d082c000c902101000402c11501a40c541000c0c10707584006007800750045107e51a5002010321 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 804678758 1250 804677508 804677519
    0x105070e1906030b270411010c050c0418141005010518010506092404031b08030304170c0703060f051b070809010e090c0c010e0f03040b090409060e03030f13020604 72
    0x10003501c00300320005c0c00d1000d03081960455500100b030501003610703030880000c188000d03c655104030420241e400e1070030068179003042e2500c070340e210030a4030a01d0040d60b0311200500740000005a078800309a003c14640b1120310461311999442c000000c0c1c0424072890003000060380d14103207030408030440c0742a0384880507a103010100500c58001210071030b0040030102c203a0b1035002c8092811905001c2c090711990720f807411420100d01d61900c6001c0b01c0850308055a00344000c0100100760b950055000f07402c416910b030280b00b03121080c0038074200301c2d5017486120804010814aa000a90104280e200800c801e6403541d407410381034589011148001031040107041c0200708070a0007802d800c401030510381000481c00011900c0381c4400c44114510120105548070128001e000d4013020381d1144004240391501094175544a02c10f078802c101b00030400082e424410345030364121940483e0841420801803418800706601d07035104903040c1d0029410703480062911120040f617004120b070003801c0300b8141418503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 804680008 1250 804678758 804678761
    0x307081b0a0506070f060e0d08010b0306040912030f0b0f10080c12041a0a0c0f05071406090a0308240418050a060f141605031012050105070e190603 65
    0x15020306030091030720400440c09440d441c00a080c1544101455401d41d03034242030090444582605030072098204060054403030354000700344c60540318142c00c3d2607507d032074481c001001022104d400078580c80144040c89011501940125a525110b134814001aa460010000090b40450350b660740030001c02c14a0040e1031050069030380c0a80c0e0390125501e0700006c00c4c0e550340555421a000c4030740c120215503182c011207801c0061600480b003036405015694400c400505000824030203d8100040401e031306050140004603220203040c1c1c001a550035060200c4010f07120002041c05034041844803010402c14040e05403107803103090902400ca10015807141c10840602461a1500d40c0400307990802000704801780600013007184540b00004048025520080a90700020601031240745000c08100a030740c400c4860140034403c4d071030110340d00d90792454a01c100c03402542040007105404040380d0700b0002c0540c04640940c041f0b45804000445160400907800c00c10003408501c0681c0c1da07000c20600d8000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 804681258 1250 804680008 804680053
    0x50a0207080a0506060a090b01080a3b0f1c14040e18010e0a050a02101103210a06050d03031109060c010f0c2628050f0105030708 57
    0x154415100416510a1450320342088010250b642c2c0e00600d0610030f2a00d42816802d004200c4c0d01d074203000b224503900001e0500b6400410f0000c0980e192506140f01108548000c210b40c0031a2a540c84154000da2382106002d0560039807100ca84580040040d40d4080010708103140c841001000c0d84821410301c0485000c064065021100c5c0e80500c004105900c1040440b44182044015952410282c01645007901c02011a505e569007244043c00c0100f4000705800c0c100940540310b007000c0b02c8002c0710854001c0310424882c0d1a80c040418800401a0b4141c040040505202d4401c2903130703291010400c0440d081071154980c0810085071190000c0c1c081e0308003458941c02c403158241081c1c0c40c0008640d00343d00c0550a241c0c140d41d40c00b02240018000c0c45400580d100524001841b481104c0800388020b203200c050354498103480300007400055190321110151080c0c044511110005504940003034031098840c48034901c0c00f00004200c0b0b0600140d1242140c00c801c1c0204020110a4540a800c204 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 804682508 1250 804681258 804681277
    0xe04180b1503100c03020d060e221103011805010506011403040f11100c0201031506080c3402030c010c0206180402040803130f0b12010e0703140a050105011202041505 73
    0x114181c0f20000d24251090522500c1645c9001d0b82c1ca80f10000e04908450880c1c100c003031350308981e1090003240c44140800c0041c0700e443e01e0004030344401508000803590030302d5004c160b00d5030030311114414054240c81c2240f40184128022b20158443d10300646261801140503243d00c401400020b01286580d455900e61a0103429031080707080083d00072580030303e400e1801401052a40c00090110b581c1440380d0950703103842160784580d07035080000c0241400e5020348078084400010448010803d128803030555206440d00c60803108a04415207807520080c4c2c020700f80d00c00d0040201c0d1a0300d035401001e51030219075004013041e1030618010400317403001c065201a0f0b9003195080c0400b0442d0308013000145105600c841c1d112030768a00d014800034106a440c1c22a0341e13020400d0200080d0100ba090300c541c19200140c3d00c40455070703200c407000c0300200715559565550a524009201d09240698083c0703060314003ea90311110588801c020701c069120f54450304c0308030f45103030090b402c040340314101034013100c0c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 804683758 1250 804682508 804682513
    0x6120b0c120c1308120409021c02040f1d070804140f03031008300f09091008101a0f1815030705100c030f18060e04180b1503 55
    0xd9051a1401d05810121a4890300b2400001c11032902400000060020041c420061030103102c0c21348003560a010b83e22450f240b04d174020409441807820200141c44e02160604110744950361a02c9132100d0225034466032155916050340790b54030720103c0361000e01ca28000d80f14988161181d0b074031008401f000c071454000c075010711214400031007803d100450040e500c1c40b983e980054104000c8508102d81d10100742841c02c0800c4911407280516100020320b40f8603c115241c8581120303010104621608524070340c4101d08804109401180c401c0d0801550186d000f1540660070006004044070b1030a90401d034041d040b102c404080d031070803444030f11012002401007404100030500c4004882400c0d5a042080719a90041180078182086042c00030441294411400c0f440b0070000740114404410242c10403892a90402050740078060050180094115002080b41d441100038007406401410510490403c41c4a548061900c2e04c0c00c0d40c160341203011402d883c4c41e6040c5500e846400090a1038050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 804685008 1250 804683758 804683767
    0xf0c060b04020c011e1b050c0c061c0b1903020409080c0d0c1407050105040b0a02010912020d0305060409080f03040302240114030106060f0c0606051c1506120b0c 71
    0x1601c0380d00281c0300a003c54400450342c24092010511844001c00741500d12074a041ca480d0f400074986155180d0541c0c0500702595100d910020700d0307061201d02e1007865003082e000125198400d0310364030300c0310b00440d100b10200046031070482000b03a8090380c0c0c2185800e6480d11501071026103810703030003c84414401c41600d850400c15034041418410780c1824040484c600500c40c9040c4081113110820503c80c02001d4890f5a0910002030301501031809903140ca0f13603003c01c241c4e2000d4000d40c0b0114806800c00508a1250600c26009585880c4155520006400c00300400d4031402c143c0607140c449503000c02040d0501601451100c2c0507003005006404500c240d0180f0802c42d40d045110000c01781868140303080c00d40c1404a4404020348441c1120b0086c4c0c500b150801c8001d03480074100d09554114075090010100d03d007422000303807030280c12641d03003d45c0036001c0d080e08015401c0e0b40408584a200c02c010700e9507041d10b0010480c0c8051040c4920462244d00d0130340001d140c0000c565011250f05a5203080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 804686258 1250 804685008 804685031
    0x7090e0a05011a120307080d24030b100b03040512070305041802031e070e042003160201060b0a080105040b010306030b04060504030e030f070b07062d110a0f0c06 71
    0x959420f01c0d02c241c8007001d411010007190a00366004285060340000a5140c045150703584052881038901c2d6031851640c9140c40e85030380708140400300080d1075000d40340c0001922400c1000154100392500e201c1c00c1c5800b44002042145481981e120f183c00101410079204a404090b14980c031044089040050411010454141003400c41c0f5480d92741081c0181c0b649084145138910200005003c050003602408105036154003e000c09403e190a84011840281c020105000e0010034000f40300086800310812440700c0190140003590b046681c009d2040680d40c07a501c1040344200c4c1c0c05c080000700303040d0050105040640101c40d40d00010314000420b40d54a899803000d0040a0f02c0c03c542040d121300c140818954014881c400c184001c074064101e400c2c10702c02140c1c0c0c030303c3c483c03013411034251000c00c807901405016440b011080c41540c3c0e46802d8180b007492855003e044019001c3c02003072a140e5203000700c030719400950300e00320140d403070710340400c6035014050310305070b41c0c5410441d65036031110441c005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 804687508 1250 804686258 804686261
    0x100c0306030c0312172508010e0610020c04020705061006090807170c0604030f0203070b0412140f030328050f0a0f0f06060906030509011a0d0302030c2d0c0307090e0a0501 75
    0x208801e41d110000032486e901140c540c00c00100a152020030042200611000c6503140e00503801032402c071030301000c0c140c104409030b05125409180541c407620120f90788081c0100402c1c0d45116108038040c6401d0203456440540741c0c100140940c042551101c1024010680603000d180311140d201e50490791001e00c0d450001301207074450b8008440480c014180c100841c18200003050103009805410ba091030f04040c1c2c0c4000b00d4146040140241c100e4110603d018402485812001c0000c60140d03643c0c6e01c0e12085000c410390751504810700d80d2440c01d00d40d01c2d50110318402c480c000c010541c1c0a06182c4c0b12148020090110000f090501a03500c0c190135a00032a1031094200802e12516010400740c82d04d00058100e6800601003140c03a4107146a1003003540d1803140d40c1c05410411102c4000c40300d5039050480c99030084608424041c4110b0a5254924544881c8080d01c078a4403003c14a030306050340c0c46a51a40c00c94917a20b03805510444052200c604030b50054807283c9072074012103c4103e4207403202c60 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 804688758 1250 804687508 804687511
    0xc071112031606110d020706050610052502040510050108130c0e071701060e0102010b061602060f0403060609021803240c0d021209010605121203060a0801020705100c0306030c031217 80
    0x403075050f4006900c000700310003270003481e43c011021600016070170154070014120380710b02207440903a0001020707803050000c10308410300ba0f82c54020380108072a150480e0010f45d450341500501e404604444001000c0c0b91805001259240d0310403101c454603441e10500f40b403d034001401400a00c111142c440100d000d0345400d8500030101980c42040c420700a100190840b49207160b040c0c010742042081c0703042c0c4003003401e5a0101c5603054414558943c50044400e010380155040200329a0904e1000900c558840e000342054109801106161071028400c00d5501c40f007040031004408809180b00c5160110410140e45c0449078080c20b0f032030140d07110068012030f4419101090308954010070301100d040240f05000103848252a00a2002d244001e01035561400c00008483c0003030020005404d915491103a40040280c0d100954a440940ca085030300c072182c0604041d00a4a400c016000da58840d0003000c0c201ca070046140d0101c02d0554882802400345046400305000204d014074a9100d83c201019 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 804690008 1250 804688758 804688777
    0x11010e09090c010e0303040509180111041202012a0303051504020703031d07080712080418052509090f140c031902040f1e0801050c07111203160611 65
    0x4280d6110a500003408082c010440d1324040c1c0d005010034030160311000b0b942600801c410307005044403518400c11502504026407a0b040084011070300045504041507500500c62003600d4882d105441c0c0e04261020702c2e02e030703111081020502d44218001c60700a90029800c4846070240ca40d15a480c0303004101640d20003842100066910303003801c1c0d01c2410340c050800703004100c580a0304c141e9241c42d00840c1da0350482d02806900c411844c412402708084841200c0080c2108501000100c03080d00c1c011000301070844540c03540c010420b038852144e09808450340141c0280380c4801a81a040c00a01c80c003c0c03085e03107040c4842941d1a01000c40c03615101000d6031046011500c0c2c15940e20b012004211051614035031019141d00511041c050141e04003070020030380c0d10896519003407012100d444512450355a02c40416540f0701400d004c80300f003a0000600d00c003402080d00004200c0c01c40188002c00688101185403500144072824012802d0701c0c402e400307113002c2c3d20081030050381a8102c018541c01003090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 804691258 1250 804690008 804690013
    0x405130507060c172b090215040923010312050d05250e010f0f0e09090c01020d031401030308070302071b1502030c070b0c0715180501020a0c091e050406020a0201051308040311010e0909 81
    0x2009182b00f40e000740860740070a14040354864158603000c181d01d40701800700030300140100c8050240c8502c00c04c2520807101d010b4005200b903041040010424400702030b4402014844142c5005a55016103880141c000042c0e6036009002d00b5090100c402d5041210000c042103281e512141c1c483ea294240d6900400170400038182d11501c120019161290b81c03030f00d1100b41424140c551107401521700c40681101d4260424184503500c010044000380704a84e00103081142c502074110302e03140030303480d05425550800500311418400364002d07a40c1e40611440711a15500c103100a1000b90000005861074002c42000c40c4c40a648a460518150400890384000070711001030702440380c4c64003480c48000304001e002821036407451b511002885a0313240100c1402a88034480b0020403c100d01170003008070580c0d403003003040b801d05290400180d4412000700700158208008aa440c0f1008441c81000c603600070040e0340741a2450392903142c542003411000d8148112142190300c55140c1d164010711980ba204007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 804692508 1250 804691258 804691267
    0x402032530031218050c09100f031518060b0a0b13090b0402120a02030604050f15191a07170a020a0f020d0609030e0a0b03150405130507060c172b090215 67
    0x81c4041f240000300180c940400401c4c04216554640e0f0380c2900343c03500f041e00070b03444000e40003030700000e0421100a582c0d4446140d0b07800d0b0034405581e0240729000000c81399080340d2540e0784d601c0b10b09406001120790001555000401904040f03520a4041c02c0003d040503060003020a01600960f40840301007012640020400c145850144191a44600100c88400160500807814040002c00c41642400742030904a4041c541410b01c41240040c051405000c0c0c500b5034100c4003000640200304201d89904c5101e0740c0e0240c0001107415543ca045165006180703044864980e400314058103841a030300000e42c401100045140c0340140400580280c4506541c5403101b4240017580965501441003d24117105120002859158644140c0d6049a010031661a200060b00300f1002c4084001e01c1071080c00d20000340c1c240c01c4206080900e002d04054044580c200c4c8281019224183c121403080401103002d03c400106809041e982d46240d00c0001840d124990104541d008211710103030100e00c0124 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 804693758 1250 804692508 804692533
    0x91e12121501020d0c03031a0406090b011e0f08070309050102030c04081006030305090f120a12110a1505041a040606080d0c02090a05040203253003121805 68
    0x41c0c0c070002004203100800030180740040041c2241854036000b010582c8030544404015582807200c84114001003040240030356490032003004000550610340404c00300709821901403400c3c501c880d05494241c54038450b100c60320408445240f00100310310203250380c9945500c04154240301075449a08940c2e6219a140d08001500e80340404503212080f0050130900240002383e400003d440206809562511240310450009001145080e91001d00c034441c413030082003400300151140651801c29200c0c01d1602c01241021519103103400000740c41111940d14100c0c006003560321640c1d01500582c1140750304d155030300c0d03c0807100303d0070341e0161072a03a119507090040c00000e00000320000328508013940b070100203074082241240001c1031390802669560002c2c0c00e540b070034409290341d1103c00341004111005400c0380800c1360b042c2d0099200703984a4159500c0700d0001c100c2d9a800e00e0805070b4280b0f245825598003207607024032105100814a88a030146100c6010720141100a82c0c4900d02400d400502003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 804695008 1250 804693758 804693781
    0x5030d05070924171b03040c0614030705090d230f06180601051002010b030307080d050f060d021002070807030804090c02030418020304021503040f05060a05091e1212 73
    0x20540220348100d141c0c44220507138000c0d040c400e01c084c0b0000c04410540e50440080020800102d08184240000040000704006480c140045d2502a1107170052040340840c00030036404201c035002c0100d0700410010800385005d004069000b88140c1e01801c0075403c25020b1080e68a036046031415550182071034181d506020300c86158000407500c80740c0c620031161701030706648001c1807250303600a400014000031118400e4008100185018003140d940e003406181401103544008112620989420046455054501001401014000c010f170901d445903400308403000324000100e03000d40c490540b00082071901401048003c1d030150300710585803880d000410007a507070302048200031034108010901481201c01d00401103503040110060303c1e6500ea2001c038000c00c421061501401001104100170403064800340640c19206a055900c5912505154425104240d40038905038001d2244008040368010682120240000480c0c0490040340c580440c50380c09104901e0302c1e901598200045031380b45 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 804696258 1250 804695008 804695039
    0x1c172a19020f0102160b0901111b0f070506090f041d010213050418032105040c15030b0604050f0103060b0304050105070f0f0203030411041b021018050c01050705030d050709 76
    0x1240004d602d4100308070010505941c651800512000c00007002c03804010095104000d032001c0e500240741c1e29602a0289018000c3da8000d02020784111490881a20000720310a412914003400190901e03281d5400c00801c0c51304c99100c1500580d8514a9814030605a04c80d0212901b94800040e9600300c000261800c10400d80c010324003490816003040001c051403d140300210b0740500d000d00030304011100311a40301c40c0680004000c40e00307080521050010000380841147c01c4940030841e1941d400c1819800d503506500340c16449035043c0010040ca09115440c00c040c080140340008500f9103403207000c049500b096a06582d40d0395114204500e850700100411901002801c4c200504164040000e58900c00100001c18030100000300341c4490704c440d048440c80d5000303c40050b200c40c0792402c0096a0f81125490004110705240780b480c545050607861030034142d002000380c45451600001035070142d0040004948030310081001212003c05441400c1c09012903984420009240590b1003051660 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 804697508 1250 804696258 804696283
    0x907080a0e0a081603050d0614040501090b0120010209030123010803160809010c080307081b07080904090c120c1d0708060906130c021c172a1902 64
    0xa8040c000214900c03a054443c818000c61146503500c0d61340c0303400c451a000301d0f068500700030304040c3c000c01d100d148540c8000c18050300b03880400c070f10380e61079404c601030714009036031540840d00e10300c0d03080f59a400c603501c2240044c00c0ca0002500c1c00c04854003203421594003880f521000440b812640046090381c008040c0100007003802582410900c0404d603140c00d901c034030000c00300c2c00001010052030f400780c040340e505550060400364032868000740241c03c00303070221007001e0294142a030b00c1001c3c20f00007095a40440d000714002e41828118810b000c020224420300303640c0511002c4c0009032190612200142031441203d4450310507107002000703d086010024005219500c3c002046411a0f0180700564401c000b01c81006807501c401c000300710300b00079001089a80305c2c10004928002030f0000751100c1400340441001c0343c002c0000000b16055010b488900360b1038010304002c620302000e01101d060000c50f1040c2c0c01c2c0003016604c980c0c003809510a031000606440000c400203075080d010b20400d4805034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 804698758 1250 804697508 804697513
    0x281a070c0b0906040608091e0d0905090114040207110619030501060504030f0816060f060e01050d0503122d07020118080412030e040204380d0b0f0907080a0e 69
    0x5000340c0010f807003400340b40035400030032401d035002900b200010842192044500c44140800e90b111002164a8414540d4582c011030300a00380000c030b5051030303006d09040320b4002907801040d48030300b010840039500803142520340c002007070120245540e9650042403030009035075042c074282d5101d040141c03e58005900c1001800000d01c02000420300d0350b040d0381400d039400f13010a5500e1107483c4100c95032142a00c2c001c0d0503030b4039004c4441c01003449940202c081d1080340c00b10460301c0ea41c030010000304400245008009400c00d00103080d482c122903010603002441c007042c11030141170009150481c007001ca50710000c2e4520b02000d0120541d0284600c0340c00000b0b003040e2242148464649041612552140b40c00700304904c00402e090510520070b25240d420010400d66465a46003102c02c83d180c44901c0288400d030201c0c070264242c4242d01c1118407023039075107030301c05c2c4c100740181e0301d200c1c010105401440c0d0010b070702c1c907400c5c40e0a85d10200b1082c4280d4560302c94011f00c1c20462603044c1140c0701c0080e905400e9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 804700008 1250 804698758 804698767
    0x60f15030b10050d0906110d06082d0a1205070c050301051311010302040509011206110324060c0a03020715050406050711040e030c0f0d0e281a070c0b 66
    0x1502d0300301d46200700b070410341042da69500c010045036006180440019158074902411020303c040c0d124024000d055980806014060b00c40782402d89554188520600c40d11048180120f0014402080c04140840501303461070002035881d0740343c80c001d40d00c0741c85002460000300c003000c0061090604019000682c020840392800b01d504006e01c218002000d030101110307030307007014090b80f0a40458015181c042c00f4a0840d581da0f00313408e190503401070801c483c40d41c10f0940d030b41e00d41c5418038180d034401c4240003880035481c10a0482d40c000c00481143c0c003071308480100302002e044082006000543d03031080c0d009044951800803442c2042c80420304180c1000010081049074613030010035640305980040c075044500d05403a0020b401000104200d0066000105144a1600020030f0b41703804100e000055a440c6030301480221200c16503403c800d40d00500c03444410314500c5181525901400a1280140300143c076000000103401c1404501c0c01c04000010b000c0c0100030161100c40c0042030f6143d40e15040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 804701258 1250 804700008 804700031
    0xc25050d0f02031c0b0a08010e0706080c1e09090708040c0b0903150907271505090a0b0d0606151101020304210203090d030e2e050702060d060f1503 65
    0x2644140944411441034000b84d1804051059000701d411120050050190303641d00c11009010b0081808020940d000320300c40019981d00441c00c0b144100850310807546402c1014001600b4960107091022200c80c0500c03044001f174031501d81181c0110b0446d00c4507000c030b140c00d180420714000e1a4216000e40c000500010f001c64a00042d0040c0c84801c003074000f401603135103e0149180281135032000c15a008900c500c1c4140c61024403c072805940281024400c2080a552514140205100e9140c1220045001a40440d02d9a02103444c982008001d1150100071ba260b480a45503181c0102042c03055805403000c0303041d00706007039025002220009604514058450b002c8000300f23181c150388034080c0104d030548140c0c8280f08450a6a80040c960206c0b2074440c2001880c21f41c00480301342c0111100c4485410006008801012901810581c1030480740c0e00b80046425070402c1004036000002400020145a03140c0914070282041d4050a601c40f80b8260754044400d952980c41c000741464180e11700c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 804702508 1250 804701258 804701263
    0x3080604051008420108100203040c0e040302150c0c010b150a0e270a0e03070b010302011824170708061c080d0603022103070b0c25050d0f02 62
    0x1c045042d4088220030301490340b012100d40c03541e0a200e000c0080c0d0113404014069503003403c50f0681e460304045801ca9004004003800300d01c02560041c00d2810b491a00300001e6291590040d4407611a1041d80c004110002c2001f03d00d242c1580d07d0034044001148001252401f4401c803212410100d40704d0311901b080d4644601d5600c41d00000700104600d102840c122500c0d9400c081e440301102525a0448203030035400d0700b001200c00d54910704940c0c10880d0000707605100005a809454000003c280075929650042d58805032002852260b40d10070b04001400c11a5068000140b9002c50180c8001d440d403c00010180041058a444000d062000348034030242d1080003d81d200400791a01c1d4000318081459036514504490002c00b52000064158466461a00980b04491080c0c4602c030850100d020462102005c800906607582c0c4240403200c08105541040e5402500b03c651051802c0050480200d0b242c42c40e288002040e107502c04182c0c2000303010030107040012054a49a200000c800c0300c001e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 804703758 1250 804702508 804702523
    0x21201050f0a0e100819241b08010e1b04090507140318070f06021207110414240f06070302010f0515090a0608060402060d061203080604051008 63
    0x5005140e400001c000a40780c407034080000e00b034007624000f45490007215280c1804181e00070b031440c6000d010024140444800903201c0d820b42e00038481d250400100c09450034004682c540360380042c0d03c0340c0c00c460382c1000544ca005694507455a0f105029810708078401c14800c4050103c4003510f801d209800c00b0034664406940a4408001000c500c40d1640101282c07809150701516030f882d48000705100f821082500a110604020342c16a20295940c4040500c40c1185101c0c00f030150704107903028104e044600c0d0061082a2007041d0030200e0140c0b400105040b03420b15071409841100700c03000c0c070420580300012100d420b5000c078450b060700d06048020030000350201c00e0081c061031000c12441c0405000b0740220b80300380902c98003000503142501d01040d200c00811410b41c0140c4521000c03c1180406006c0e4405403000f01740100625140c983c00e010682c2e009100c0e00e04d03d1a42c90401054410407000c842030303071900945d54107a071400c06100b0081218005444c004142c0c907110010421180c0104220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 804705008 1250 804703758 804703769
    0x20103062601050c090a060c03050d02030a020702210d0c081b0c01090902070819030b180121050a350d0b060c0d051804050c030403030509060f0a020a030b0d06140a021201 75
    0x19032340321300c0c0c2c0350964540c001e10f181d244030f0034000702c10008102200e07406019214003c035880250350855528089440181d003a8001302604251703c003601c018003401ca1105d0b8035115480d0a880e00c5c1c0b24ac40003c0214481203004440358100b008082001d607402a4188081e02e2400300031880d08480b581da0720258450741c9a082d180b8494a51aa90214007a502c10303404984040d009100242c40740c0c00e0300c0c0d10040240104240442c01080c00030882c282e505054010301d41c05801020000d03000d489034040e035070707200d20b1941d075202040c07180c054800e82516151071140301903201143c5514507080a04242e691560b821800b9101c01d008a100e40c03100095240100519410031540e1082d036400f4030703403007004e6003c00180c110342010184a500c0c10803c0065100e10700a0b6410859034407006491a01c5020568910101315500800b0855414a650003410008210b0600158074100c034000310329080c9610105541d01541d80e22041030450070085060361101224804601c4c00076440c01000c0800f0040c01407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 804706258 1250 804705008 804705017
    0xf05090706210b060a0e10030209030a0f0f0503070606060e041b2d0c02150307021c050403021e0108010609080327030102030f040c05010302071a04020103062601050c090a06 76
    0x1c2c5a80c0d403500da40b04000081001e00980d68412481c0c1c0e02610700c0381134420380350050503c109825540d51081c07007a9070640c0c40c000c001c1d03d0fa06040c1e4454488484d1600c0c0b080e200c407401049040c001900030401400110302ca408041040c0b40303072520180c4007104c1d40000034016420100b080718503040c010003070a0103201c1810030074006020000102c03101060000001050a0401201c608640d08048050b200e80d100300c1d60b400e6180309802c24184d02e0301003559000d0243c0c1c03080c0f0004403810541c1804409004c554600a4105a80c0741c00140c0f40001d0701318610b121500d21588103100d941c0c41490180900300c4d17410a0490b051520481c1541c921030307002c1d441001c0c440c0c10031811440c0d601d01020f01004800038025900d81c2400c0350108601c5600f070310111039100c3c42c007000040c1035000740240c0e51120740004100e0003404803d06c2940041000804c01c0307040664450700070402000b43c14160610050180f0a10b2442c4100c004040c21280050b001e5440d0101c1402030794015940c0e0380119081c2c4045181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 804707508 1250 804706258 804706307
    0x10030513080a0e150708090907110115150903111309080c0c1201060b030601080a0912031a040911041116260306010e04020901020a050f010f05090706 66
    0x20030003900d0005a00284501070006410907042c2d03102401240c0035604079071200514102404010042c410b001d4014600e45c2c080c8060307204d901d030207064194084071074284113003003001d1441f01d1070848502c1350750710f031b81c081d00403400f40b11035000f9403e2003008140034203000036441c2c00e5032240000c54249a0a052082840f0194011075680d95003003082903940c08801240c58000c25880c003521003254006a40c002e034485500c04040030f505000e000111203800304000c1c03450301c8880c0111540703070008040c1071500742c4828030000007900030001404040d0096038001203815410000d01d5009000903521072040c0d00380032500700407840500c00c401140800700c80000712280c1e80f040d4140a03014071252640090031404401080c04240848800d1715103074542100b4029280c0100707200c850206031003880c00200f80c095070b6109410181d0050014040500498148104694409180c01100740c03800c03050f40d4555003c074402d0303072440c0109900a1101805850384030304210f0001c01d001d8000f01c4c4601d80103003210 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 804708758 1250 804707508 804707521
    0x3071413050a0603050c0108010b03060d080910030902040509030f120709080a14071a0324040204060e0f0a1a07020114030103030c030f020d090302060d110c0f0105090c100305 77
    0x30040301501010a00c107001d10b190155280d002011503100c00d64040c003803442c0c0241c05612800400b4141e600c081080741c21500e4003024000703d820078180850b83c80400700002822543c90b20b5072401c0c20700c0a507a01041d0328603d4418401034400280490703070260310601c0815410030351041030f1048081c150002402c1070303a4103071048440756425480442140110018041804061080715051880100031155280e42c0c1d4090420030441814001a48070018004110100b1400d000300a40d0b6000004001d154880c01c0c8c00075040360700c160f2120003c100b09400250702814817011051000f42c048400e951018901429101600c01290815a9032040001c0e1355045a004000612403002e007051659180c0d80c486c64043e240c0c0307604580c20b90103d14024010719246100003064840304180780c1d0f502004034a15424088983c0240d4440075003903441301c44020460508201405c0bc449081e40100407040521a14508654011340f90440d180c1000ca048142074840c402142c181e00014500081c1564868 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 804710008 1250 804708758 804708769
    0xa0207030f0822080f03130302010c021816110105071413080319030e010b13020a050927100506091e090a1d061003060b0d0606060206010f090b030714 66
    0xa1564610b0006010140c900b8110f86950030282e039003c5003100d80d05202445501c0d603034020b01c0d412807900301d01c004060005500c40d2154110082c800b91020405105454441042c500101e48007011043c07110b0100348240e901c400d1119607421800700030091801d0501c40100007074503414041001d290001100c00d241c8801d82c0b20103004055000640e80c594481ca03841c1e812032100005100700090409602c4142c44006125030080e1b05802401100d555403600f0514000c0d4100360070b850240038043c8804281d5840b10340c0c1d002d02d80208220b042820b21000700d000950310002070031a581080c0e00601c01c1c0007a0325150126170101400711010140c4103905484200030007201641103800620070310a100c0480419044001100d034010030b01c8440101510b01d4950750402251001c100041800c01000810318a0780808100f9401611402c11144503440f03003410b50b051940100016402600100440b034103265240001c0c00c1040c8080c0321120b00d40c4006a66200c2500030003800b44c1c81000b2001556641 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 804711258 1250 804710008 804710017
    0x3120e1504030c031a0f010501140d0905030304050d02070b03131103150a0b010c0b0f0a060e0c03010806100506090909030d090528030206010306091502220501050a0207030f08 77
    0x10304040d0344a4680c078080381d603482648022940c042030900d0450218820424086c8603581c0400034401e140e180000441e44407a2031000c0440050741044050041c00305405a83c0b2218000c00085541e4101860120b2819141c0507900045401044c81885608a080116a0032000384003c00c0c603101d10720f042120380c0d42e5000c441c440e0315204451082150a03403aa00b81c81c0b15810354441003101002c0507005580410841c1c0000300105010800500760610390501a41c22500d42440003461307903100d04200e4205a0161400c0c10300003c040300401552a08000c0b041d80300ba0140303103a2950a123004049917240c000c04615603c1024084001070191100b08140c44058075904030502500100d410920b484120210100d64402150140b00207100282c00010b40c1702541580140b0283c0e02c0c0d074a0b070743c0042c03004800c12101701c0300c008104451490980040c00b000004590010090792403886541011102c0d81e2209040c86401c1c80391000346500841c0300d40459030004000e0050300c40d01c0c1b400d445188034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 804712508 1250 804711258 804711289
    0x12030201020d1415040b0315040c1d04050c0d0f0210030b060a0f0315050607080307020a02091005091b0a14040f0b04050a06080405073b15060403120e 66
    0x50028215042020311039068025134480010300b09022840c402d020989806240b000d41503030202281c0000d80400104441d8090700130032006035502d45131143d0304007409840040c0b80801102c501400180a414840c9221843c012a00060300d040c00b5502c2440c100c10351076011740f0424201c0c0503400c41d207029070064001c01c2070080c901381d40c039441e1580c0504411498104100003070b1a00c840f04d140002c1050b410b800780c62004080605003c1e2540d0b0740107065000608100031401084440070050325030030301090040c2034003069a0320003420b06d028481000b000800c01103180000c0100c0481003041c0b01304850303010510345406042c0e40b40c0f40203011414856070344010003440a140d80061358000203c06001902c01c122511050b03240da8860484802100780c40c09040340e0400c81d010860074501004060300640d110990105c0d00084100c0422040b10032803031401c2c4065210700304480e00c0da03070351240c0c1c1d0000c4048480b06d0500d03056840d0351941d00802c250100521200f0810405140c0e03071420a07620818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 804713758 1250 804712508 804712511
    0x10210020703181824090903180b030f161707180905150109030830040f02010f021522050307050d08070c0b06090a06090207081b01020703080112030201020d 69
    0x603500e518400c22400000119071003940f802c5c2c119401c0b1403e00101d070134450042c100c2e0000d1a0b040660007030041040500850030b0003c60300384101d449806101c000002c0c85c84004117601c80c980f049032900f501c07400400f007402180c502030112121035000300e02a5081001010310f21260342d100c2100380e460100d8551020341041440f00001400021500254469200c4181a0b92031450610041d0341c6180a0b020042101c4010720082c0e07a0759030038000071300114216500d045034292602d96a0801c40ca400e4506407041024502842e0955801c040301200510f6107100904006441e8101d00c400d288014140c92208410748010115011400a0307203000346400c0004d0300c2d904d101e107281c4181e482201140c0d0402040c55130340000c04850080002c500e449400a0359070415030340b80000c1203800d19000300b01d00c843c99130f28000400c01000a101410501d40708003c4e00e65034403806202d6000300d8070303120949107071617004201d180000b03036110105904440071407206003030080b80b62074140d0190007400600202d96 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 804715008 1250 804713758 804713807
    0xa0f06020c01090b091605010c080c1218010201050f190f020d0c050703091a030c03091c05090102060a090215031308070606031101142b020a05031f05010210020703 72
    0x194134000240110060400c80300769140e00806010700c000313184a528003103a4900c42c0a00422030800c024080c2c2c94078001a500c0c180c284070b42515040c0c00c0003a502802d04182c1d944420156024400c0c560000d0400b0165105403400103002080c003071880c440c0842d03058958000480654054058800c00d0820742e000303002c4100140d0004007160448d5406070b0003e0402200014121251065640100f0101010741d1459603400c1180070103900151040e01c051183c584020040500d20803002c1d401402a641c0594030b0303c107880020700d802c00c003900c01c0d4942c2e1310385000c240045c2d444d01c10401210710b040042c5038a80da226410504141c0c15a02d003c2d0100400151030300800103030741d02c12000c0d603106050300b03801600d070000112503c0303a01c0580d258003030108001055030806000f0300304000082140c44c02e182c003d01d02c2d0707051007643c00280c207000205001006004068502071400403030801c070160645621490040000d6a82101018140c41168001405014075100d244000d0b8642c0c04940c29a2a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 804716258 1250 804715008 804715013
    0x40207080405060d02270f10021f020c010e12090d02131103010612021305090c0708071109061005071506170d020d020a02031203180d03061d04050a0f06020c0109 71
    0x2a40c0141b60404040e00301101100c4018031446030312684490260000c040980c0707003428007105103044600e103400c0d0b118400200800e110710002d00840311440290168484121103a12401d4402c00c9600c4869a0401c7c50300e0184c00c81e20605403110180201c82c481d10784082030000c6000300e10204413009819060581d071032a5802c8a200850494505645600c0424081c02c3c00d00b08030700a0035811482c030701440000f0480e5252140340c068000617066140c40c90580309039680c140981c02141e04a500c1e0602e0381d207000940c580301c07040310350041c01641c1004144840c044010701c03600c60610003c01480d003404660b081d241c080d901200c0600349002d918002600321150890792444000d6180700140300e00382e80c2078000d41c408100b41c1c94140d40a0001d00701341600071440b150581009120f0300301d1401502e04468800c0c0200b01c01c0d80c50359855100061600d041904598208003001b0b01e07103091040078403e0000140c800a2a2400940c0020711341d00c0c0007803585031050280c800c2442020040d0300b4004074005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 804717508 1250 804716258 804716261
    0xb01211509021210030f1203060513050906010605040e0a020c01180503030a0c03060510050309120a0c030f05030f0a2d0605040b0901060504060f0e0a06211109040207080405060d 78
    0x10303400074800d04007200c2e40c2c034213100c807003c5945030000a15450540048100044506a0440e1500350604010645584400220f00b0100d550103203101502d4071807090200f1b4500600c240ea01402003450164645420420a410760b071101510070340000303600090107141d0003000e42c000d051400401d050b42c40110154100b0f6030f030342e800556049104900d0601d1641016000e4860201190000390010300404060182514545c00040c101c0b10b1703d0107000100c036110103202d00200b0890b640c503191007905c0b90b06402c2c000c02c0a1560031080e0107210080092000d00000c12402e560700c003100b808089050b40700702e0310201604051040f041601c07075801c80a2004603481d900b103181924000c4d5010410384d402d210400c040e00d60288a01d2010920030441407080c64443c0c20f10300c607a0505070074810303600501c0700041500349641c0d510810010f140000e442400f805080280c1404142c0e15906004000e880710300301c08140700d0450f40c1d511881e4001015010000030b070040e20001d00009140f81d0715071421400600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 804718758 1250 804717508 804717517
    0x30306030f0812130309060c03050f04030503040f14011b030203210712150509040215390d080709030b0a06080111070f0305090f0603070f02100b0121150902 69
    0x502c3c21400700c006120f10b500e140c40b494807180c01d562001310341b40c940302c401e644a03800e00c0000e9081007020072022462401c6c0c04000c0c8010740c840c10045603201e2400240c9215234005030010000f40447d40d00c0d0404580c4e1209601c040c010041c2c0c1000c8070780303c8600e820382c554414104288200114410034078a0443c40b0400030384104441e45802c410143c000d892075048404400c4c4200d100f00c0241c0e402d0042d82800a01c040e03000c0e1010740000040c175a0300d4480505a000005201018241560700340041c45108000041000040080b22014041010000c2d143c00750308a1407010007203040005130000f1b01c14000d81c0e00441d00b02c401c034001402c100718220007070131150103140400d6007002e8044406c107007800e08480c202d40c5c1000804400880319a0122401e078040054142c3c40404c02e070400300c50350358460045008242546070150355106c40310002e410440440c00c804019450180090001d0349c10285140c0c16851508195a602050303076006402403038660a52101e00304450000700c0d80410960040c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 804720008 1250 804718758 804718777
    0xa09090c1107060f1e0302070c0308040302240a0c05390907051b0c09072106261c0521010b162a03020a05060a1b030306030f08 56
    0xe802c0580c440d00c0035103c0b072881c84403440005401988098102e281d401d0425200c01503031901602c0c1000946a0400140c1260000e40392000001800c01c114500041c03041c51508071500c1800d90311030b03200341e0038540780941660b502c244540f003c41d4008101081c0081034425804201c070f000ea48482c1200300034483c00300103034658a200580000c00b00c0b8680704101d1803240910303a5a152403c1c1102001c810220384003403003e01c10784103030941204d031a0785a00b00140300d00016551000c61001c2003001c40c55101c6007041c0e4290241c6480e006201d51820b00c0c0105190380d00d00c4004505c00389000c0d204c0c40c035100103508200840e47d00038019045e030b60b0b0700c0310050004000010100d650046401c0085e00d40e04400e200e0100080b50800c24801840064600f20600b00c1c01250615074001014901c0081116123440079a80d83e82111006e00031490807072100d4000c1c0c0000e644590400910000182a0180210480002c0b044c000d400c0d90405100b41c02160145034494200c03150344400d490100300c2d541018111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 804721258 1250 804720008 804720013
    0xc030c0c1806120a050601140907030c0801050d030903020d0f02130510121506080f0714030309011b0501021c050901090f06020d112208061504020a09090c11 69
    0x20030080e00d4014458000100c88198416490b02e418040007160540840c104450340144800880410002c0c05128024000310620b10300c034040520030400c0030314004109105141c50055414a042c3d8404000d90549a064030700d4114005181800d8640d50b40702c2d0300c000e40c4224080d240308100b000441304c0000c0740b482030712035040100c905131200081c1d450443c4e04811200700c2c000c00b08000708140940c0d503803050281c04081084011074480030142e480940050701c5a910421846180e8402007103000000c19420188180340252480000c1c1c491040124841c108101c41048041204280c45446d511951001c000c555031080c0308140d210f070301c0e003d00085815030b15000000e1440301040c000e202203030b644500d0940b610304455442c20000d421041684502a07900c030722404e081000c0000400011050003c09a603900070405807104002e8a608015040d0b0040d200b4000404088141c080b0007503001c032409612600b2180b411038115400381d0000c0d210764145102940544c1d04000c40b035001d90200f105 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 804722508 1250 804721258 804721273
    0xb0c070312140d0207080715051f140402030a0b0307060c03091d0703090809040c05040f08010204060f05070201030b10032f2505060702030c010e0606061605070b0c030c 74
    0x1d541400d4980e8031154120b004201c15002c00b48243e00604400c0d2180310f02c035080c0700c1d007500e808400c852940b12140c9099520400d00844c2c034200c80d07a40d40f2128090904020300c0c0d091054080c01d01c4c0c4c80c400802c0c0181d4020020944140712a0401400c000c000343c00c4a040d2a91080001d1a0f05410501030700800d000c2c05011407800407902c80462002c0308005484416210300390100c004000500d802e54006405105240483d500c9015035010401c2c40e0f82c8040d20785092160031040745509500000485e881000b0400030181c0104196840c030f134090070059211a441c2c001030340a41604030f5202d6005240f01503040319550581c0c40012820b2802100301d440340441c10885e43e00001d51420a0b03062002803140c0c01203080880c01008244c42a007020030255026940c48a2508034180e0380f810150304041260445010244541e10040c0a6071008140c14281200810000d1040541541a04414900182c180481007002c0c1000f80b1807a8030301541c8400002d5195113a400c00d250b00b1005029540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 804723758 1250 804722508 804722543
    0x81e03010f0803070b061e030115030209092d120313031827020906040b2101060804030309051f0609060902040e060603060109080d0f0e090f0408130b0c0703 69
    0x640340344c25840443e800e6146c0f5000200036800b051514403003118003200103541c0080c0c900b80904070310041081c03e400c402c5411417040218610005100c081181e010f174840c09200c001031440b540b065580004074850100800c8102d82c2000d0388110309103017580740081440003400c0900f02007203840380250b41d214240e0745152854900c4001504c54903280700707000c901820510844082420001494050043c6030503000c2c004501141c1246d0f01c030b140318100214500d02440b07d00401d0f510b800801880e10b02c684d40c14101c0207403175004040e03c080c00b0141d88010900c100f00d0200545114030f0309240c0c41105c00d424075142c03100a898180108051281480c3e0000f80c1a01980260f905895031038207482840c0d070b00c403414000e01d90402030081d0b04000b541500082c1948041c4485c6c101e40442d40c1e1001c0c9030068081c00504458020705199010365174078410000030f0241418001d07040303540108616030303c81092031000c45492141d0001c8000d07040000e000742150100103403910441748180b0221000300c3d00d09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 804725008 1250 804723758 804723763
    0x6051e0c070b0109020f0702091302010e0303131a12090c0a0602012702011b03090e0112020303030a09050705030d170906010537080609100b06070f081e03010f08 71
    0x7480201000300c0e050041c845103400790003801002d80710407200c9041000307680000d0030000082e204851034503550240c5006550b40b049510580c04c4003640114074200700e03229061011616442031404c484005443c07424001980001c8850943d43c8601c3c44a132801e19000c036a894040085d00140700e00000c1000044241c018002c070300341c2d5040c081045087c0b2440c00362104a0750410441281041002d141f04c0c0b4126202582c80452680a030392514046403c140103d028040107801c416905192a580f80300140d60000c00c0720b520003480d000c04100050103280240c0313420b2594014583c50b00500ca03045003d0b60340400485403032686031080c00d05588908080b142c0b1440e0038080c543d08404603424074041080c03800e14600c0b0300700741a940d0b003588100c0001c10ba032100710550804600f80e007100c002d006042000300240708000301c14000410201e03103d48009076180c8150f8000030180f141c861188014403502205603180ca80c80451061103c1400d0051104d00b6402400b4800714250754070800f00e49040300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 804726258 1250 804725008 804725017
    0x60f13060e152a1608040f030302070605090901031118070c03080a110f0703050d050103060b121605041a12070e090a030c03080a021c02030a0b04020f09040905030706051e0c 76
    0x800f26070080c04000c00d030840460b6800111381804000005034400001600000208000d09166220307001503421854000d041c517040e503001b0b20030400184040710b05940c42c0a0118116544400305a42039400040850003c8040e04200301c4415442c0081012150300000724103103091190b0b580302410340e15546c091b02141c98000900c8603920b03040c000745604809040041c24224000e0410b581400c07950551141680c6090300f007162003c2e110700f00c5ca1001c1c101807e240d0520b4072481c0240030000005c401c051161103440c810a44034580f5142c0641840f078410054035074884000e800555048400d1012558400040c81110302d1808400c2c0096807100010400f0ba01c01507266503100c410561a88046407001809030841030310703542c2003004003200c62441c51507102c0703138121860168803442c1080d403050071100310071241c0b8003684c010407110410103005022504001001c50740091032020506120b032075030252400c0140010300c0d080c103111000c10b1242e81200301c0d0107018071034000380e43c80391600b0145016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 804727508 1250 804726258 804726301
    0x4080d0b060705030f0a090e04230105092113030f0b0603060c0f030411280602030f07081e0f0c2a0f2d09090102040305060f13060e15 59
    0x13051082c001101181c0e0b00034002e501a80c680026040d440700350a403c003060039941224802520103616080c03002a8041d92100020000200000c1c0f506848890326820b11550410004040c03030f03000131002c440300c4103485400c00c2d400c003202215510b0307113040700c01440b806000345da5003028140040c1c81d0b0310f80014840e2103508000385c402d00b0000a5011450390b5040a08201c0c2c103164030303114810940d1101e80d021160030142200b41050703000344001e84209a50580c0041d01150000c028043c010400f110407105086d90007007079540d840c110185039020b14103541c850009501800200c6200d041c0e06440540014807089094a040d140041c012902012891302481c00d903c0404095071090703c3d0542160740f40d194060000c03050802c180310064000319041420308141801e0480c41c2a031402c04d05030070b55100440e0402140340c0317170954032141e0396544d000b0410fa00e03000c030560005002e10100380300e200d07000d13911000900850401519503911820079640d003801801d20702d000610615030350410110084c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 804728758 1250 804727508 804727513
    0x102130e0919021c030507140105090c15090a061701060309240e0f03181c1b090c03060e07140a050d0b0a03030e03070b270409020904080d0b060705 65
    0x311001600d42034800020090313a00654200c442e0014141d02c0fa40c1980c207030303c2942c4140d603440b8985486160031840350411605689020104201080d00181000040c00101c80440728030319400620b0105128440034160400500780c400100305070004004051f06846d40240c0e11039a8a800e000c4085411460026103962004600801c0c0008841d4400244040d403c10110300f00b900314040520307103040d001407107450342d2000a4407100d4203500d070b480f1544800201d4041715548501000304049800c14600541188000e0b03203000c064446000c2c0c0c810080c807054400703002903d0144070140007001540304010158414000068009204041007d089000100c4031b070f04000402800b201c841e08846003070302400b9502d505a440f6070f40c40d0400b9000640c4a036498074070f42c600c90000e00d406c0506a0b400b90301d200c3c0084c0440141c01c5845804201a800c4088040a036404084005000b422840d40b000c0c0d0030030124024007080c4400304d00148400c03014400c06018010441c2c0c140911482045030184c020f8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 804730008 1250 804728758 804728773
    0x6080d0f020f15070e01050903011d12030f0432010903090902070f080d180c030201090816030b040809040f0506010e010c021e01050c070902071a0402100c05120a020102130e09 77
    0x845c060000048010410714289003805818004203003114070300d0320403600c810301c001d018001c104820405007006402c1c007119182181002141c2c2d020980b0081c000401219242150300000540c010541075401c440040811403010080801c9009001c1c0780001d40c0040c401c03150205210ba02c5008031211503612205145084480303031503c0f13103250003240e0750a0315540c8461210403c110044400080c090160000a03421840d600c005040d900307244e4170102d82500007580c0c5103100b2011404600880303400c403c034249540d48514118025200f00000d180d8032910704003000382070000130f61100d4400c12080e01d9105141d17845800640e030314174440c94020342c0014030620740034222000707050314140541c040c1011424031080710101824607040d074101c070f02c085901250000a000803004420301080b0881c0d0010454109500801d03030704d0344190302e08000d1018105408080010030001c40002e04032080401c0e03281c2c2810750307009002c1e610040d01c490000d07508160110310802d110a80c1c0d80601c900034010303d00d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 804731258 1250 804730008 804730021
    0x10f08131407080703051608070e0c070204090602160c0b0c0304230301140f0606040e060f010c0506130c050402030124030603080415030e16051306080d0f020f15 71
    0x600700040c0406014000c650000401e48820003007503000d14403480c0030b00400450f11802a02e4040079034020340b01c60f848035504000308a450701040790804020050a6a03441c0c01f800418050845c4401c001c103500d10005403e444e500c9802c01141645110f1499400000c2d507500100c003a6002d44a14102c441d0010071003004844051281d800e00e01065090034600780840074006070840300e8020f44950301d280804200224401d1041c9040d60110044030f10078141402d0420400d10000300800c41070141d01000500017141e8080e10707500c0b801651110480c6c8a500e0701e1403102070300c08001e200c02c942000102c0008a583c0c03403d80280c82c140d50401c0004c078107881100c0000201c60325800005000d0541e6500088049014540104050700020344443d6105241100040072038141019004a541001920307018101d0401000401c464080741c45410050740c02e00c40c0d20040c044d44d030000009201c1d5020900d4000c0c0c1114004003102020340036100d000c03480c8806242c0354107a842401812012103c0056603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 804732508 1250 804731258 804731273
    0x4050912030601200d0206041e0f06020a020c0a0f060e04050609220b01140f01020c030a0210120e0a030e24030703110a021f4511010f0813 61
    0x80000f040310344400c02130a580b081d41050503085c3c0810050b0020010001442005c0c0300041d01c811200340b80300c02400140e00d83c03001c00f00240800400f400e4001803491200c1d0310070006904000c0000305500700c442d5844030b0700001c495051180b00041017082400c44030628052103002d20070000035283d00c041d9070300c8602f0340412010f400d1600d0121610104800041a000d05045020701071800c00105030513518020840d40000c1c41503120304561100e580311403203441c01b140502d10715034140c51130300410a81020560701c1081850180406500d099040c600e950000606841e14600a486040e010050901400801c0460072003914452151001c80d000600c6080011a8810528980003c041408010301401503002540321310041c0e1056038021000d8003959a07451070007081607820004500200c1d00f29480180840035942402030f03841d51105c806000036600b114003280079584008025903490b00c44200c1050b40141400188091801d85201d4052460300f030040540c0003100c1c00320006e41d5901c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 804733758 1250 804732508 804732527
    0x90109031107181515090503011815200f04050a060509090403080901020f16110103020c07051306030b040b0406060504060b09041a0411120c03070c03050d110d0b04050912030601 78
    0x40d0091130001520501d07002412080c4215a030301e4203220b82c90301d01010300791180e04030351340020b01a450307110001400351021504a280c8500300440c049074684000c818241e02c810658403800c2001030b541092025600c024400c1d10030807100354840300e46a001c104c1d81c500500c206c0c0b0360003090440201e0046405400c00551042c90356002529151280b40c50f15801e421010007070b050010f0100d00c0c07004001d1400d8009030403584c00c0c60700314180601544400d03034a07401c0b44121409101e08190380800c0c80740f10b801c40b101841c1c000200c04064103152801c2444c1d0714088070b041d01c0c400d1504402150030700d850701405003160140d682c60ba05046011042100510101740602c00c1d65450540289094549014961408503001c09042e02e03100d0741d0140301e0100340000d000154080040003000360260f006041800826010b2a10070f8a408503003028000400c048080307100100c1c0c010070041034158050b001015074910564080c02a9228500c140350760b0004104e100114020900008255511408401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 804735008 1250 804733758 804733781
    0x110a021f060b07060219140a20031b1e06010504020a0507230d0905030627070b091c0308060603130b01031203060611211209010903110718 61
    0x2241a034410425003150f03c02142216000d4021401d104c582c16038150b040121061410440400074492003008860f104903400c0c101130000ca280300074812100700410501c481c0280b812641e030740c1c4007101550500100031807503180c81c0c8203221018401d548030711500c05800c801c10004000c0b03079003000b04100c0a50080804a0300704002400f0b2800801e84258218910002a484d440c1d1640310280c003090074855009911024444124400c000a8400007000ca0b4480c0100c0d088076030407800240c148016a4078188003402a10504002084141500c001840b1844044a02c1101042c040001010807a44130101401184075400010164200007004603400406d040450204441a43c1d90f030010300c81c00e8005032014a010159080074940511584003d00703864144003142c03d0085010710b43e19442000c0341d2071900c602480c0b298074101208140c0303484440c0035182c5000c926098107042d000700060303c000d900085511030b44050b000e0703012951009481c654052400e00100313591149001e040d030306500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 804736258 1250 804735008 804735011
    0xa0b010905071115070305101206020c010905070801060e161e02030409150512011104060507020415140a06090503030702040e160e0103050c100e04150f18110a021f 72
    0x4410f5140144545120725060405800442c28040d10080407501c00800050295910180a000c5205d000019200e0742d41e0103000542d03515218000c05e405001314a50090062146a0000c00c8094040d00003030f041c1c405d034034070003c000d0f6951480940c0850204014070041841a120050940600c0d114804041c0c024012030386071564561543e42260403002410003011500c1905001c01e2070306001224041030030320003d020403000000001103611581c421a001d1204c0014000304649503504858031044408041074000382c2c1d80e901101d409000030101e584241d510032004280300740a0181241500d401400542c142900c1e6400d00000b00031055440300c40b03104100070b00c0c2c0008038404902c80070780306006505003a03500d149810b52804840c00509403003980f042a8100c292584851aa4041d0f60b040310041164a00c603103d44823040c28541010355068807081d00400c0e040c131031481d14403a9000310001040782c080c00c40d112040701d0150300c04210040c3c000381141080c40300c08069014122611190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 804737508 1250 804736258 804736277
    0x150506191509030b01091e0204380706020c0105062d010c12031b080622090b0109051e040506060904050f0d1218032f12030406050601020a0b01090507 66
    0x242c4070413000c0c0036449030741c10310386440b81000d000c044c110305424462284403003035040c117040100700140e4040040c070440303a0b000c1d1240c0700c4441140e80c2411207038065405c05460354401c1c1a00f00040a544240804140d03507080c1800f00303055051249100e81c5034118001000d0440810b009208810750001c2c100a04004a0880400114060380228a4040d0f055103001a054291150096254a07441010414021300c1402c0000d95125081c240e0b03a0090030344601d139200c04821700200000d101c5c20728007901d20310662001241150b00ca91201d40035104641c1d1051030314010281c469010310089400030815000640440c0490070300003001500700348100140c640304180f40030201c1c80c1c050307880c181c43c0c00035000809030700101010f8030505580321500c4444d2001000c9030f8401620000724a24225110014a00c0e41b02017061180da1000fa46d050541c140d544414440804c403019400a0790185d5500785403001160556000103201c03258154000d854100c0f0b030b0320303000c0220002c20300140b04005001548a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 804738758 1250 804737508 804737513
    0x90709020d090503030f16050c0606100c06090312060f06020c2b03081905012108190305060406080606090a1517061503060c09062515050619150903 65
    0x7070762103154488040b074940d01d44400700303ca00c22541f13071844041c00030411058000304008516030b90721450584031140500f814a404458859084030041c14007407920305041c0401d944207100740d2000d0050742d0300f03010081c0c48407070000030010144180800742c0d00c0300361940480e092a00c8150802322040151150b00c0001100d038440c1410381e0316044000500300700070440700540d00e18444010001c0b605040066605111089034241c612840c18109120241803800400c440c0c0400c40f0034581152a42040360383c50380c5000340150205031030440c46541408004207080c8000a0140c0c407a02c4010601d0640b500c030f41240000911030041c544200e10380c401d8000c01c0311701d1712188003555481002c00a0801340361555480c141c400c4100600c5100c2d0f0001010b02c02d141c002801134508162048842c1983c4002840e110500018001e0001e0007404545401105105100c10500b000c80d81c811002d000a1755442c04000340a54600035540d403100c8038640c24401c84115403a110a25841030801074030a98480c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 804740008 1250 804738758 804738763
    0xb1602090615030c03180c1809120f0c25050d0809060f03040203151005100e0409050c011d0109210f050d1407080a050a0207030807060b0a0e090709020d0905 69
    0x80b541d04c80700e0f0303d0000c00c0c0403010380d00109115100315460054804a0050400204d0748507182c038a441079150250045007441c0b5040c45a0141d0b84004400e8694983c8100803892194000c0b21a003842070080b016088030086d80f201c1c464140700c900c0b1851041440c204020003880382c08101003580d50980506c04185242c4641009011010040046944134581441014500109403011800d60043d54007841200c90f2851001c00035104100c801d82404000d4540445507110340108090b801403d2201100c2130000c04200c0841082083e615084c0c0700f26030030917484100d240715400e1400500c4c3e10b031080003921754100110055101040204140044680b10312210b80c070b0f0f01034261843d400031491030021917000f40440c0040030740054054100140f98031014007500a49070710a05010b40051000611442800020040c5920000c03494076030700c050801500a03e5000390240c019400200049200800a40d60600c030708040401010f1031414150704030081d40050b00803028040e10f0300ea0b001d0008070113 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 804741258 1250 804740008 804740011
    0x30b0f1008030706060e0105060a120b040e1e070602060c0a0309060b09040b0f06010c080715090206030a1b050412120e0a091406060f030112050309090103060c02070b160209061503 79
    0x2c12000c140d046c100b21a141d42104103074042c0d48580e40802c0403030807040d001040c10340310b2001c1d44000a07440340701a0200b4050708184407940440d000300c4010090a05031900c07900821280c180407124180d484040a9035120000da56500c5000024080503441d0351280d0024980700340b00311404942071004a001c04c0c2403840580d011920762000c01e0030001e0615502e45000e0748100c0910f000100741d205512a02d0b120300c07401c000600750079481452442c0244494100350040355010b07000c1741c1e07240b50440302c507030040c003180c806036408600503100c1e400141c2c4100243c405035000054042e0130030015540b0070006041c459000c0f400d10016071000303415960b450005100030031a840c808620040c4151007001d080d03d00030b200921a00e024040f03c000e10a045090781d0548561624400d480105400c11511354003d80c08116070001d0700d20004420020745030081e0102d441181c00700e0b05851340716418404213000c1c444450b00c003003141c08001300151038040b00458000c40d002d042c02240c80082e05440e03849520 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 804742508 1250 804741258 804741263
    0x109150804030e0103050c040b0c0f030f0c0c0a060e0d050c04020d0b03010609020a080f10030b161d221d0f240f1504150f060504030b0f10080307 64
    0x580c0c100024140c002d0980c0b002c00780240b03810000c500d8085603202d4039015034021b02c014030401040d82ca80b050010400b4444018840d0112074880400d0342d01030400380d00c0403640444601800401281606003840a441610203540714001a40504420712018046134141910607128407940307401c0307a031158401001c0c0302154600c041404c0f001d403803c1c5802d6a00c1544004203551041081c00030981d40401e0542d0080740b001788151003a12036050540503044260000351100b000c000c00d2088101e203011082c5641d09040d1a0f2840820018440c050301100200c042c54203da45800d0012004403206004002203068810001c0c3c1451810600000354643d0110500c00380c0c42003d000070f01402c204880e580c6601200030051101018445810000c1d8006d0301043c0c84c05040070101d5150364090105803014440508204649001c410401005400301c0c806d0300000310b125000803030228400c10855090300e030492902c84840c2c071840e000c8000180c000302030076420a44040e010440315800d000902c6000d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 804743758 1250 804742508 804742517
    0xa021501030c1d010b040b0901090807060306031101020f15090f0703060501030b060a0b16020418050a030305010b0f070f0f0b180c0105090d02190504020a09090506042306010915 78
    0x2030500c0c402100c0305181c0700c40c0d01e25920041004120081d070b44801ca1b8103880c034284082d40c030b407060800180c1e5120040e4110114600550001090543e8103030f0101007140e0065121070711102c40080160303142c41a4104100c0d5540008401c1070000340c1d500c071580d0304806040105c4005400610900b030802c00ca0360001c0320204d0312180100240b00c800c00d0141d4203d001101c1c448140d9141400c00318882c414038010a10211260000070b0565030340354441c0d00e03105141078501012400d03d01d40a40c07507007690502140801c0c42e000010980c007000c5405ea403510070b15504150301d0b011150302c40c140301010b81d6104941d400000420f040001d410203038200e01071004a240001415990403002d400c105440420904101040c042881e5594070405026800354050f21001010702540701d021081c540da9810032038105000040c3d41c0c0706550300410000031030b803008400300b082d900c4103001c12040da509000310010b14480050320722680100c200c901d640050050409090b01a82e81240d5510a44016540401310707 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 804745008 1250 804743758 804743783
    0xe100e0f060105101b110d06141b0f0c01110f0a020c01050313060e101e0501090509030f03070c05190b10181113141e060a050a02150103 60
    0x40c102006500e01408040b15070001a44542c040102051080707000805260700c04031030202402400f8070781204590300038100743c0d402910b608044001c3c2254a826005c9a040000025291042c0604210000c1000d02c5414a40074007070100c1c50154205d0307003000c4001e542c0c0f000c841b842c03440000c0c001e0450311f00c440c01107500c803139102e1000380c2000c0c1e8002c0454140310b0304004104103012448400701803541c0c0820006400d40a10300e45902d07204d04849001c079000d1900c0f5181d07400f002985010f04401958003014003880c0e0300c940701c00301a1030301655072144030f510512203641003a08200c0034542c030410b54074001000641e00c3e00d80c94074284124440c0c40709130203500920003d00410f0102244c0c080405440201407901e130130300c10088005081c4014241540c0c0c0c9040304800b2142804480d04481102001c200c0d003622442060a18540036500b5842010040401006100c0b0101d440b040000d00401c21400e00f41c00318000c0da40da0b4801c2c65001c00b1400340440b4940c003150105030440c0a54024401203020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 804746258 1250 804745008 804745033
    0x3030305220203060c250803010807050a05030a120203220905130c0501031e0f0b0301061a03060f010c0b04060509060a0605030a020d26030709050619030e100e 70
    0x11200700c14807100000070031078042805030b100040d0442d040700f41c0541a0340c0d6403228600c0345042e143d11a450440040e41c2c0b8800c4014000481c2c042c605860140068450155446040004148a5200c1c294040c1c001ca5101c00115101c01c19034821841c1c0c03030040c2c07407902c00c1a10344100c0302507485203508000c40b10003805101055031449002c0c2e004caa01e03400c118400990341c458841200c01803056070f0415840c0d100200640b116500c001c4060218440705001b082440c400300009002c00202840c080c0d880c0003c00100c006400b111090820228000b0610b15111041801282c1e1921001c80e414015088409000500382e14240c52144c0d000303000c00507460908401c0c00b400c000d40507000603403040c113002c07007400641e0b0302040075030019a0482d10040c00040505c0c2681d55868078030301e0034506d8800340109410065a610065104511980d43d119541c1d032102c0c1088000d00440817110002c0200150f584a40c0b4041d601885a0301c45460444030f89002c440d00d144240c5080000c0400d0a0300b025050204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 804747508 1250 804746258 804746281
    0x1110a02161a09040b010e040f051b04030f030e0f0a17060c0903071814010305061503011401090207020a05031c1211031308070609030e42040f03030305 67
    0x50b0008102403500000c65010700100c6006091245214698880001c103490b8090010100401c0b030240c4103020440c5040e0384070000784802c5401c821060003811031070b0744490400044038180da6101c40d03904c07007903400360701c003150b007010075682c000e401412004441c8556a1003d480710010160340d21007001e401c40c0c0c40d03100c0307041070750240c14004480c03824461126503503404074468050f1051030a41115074078540c4c4001028207800c0d241c5900c5903000d44004018480c0104205100c1d030b000740c40c0c54800903d000d0525088a1450014030b039902c400c2001405034050315001002d0755400106040042038031000002c0c00d0203061744003a01c4103101500407442907600306c2c02c01d01450507600400c02140c0210305075090b942c84001d1554070340182008100d010400d225040d90421078000504011607a150325029052422406078644104030f6100e2032a001640400c03403805403941d03408280b4241015101000040a01c0905485144010700007c80c44a01c14241c0e030000b03501982c0c0200e880e06000350601c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 804748758 1250 804747508 804747553
    0x1206040501061434110103090312020c1203091c08060f04050c1209100b010212030c13170d120e1e010204031e021207030b1f090911040501080f1e01110a02 68
    0x241418140007011010031380101212b000442a0100541da03444107004c224140b000601807030050340008001e10006180c00285101c011400c200c0c400040261584262038154085400f558030030301400c0442c200c0e06050704540d40080c504e0681900b03161000f400c034660048200d40741e41c0c0643c018060384c58802d00754015030280750028009800c1007142d200c0c0301c1c00c05210082491491130302c0010380048003005141054014003044800c801c0500c08400403076161406145450002503140d003049030744080364803404080400000c01448151002843c1000c60b40540308841043c0d5400d04c40080894001d002d1500c000b94440303050b0f41490307250f10411450803030090425103c0d61000c5400d000007400301d40d9041e0054030440000c03c1c2000700e1003d0149901c2d1075007110419a0a10080700100301d100e040711600e01c1c00c100c9040c403642e84c85420290380e604000342d020b501540018680c070500440c690350071402d0343c1c202e8004181620b030650582d009902c69601500141c0c0013503590280c4004000158 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 804750008 1250 804748758 804748793
    0x403060c08070e06070507140312040627050603160513120b0f040b0c07110402040816090c0509060c1e030d0e2d0c13021206040501061434 61
    0x85d08002007031b1034007565000d150050092120140585520582c0c003000035070069600c0f91042681c65444080040c0000d101403860030030801d45480f509202806c902d89101a558081c09032070650761545243c803020700d4180000c0d8180001000400038002d01d00704100080c2070603040daa100030780b49190038126200e0080c040f5640c4504202403100050540810319080070200a070309440d48194105202c030324a450b03840c1540700f4400140029042d13004580c1410b000004800d04040581c3c0b081c589042c0d50038100394100149003000444101d18246e0050321070f2120800c211a04c00b61198225109007203840981051584041069160381400b03008002030f0500b5200500210130381c0c0d0118813498042901c9001c824203103920300d2902c04904000140c0c03804802012040e10f10081c004c903100a40c0300c01141c03495012540f0004006044c01d028aa0403500903681d40f00042d16101451300c90342d040006d0381c15041c0b90903031600003806865040c550821281c0004114081071a1518908841c40d16100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 804751258 1250 804750008 804750019
    0x160b06061306080c0c07060f0806011706011b050109080306120f0c21060c04050301061e030b04020d0602071b05181f0906080d090b120c0a050403060c08070e 69
    0x455801c9030850070000c00b1074619040840c1d01d521841c0400d8100d00910390f00f08428443d1a20000702c03079900c408105548065a101d90714291102c100444140700100da11061035240180401c074154455841000415400502d12605946651300c0c0f42c25528181c00c19a02810017106000d45407821100034611202807100030110880c0e112816034036001910001c1c0e10424152101040115001c0e6000d01da03c030850050340c90503d032224140c062500180616030181d86820000704818001880e41900070900b1700c01000c10916550b141c1c1c44600c00203104036080700c03c0090200001d9080d001411055101c0c05510021002640c221901e807165075000c00d00c03415203c10b01c036042c0c03001039a600e81c010103021282010040c5034101c408001e18540e20290b002072070007800240c03240700860143d84486060b525880c085584d541120000c1c010110b8050103000504040342421480c07030000c21000c03500d8106941441daa075110f40d0b0454240800c1500403903040307070070012101c1e07001e46840c4100d2403c5070b2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 804752508 1250 804751258 804751267
    0x2307030f0302011112010e13050604050a1b290f030c03060f0a050907110102090a0f0e0901050702190201030930020d0516020d141614060a0e0411160b0606 68
    0x41017032038180f007225000c441da14042600d26112482008201d50070004545040c00d00c0d01d481c80d610404104146c41c065412156071900103285003c1d101115031203400c80300041c42e407410300c400010101004410601c0100104000b09070107002441c8520205040107440b032412005000c8071541103017006210301c65201c824030881d1741d000d60b40c681010580c908200c2044400705014020705c18806000d42c00180b164000038400c401904400c29128050040116511901051800d03a0400c0c5d030200c02607000405003940c144a44014040424014903002c41d0000c210303190010311206880e102801c61081c88580300c1034042c040c0d41c1440401c442e1009100d80702007201c00411074019207104505858140500c4003c2d5035642d0807580c80140c00c004208046490444030316503030b600c0005414904401c6003400038580403420103001e0311043c090501890305d18040d0341100c46010720b40c591a1301580c1c0e500742c103440e1138000000e02044131910600502002413810b0494202100620031407143d0030410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 804753758 1250 804752508 804752527
    0x9060b0304061d0111070611030912070611120a150303050d020c0f03160c080c0109060804050313090b190b070b1305010c090e07050307020a2307030f03020111 70
    0x12241e00a0700000b00041c4000100451030842e030702000e00d00c401e0340c280060609030700043d10040403401c0c890401080b43c041c00e004450024001160001000e400010481e407128800d000107104c82c03441000c0000705c46a0410b0b004000360028850b107081006460104040c1c5850383c4034074803070710059100c0c1100301c030b196030350081c11441171280ea0441c0980200d22102102c1c0c0c10071912480d080460b0a032500c0e0240b00c401c1c2a0501300c00c06040d100d8030081c0c080024901c1c03003c100041e10820607564402c0c0141400400d4a44602c060000c441d240b0040001c4c0085203a03000e1614050f03e008100850484030000c20403c0b00741c0c1e01205410000c9980c0c000700038044000d811910700d10350142070504030703643e820005000b0300f241c91005000da5082041c0007000d1540840800103555030503405607099280d00c3c00844035404111b034204050791061181030080390700000900c1076aa500c020564801c008179241c642051102c2d801100c1c00ca008900b5401055028000d249103c0a4050100c1c144180e11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 804755008 1250 804753758 804753779
    0x240c0e1f030213051509040b06040b03040f210206070201110c060a0c02120424030e03070f1b24020604031b030311030c03040c0b0a0c030e03072403060906 68
    0x61564105050b4006078581d15403104945000041038028070480203650012014045a030040110610652500143c0d05040c0b418100b594142c0c0c01a02c1d24504560341c568440300040c02c0010203892b83d00007650f82c07000710600c04a0002140340154042d20503420721603c080e080d070388488594005240300348810304d800000003602580c01540c0b0000070501034880c400607420252003200701c824001c0c0010300072418202c1d0712035280384040615882888002030540813800c40d4600c000244807900300300070030404202d000c3c80182e42c15000e442e024007124006040f00380c5c0c4950590002041c0e440380541141c2900380c001d21548a8a1640040c125a140030b680040035510b6440703081d070030300c1082460502410b1196018910b55030000205903030300d06040030b03110080d410440d030403600c0c03030015400450f0030748458068503c0d0031030b0707900c3e00c00b075034a4541c1c0c042c0c4288800c03625494061151900001d907074000d81d480175070f02403001da0714104c10804c4004002e0603148540c21842384103060440401080071003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 804756258 1250 804755008 804755059
    0x7080406121a2821120305010f03020d02040b03071511010e0d08040813140f01020111031503010e010906021308060c04091e140106020c0d0c03030309240c0e 69
    0x40c205881c0310310043e2080c14030790f0041c0e41c1010103407540881a0104048103090301d690118090030310007000002e0310b541101a80c2d400d02611b400b400f55500d007000107040c05070919132194402440800c031081590007191810505901c01c1d191100c8a100fa03099440e003024014071240031200080c0002e61000343d51650f500b00406d0b42c0410400042c0c0010144601c100581d040c5aa180e00c0600d5071b66030369803a02000c2da4080c151203201c1c2d0484498062598014404d010300c0e018042c1a1070706641d2000c200c170b01200080c8400d66055500c98110b4000c6650038070915003440d00c521001602e0300d03105c2001115442644e00041c0b40c40c1c1c00711040c0700303101000300195022103541d0200821480380000f500309500701450220008113081c444c94080a050940e407840c162135081d401c41321602d040c0b508010a13241203810142c0141e02c001c00c28070209200350020b5003003038011800705600010074940340308406071400c1e03810042503171070a1000c419540301da01c07241c111008840400841884054034a41501c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 804757508 1250 804756258 804756289
    0x509060f060307050d09050a0201030c050c0c1009030f2102030705060c070c0e04030f0f020a080706020309070308030406050403090e070206070e031f0e0d0903050712020607080406121a 81
    0x70040000b0f11100d1180781180c007540c40c0e2140510541c60705103405503481e1a0484101e01203420146e43e40b106030712640c00d491903071072000024108008804240040c807071020200d0010400304410101c0410301b25009683e205104561003840e0740c420301307003000868200d040740900310b400030006100402c000103a6030750059002a0042e0b500d0f00d080c60300038080765407a4868071955804d14100310515030026030000c50000309032130303d49803500c6a22040303071074078202540200541d1061100d01d020440e07507400345074891040002c40d402d954a81c0c54251103900101c401310bc07120340b94000c000400d61702420fa4802801c511900080da03041405021352940c000500d004104414450680c075156801c02c40b01b9101d0031036100c5440d041141e000d110303002c0d00c2ca007800341845103d0b40400c80c11310752241d4207440132281c024015100361802c1040c0d2001611421000340d900120038498440450000700003000103200319140d080e600395002c0c0e08601502d0400c00001008004a40c445200b500c40c03080e003519030304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 804758758 1250 804757508 804757519
    0x122d0a03180f06021801180608090f060412020d0305060d08070606150f090b091f05071a01060e0108190b120f0c120a11130e01051009060509060f 64
    0x2481d40e0001d098081d80c00c04003030031600d202041d00061240e80d5000380320548003400c028951118800054035822440080840c1daa0a100e0007000002c0c851080d032904040051f0070380d41c611005a001c0d618061055406841c8400f41500001d5800d40410900d6001141c5040600103490032030300050200c0c159103401f4184c40f40005800d001c1080c9588160301401c00211402e641c150107200050603460311648000100c2c1c040040482e4420700041511a8200c00914103075a183c904155480312454104241c000d011060003113000051b80c0c2c020340038441d10440003000380c0b903250010013410101c50744026418485a801406014401007034038074035007807c5240203e44515080040342003441d00c96a928480c5c01001485403c03030a010509407500701c0c0c1241d603c4035904c841c8100c0d42e1640b45192004042360700c0264907914074204213013000c8040413400070020711086078810322401d43e40c2c00c4580100342241c0c2c003001d0054070740c0382c4141d40141c902960b449420740760400205030140e5403400d9191081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 804760008 1250 804758758 804758771
    0xe09150402090a170714030606060c070e040317060907020a0209060a03060204080f07061d0108070903051501360902060c0a0f120c0b060d14122d0a03 66
    0x6403900d0701259030548010308100c25031684c408191a900700100c0b810340b014080c80100040c54452100c0012119600801034a06a2640e500b000000d9000711a000e9031070150400010b9280c4500c103107036214500940b10302c10320031071390340108400c4540140007501ca0030b640400d210760268001031440e030a0303606031900b05182c0c44180000e08400281e40c4010401d500014000c5040580428070902c2803038901c0403242495210318040d10501c1c11104d0f8002a19040d44860300b5541c401c8001c540c028040d170402940490f100e49a041c2422390450449068512410041103e480502c9521805918240109400395001c079003958610440720700842c4003546494114055590301da04450340609804201d0b03100040a151209542d900c0c8101a00c0c01c501072030860b86080d0054080714800c030340c4084480d40a40d10107007005410700c0400c1040c0c41d181d019268103010f14401f00521030344500340c01840c81c1c9929410100400d4007075404034480c115503440380402100d492007400c2c2c41c44107000e0f080101e0031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804761258 1250 804760008 804760051
    0x10e13061113080f0709090b0c090105070204111e0a09141306031a0703020702090106210e070503070b07240f020f07031101064b150e09 60
    0x7074001d0395210300814030b00301c600251040c40003494003c0440700d1420b550707044e076071400302008075074004001501ca07a443c0c01c001a11a80c0c100010003015905042003400c010700b0707801240031102907682185c00340e000090003150041c00045000101416019803600e40500103100910780040e611441110f8034950400301c4440d95004814032006442c0481008440d03070742d08000c1c000d0b0f142c441c003003850446ea11011a44c441d1003802215130554025040c0492a4030382002103030455090306164120a003c50006032110240d40180d5002d08998002803103568203002c2010b04085241c0e12030010f8400401591001032104283c4501900b0074100e00c0703a4600041c0c4042c40a080007095400201d407002520324100f5032154041c1c85403d01998400c00344c0340180c0402800c8620074094445a00b051054041100110803140300d00c400800c200d01400d840003020a00300c82440d0500c0c94040d0901c0c040030303caa1000182074198610680c5002c110601d80307a0301150b20240083d000600c02c070500c007018440c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 804762508 1250 804761258 804761291
    0x209040b12031c1407051903020406020307020906010201021c0e0d020102030910110427063c05030a0b01141f0c060204150804020406090b0315040c0506040914010e1306 74
    0x410303590618101c1c0403031410b00c5c0018035550128054450340b00d800781c180740c00745110303100766015100c840e00150302c0c03c0e08a0702003002e5004028035590441d03400300a04480447e000c482510301200504000c10600c1c1031000c0c890500f96048100000c5a10510401c41452000554400c610300310160010300c11002c0d8108000d0780c8142e800c01000ca030000341d4469a18800c000f01103811100000c01080000c1e150000540c0408800d6003640300c501e0200c40e90039942d00240380c8100e2051802c0c85440c5420381e56004241040c02d20381d01580c070b004541004122402c003d125090100100701daa4005040310303002201c03100d56104501004000301360048400b04101340d8120740107000c0000020500c080c15510090088008071800ca000e91305201c0c00055a01031802414103000b001405090302401a031040c900c80b11004106413a6815850f40004064507a40002c00c0680014800410040b00001e0442804541030740900441c1d4030b84000c00004903885c144040a25034040c1012034400c180e01d04001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 804763758 1250 804762508 804762521
    0xa0e01060509190b09040f0b1005040c0e03060a0603120503071815020f030309030f07021311031b04030b0127051302030f031207050c1009060209040b12031c 69
    0x940050042040c0312000402440c8080d030b00c00c0c03414040c0030600e00e41c030501c005d0316420394005183c091004030100015122031441d9078815104004030300900e03078400008040d2110100c400c030202c0ca911002c40c1c4030341070a10500e07034000d0b0003c1d0280802451550b400240b07020900c040d400700320f804030204250390310401590300941c00702c0e20061291502c13850129034018003a221440984240034034206844000b005a9200300d454101071070a1001101504510707501c0548100e0780003900b0300c2c058200d01024414021403a029400094580c40d0140e0413a15003030130040c044082950a000400c00900b841084074107440d401c0382c1d1848407003150009000c4d5410a51643e22101342481c0c104415403420408044006008508580385124500011501c900c0b0340d00340c4002c048502c8001414990250004022030f900f007204442000402c0c0454004031104104101d54980e00000c902c006d61420b8080c0440380c12007203601d281d14113104035074a6664402da01c8028101c00e00b6110a5064020b16030040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 804765008 1250 804763758 804763769
    0xb0c1c20010f0501090506030607020a02131107020301020a0f08010906030f02010c060e010c020c030111120103111915030e060709170c09190507020f0d03022b060819020105030a0e0106 81
    0x41c0f00e6541c4820901010342070450703c0900030f00c42c02e4001340680d44001401d6410f641c02400c02d00c0c13120040540340004d40000d08000e140c0a0003040340d480140c90920041442900907518903410000d0741d42d005280c81410f0307105011841c10200180042411308107031755025a42400c01e0404e4104500c3c006000e0f00b03a07445401140d510b46600c0380180c50700802d0001c80140110002c002c10701001611740e0755030081d1035503400300c070480000510001da0b4105540703844000040c54204d00c8070240f03418603003d80c1c4135000885108407203034030201900d40500510848038449006007d50345007541000b010b07000c00d886a201201741c0164120b001441c00c1c0840142d10300c002d8484895881d18101e0f00c003080d4483c040000780c6910784400541032a00c045980e1581c503003030002400810505501c120080e40040c0c68455501c14884105507126004400c8402c1120340300300d001c034855240c06921810b0071100030f030b400c3c500210100010010307a0701030226548040382e07400010340e80d040360742d146004002d82d4008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 804766258 1250 804765008 804765011
    0x819030e0307060b090a1a0607020102030909010f1503050f13020a092301080c03060a1113080d020f0105060a181b0809010c1d09060d0209010b0c1c20010f 68
    0xb6802401403603013240c020090180d400d0074050b1150301020741100c0411415000b4040d545039429a84d15044000b85840740c01481141d00300001103000600d02c000c203a00421421750581c4040020040d022200b070303001c80040c1000c002e54a0071000e4086031441c0104529030000300381075128215a1101d18150252030034410422200d01003411100d11403200310110740c01c0082c0d0320000201c840001800c00d04103140600a4200b540390340405401421044c400d01108140c05e0080b030224800f0303416103400a004000007400304602d8030340c0c081e01f002046c100d28410750b410301c8100070441e1941106241102d204800ba4504032102100306802090005c1d501000c140c0c14010f090000d030351181c40d941c014403d03013008014942560000756580b1503d1040d4140b440c500d036819a510b0302d422007499030301510103091401c0c90318065000640884098120344812003000c01c2072103e0420400c00444e01266803501d00380590306d901d5000d864040c0c916600d02d003280c56050840180007082d0040d5000300f1b0b00386030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 804767508 1250 804766258 804766267
    0x80406020f100e0c100c020d0f120804020a060c0204020f0f0309070605030403080105010806180405060a0e01060803041e080f01091205030f0f07020f060f1b04030819030e03 76
    0x945480c00440d2646440c400c0424004154001d03100350580c0400f090000c1125844180900c0001c01e02103031140207001500d0094405030b1182544000b203c0c2c4210040000302e069440d2142c10010a0810319007040042c10800c40181c4a0526000a40d140b0381086081031005100140181c0f1641c41007103581003012a4000b80c280c2e030344011710f0044c0075030700660303240d00d44030341c0200c0b1240802c8070041c0005110900400ca00e501410400e5001000600703201c1a5081e04140c900820350142c904550540c455000c20401c0040d03403040e014480301080c0280400c5140c113000941da4052409150203040c0c6203841800c509200310607050092415506840b0072004807800c590080c0100c0760180d54800031003c94640152041e400c991080d628480100b005841d04245100040c40050100040d1312034a402902400f0040010764413030429139071820b8203403601501c2c3c0d00c40040301d03000c4451048070500c42400040d8108050f508003c000c4014130b41c584126040803800703010788550480041c0400207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 804768758 1250 804767508 804767519
    0x6120209060f1216210c0902031803070507050a15120c020307050604051f060b0a0c26090a06030504050d0302090d0210030c0f090b0702090405240a0501080d0e010f0c0804 75
    0x88800031140b0b0505d465403a05c080281030300f40c4031071501c0e008205c0702c00e000040c055006e8a80c080c6421480707115441203140305501040349141e118880c25503a65000d41c20410403440c4c02c0c9000c030054405c00100d4161601d03092000b0709820410907120840ba9103503141c88030350714420419240241d410504039006802d090420b540c4031800040002c018480c210000d2180c01303050302030841110910700038a0315101180e40100e0380748210742c0040710003d0118110800401c0c40c94042102891101000c583d141c41003030400c244c0505c02ea00076070505051004100105401007119a4070791050304000d07a44050314000240c1501d0900b00007075115080200c180070180e4181c0c000c1c00000f8040d250380e80800440c010555241525100d4200031230004c00020740107040040c241a0414420400c0315200c01ea803803840d00040b11514001041094947c007007103104245c90040c2d0b8010400903024042424080324000e002100c424402c07418001d5004480440700e210b840e401040300d4002e803460380ca0701c1d1240e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 804770008 1250 804768758 804768793
    0x210f020a111605010f110f0313050a0e0603071802130909060c0e0f04090309090c050a270b091c060f2a0e1207150306120209060f12 58
    0xe6450031158840c480e02451460b03020800d05007070b00ca050711102d0024800c940110f440110f100003c01c203d000b580c0c0a52841d50041016042d512000495020000c0c2088203100b002000750b84103204c0c40c040340050000f251008145003042e214940c04060800d0122507241d4068410b010300c1c110716805c602000541d6101e01c3c0c1c0f182000d54030621007801913100820301140c00740415581c0360741c000c05100e9041e17210b01e00360f806011100d100e4100800c2d0f039907480034a68201d0344006092408500e001803d2415140d01c2200088c0c91100c8960402131440c0c50400c1d0f02c0440c0b502c3c05220140740f80010700072569610b04843c9508546083c0340001200380300e103031113009807108000c510401410154120090f02c030041101e0111050030940703a50301d6101c0700081b161003280d0510250083c02c60102d944508009005040c0038245992061070101008200241292400d501940b41c81c00d03084200001a070b503c100207a0001c41c1160444207181c0c080f00011007070b2207403428020103441840981c60020042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 804771258 1250 804770008 804770027
    0x9150a09060b04020705060a0b0d1a0907170a06110c011a031606020c040207060624080f0c0a08041707150506030607050301030b10030c0b0309070f0501210f020a 71
    0xa070600744840e29404081c80142e001c0d00c130340100740d60003101c00281034082c168000d401409008240904001c455151a81e4801d4041c1c90007034820003032410440300034020000000144540d4284030f0842000c501c49a80303400f0b250000a01c51501c5400e8980540040000ea503402c02d1808000c00685282609900100d03070121b04050007400bc03844960b0b0b03a14490000364085494580141c00041d04060400c4001e601c12030342201d05a541b0351000c5840c801c4400d032100d240007600600401c0e01c01d091400781082100400c0ea0000300801d0f01000410030031802942c90340c9980d82401c4609403210b16051000300f552168020300c440000c103541d41402020304142030702100e50303d0100865111402459100c1d201250110f0106a00304010400142d4104080d58410404822596030769100d550380d0421030300645c80040b04000100038048900e00c2400050007c0684051100d09140b0340000681101d0b039407407601441c9a01c141d4421182e42081c1c001203552810079008540e18101d8880140c01c030b100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 804772508 1250 804771258 804771263
    0x501020714010b0f01112e0606081e040f120e120c0103050f10050904080c19020103180201140a02011b0807080109050906060f0f1e152109150a09 64
    0x802c41008104d5500403113440d100340e2500c0700540302030f070b07080b0850502c02e0800100c0710100071003074000150040c2c00f40c800d4101412442e55044e16504001c041d50380c65003081c0a10090802801c0203020000340080b85c00d0050300d50145103c035640c0c451400644d002c0b00789410b900d400c80810b0429004480010811100e800d0090300c0c10889074440fa40d44080c03820044071801844001d4400911107850a4294184d0085c410004075143c04070181a50b42060925040c000c004000d00030b00104560301070241d45c69080c404102c6210721206500003d018001131028219154000501d14151300c0c0b00307400803694140a03800141c01400f00d071030014a20300e01101d0131ba00040c80e000011501d8030060040038059000d840003403040d91079041c00c00500802c40384032160310240d00c1d0013005003600c8d0840010381d40390468a035208103c52000511581c21482800c49090354010003000c204c10040c51030007280c510b100c01442c0e03000e03070340c8000701c614100c0d12011608a14900004014060310541c03c642011031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 804773758 1250 804772508 804772519
    0x30703110111061614040b0a08010312020d08160e030f03041a03040510182a050105090306150307030b04080c070504090b040b0a0209040c1e0e01020a0f0501020714010b 74
    0x341c07510011a21080256500c00841c016a0664814284140d200c258502c5e666481d41e8502555000341e142d40d0f80c00201e816001c0b031031f00d20042040c0490440001c0d108800380c00600150030b04280002c0848000a2241202d020011410200540f04142c031900c00c00b00a41140c00c0c038400b040d042592900719100b074858082070300102030125400681580d00460b800300041c100c40181c5071281000c0d0800104c0400d40720090f60445020039804036120090305a00c003e9180469101350303000d40c01c845a600b0103414080208140c0e0000d480029040b5401002c0c0c00e03203901d5500c0311100280c14418213900141c0344600d008203000c1030003080702c02400c0703d400c0c01d400c48034a5980d038403c0c081668586c01000e00501c141c5d10006011600c0c10540f580d1189404000624056203400082e0445007201b8400002440c4041c106801814841d04018815104d080941c886400000001c8d41c0d080d280728020710a4402002d06810020b00350151800c0b158040d6940e9420120100c0711b500074030750410f6061261 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 804775008 1250 804773758 804773777
    0x3050f06070c020901090e1002040303030f0c02071823040c061706060f03070c0606060c020f0f0d120c06060603050915010e0c07030e0d0602030f0114090a09110307031101 75
    0x20b405066014019903020780341154503880c1080400003007a00c1c005117142402084e5246002c1501440204081c0d840703610300181500202c5280b0044886121041066500020b410b02820411101102880042e01c001113114503e401001258960aa0b1140610302c03054041c403041054031444681038600030307601d02c03100910321102810f68110075214590040810800c810103d0415401568403050341d08200d1103030740940d80d41d60119940b5500c150001404519020110316144140b0344c08030404440340a04029410005489400010300040c9100d408071008198940200d03402400e03141c01550402082d03944140c0540907003406c9910420038050f56003400021700c004403196041c0e401d0441c1c155100d60302c81d06800416030040350107605001002d804400103070b5032044c1d4075060741c3c03003000003586034107001110741e0320601c0c1a0490010607841c03103001c0752592034400c4620360001d108500403542d600e0300d081a0081c190000c0c80983c05009260001c81801300164288184c2c1c082030ba100380a0f07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 804776258 1250 804775008 804775021
    0x6150909030a2a0506180c030604051915060e0115020a03020d210e0304050901060507050616030b03190b090a11060a022407030c0507080d150f03050f06 67
    0x224407032046080042041c41603640c00094201219102c0940b9002007520f400a42c0d0325290300d07080c421115007004000400e604003040c082401401c0c814842a001050103051a5840e262a0311326108240400e0100303840b00414840c40c00c50400041200100804c0001d07207600d10300c46c1c3c0010034083d8a940209440c554050540300240c00801c02d9050360140c117044d00008070454419041c02e081c000d40d41d00201e50f81d080441148202c11030800f4100055075210310b458180507100105900a000f4000140010780104102041c0681e1004920074118032243d0342c0d51040d00103020714501150148a400350f10164540d42c0344580344d030a401030380e4019180d51400039080e0303180e0b104000104207001450a0550a0910101a05952203d8019501005400704043c0a2110100b11000001d4200418041600e40500c201105459a403504074541031781a105c9079440e2044000700d41d84660341c2c261a01a0161075204000641000780e00c1210f690780c0d0b07007403407503982e06102c000000c2d030b008001c0403e04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 804777508 1250 804776258 804776263
    0x308010605030c0d0507031d060402121f0216170901030f20030405010f0e1f06030309051c0c080304140405010621020702032e140a0c050c06150909 65
    0x1140c82500703c4a4034015a5400c0c20b0060b00d40a01035106060711241030201d0080208082038104403502c00400c0b0724a040e00400044224107405152980c003d030303c00c004418041c0d5150700c0e42d020904405a83e80d50524105c0351214000503000d005c10328000c0401c1d03804c11540008184410090382c092060f0180c500c1814100c1e440815440354485601030030700c0c80104da1901540d030140c0940000201e0300c500f031400c601940c420160f410b2440c0c00804108185120654410301030103c1030000700420f0b070079694094110350550255521943c0c0080b07a200207590601100241903070b2210420281aa403141384c0c607a01d8016001d00900c8660100e0212042d051512840341201d42c1a034903800800e41440002a011540520f0044c009400300403620150b1400c001d8106200308420f080194600180b0350304841305580840080365038201402c180407401e1001e1400d03000040e5200003d0f402a0410b0165814441c2003440e403c0e900804041010b117580d5a01c00c5024100c06944411700c0740e94400c100d54 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 804778758 1250 804777508 804777511
    0x503190c020d032705070e0a0203071b0203160602030924040306020f070609050c01200703030503061206010906031a0c07110d1416090c0207150e1309030801060503 72
    0x80040c1d128034a450100b61003904000c044400008881601c5414070503c0e01408803030110036280760384203900400080b0b01c084401540921081c40450441c1041c039070007002082445005400f1180380c50f100400e6540c280500105d4020710f44a003000765982d000b01a440f074001948162083c0c00c81e01c1c6c001d84041c9141e2002c01c4008400900314542805c40d6100c40082d0444a040c10101c07000340200303000520b19201d00e0040c20700460040040000c441c00040c00303410400908081d4050942d18162081c50008401003038030b9050030825140d0340c2d0ba8005c50503103141d07016102d0841c0300e03278000001c01614a5000c0d00a880c01100300022102c06580c4400d0141c40903100403050010420020011560b07500185096590050030b0a100c0801500d0348400b10808040e850641d03001381c2a4000841c40131201c00008002d002d0302400609403854000e0f44802403032140c103042107405d040031110310b803040140e10402c4500400c5120300c440c0c10f00125005150b6244200e021900790b40020910350b0168040c5c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 804780008 1250 804778758 804778781
    0x30605060121020315030304060504080c0a1d040203240402090106030c050406210c030203150f0f040209030c0a17120310030609060902220b0607030c0b071b03050319 73
    0x340302444480141c10004c1d07000034007202c1102d0000c03a0b00401a50103000a000500842d5110b42d181d90030300000500702074510403954030030184140100041c034090060f101030310707010350081c801565450010900303000c0c00f060806009842d1b260300c2d00140c035051b805c5502850003515186016a210002502144c112550f03d0010a409000c00c02111b442181601d40e800300041c007414000341c99940320b405460b940c2e020080400d8002c810803070310100e0081d94851400d402c84103d041e928100020a003c0001141514007a82d00081c0d0562240c6003000822980100948002c030559928120b03c490b041e0405c1c0940010b001d80c0c0554041c0e111004143d9004640703204400c0c280c0351850740c406c4002c00400310103c564985807501030b00540d42d40d006036070719024052050072813611350449540407110821900b6224200500c14140800c1e4001d010221031580120f007d0210340ba24000ac1c0e070100c80034805401c0008585203820200741d40107010798041c40302480d034090031960602501040d54a0142203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 804781258 1250 804780008 804780047
    0x90402151303022206080a0305071b1a09040b1e060708040806010e1b18060c10060b0a020c0a2102030709050108010228020a0321180308090a0309120303020f03100306050601 76
    0x4040740701440031a10380c6011140b1404200d545207055100c00040e05540000c42c2c07004140f01d800c1d3b040901400f48841c400b20344440b12900b5041c3c407180c0d040070181c03a03a4000d20700468101d041202c40e0003128007810018084540960b0b4070007012000010031a040000c0e400b640d584607960601044c00e80d00d40405415803084001d520380705001c169006501e85045030300c1000c1c01c9010000d0984103e40181c003003a031000ba6514080f500c044e18104c8003981850040c000402d003000040c0d000a40880c0c1c2c0403041d0141c0310f01d0025400080d1030300b01c89401c0007841c0c80c03404000080540055008106801c50741c000c02144298441c89820102e490203a25805a040380d154000020312400c15800300324000c1c4080280010412810021114180710a00315050340101000a1540010340350343c1c408007c0e03005009007400e070baa00624615262180e08080038450108200305030094042d00d03041c0c40c441e2a500c0e00c0b4070705488403140f0140640300560f0144c2c0f83c00082601548105c3c6000241e8101101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 804782508 1250 804781258 804781267
    0xc03060409021908070b0f1243020f06011e05130f0f0c0f21060608040203010e0f120901090b0a0512060420070c050901030c090b090402151303022206080a0305 70
    0x4140c01c0800412038004541d003940d41003c940b82700b411840d0162650303099030f440386026403c0490350301903100c030903015540000c1192110200c00910581542c1c0300312455040555400c0079074007030803125000254010060302115400c41890362183c060041d20180500c1040c00044803001126070581049000643d07040c03818800c42e0103001160110100c0c6c40031041c00d01460120341c0b046580c1c94000c1070010b1452020300c01949424001d030802040b44802400c400c603080c40a603642c8140590301d0150344d400100b41c442290b03008040c0e52001f03000d10843c15030f42e0310f0300900060156100f00010104c4c0e0303074010f011130303581d003098410a0104100d00c40c0703500c0c10b824649000c0e6070640082401f1144460050404102600c071403004034000c40c424a0b4144400f030521085800382c03060808a01d02806680040001603070f2950b0403c01c0e0815009a5103076900d10381843c926041c4840d400107904031421115109030700c1200340130b2284440b00c180003001455100d0404d06e40350000d2400c040c000400611 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 804783758 1250 804782508 804782527
    0x60c0708060f070c152309030a0e0316060f0203070516031a01081b04020415020c0306090c09010308070302100903050c010b011803062f07060e150c03060409021908070b0f 75
    0x180705206d40e0780c43c548010074922000008113182e07036003101c40c061160400302d441c009458001ea5030070105107044019000309881202294850390709481940d04120b07180868500e542e00030300481d507541e504882960049002c4209100c401e2800344001c4854030244000e104c000360b20400054182c80d18100988561000550800094071103c2e1609500641c03c01000409030040d410148501416801070700c2e1010a10742098140100100b034038503240c01c0388a09072034503030700d081c0d4880c196507000c1190f5031500c156003801c034030340200300c3c0c0700016952501088005140c2c0010182800b0030308207000744102d4520303200441d41501c1140025440c40449102440006c000350000700c1d10310030741d41c0c4203c0f1007001444560168048940b410103000d01c0040c00034240601401554218000c4a00421034082880600c000400c4d00030400c95011a020000c0b800719501c6d500500181c580060101c0d5a0b5501e410040542c0441c0d0303c2252018455210300140208011040d00c0c0c88001e2019801c2c144032101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 804785008 1250 804783758 804783761
    0x7030f08060307050409050d1b081c09050109050606030708030c0619091502130e0c030f1b1c0f09080a050a02030f071a010b0f04060e060c0708060f070c15 68
    0x16001c164140240c80c408146070b00c1c1c81c13048510ba680520300400210380c4070480640201c6001a252252100b43d01c0c240c80411403000c1241e6043c520310614441464802405100030145448001c005500f42b152060a001000030f225024a000710140c84449a455051503070f0391041694804982c0c011000280b020b400344100c0c0980071a40c80720106085400347d5402c104070104420300060b190f400700e412007080a0415416014140d19079040c2e0310790408042d10034090100404010885d2400b03030001e44a0000c1c080c039901c030490381d148842e4554a00514084507101c10700c04005c455441d0030500c06024026002d858070594100090320b1a1950780502110164031410402043d84000c02c06000342840c0040105a80b030b0080c901c6030340c45202050403e0720204103a0013003504507028070101000030b02d024111402c852550030810b24800072000032445c0c41c00385000c852102e021f0344e8000200d1240105a8030310540e0b0a810000305941c42c581e040e20000710501c40900300c420a880c0c1c845000e07005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 804786258 1250 804785008 804785011
    0xf110a0f0204150f06031a011b0f150b04180309150905090106110105090105060105030112020406090203040f0308391b0c0a0e0408030402220212040c0b07030f08 71
    0x60310215004400f2000e54440588951000e030754207030051310030420346a140c0b051582d41806054a480200e41c9400020306211401241503600800324117010100404c00d6580d40e0001d90100d8a4403410000e04849801803408281f55402a8103002100c03003120400040320f02c036a50305880d200505030901c030082d0300b103c0002c003801c0184003802c2d1010691b5643c100340e141c000d10f803d80e61104442eaa44003c103081d6a03000e08642078030b070306050600c045681c000c0b069a0546810700c04031404514140002000340c4080d600c40182148000b080c4802c0c066440c00f4480c0c00740c001c0d100d203500c0340c4940c40c5011100900085884c0030300802411440202d0180701d0071100303407000801c03043c1003060300c644200c1c100c001903443d00c0740f580c0203018220b002e06110700301310018040030351198014940b50b11a40803520004000030310810f1502280010501558025610001e415500315290141c0340b0360301c0d100d0482600c0540d1a140c41d010300081d081904000c891180d589a618022900708480742903a05140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 804787508 1250 804786258 804786263
    0x605041b0f05042d08030a0207090e010204030b040c051c0809040213050913142e0612050601061706010e100e03010207060218042007020103020d050f070f110a0f 71
    0x10b080000040041030704024032204c04200321011340280c1076010f4001c0314815a880340000380c0003409641c1d801034001c2014401c90342040c07000309001050203100d031700a204070340006000780d90190500042c03000c0090301009469040d00c2140c282039413034041c0d140000005000a081003410094001141803640140000556802d1055070490700d920004280c1c0400300d40c901c2406400e03807510414802002504800180c2c014082c0c01c0510400b004900c5848841d000d403400700b01e460204a006080341d13800350340240072000300303c1850348007480c1c440e03214842031040d440018120211034411a091343c1142c0d01604058542c421819410401e1140441e070244900c0b050080f2964030710354944080c00205a200d1140d030006965459507284a101e6134601e40c01d07036006920304541c100138801c202c0340c0140c1800b05001031684500441c8012400f0f4483c0c8400c3d41c64507410002480141c400b41100c050250304291a4100d011402e050201d0304140c00d01000d00c0c1030b51014080d04045141d0b180708004060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 804788758 1250 804787508 804787517
    0x50315030a0b1f09090303020c0610060c08030c12160320030f0601020a0203030a020d090803040501020a0b0a020c0d0806040b19051002030d0c0206070807090305060c0a02190507090605041b0f 84
    0xc4e92500c1403c2200d0324a20180c011035000240c41480500500100fa841312440c0400c11501c1d003080303402001c8010741d0310300810042c0c000011814a60380002a915441004481c40d14180b034034940b0300300c00e2104504a440400e05210804280100d051490210442804042415a5101c41070610040c2010b011f03241580103494031400036841c1400105403400842d00140341c00c0c4150078006100550b03c1d131113030a42e0303002030100f401140e80c003003060400c003500000a281141c0740c01c4810002407007241948409407103001030280c0c2c0036800a1041c1e05c103032000c6504001c4003680788240035055084440d605c45440c100d141c06e00c01443d01c6c0308400030010491044a003050902c4844400f19103180c1c1e06800540e1000b820001030643c44465241e02caa43d0b03181a595080c595a903c60340d41030041d0648029405c04104d07454007074820001c03040c001c03c903400702800000150500d00d44030801d90007400c1d00682448408641424107000d814040540c1004020100c60100011600208201076560030003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 804790008 1250 804788758 804788821
    0x2120306010c06110913060f050f130207050f060709030b090616050f0d0908040828060c12051e090123040f0b0115020d0309020906010807110706050315030a0b 70
    0x81d15071b048100c1c84070001e0600061800c3c00c10b0303a410903038083c980c040391080c00b0911030302c215602c031403209014115480c4000750300c90310185041428001c0d4040e000c1c1461042008000318160f00c401010308607801410303554516210f1141040c0c0340c0038101c550f1a92a0f940b00c000898a0340b254009140459030188460300300200e0081880a843d0240e0b020b9403403c0005c50b007071204c45018800003541c040c3c0309815000440001c41c407005414005040a4816950350301a400c00a0284d880d0401a00440d2030400a0b440c10008030040c02a80d180c00b00f4201450030006000c1c40014803c8006806880072142c4074070302e40c142121091600200f040303404c01040841c034400107864544980c082e0000c035113a8011814500c20007403907d01303540b100c4400c260030021600c0250319400d0215800000a180c204119a0340c03490071340e20303880c41a80c0e4111074811030900040e056803040241d801380e400c180c43c1004d00da440b10101541c0714036840010704000c0b801c1011800c07021400c1900b60300007010500c0304008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 804791258 1250 804790008 804790027
    0x1506080a260d06031109190f09140a1a061e04020f0a020307030e1e01031a060a030e160f17070308040e040b13050318040f0c0f02120306010c0611 64
    0x2a030002080d070200329444083c2803081105900c201d100c0144150741c9610b0900d840700444944100c1014850006980c5000c00c01c1c100015404c40b8018982211203000031551420b20705a5034034109100b5940f18644c082d18101c0315075007003030301c0c0c1c0182d4008145040e5580c3d20b403029902000d510311341540c06039007046140c002401540c054001c0a20980145171100c843e401c000c0c2981c50280c41030341c46560190b665000b4015605004800c5120a10700007079101006c2001001110404c00596880203010801c501441d1b81600702c01180e000280940d40069004200a00c4183c218080c84400020201c4c05200c85405861114207110343e0340204d80300291b0b00d407161081c903409504800142074141d0204414021481540350b040030201440b00034000f19510341c540c4030302034441956800c402031301521189076100e400005c0440700c1400c0811044403c0348010304401d2441d580c880250244e49011700c03040d09030400340c1c0c1c85000181c46102e050460740d80d0310001001d07800341a41d00b03503506014003c01d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 804792508 1250 804791258 804791333
    0x9030a0f030203040305071a0a0e1c081c09080405040510030c08010209040e0f0c0906010c0c080a1e030c170f03090c01090f03050c150f0f071506080a 66
    0xc000c0c02030300950758690035811315900785903440d04850518854503442c5800000b10400b1681d036242140f030032485248080e0001030304400844482d00211410317400b100c041c419444018102c2c0401c400d19141e10703403140140280bd5412744440604400c4081c0000c00c01410b003a01314962200d07002c085091055101c2c0d55030052550b4a400c8120320b03079408150355146041c14480c2804162003d4002c04455031400c6680380d441c09401d41c0076000f08500404207455074042d0741105c01c2c182e8801d04408100f0707201e0008a541c0c151401042c0c80d600f445d652040b04024a088140680036010768654a00320340c940c40b07810240c184007441a0440c0410420714205207680b401a501441004028101d2985003000040c80e80d011500b00726081900200100005800002d0001600b0020351b1182074040d81c0c0480041c030317809a0100000b81c0c6500066120340349086000520406203e400c64600c05503040340050101c80e840c0c06440303440c3e40900140d2000c29881e0300c10101c8020030385442c105060b00c103e84c421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 804793758 1250 804792508 804792533
    0x40902180d08090301201902240402090606070f060504110607050c090a05071b050307020d230109030503060906192705070c080c010908040621061a09030a 68
    0x950342c1002080364980d524081c01340f5001400c2034000f80c0c4802c400015590000d10038000213102210614410f502000d00900c444180c1d04003008007642000000340c0303002d90100048a040b44520041c400084003843d1140540348215080700d4820321300c0090755100700c0200006002943d240c0543c0d0301c42c80103a500d90380200107152090000c0c04112810320113101d900c5602400c005802c0f0300384020803000b02c1d8400414640110b00c56040348180d1964200542140300e440d5001c3d420406521006080c4008e456210410b56410140c040c00004001d183c142250009500180003a0382000820700038030307240c5091034000342c00400c0000c0e5050001144910503489612400889a69030400040d0040709003002c0045103100400b0300041c13038032110040c03c1070074481004100f01400700708210110000d41c4100c600c954400881035079103071138502c041d108500c008007490340b1001001e90381e00c1d124030038001d550032900c1100d00035030a0703003a940d031000302d0b078000300c40090705403040d8922403020500c00443d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 804795008 1250 804793758 804793763
    0x206010b250c091d010e150c39060f240a0905060a1403100c1707021b0103050103020d0b100314030405040605011b0206090301020d06091a0a06082a0a090e0912040902180d 75
    0x14009c000022110510490500c4107031852034101c1800c00072903100309103807c1e5000321447c0005003d4501240500e6481c1c1c0802806500300e0300540c3c01042d040016071119000304c0d81202c00e411540c3c0e03142e42000b040ca00c003004994240c4c20025400d1074400d0650415540c0c00294141a10072100079890704156074401ca40140c01a40000d684c5c4c1130000207082ea40709104403e113010b20166056801003a0428217800c40201100c00040c00112041c1c034100400d0055a408224542c4540480c0003151f5179400c2230140034030031841d0900c0041d00f5030045001100a800104682e919440d8035001c0003c0350b044841c659405540800a0000d214410b101d940c0c0a095001070014141710902030203e0b216804d1600c8a00904841c1001d20000e5002000309a10114140700c0030140320195490309166141c510180450000c0071940c104402d030040c5556080d2079544d031424160380c0d2400c00446d5560281442c2400f040030030030050004685ca40c0080510b0a0b416502c1c4d615142c420300822903041d5955402e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 804796258 1250 804795008 804795067
    0x1050939270601030204030b040b0a1b1d0103292101050411090124090905071e1b030c050c0306011d070206010b250c091d010e150c 58
    0x1070200300c58407440030340245083c0303000c50416081d41d4841c28211000f4001030301011040700090410301c119040001c04604c000e0071100084010309015044000c0c6c0c000d010844402e003812039966511a104a89841c5140320180d4856100c0e1100c4407010003e9400160700051007540381007080525503802200c00810000000722b515003800c3c50591006400300035481442c400d4010440805c42c80c19a6030f00c00003030a44400318460303041d802c0e20181004d5200d0841d4a0408040254031b41e003241c40c5844500514241d41882c00c0a060121180750020f91403215102400403a403021a105061501c0001d00c10b90446d481d120b01280044c0c0780400c240e02240201c3d0b07142880d80c522040ca11801038200344580020b000550601c1c10100d9140102100c3c010f100703c114540f0b580380103901e071814065a4120800f0b0040589811841010340002c484c40a8158071011200c0d00c4200140b166000590b010f074064054400c0c5461040940c02002c0c0902a240b401440034804503501400710000c6400d50061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 804797508 1250 804796258 804796309
    0x16110d0e01081302030303010515090319150902150903030c071410020708060f0c13080f19020a06181716061701090e0a140c0301050939 60
    0x1400d5400003070202d60341c83d03000203a040c0181c5000050300c5c191a800c4403410b00e00700300d2910b00b00581c0652002541e141c070401c02130401250b060044616528020710f1070b40c200c1e000c040d420b42e003a15003400e0700079082001461404000c82d074040c09803050010060a607860140c100f090b00340740c420341d40c000584160500d081c00b030310707498141040d00e41482e1500182c11301c286400201a03e40d00010f20031a0103103400f100103858007218404840c80c1034490f00700382c0c021b25200ca0360305a4944450307403440d0311480b441550b8800c014180f80e02c0d514a40d0700070318601c159401c10001b102d0300c4030f80c407602884140c0a00030200e100388403801580c0350b100c0c8034001090703500800514001c1040d0145e02400512081c02d00302414141e4000265040d180c000002140001094140c42e2410803054005000003414a44000043c140440e00007403c3d00f003107000780025201c005500c2d880c0c1c0c82007a2501c100314426114040b0000c509482007440482501c8901d002140c1c00c004503280f800d0007008042005c18226 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 804798758 1250 804797508 804797537
    0x106091a150d0207060f0216110a080a0206071406040b0a060f050904060b150a0504090e010204080d0c051c080a05010902030907032a08071403011416110d 68
    0x304040244081250540504441c007501e208a9200700a010440c040d0009001800d201c1141c005800e04140720b2411980c0b144d5840010341e400550000441c0c0c50740091003514586c0c94900c0c110026144048040d01000c03460b07a0070020305034041c00c8100c603084411265495030030001c1c00030314400c41c0034842d0b001a5240c0f503c0907104481079034105915a9001090601142d121700750810f50055016200081c0c0100306d03000609007074640c1404000c000e20006000d082164014003a104480c2801000d001d54480440440e00b40d008500846000780c0c0510200c88180e4441d00106001c1805001035583c2c45803154a08405503101000b44404283c842c020720490598911600b8010000c0c620218254105000c0844e1683c500d84400340441e40d101e00c444d0070341e15031003c80c00300c4403140c902c2f80c8110135928030010761a0400703441410041c50110341100400c1c1018040c00d04001b02e0420700500fa942c0d0f880078140c00c40c0c882485d0304100710794140d08511445041082482d440c0482d02d402c0d020f001c01c00d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 804800008 1250 804798758 804798791
    0x27020f040b180a0e010e131205031e150102070f12021512040b2508070507080c0105010801091203050103081e210a0c0c0b04080306030a06091208060111072303010609 73
    0x3a001d10700d9408007d4048000c5410340c3e284d00042d03d10703803078050b60301d4803548601a00d0414110080038030540c11001c0c0404c1c540742e2418200460401c1e000d88207a640d0b14010030070f81c14500d01c43d070324029002c000d41500516101c0c4000603038010360a04c682c02c0080007014403109480448007202e510314004180110002c080703401c04150413224890b0b21a4a4941e030b0020704484001d4001000e1007000700e050801c002e01c00b001e4030503160040000300301c5917039143c11490223032001410035200c07010000407582c0540d2181c05154140d981115015190030f41c1034a090b080310015010154821100b0700484001140c1c034001c0c44d81004108a20800f03c1c2004001031046864904140c003e000c002405c3c1c100003002c051020340d0190700591a02e46954849012a003440c81c0c1440041c400f618105084080000d01c43e4400240e115980e9000756581d1107400540344522200011031382c40e400b8100421056105650441c0c00d0820394800c06110703c00c0d407001c20f09440307503034011300091511050400c040c02902d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 804801258 1250 804800008 804800011
    0xc210c0204051f06050901110a0f060c050f0f090a0905181b180603010b0a0b0a0915020c13020d0207060608010b181303020a0c27020f040b180a0e010e 66
    0x2000c809421142c8a18043c4400304400e11684061040c0402d119915a014600c0c425298030101c050360540e45c0b1500c2c046032400703459201114014070344494442ca5038460000d840002c0c52900519291181da140c030189280c11841c0c0065119414a8002c01d103001a4018079005442c80d10b0074660f0000440982c0d0308140100b25401681182104012203030f0b0f5880500041544080e82101c0c2aa15142c000c2805001d80c10034440c1c01c4a01404009201000c8200130902c1c084541c0d03903030035030300c0d181c0c2009040c2e0340c021100000180c0c094480201e07a03180900400314920380404005143c00c0040c40c0c40350031381c1c024802c159074140c1c0c0e82c0720802810000780640d00300d554007280e2020201001c1c1080d8000a400584140c9401c241e01c1c004408050080100030701594000c0c01c0c810302d0341d40c0d41100480382940340404e9944400c0303404855220b500c4034001c3e228000307214034504e030408d42012115001604101e41c480281c0d01400c0c008012500c40e02c020f10054443c0b1803031880c2d01d40c1002d0024211480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 804802508 1250 804801258 804801271
    0x61a04060603150b1b0303040f1b0608010b0a021c020f010e06040209040f0c091407110a170c0705370308090f04290a170705010c210c020405 62
    0x10034401400f0007550080701010360310340301a007580b1656052036048408441a05400480c0b200100340002c2c4801000d00030803ca00c01c481031740e03018500d10b9100840004a10804001c20f414900510140759410f001d00b403070304000c0c0304403102861100700c40401e0b4441000c214003da006096025600042070141e008140807a20042c0542e0a2960208113510340c0200050052010484210f0070049503040c95002491209402e2150240200c1c00d000000800d03034a0310041540ca9a070b5030100e0502180d00302c540e0340c00612006a92050548a40c01c65101109080a5000c0c00c1400b003156038801e220941c0085080c0a21040022580321004001422469030482031440c1d003030810000741034104407448102c007601e2103455003541c1c50228002e80300303603407600d0780b082054940a00145661103e0740032180042740c40903022640c8100343c1e641181c0c201c8a0f4a19600301e808180001d5002d00042881d1900c19010500b1013007180c8141c06000d18280108000907608544101c1540303040c2c00707103540100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 804803758 1250 804802508 804802511
    0x290d09170a0f090812090d0f11040c0804030f0813020a0806011e080c040b220c080703090305030f07020c0307080304140f0303031306180308011a040e0411040603061a04060603 77
    0x2e041c4141280d44104505085c50301e20000103504001c1c0d104c0803000101103502c212903801c00b081c61f1615000314800014030b140200d2810790502501c3d8804d140c00c070b0007150035071120f00c1d0f0003408140444240070b0040c603c610f41071010300041d0058850314075000041c4046e001502d121750401c0d2407030f01514800030100800c000101c806002d10740780803985805c045000c94001606801c0030022982c01c02504c100c420801c011202d0355030032400c540c0c204410b64105581d82038590b560320341e0103408071425418003400103001030001620005d040085990801400d0045075000310508000928012468000b660750703420100d408c219800003100f885052520440d07160000706025408a59207010007490400c030000340b000c0103400c0c45282c1e81b1404500d62100070b254454042820040d0190700c00f84030704002a1a02105042c0c1c2d04030b0302c800c1e60103551041c00c540c5900e841340c0d00e034447d00000c00c1e0950f903441a075030000000002c90302d20800312000c420000c1e4041c180c80c40e800300400c03a20903610250606 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 804805008 1250 804803758 804803777
    0x606030f0d0827010b180c0d0207060908210601020a03080a051302030d0905090a1109090903090301020409091a070207051002250e01290d09170a0f 65
    0x44102040360701c19000035107014103065032185030101c04038824503035241008128000d100c14002040d0841c14049105440349100303081030940644480c1401c03100e040c0c040b0010300010418110340d4008128060180b000480c00e8003194640840540c02804415850100152004000c0b911000301036400300d400d001a0134007400d55240039100d00c1c1d004001140d0581e40764001105121144034110025402034204c2e403842601142c007411100d011301980b84074980740d000050b26400140542e05181d1400c2d036034030f420030f8404170a01209180140400c919400301b03000318010398400348050300c01008503540c0031030341041c1401c10070700189014500c0c1c26003400d800c040125254000031035104403627017a14000c40003164560f08900303014500300d483c0c9001c40424086c60100912504440680d00002142ca00d00d99841c503401c541c4d900084080d001030ba104540b40242031100c1e40180c1080c9001e0007010524203001d0380c0d51714102c0d0410300c00864010001c280e50320043e80c4140c24036034407401402c0c0b840a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 804806258 1250 804805008 804805033
    0x30203040b041518080310080604020a051005120c03010f12260c0304080c010207050a0e0402060d020c0610090c020102180f0607080f0403061109060702091b0f070203060603 76
    0x5515004002503c59100d0f03000d0002e40c3d0700d42e58080b9500744400600e2a09002a0345030038440c1c0c1d8410b540d10342c160901010040741030314010031028080c80d401407149580320b25100501941104a1800105100d814004240700308529000f080c81a41040c038601d13925070500803202828800364000a00d101400b0302c1c22070015101c1701c3c9001c2c00b00300781e420a0394a80c4401c4000b850520036183c0100240c0000305000644400c006841c13090300909030282d444098969040c41981d10b168464101084c800c14003007405030501100070442d2285010003d4540701c2804c2609140c00029500c00030801c103401001c00480c0000c0c40b0383c40100300e151000b91700d04501407002100664898110078881d190440e095045952220708507501c132036000000740d40382c103091114007040360400e12003a1181801e00605c1c1b010020705108441c1e002c1c1c0000c3c0114200200b940902c060400018004400030142c1032045111400103c003a01c50300242442071641c800440c0b05060403d00c0281000c0d000f07030b1111001400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 804807508 1250 804806258 804806273
    0xa0e182a09160c0f08090301020711040b10090608090a0f05060601030c09050f01080a0b0409030f0806031f0b04061703040f090b0f01081009182102071e0807060801051003020304 78
    0x2100d410400c4d034010901e050a20440500c82d0304646c070f41c158400503421040004101078010388040c101c03002c016481c402400c0c4092242d9403100c50300041c3e22000c0500043e809000c0441d0000304020460700c40090b56079902000300390700c00080e40c1a034001d4041013070035a41405808a140324900c0d02d407000c035182c80302140c0b180c603030310050310b0500c1580800901d00c1240c3e07a000c130001590041003401907200d20b040c080c240324251a0f40c1d0000540007000220542400582a010240311104032030100d0348030005038000f007203896020750303205807100c02c00100001d15a0044040e4801e880103596528030702104480c0c841c0c1c5031b074021002a4140303040d0001030707074840e007280c80140c800382408150b80d0f49400c481d29185141b90000d10010717180404109030301901c0c003195449540300e140410007000b500e90840c42454280482000145c0c0500310900461000d444103070340401c1901a4160015164031805040404540008dc0064a03a400400282c64031103c6245105200d00302140741d800c180c0c40d4bea1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 804808758 1250 804807508 804807527
    0xe041202011a100e0402030a05070206011a040e0c0d062d05090a1d1515010201090c0b0d1401140301060f0819020a050301021206030601050a0e182a0916 67
    0x9118030f00030303d000d4441601801d501070711810010401c42d40c0e4034080c2000002420240c465800600c50740c0c0010401400b01040c1c031115414240b02107003040e2902e407000507484402010036000803414001598011074034090f0344d0280505400000c0c2c0c030031804032138074455401a500ca0701c0019034254108059100e0000c00754001505890115207030903941445140280c02920a074501e1103014101c1c02c0d1541040c54107405116184040c030100c5005c0b03801242030314002c40d00135200020341802000880600f80080003030040d80a000724203409604800304854000b648107140d002d1060106454900c1d00b031194401031311400c0300c06c040c1c090070300d40b041b036a40400e50f0a58880035030203195001076544110714100107080c002c009558030980d0a0304440c0001081d5505402480b4503000400c447c0303000d0041e10182c40c0107285074421540c1c1e41904658a081c80217a440103401200c50b402d00c0c12007001c044000b0f014482803050705c02c2c00c802c0c06010340c0d042d001b0121240504890444a400c660007407414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 804810008 1250 804808758 804808811
    0x5160c0b010b090102010b03031c05071716121a03070e010f290c030703140f1c0603021c0c080c010806040f060f1e0b0702010819150e04120201 63
    0x15201d00c01e0380c0051b4010411031116036810302c4042005101c8210b8542015038800c0c041c20180090f8a9440040e030340c0140040c0f01c22039a5581340002511349a03214202d441301c0d00740f45003442101d07500700a51002c41c1c00c0c0c1c2e035a030760540e00c000030340c1d2a250900700481c2d0010071512606000f2980740c25685400300e4000c1c041d105c05031141400032030030b4000c00140c801d440c05801103001e17a03401403001250307581d91004c481180410b00000c000c400305840503003a10039010255110504c0c00510a2013042e41c0050900001d0005079102008409030320f484950102c602444e40066600f800346042c0301e120b0040990020400f0341c891403511030917903402030815420035000e131800300380100c821006502800c040d407c160800d03400c040d8009086401000ea00c4a0400d61051085c030b01038941021450600c2403400190201d01102c0c00b080b80b4410f00c020048400150507000a41e5042e1641a418440687d6000c024a2040b0301c0510041c00744900d01000c101044c3d0008208138150512688101d1060b074029 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 804811258 1250 804810008 804810029
    0x60b09040c0e130501140604050a060e010603090804380403030e010f0507150204050f03340b0309010504020a090e0709021b010e0a0b0106020a170d0b030a0605160c0b01 74
    0x3c40c0d000c080e50641c500c9500c0c1c3c00b000910044041c1507144051803012180c5510480c00c1c000454070385070302c84c0b040c0000d441a0300f5142d01641e0070008107402403c280102100c1428003000002605110307207010895110840480c0f40c5115100c2100c400c90048412072110847c800b0041000005d8001b50320640000c020f00300300310301030310864040d5001d0040c5a03010348110036551003c88540081c0d401402583e1085814081c40c03230103001450b540d420310700d500912140f84031040d0b21504140c202018090400010002c2c1125183d0f280d81049400a031490301d40341e9120800d110452502c0104c881c068243d1140401c200940c50301000e644404501c07511050741d500194801c5032140c020250340700740816a0080c44041101c1c4400c2c3e039100080300084d900f40542a0010030281c1c40424210384158200c1c2146000c2904d404650b0090b0340218141810681e9405004c40591014440100c016008100000e19032412031640c00141c2c0b2052102c00402c0b5070100568002000803d41e1415200c06502 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 804812508 1250 804811258 804811261
    0x1317031c0b0415030b10060215060607080d060e0c1216051605030405090a110318010209090a090b0105010f021b03010908031f09091e0507180603060b09040c0e 70
    0x8548004000c9401c001c1e801904000d03011202c200020f4030282142d106428005d06aa1060321641030400307075000301401a005440d4408104144074902e40d08101c5c020304540c0b8000b603959a0b400700c0d50001d41c151529544405c810085a03400f02e030840ea004ca083c480b103919141c40780f1591a0040c030010a028601c4000080d03000071103110710281e400c6c40d0290741d0761388865011810b086d0f9032070300b0a101c0d040c0b24840c542e001a940c5038650240391121101004840d0031611204802c2581002207069103960f91f60038098107500f0390703904002c1400746490318000622046541010215a54140c0089051101c3c0102001c541c1e130307000880301c0c090041004814044d0500d81c0010b07001d05410f00020301035040110034041710300c4c00146118141c07a15540c00e50303c0706940e009007105494181c0806482030f010030014201d141100c04652400a10604c15108965101c000e801401011400d6100c4001d9544030180100f25191150584401e030840d5940d04030310701540d038460605814011070580b14074640 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 804813758 1250 804812508 804812557
    0x90b162307030c080a050c121602010531081c0203030105010c060f0903020c011101060e0402040c031404110109081501091509090305093f031b0102131703 68
    0x9054a02c007640c0b10004070f41d00c00c1d000c800103109401c2140c000946000e03900c504023a034000c000403611a40c42000c00c902586500e41c0054a4a400400e849064000907001c0000301c005007207a80e801504800000d0080d5a051448191814207c00f0b141c9400c1907210549400702c03034000064a0464000346090101e03e2028503003640a0010720714040400c03401c0c800801c08054004c50816500442a40d80782d43c81244803d4560a884440c030500103010010800b2901604042d000f43c20000c1840c140805c400b0310300c0700703070b40071102e0121810b680101200340c041c0215a4840b100348014010540100302811041d08150b00301300303041c414a881b440d542c0300180000d240442170030000b409143c00c10042d25459060190143d48036070f00c2d603803040c1106800c0389403c000b5075080110304080c0c50070960411074410f00d0510038042d16051007401b41f0082c0188201a240f010404ca9501340f1000056219141c241603400c2000310b80c2c20682100c3c02c100c061945c9814000141d540000080b0b08090451070140e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 804815008 1250 804813758 804813767
    0x14270d0c051011151503031903020307170f0403120204061220072a030b040f05250e06010311070803191d060115090302010e0a09090b16230703 63
    0x7502c0070b000701d00402501c2000d85130085041d0344280b000510450b902c0c1e00685c1011340784c2c030801044c503501c0b0032805000155030f8881d601444d8082900e080800d000403c080014414020880d46400c0c2d00e012502040100750340078a00050200c0e00e4041507007001d003869000b80041440081c5400c905540f040300740d449100170320740b06449035842c0c80303486e58405040c02c00b007500680d005401d90071010914803c010032120081c01c00200c80c2c2190b0505119200c035682d0940c0001390520039900740c4102d040308a07800ca1544060b40303603080c09841001c03d25103850618840c0110080100d8141071404079450144003c400403141c00681c42403500d13130b0702d0b0340d07600071030740520402a500c00c0002c0c0340101c180c0301c03048002c4003010100e40d06421100281e03655001000c0b00030607280c0b204001101e00d4000c00040d4000c40c4021041400100704105141d01c4100d031a048a003c44810f650fa2200740b402c3c0200303402c03003410484442c146840c0540d00e136065036200ca030ba110342c40182941c08002c00582d42c000d25204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 804816258 1250 804815008 804815027
    0x20d0206091e0111190314060904031d06040b0d0b0409020d0b0702030c1c120528020706020313030f020f0a12020f1b0a12110f0114270d0c0510 63
    0x504442c0c0b6001040d012010341c6080301744a5004c41c0c0391030007800040c2d00000202c1d10401000b000d48a02daa101e64003203400615414007002c100100c1c60041d6810b586003809403001e04135882140792a5040344414405070394520350a00d008504d800e4064016031900307422581c2040c0c20001114103621100800c91442c030030310101070a68083c008600010807a95000c40385e60194551345e50010009134440d001c01c482d4103640c44a8480001b0301ca900707003040c003002d0f014040b016030403005081c0307840d075100c020990380215659116203480e1030721081099005812698901c0303ea10042181ca2100a06665a92400079026059a00005c250080c00d442000003103001c044410942d2540c003010ba40480e500c0c0011680540300c0d60010030040344c64041e181c40702c80d2885e0407a141c0014140c10b042404000e4904035406810855116501041c00e1044001014200c0805070741d92480c81c0400c03881a00781200705599441000321415010201e100ea428200c1622400c4604020308819000251906000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 804817508 1250 804816258 804816281
    0xb01020312041a07020d020a060b01170c03010e0c180118170f100902010509060a0306051503040606050409020d0219050a0e0105120f070909060609060b0a020d0206091e01 75
    0x404100300070400005032030407003040d00a440c802800c1e41300c02500740d13110303001c415030440141d200b46a0072001c81c8040d040820f0119043c1000c180304035440c0c0b0f140e800d0080441d21035814060000040041a008409695103c12100d2086061640380c14011840110783c0401d103041041850351180c2c1c0404070075200005022284140e442c014449030f06a0302c41c19002000d05032800b803d41c400d40001c0c0e5078040c40080c1907059440902d0725882508010168200100c1c40d0201942c03424085215100c110030f0303880b41503002441644901d41450280103076a601d4005078010f0b070401c1140340040c1c07202006607038000d5049844864080c1e0a02002070580130a504c02e6038010b01d80040050010307403221055043e5a0240c440c000c10400c903500b02d0b41d6491170034070400e00c1c42e48481d07400c0100e80d0056006180c00e034400e81c80452950341c0c0f03644645c1961200e801a180310807001500310380964040180002119450014011520380b2031400c5496054035130542960307036050000441c5100c020352000444a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 804818758 1250 804817508 804817537
    0x41502030403080613050108070303050c070b0a0903060612020d11031518010b0306040b180304120804050f040501030c0918060c080f09010204150c020d020405010b03191802040b010203 81
    0x81c0500b00108811020703509140103128010b155200b9a01c0c6000d250b041c5c5400d000203140c00d0b855030b582141c159120b52032020150081c55004100c441c0130200805208181e69214251982141000d0088941c0b580c88022424040684840183c8a40001a010f80c3e04039405098184001010034140440751010b080e00010103401c02803007a041da040440825548002045050119424940e035802c080c0e4001d80981401c40000322101804030101140042030001e40f81803a6035031070100a40c0301500c601702c0755030802003428004d46c1031a0403850100c47c0d04550078480e0754507544501c580003000b030290344080b0743c554600b03069901050f400c00481643c03164003000300403940d1000034100c810a4507202e503520804000f0600d5500705009580549a00468000410f200348800360341280d2021404c80c1c1080714550f540d00940c1c1c95100743c900034500c81400a541c0d1404071603441003003071b0305024200301c1c0740740c6440f040c2040c17003182c4c4501303810340d065800150314010b40006078514000e2820400005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 804820008 1250 804818758 804818761
    0xe06010e0103020a2303090106080609030306040203071115010306141302060c031308070602070506030408120711160509060103021e0904090b090106030302010f020a08161e11071d01060804150203 86
    0x517410b45005500c1190608000c1224a4030354400c41c0e140c00d0203031001e4095910900103d80107242ca40d0017103400440c103080c08209004a81203a50521104201c0c20071101908801003041c0901405114800d82000c0d03c241d030907141c01c00c540d00031100540380c0a801141c02160b000c04883d02007003103070043c0d0071a00d400c082d4680d649010706c1e91401940540001802000c4000a040c205101503900659102040034145555a4000104000b0007884030f800c00c072102c0c1202c14a0748040c002201b0713880403805420340301401d01003400101440606183c0c10148100300d66041d540e05400c401608400074100280d41e0200d550002d0098021508080c0504141406102d09030a0561020007140d02c26002400b0901d24020210304902a1901010109988100044640c039208500103110003040c280303c88480c0040c900d01c240e031100c49114030042485000460540708042080c18001d104100c441401d07019811180300b0104810321490083c000703900042010050f00718009101409002000c640b03e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 804821258 1250 804820008 804820067
    0x7030f021606060801150b0d0b031009080a020c0a0b0f03063601060813060b011202040f05091b0a08040c05100309060b09090304210b09160e06010e0103020a 69
    0xf070200340706448a941c070b00405908208031a01d2114201c1d10781001540c10440f540383c1460140010030315890303045c0207065061140c110a44540c010190140030b01645440000700043c1c03520013a1140188600e10383c48040001c200764200302d504a00981420035103c2d2680d41c00b10f008030f0356002c0d2844508600303000c0700004d02884010f145006840420380d0140c2e0341e80780d9040e00c2d03e0b00c084c0c2e4650341200c0c01c0b410b040302040454109112144040c5403148051451100c2d0100300d80142e04011a41007039940200041c1c5400c02c010740e000b0b01c0030b0b2003520340504032082851442c07040203541c005202905000400b80010700720050010100940041402800303594028014441102c044417010b141c02c0c1c5904c00d60518800052195103103800661405003404443c10003d4a840041005451440d5074980014401400d1038024038aaa004002c184c40c03c40c01c01c0c0b071100e150f030013421081c080035040045030380e0300409101d4000342c02e0800603520007800e1000c59211000711324211062604e02d400e5080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 804822508 1250 804821258 804821261
    0x1e0b1b2805070614040905090307240c020c0d060c020709110901031109090411041808070b0c0703090e04030c1a0901060f08060417130e0405010c08090607030f021606 73
    0xa01a12600540b01c000ba228841038448021411280a041006000c02d00585600e60700054100130f0031030450341030007400e40e42c00e124030034059030404040c1c038107030700d010f02c4143c0d07500801643c0c400e68000b40a01d000340b40d0129a003a01c5401001e41417a4a07140000c20f264003d208000240001c0340d400d01c1803500c5a0f000a803075a0006e084030780008d240041101001166030103882201c039000740164a95207403500c1d000c40c0d040c0e140f1410b0313134048e82c0c40009650001c0d00e2004501c040b0f01c82c001e8944c943c6080c4c1490001c0e420000c10070583c0181c204041c00c002a40f204d0703004251040071024080d140c4650030f044490341d282041c0108540c0c2c4241c0790030b4440803050354261107200082e00074025aa00c500000c00381101c81d1155004d654095804240011080c840300307030a029420302001d0038035644280c5409500007561200480c070300740070240b000b4003400303025007803044203107050604060411000301c5076612f000400300410580c0e541e01ca40300b00b240e5078040320781c036005a05940d5406e01c0300742030800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 804823758 1250 804822508 804822583
    0x1403070809070e07051b07050a0311040c0801210528020f0a14060d02070506100e0603010605010509010309021f0908061e01051201090803101e0b1b 65
    0x40951184400c000340040c614460341c0e2203404c445d6601401c6c880c80a80404612000c014101c402d8090882d0118050f1a203591040046000c2d000b02d00d1460011300c240000c440040400310108441c00c8014084403c3e500140d0240200c0c0c07020314160107103e42885800c000c0c540e228000407040c07000b05076810440d88203403500d00714001c646c0170041d40c4450040114420482c4074031046c400c6000c92010803480c01a000c0c02072070410304009031038100c140e43d0f440e08010040b02ca040c083e40c446c240601c40546144103031544550154002c00a0070f00b0030001078914058201040d040548a40d403000842d203880501041000c03060650100d112482078001e0400050380c01001400c2c03154400194005c0c40c80c41d40341d0090380c00c0c2c07040c000450342030005101f48020b0705c100500307540d92181290000913034154019807003050391041d000041810030082c0c4030f00d0f8407004240c03101c0c1031072480d06006d03144540d0704490f02200c44514180203041c2c2146902c6c248170100031015951400700020394119409203c88a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 804825008 1250 804823758 804823771
    0x703030507110a0b09091320061612140a0503010b0a0302190e100e210312070e13021306031e020712080906010608270303160f030902130b0114030708 66
    0x711240d6660050001d41052142010b44015030001d48c800080078030b01d0600030301030b9018040900d45501441a56a160701c40701e4202c810308042042408042c0e480281071007030114400c40c1600c0d16100d00c800410b81c1c0011b00170002070541c001442940103000303a0442e0502d030f2100120b28000f1000304000740c41c43e6159221a03024002440381000024840e00d40383c0d800c0c4100502110074a00355110018204160384c0381d811052104015505040b80458040381c0305003082d5456020181000c2300707003c1583c0518030544200350060002494001c0340e4450740c07041d0388041c43d0006a525040841415207404a0704201845200003030800c14061070b0443e00448421a46600045490300a0242e07507a80c802d106040001d6840c41c0850080c1d800300f001030141c0422101585010400c40e000c46056520548601f0201400300e0403115410303802041e5040e0442041c00d00300540001d80d008203038440340c401d0780740c40100d594230180f01e60b03a80030307801220b01d0040e41e800d10741d1039181c0807101401900041c2c079207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 804826258 1250 804825008 804825019
    0xa0b0a0813050d1211121501030902180105030c0409151a130203040b011406040b0a020c1f08010e13020103021b01050711060a050415052701090c0905090703030507110a0b09 76
    0x41e1254a651842250f14104c2d00e28180700f847e41d908800812080c09804040741019180d183c1e0002590700c0d4201d0146040c01160702c00e03115403501c41014904040244e001d40140c1c00d042500000c540049112400003054110109049d040750000080000030302c624954411500c1e40400d40b03661195008e5031081c0d1080008804a980b603a65001c505c40d0320700c0d4410341c0b00108100c11f00036204554050707e8280c00d6030046400000038980051024207e011580701480006051400550760118407580103290030011004a41440351007101d5180fa4503030041d0515400080865103c0c1c01e25880e4030b100403565001b0006400c211070300402035946402c01c5911031048a0104e50401010700c00d55001b260300000d03803040340a03098035500250400501646420340c2c52920701001401480240036550b24050000448065914160b0340981d260f8104d4001d052a001c20018059800500395090300e800d82415a12445945040703001564000f120b1070b0003104110000505043c0400644807080080307a4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 804827508 1250 804826258 804826271
    0x6050901080604110913061d090c042c030f0301060e1f0f03050606070b0405010c030c080426040f06030614091306200f0406030501050a0b0a0813050d12 67
    0x7000107403550300b0380380d4060343c1302041100c0040c5001c10040c0201e003082103021411b590795610003d200300300900c0210111114504202c100b800601c6440075000046600300110b68800c0011400f180d40d029100c452044c01001c40c0458503810002e407100102d9424a070303940d030f40c0c54003001400b06243d0403185020346411603a01880882c100c040760300611107030ba11a49038080180e0101c0241202030846a003211007084402c0c003042c481d10090348110300802c0041080382981e0001803c545070a08108200040c000a0000250141040d1300029100c81c40c2d94145074048160903a45120759404426406408280006c006800d900150700f01c8070106055401b141c445000d000010340110b0744410b45104110740e03440001c000f07070320002200105506078403031460040400c001742e034082d801c210404035001c6000c20000344d040c014980506020740340ca4010030724090400c2200e024404e40e09007031214041c005110309050030004c08005d03030444219501641c0c40b90024114114040760b02e450b0760709001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 804828758 1250 804827508 804827521
    0x15090b070504031e110d050d0e03030405011d040b0a031505070f020c010f03020f0a0306030b0703091203020c0a1a0a060605090a050108090c0a1710091a1f0605090108 73
    0x1042e00d080381d0700218421044240c1c240c0d0110a181c0034071044810325482c5002c00aa0303191a50804601e622440041454200e641000340640711400c018a109900c20001884140d038400d4020210292501400d4402c40c686070025002e0124040415044500b2803400410701510710ba4000d03880e14040c1d0100080d84518a0446503928684240c1026a01c101441081540704611007202c01985150042c140940c0c4840d002c03c3e50302442c000750000f80c6401c41842817200f00019a50813040c4c03030508001c0155a40d03203100300005000d400340c084c9a4041100004a00c0c113208998006901c42c0f91000b040f0404242215030714000d0f107800d03481a281c1040803078503034000d00c100c5803108001010791010603e018011030f0104030040c0301041d40e0060306072030307a50340e141d10301200c0151100da19a0701004002c00080c9103080c25a00002039060300302141e14000c501014640000c050142500300303103540c1c0b44000c401c01e06026007410744a8444440000a04c0f550041c0a8150380100340c0e10a6203a0b2511b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 804830008 1250 804828758 804828767
    0x302030a030c09050a0e18030f07060b040204080d110a020d0b18010c02071a0f040314060c090d020d06180b0a0e0c1005031815070318120e0103020715090b07 69
    0x44c080c041d00030701403038024070120744d411240e90f9002246c608801840300c51600c099085400c42000e12441c100c000c21014100071076401a980c807000300f6601141801d107803c1714159038840e400641710900c21001d01c4401c6458082c0990365203160081c058107080301c0c2502c1c2042c40e60b030084550103442e04051201c20030245060090003c12101d13640141402070808240399221400c89419090759403003080401f403d00c400740f001d0001180111082c80080d62409120317428800010140c000c421401c100909069903082d0030f100c595501941d584968641c1031030500000c00c083c20b465003801c407520082c001084a4035280c50b02c6000e61207410f01040c0c0341d0540c01a07885980c0d400941c2d1220b0f0396113031601c9081c4104080e550040801c941100b080c283e104200e41080e5928520040d5881c1e2802004074044e0180110981c484401600380300b0f035541600d903020070104d0395105a0404c11900341d940d030281c1c405c0d0180d542d2036400603a54a204041580b4000042079100000c8990103003000005510a005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 804831258 1250 804830008 804830027
    0x212011a0406090e07061206052101051f2705040f06060807030201020c06071703070804030306060504150804110415030b070c050304031218061107050a0602070e060f0d0302030a030c 80
    0x131070007450b01505180c0191100c025100b1100b01302030362004c00003100d54402080c044500d00a5806050950040c1c0340c4900351940184422408030b20001a0480402400460401c403128a42008460a00608030841c1490786a640c0032003a4101001c0c0030174450b80800034034500c2d100394800c1014565400e60643c0300c801500c4041d0140c1c020b2806001c0501706040180801c0e40704004001000c0d03290b0098218680095500d04005545201000105605440755101810b040d0802508091400d40901c1c100c10b102d1440c5020400c40070003180810291070300c1c3c803140210080040c001850369030444940711040f4482030740c149070145d0128000c980a101580b403801d8114000c1c51506013036454015460300d10200c15410010203d22003502e100c81c40801c1e41c05400f06684152480e4070b8103d45078a0025160400c52081500300010401d844d00022250300700c0d88481d0400e141da03038070b550005e2507203c9560f42d0140c110018882c00d01c10194044003d05120049031010040005a6042151007480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 804832508 1250 804831258 804831281
    0x120105071403090a0804180b09040c2303060a231b0c030f130302040b0307081b04111305100309020609091302040903260903160212011a040609 63
    0x40c00214800c419071440020360344035907000100c85407808655100e403200e0703010350b000302c0d990503501c000c0c0c000001880c0541540703580101e8900c4850300301034031520105100c6d41700d15080c031114160507816501c035490580780c1820000301520920300d005021100603040c000180e001080c03c0443e0440401c44030011140220050100c41c0c0f40001540710750f8120350700c02e4102c11003d02c400d000498210310524001c00071032452403071100c0410321354414801521301c3d40c411144a5049200c0a0001c0403000501808000e10614030b14107110a00020a000f000c0c0c02291031480785c00050460507444540904004640e002e80d07a802690b450303c0300c214101c50b000b900083d131242d8100305900040c544096120303080758110540075070034040c6e5070010301200d41c0b5890440114000c5002904185a4003030a0f00b50600024202403e07464103d12072501c130304c25103403282c07a0652445210303815034541003403582184900c600200241c000500d1031a190b40c9021951a11590410300080707540842d60081510165 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 804833758 1250 804832508 804832517
    0x2010e06071b05100902090a02031510200109120206240f0d050115060e060d0e030c0a080405090117030d0506041b050304060b0d03301a12010507 64
    0x110340c44800c0300c400007a03054081880b04960704040104a062140301a1042040000203040d0f1241c0b05200840d5001404050b143e4410300812000d02e640705010342c0368440c120b924240e04806080182d804031500440740884a080c40a05040c401055000c032500b94011264103031031139020801280d8a85d812569889068024108000c107448034020003801502c0c01004003141d003134084003068805481a4080e5226910f81000d4800a04480d1044002c4c05e102c6c9070207a016603440000c40c025119240d086402c4640e504042c0385041030900a031030a2012400070758040c0c3c501c909101907260404c0c003800c1c0c07003620403400010b04492001d01144401d07e51030091030070300710030304645002000c0c002e040c00e0700300d80c075140c00c183c10341151240480500c10503202d0302c1e00e904050078124222001900050300411001402c0b030040303074204004100c4504020a01f01c43d0002141c90b103400c0760000745800054606000c1e40c1c08070442f100021105c82041076418940c808100044207007a103200351060f50105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 804835008 1250 804833758 804833761
    0x1d030403080307031e290a050f0a0902070803100b120a3303061d07150302160c05030d030507080a090302030c2556031602010e06 57
    0x14040000b0b10f40c01542ea040c0010600d500100012080145044505685030b60f0f61500016140707245c4000a4120116050340300c020780d460114a486607a13004941c85081303600c421380700c5a41d400c4140c40c040e008452041d0345803042c5203031030036403070300f066520a10701c201031f000c003289a050700010703036980100d082081c60b1151202e076555070042c0406403038020310941c0308040c40b818507100340c8181e0542c2a14040e0280207442c5003041002c95110b400f00b0824014041c41c0d4003840900080c2c401d043c0c1d54503040040c40b0304002242a0001e1065415103c05c014140d50040c0c28482c4185121040750000c4e015600b002d484030000304c0c22038808681000c013058a0501003540c074032039a402229071500c0b0380100c1c1e02d081c0040180d2480c20304481c0310048418885c5004230708040c88405110f004222400160070b070404800d0000e1060701d010819800500c40c00c0215103152404540f0707101c50a402c41c2c02c0d070b007015448010707941c10741d901c11268050441920140e5441c079501c140300d042400f00102c400307030229 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 804836258 1250 804835008 804835013
    0x10020d060e010b1c050405010b181803130614040f0f090b03030c0a0311031e03091903080604020304150e01060305120a081602010e060705041e0302010e01081008010c02010504061d030403 82
    0x400001c6c2c41540d50b59030f100003503500394441f40e2030a40282103556803003c00d0700c0c0600500704056202c581500c1c080c2c0003400007950f00c0c2c1c80c2c01c006009030351017424154000244003245c015a40940e51040c03001002640d0002801c000d12501303001910806081030040c0005001419542c0c452002d5611055220841010200344a000d1341300c1c0030f044c60402c0e01e107817040d0840c21010f22111035180041e400400014803082c201c0400c00e80312490501d0344100f25040030341d20050b1442d1001415640203a800000040c10401c02520f000f16910f60b98800f0841c2c200082601e500800003404101c45e203100e03140711010542d10305016580141995a104001513880c06141d268904220203c80b00307644d2112016100f0710800d000c02403003240d440d640e040c3c0300e41c0f601a00340801c00c5480c6502000d200c1b11441400580d03070103814090901c00a081c1110a901c6504401ca00070b41c4981c080d99095113800840c074a8039a042d040240034900a102c04c0c85200025000d41c50040300001840b04185d1040108000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 804837508 1250 804836258 804836261
    0x303050717040b0a050408070518011e090222060302030c16020f0d051c03020f0f03060d0b0a0b0f03010513030807030612030c1202060615070510020d060e010b1c 71
    0xc030255025a160b042c50340e500c030005007075000450060085034000c607003404090001c010010090104403400c03441180d8150b1044110b078818000c02d038911690f117045408620b07010904000404408108541d075049a03048102c1100c0b2904000302204040311000a10510a000b9240035448801640e8031303040020038030020425506008980154401040c005a5070307426001a5880b409400a44070345110070400c4031680c031140441c4400d043c0b040c0841c101c801d80d27600685500c80750003583c00d42d40707455400c0010140510f22000030a002c2030101040360101d0b00f9000441d10318000d0340d072050901040800c00d400e070750003200c201420ec2543c0390a840032a00c0f40007060f4000c292410002012a160f1801420107404080c0c151f011680b400c031501c04005100150f250305480310720280100d03061120000f0991000c00c0300f10300e184440441c0790000c1c403805000c8102038049501c1d0840d56003062040902c094001482036200c001d40c075400000318514035004690f60844032000c0e010000e404242580d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 804838758 1250 804837508 804837533
    0xf030b0a050409060207050d0513050108040311010509071e030f020105031f080a11060c1b0402040f0e0a0c0807080a0f0b0409030e0906030a0807061a1c1b03030507 72
    0xa900100340300300040c1589882c40703040e0040c1c4c0544409a0b4032170303d500b451850602084040b404001e8204080c0500350450401030341620b100346404600d03038a60303003422075140d100c0b9100894954070300000e00c0059840043d1001c200c07800d40d403020503a104040400f803011440c0c0d00c000b80c80c019080c0d494400540c8280020355104490506200b06007850010300740c0d00784601e4004904a0384003042203002c1c44110103110088010031a8454981000c2040d46911540e900940380c18080c0c1000c402c1500d6030700d40d01030303e000c3e04541d07056121803a595400c084e02501c0c203461900c52a407408164064861151607000e102d240c05440b80d0000d9200c041801e00184240380c0304500b0b50380d0310743d5a601c16036a40c2c0201c1000b5130295031814210109031007040708005001d4500c612907409003540c8400aa0410306a0324023030340000340094486188425080c8031041c03800f44a138040c02e9640c01c0d4000c040010801b03030b402801407100400c80305002ca500d0075130705031f14007010b00419400d1121000095403c41d406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 804840008 1250 804838758 804838781
    0x2160b0714041a13080f0610080c10120c0206180114070503040c03020d050606090c03150108090c03012c010203010b09130f020d060e090c090609100e0a0507020c090103030f03 77
    0x1c510384005080c049142d5003194000f88069004a1644c01d10b1b107000b0054140c11215009209941c10b261240311a0750b03560003000c3c03a0040e40d01402c80070059001d41d410445c940c50b008018085c0d01c230340300f50003501d80c502156007030310300c4a00c100000c1c42c290381445040503d0b481141c80f140e140c0c8441105943e9900004e008a9403e03220250200058403088049400c0a00c40d0004280740d041001c02c00c40d0f0010028032100307140d2028802c218885180d0304405045420070300341110b945e181c40398014244a2004a8117802d5801c00284d4444400c0e04903072000310001c0541042c095140e22041103082c1c0c07000b0b20403182d00350400c0c040042585402c07810130800102021000405900001d221000d90700301e00c0c1b402440756a20306d01000644551a011940b0030469005840c0c00005000002d040301006072209000f60481d40c0051402d40343e4440d02405440c64a1a41e00c251401003940c8015100481d03c4000500500c140650642413010540d810380e60b168440b91100c14529500711700030000c80550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 804841258 1250 804840008 804840059
    0x4060221090123040e160e0a0501030209040e0616080c13170a0b160207050607020a0603020f040308030c090117062202131502010605060a080112060f02160b071404 72
    0x10f421150220800400003000040290403540c40c068594020003048250f580c8140f002d4103450030000c0c0e44041740c10301983c0090800584400340603003c500140510301000e101e500c622018000c2030000214200c140510640d0799400741d80c0d402240c5003180c0030f04000b90020101c44ca00900409244d0708440c0004044601214040b20b03484d00e41e0074001d6400e0300d2801d050341100c0381d140c3c0c00b00c1e814440213001d40030545a9500e400f5066011480710582e5109000c2050350200320504911400400ca900071038220240c0c5032282010354040055900040f801c0c2d010071000d80100c40014598200366202e648014401d200d509202d400501c0e1711040020580912542040034080d00f03546600c2000c050600540f2900280314a8070002e0f00b101c41d5070700107601ca804140850100181d1016a180c191020304204030380400321447c20381c0241c500509100f41490000c110044040180c8417429012030065000e044907440d41d1f03c06542a950f8182118040c0608000502080781008549509080500300d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 804842508 1250 804841258 804841307
    0xf0c0f04090504064505030711190e0115051303030206060913050c100905031b031501080703080c070b040b0702090c09030a0b1008030c0d030e0c010e040c14030903040602210901 78
    0xc1301800c1d40d10221080340ca00c5c4000050300b0f4182801d08400300c0c4124840cac008200c0c2c0f400c0006005015805107d43e01008506081ea64040c51080d400d90310020041180b50324529103e14010f5121041210018080c0700b026000402c01c44240060420380d942100262003c0c000c1b40040c850340380d54542a040c14800302070303000901c5031001c210b00c81e02a1021001c00501d01d40c000e0406007410b4150704981e40307521092005100c450400b04034003041702c3c1e00403400340d5034081008485007001802e9002406e1440c0210300003902e014100d008010442c42159600103c2c0d949030ba104010f4001d00910700c0e0554041c0035100001400d00401c01e0b00700c801030501850140d80c2e10016841d41c2c3c4010341e0b81c1290b4101c00c1d114221242c05018018107051600c000d01703005422180024000c0080c070008612031926014601461801444114000200d4070303c5c141e641e240c030304500707503a0341d004ec07040c1030040c4201c03060505140981a102c4d140e4040b80c050700ba14203c031203001101c0843c041e004a05490101c8103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 804843758 1250 804842508 804842513
    0x70803040c14041b080a1b050a110616080a0615030504031e2001110c15010f14010302180d060c14070c0b03060102030409140f070807080f0c0f040905040645 69
    0x4041f01003120480e5901542c0c0c0b54100c0c8014510000295418015440300c0240035086900d5210031000342c0092816004503038905a03400003500d00d541c4034800000c8210161161503a064200a01ca40e0003a00d45d1814085d1030a03200d0074010340740307144000207100b0b0004d0a801031100c0b202c0f0107100791034600100d80d158180b0f59840103039000f02060702d00f950100d03004400c80c814164040d40100300c40b0f0000c03030b507a910300900a08a014200f00003810950300240c584000182640c0c228000140030b80307040c0b00060300e841e007080244444000070001c9409940300b040e40407111801c8400c800d5100002804481c80c01c0b00000e001e810117443e042c1580020f02010030048140e01c14000e4000e541181d203502410001b589441c24800500340e035040003144010089106d400c503a03026008400d0748640155a40c90810b141d07071a0150034004001e0017400907001580604a401440c00307240126010040400c0e1740030050804035120400040c0e24403004102110000710181154215600b20520406280c3d40e6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 804845008 1250 804843758 804843791
    0xd03021b01020c0615060c060712090519060510050a0b0c070b0d05160c030206040f05070513090b01080a120c050309040e01021305030c01051e070803040c14041b080a 73
    0x3800c1404560348a0000c0041449176000302500c010810345000749040c0c03a0103155525184020042c20a100403080e0b80755404070b440e445040390a8001c1c00b41e035000618481c100b00259060310050320494200008903104070b031030069010031104006c01031245245850740740301c0d10340c10040041c20f484c080c006000501c4062075004102500c0d600000140f07503d0644001290201041503400802c0301c1000310034000707034000030465001070300325003c02c558026502c0c1087c07a00c586900031680020b54001c8201400c24a908100c84151050648240580e01c5d200d02603500d05500394090918440741035000207190080c1c4800c0c075194000c40c2600e150100d1071005ca8103480031160302c40d900341e500240c00c1c4241c1006501d00c40103000c00314050840183c520780024103a004030100d00000d0708060b2030710030324281c00c0c1d411540340030ba100d0080c0340c5074a000d051203d4400704611031031000c07070100180c00c44103140620404000a400201710b41020004510403039003140000c00900d0241d80d2100402c12002b40d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 804846258 1250 804845008 804845017
    0x30b0d0b1e09030a0f0309020114090d060204082a0a03020909011b11190305031501022407021204081c030f0e0c010e060306060904110d09050601061b03020d03021b0102 74
    0x381c500440c1e07110b0413201e0041640d881000050f0030149802c0e186030041c6c0c3d00c80c8440300444800804992135500d0000010a0401781c074900070100c51001034005100030001c1205001e80f916078000340994118a6000304100d00c01050099110303684580600c014a000d1000c10b40011a5400005030400400780901c0081140c10365040412160001c8020342d4404001040d21404100c11401e0411001c2c1d401030a50300010f01034043c49655400c0c0003155910800c64441c101e2003202e007500f4200804803134079507141c400f5503d00005000750b00d841d036420440309040360100c41c458001811155031000302d42146441848405040580b40c4500c02002c01d03c1340150007400c08040c01521003060001c2c00035003000c10b000069801118140200302c8165941000e483e0000815200862082c100c6a610308440c0700f410030702501e0354602002c0380240540024140e058030314546840c0305c52030202890032400c482214009005074080c07443c02203528420f401411003e44074007021102c10914110303403800c0ea0007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 804847508 1250 804846258 804846271
    0xb03061b070b0103030c21020c0f011101050112061506270e09100c020a0203070504050c09090108073f170a051c0c080103110a030f05060f0601030b0d0b1e 68
    0x1400581b8506001d800303068298140c102d50307100c0685000008001c0d442d013071540c01d003500c503050480c0004044d900540d003040050034018020011581c5030250b4030300012001005941d024541282c90755141c036510003034025151180c5901144078030044401d128201400d2502d003920720749a00008040308078080760ba006004081c040c0200d103155142d003074200d032041460382c0110b50210001c40c3c05a04c0c0803130918155041a0781c04a03945e56500c41100d620f01c13401c010541c11000a500010340c102001c00d07000161890441c22407141c421841030018a0b08400b07d544ea85d800c059040301010345d15068031114450700c0703903540d01c11988103c4440c003050b070404a200d80101b400082c0a502c141d00118000202c00e076006410045481a07020003130607001c05000c001c3c07041c03021141021650340c910b40308400850744600305141076030b00382c6080c2780c5076582500d03119080c041000c0031030001d46c000d0081102e04032003d40620885090303500c0c0e0130342200001c2d00d841c00c071a4200c03050500510b00301140500c1041c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 804848758 1250 804847508 804847517
    0x1602040603050d0e03011505060309010b190807120b0f09070b21060a15201906200910050705060a0501050109080303010f05060f1209070f08010b03061b070b010303 72
    0x11007203c3c000d0b03c004041079009119914000c01145a140b10701000810f44500362241a00ca580b04005240146500d800700d9604c0013969011003181e4032421021400e5890312015146081d03a80c1000303480418a0840040561141c00000744110400e4500c540d440b070a035108079554640e803141c0041d0140e00507400c076803072541c030b0380b80043d01085510b001c01e41100c0241ca40c156503601e030211600c81016107041840c20402511144e038800302d1040e40c918004da0084041c0d135500032214050f0450284c0400e401c9901c42c0c103000030303031810007000416142c2100060700c004d4039100c8020108148550710051a00a000041c0561400700e81c04010191044041180c001002e50504c0009400344586601c60341c56644100014000e10218010150440740f003541d40540300d017541c50405006001d01c0181ca2070241c2c14904015546000260380c000f03d80c00100c1086c4143d4032000c1c3d0a0030ba0320202c2031103425a2242010aa42d070707800d050050404807814003260705103c1d151f030715501820f0003a1320640c00503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 804850008 1250 804848758 804848773
    0xe040c0e0f0307030f290a0510050102030a0f23210906070207360506040c1403150a030b040605160503060d121101020412060b03070e0c160204060305 66
    0x6040055603040007441c11401403000c140b4507034806200c100d0701800144050794507000640030a41403c1481d8082101102001d1181ba0080400c0020801190243d10070382d0f00f00700c006803c0d40040308a555810860751201446c030485c80d015260f96510000038001300303202d42681c003c0381c6207010103400c108807002e20000b90a42207403c401414000500002c0e0700e500003a081c441480e800003400c800300c0340c214000031001a040d5480c821103100c0e04424008485a150840c0c40032092a400f9034816136084404000c03c0244c50030480d2511180001074a050b50100041082e03009a00840315039100024400c60540f6140d948800d2442005e6804440141c0c596052000a03c0344600d160b900c41c1e21843c4c06030461074410001120b0b542c001001404800c800b01da2110100d115130099030b22140200025540c07556a0424000310103e54072095031078524216901d10300d4074000c40d903c0304603601d20b0100c400d00c3d2581440c00c0c1c01d580c081d200407001c075412403004000689842c001c0f48010b60244010340f201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 804851258 1250 804850008 804850037
    0x4171303080d0f2306011b03110f0609030417030706091208131a04061b091d0f01060516050105040f020910030308010b0702040609061e0b040b04050f010e040c 70
    0x159000201e00c036640c0ea0030300e43c14180b20014000c0c0b1003010a280c11004100d41c445c1030060b6003c01c070000f243d00b07801200c80701c40428140c020141803554549001201e800c4c40b01c1018007500c5200554189075150000c02080059803280c4148035240800842a80e1814589946000031541081d10461f81e205003c0b09550090b500f01e40810781c0071020382011204c644c8595103150410401c02380f003001c1d01c05040701040c2446400e40c00010003204403110081c003196a4107000d01171440c14030a600c003095003051943c060404aa2609018040040600c442a401c105003a1001d030025400c03035044860300e8003042d0100f0000d0180d9070043c3e0081c1c0c41d0310380c00740c0d440c0144072040703a008040c80d03c10201000108000f99001c0040c41c11580215001510303071007107200090151416900160900f81411404a09040202540f12545003405441c0703035081c0e644d07554062035000d01c2c425000c04540c180010402400d203c0720300c240c2c60105140100c403014031040060111400c1544101c0041c0100144509 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 804852508 1250 804851258 804851261
    0x2007021c0f050d0e03150406022b200a0305040510090c15030209030a1e080f0301091d0604080f040b030f070e180402040e2d060609040b04171303080d 66
    0x201c1181440c0881c2d031381c4103003004a603480c0b0802a06040c0c0c06400400038045c41080e50545c0d044840c1c00001d00988a1204040b5031501400c2d100030001c50703c4c007c0d050007071a4894502c110507541c0c144119042c0a010314040d4028038000300181e07a20301030317100d810454030010b12070108031520842120f042c076420001d210501d0754060038a1001c0c548100550300c031650340040c40340b02c45a072080c400b02507030441c5546101c00300201840206159808201c00140c1600d1001031030580d03031a000c007000780003e10010722900311030040b6031010740e03003000c40420003180d0000c0c0204050440707134801c41d1805680300051400c980c001c0740c8070038002ca004800c0c41031440c1d10401c5220f81010440760420581e01d0300c00036091004002d00002d01c610f50ba0180e0303400310401445140c004400f841030f5030b51016200c030501d00d5620090442101c0501501000500700d14040400e07034003030703504100c000340d403507440c2d0340d440b090742c4d4100d1500c071841501480041c0c0020041c10008000d107110b4490940c445401108420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 804853758 1250 804852508 804852523
    0xb070e010819050601021911040506061312060b060d0b09060415091805060708010e100f061115152103030c07060e01050103030503192007021c0f05 65
    0x1410004400140321200d0780010410605040b035080c0001c00f41c0740c080040c2d190640301c1c40c6020401c0c0c88220300728240b04282d5100c00c1a0001a50b09200542c4c600b410055103100e034030310343d100e0f07442d80d440c0078040a48000c54651000e84a01000964030a03a00005000c50b04421074403940030b0340f5030800c03d519040c41f4141e5a0001015502884401d00b8035404541345442d0b0b02070f43c01c1403503540183c03400d00c422203101d032202c0d40d030400c05950302420a07100c002d101c01005d005042094101ca00841e000382c03548035000c0d0440c0c00c0e094402080c0da0609c0400c80f00c8900440301c4a03d10311400c1800340c031410800c40d8103405554224041b0741c00004545c10300c1118280414603111a0003040c1f42c0311507580000c001c0380d500418216002e590350b103251a10600411050340403141ca580303004000310030160050011405464401400c6000c0b008414840c0141d441014203c0d6890400013215070341d65040d00080c0c450548001d090341540708900001a07402c065920040d01c1000c3c00d14040b6050090074020312 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 804855008 1250 804853758 804853787
    0x70b070f030506030606010c0c0f08070f060203041a030c0c0d0e030d0216051909020a0c150b01091e120803040309080f0a022407060e1204061205040201020a0f0b07 72
    0xb0b10042c03400e01c00294603242c0082c0620b060004000300c43c001c020f882e0080001800d85121020305450310381090641d200207038018661b2550314a100840c0d960f0001003075804550701c00c2e0912a442921030361a8440303820181404285480902405100e68070a10440d808116190786810842d08008105890045104480f030155004003032100c0140d41111181c20907150b0603296244031001d80e031105001212160301c030500ea0303803000c00c40f0b0526960001c0446015401004046084583c160070002150040090300740414000d60007007100c02010886141540881014068880d688112048028411401c201d890b4180001040201a00022500080c0044a0042028415161074159201c46d4803034041c0c404c07248540780300071910800248580d241000064541c40700d000d403808201070007c0850f556824011a8003a1030030182d1042520111001641d8000c4e00c012b140f10f05400800010340180c0c11401400d01c03004c00303e24283c030b60105180c811100078481c1d02d406500101900b00036582c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 804856115 1107 804855008 804855011
    0xc06030a1410060512070e0d0305030402040608060105030706080a0b0a080d030e060903070602090f27060103020406140a020109151e0509032d070b070f03 68
    0xc00398204858407072140e842d845855074941081402e010340300c009074040c0000302e0a081c000080c0d50304800300c3e041040c2c2c83c1c0001008210010b0041c0f80a40124a0002c02d1104504041c440d003030041902d500500919410040040c0e1102d8042c415003003000814004280c40324507942c0441840000100b2001c805561001569210170305241c481c0046403409415107400b110100307120b8420f10359032016600d05000e640c2c500f002500050b025a401161080d0310360400d40711450340300000c144400850b4070327038078040c1c0c0b000300f03405002810641018018042000f540b60440c030a1200c001510300d03840c0e180c0e080c0c0c0300224014191080085d141c42d40201001507004510362010720311900e401c604158a64540c00f400003a0792080d00c13103101c10740c02003003103070010800910f40001082c60351548030300b0000d42c48603c1e90b26400111003590324241140a0041483e0002148001d048803400d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 804676258 804856115 := by
  have h0 := BRFrame.cov_init 804676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 804676258 ≤ n) (h2 : n < 804856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
