-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3477
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:46:42.846574+00:00
-- url     : https://prove2.me/submissions/a1a371fd-fd78-4371-b402-58586f96e284

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 625179856 ≤ n < 625359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 625181106 1250 625179856 625179869
    0x2132307110f0f15090f19060e0601060801051e090705130e0106021b030a060c09050a0e060f0d050a080a02030d0b060a020a060203060f0607060b01020d080f24030a0308060109 77
    0x4290340390000351012130071342c880c20050041c2d0300c115518030a1150900800014124403070003191044203c4000301503001d81e145000d00410411440602142a0b480d0803c0c0504000706500100400843c642241c030481c14250b5401c5000980e4600c0020509000d030035504200401ca0102d00350300740415085100e401081c8180d8180c2e013951415402035105d4100e030707129520406203d036102d070068804110043d2000c0c0c0c040400c000c00ca281c0c91009101d241e4600800e441040ba401000032043d51186400d402540300a003203038420503d00c001c021004200b480c04480324015400000042555007010348101e10b00e40d005150b650303014206200494030f0f0310050901c20202032001d00407180d40000d800c0030880c0d0214005aaa881e1103000407100f0180c4000e40f94003210000d0280208429508040e00d442e400307030210383d5944c580c074109440c83c0701c040b5084e0003548484d400169086401d9011542101079010081c15190480c6e00800d0904400710f82c144c010600305014420a035a00c081c0c041c004040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 625182356 1250 625181106 625181113
    0x6030e03041203050d020403080310050a0909080301140406210203070501030c0c0f11100306051503012102040f0e0105060f010203041a030a1d0703060b0103020702132307110f 77
    0xc1c07000d40c402c1d20380c0106024041202c00304489001c00f4540d412100034641200700640c80c1c1c90070980a5012644030b008650090042c0c40700022080700c0b50040d080b185501080b12f07821682801040c900c0d5200c0d40324225030040d10f0b6680043e00005071500c084ca06080c103512040ca090090041c1840c040e1035500142c10145003c41d1640f0980d442910000540c0d40300078800c0d00101ca60400280106051409560103081c64509040094155014004541c0c00782c0e901040b2842000507105c07903000034807500c40d04421080b0401d0352000c18440c0d05120302e2004100090601c601c00d885030441e00d10703049540d9a03a65a4092041c0c902c1c03d020203007440042480114503040c204514901e00b510301c950000700e07c00011010505039001134202d04904000d035454004545111044a0356412081c0b100782d13000c6190924083c460f5101c0d0013210400d9401070500704195252481d01c00040010700309600b5042c00f481030f010101004550300324025401b550b9003006030b0196007041400c0c14480031b841e004550 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 625183606 1250 625182356 625182359
    0x120106091e120311160503010e070602070302061b030f030604151401030207050a021003140901020f0a050c1f020a0e040e19020d060f14070302160b1f030c06030e0304 73
    0x241d4441001e41d4000c4607080c84512241c07405a0b502a1440101c030058091708205000300818403107400100e0341c007203000380a03c0000c4100552038090740d014840044c0c01c41c1c0802e01c09400d00d40001c000c0c1e0307620608800c00504011010f00d0950b08000748489101c4000002e02001d482e15001d10002c00d41c002c0e02c501e90280c98032801103003943c03910011906040d00412180240b180a2280782d000c26000751017260860041800100141004451030290746000030101e00400014070a4441111248480c28039046489105540a40125510360712501c0b803600c2c4e100703042982060b022070740c0603080ba000d40c6942074548007030700003864002143d0280d4688104181030040028200c500a007200d10300810040441c00420303031204001401400960a0030303000008080582c1c410031071440b2004002c6c40c1605c50310021070503841014081487c88003d050404003050228a1294012440b1242891100b0711300408040d030405c40d174001d031624921013404001040e094003a690300d8070b558002070361920303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 625184856 1250 625183606 625183649
    0x5030a02070f170d08090f06040506070306120b040f14031603030c05120a0b0109033905090414030d09080319020906030a05070509091501090f060f05130b12010609 72
    0xc400c070b01d40700f42c04c004810020400c416400e100c3c6091030900f041c1070360049d282c10f0418654412040ea0400d0004e45808800a101da010402ca011030642c001100b441d9925aa101c1100680505805882c900120032402c5202e8108000038041014449403081800c4410705028040311029407221080c40403c000c802c04406035051200c0d07010010442c001031840e07512004070740320100354200801c6a61101800d0800c6e042c444550a000032609040a5100504424003a00c00d5424811160020192004600011200108100440a035800312400e00c00f500a040007510030000003641c40d142c0000500182107803100900712002e03009070040d40b90103803000200d04e03980320080c5442c0501c0d80d19408111902e102d081102c1090307000034000202801c101c0c54809400e144098401c3c04210900300000e0040d4a400c1d03400101c44091b200e0080a03000c117042610a0742c807800900354180081c107000725054030200054072171800507031901c072041c0d03041c034001615000c0a84c0202040000c4d55101c0d807480b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 625186106 1250 625184856 625184863
    0xc020609030409020c160b0301031e081b01110301090213081615030209130e15151203070209070206061e0f060d0b0d030f20061b040305030a02070f17 66
    0x22101003100040c1d0352002d51720700c3c0b414030f9803101c0318002441e50100002004a001c5c0007560582c1d014440400500100a207400481d8a080070300616001090200c504001e0127080011580c0c4820800070030b80210002d90116154130981102222075808210303120302c075114016000140c5050350050264003030030088041d4a00c0a489120400099035180c2c0441780d21a0701aa89540340140044441d00c2c51445500082c100180407507044e032040780700240039500300c164000d0061400f410011240038400c81402034460b04060340001a12041200c0e00068039110700b407070702c580c6107a40540710314242402000002e01900c01064100c801254003070410b83e44003500301180070f0048030f41550b940e00072100300001c1c11030410100e0f0b2015400f2248818180c0080311a13481c02441c0d80c9445810502e2003600c1c07444e6041d8840100e0b0f5510a1001481a035101381d40001600c41d00e9110600301035a0303544452a6034480d494080060b0032074032003000100c0c201e1520344050f08420400300010200540c1c1d060f40d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 625187356 1250 625186106 625186109
    0x1063f0203040804080321060102150a050c07150c08060a0f1401141b07120506040620071101080a0c0503131b061d09010812070503090901030311010c0206090304 71
    0x11100e038004081810043c00d48212001065140d050300d842d101022807107074141010500300c82000c0303d20070005a8961012071341c0b103009a012a46c156590700d031040d2450003404000e000320700d4401c041107280081156064200b079500c0480d88082000c11100000808800000d07100d0341c01075111000c1031040f10400c000f01000e5a440f01014040074001000484003010015101d04510000203201c1412204c074012006c11112400200d5003800d985112807450600e0511014205400820100740002d400750851500440101c052104541001c0d040b00c1d01640200c4c3d04550381500c0440b0115596007183e401c9500402e01072040040408012018140340702c028a032892044034030344240e04010b0850600450f440f0b048286071038184e101c0300080c1002024000d043d512a449230800202c51400c0301100c0c0c185e800c584090056028030124648154200b020201c41d1804148405012a2540b00281c0c0c0254065a2800c503101111000d450031108104600400c54011b0000c021050800008440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 625188606 1250 625187356 625187477
    0xf060f0f0b040f11033402030c01150b0f0c070306140a1109010804030c170f130801020906040b1308030d0f050f0402092d070206011a03040c2106050106 67
    0x2000350020202c007608401d82084c040d01b81e1140c0210700c400ca1503002014149002d0400c0017000302d40140058a0281e26051088043c44441000988941d42d0380e10064104080a101200c1642da1641c0c0d41c28242d401241c02a214140c20340c0800005400d45d029000d5901810400c1d90315003000c41c0300080900d41c1c010000760a00500c50a1542041511507007184a032044641c51500c0701c1140341031105d0356208107174801c0344a02c800c001141c0d40106108840b040000108003528043c9050480d20498105000d01c00f410442d034100002c1401c01803000741000c5155500009003a60021280e42c00c03581c2c09418603052005003010880180c031103070007554001502c0b041c80704807078119070310800d842ca50302c1d19a4035410310300c4800c0c40f000d0b41c0c0000d41141621550300c440d000c180c10010a80e82c2c0c03030000715000740c003000359a41c0401c030021011803140d1081c080b158080340040c2a50300d91030b050790b500313910100010f44001803c12540c030a040002d40c0c10403002c458100600380e113120000c490501a0b8060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 625189856 1250 625188606 625188631
    0x903090e0c0d1127032103040b2701140c0c0705040e01020f121e190c0504090507180f0501080f0a0b090903090102150c070f060f0f0b040f1103 63
    0x3d04044030b07800300751900d00b0406001240c0c04061280440d80c00381074140c1050080c40b0303c2c035041d142031030f01c3c044000061410202c280c2c21079440d61078404e1400c201800502c0b82c103030000b5200b007200c001d00c1040005201c2e024004121414048600300703944100a148030400c00d001d0241d24001000480c0e00e00c201c074021540030a2940c02c04003040d0082c440c0d9500304048640008007a0180010048901d1140c8080d001003400e00c40e210369040703c0120115005003146074192039110b100b03411640444078071340e4186802c60a05445a58200486000761071a03800b07e454001c840d441801503940c1d180203410100c03101d004140c40c000c0041c0c002710740600840400d0201c140040c0c00ea1140703520114890400400c100c515050020070380c0d460341d00c00c400382801030181814400030a0440042e050180c029105d0440c5400c2c00c1e5142c8524008654204442580c0c41d60704070411852680280b55101d0406035000800e42c50000401c0100c0d106019001c1842c0e040010f0312640c0642101925404444030342007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 625191106 1250 625189856 625189871
    0x609120903100507020304051309060e030327070f030615080c010c170910050c060702011503290a061e0e0112060b030703290c1b07090e010903090e0c0d 67
    0x5900f11f008035040030380c0040f00020301c081e43c100da07600a41c0d080c2d40035035420000130002400468681c0f10072111030b071300d0b14901910f0101900006801c20200d9140c001500d0300182c655103035a602c08030075403042d9255a00c1d41d1204034455451700465000700310107030041c034184001c40e0000c0c00408a001c03010340a2111b88485001c455075034000c4807600f4130010010303651000f0605020700b9a0b045030b1030710b40c01e41c8524000600d6503401407203654092550090b800c89401d00e5607440c0500d40d04600c0240203c107010030a085411144c071308056004128901c3c2c0410340c2401c000f0714a4201c941103540d01100041d1442c20400c2403000110b5030306440e00321101090303034269402c2078000f80c042208180c3d0144100d07100003050044040d030010744220600c00c04000100450400494980141e41400814108001084a41d5190101100924519025100b0f556a1003007200300b2540c0100c10126941d4403085030b0303030405030b200030103c010385800c00c4010054103107e60117081070301035080301340c0c0f086555801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 625192356 1250 625191106 625191121
    0x110a02031f0f0e010219031406060706150306061401020106180203090313080303040b06061c0c0905030a0b010e011e0b0702010c0822080106060e04150503030c06091209031005 77
    0x842c001d1401d0200501814041200380b50003580510580d14400d081000a803450394464002c0e0400c0e107858515010458403080f08000590b03010040840d034580d61900c0e0203807441d40c0c9441c07900055000b20300008289142100071030140d4410324071107045900d4000b060000c03001824454500c610304400058480d40d0381c9c20340e2031651081c0400c00300c07801d4217000001440c0200000440c41280300c5c4441e41c9464940e070084c0a980e0244010007004280741c0020342c5505411503010f000c044587e8903183e0359090350740b804281045400c00c0159250b8070600010301c0348003030240400707004040310860480c0c03401868040500800071401040010400050440e080d60710545807006029001515956103000183d9424005240c0c955071070480c031583d2000142c50a410b201d0030707084542c180c480f480307406400010003004040266843c0644c0300301003004a0ba41c0c400b040503000b0b49541100600c01814a03a0801d880c16000070a0070640d50300801c2030740034684002c03940b03c107940481040800c15407607021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 625193606 1250 625192356 625192361
    0xf0a0c031e050708031309292205150a0305070e0c0d020f0a020106080318060313050d180806010f17100510030b060402090a03080a030f020f0901110a02031f 69
    0x1a0042c1440c890144085a1410080001c0602040218041000c2c41d075070040c00b400e032090300e004209511804540e00204280b070340701500c419030008103002441c982140c121002e15a5100c900b01c000c560b1034003002000c02c01c5a00c0c80080e12002c41d007010713015145541b0296194140d00800e0307060002d44000c52038030100c201c1035884076249524103549034032000c0207000540d000300c1c000c10010741c24a100000c4104021048500c0003171011849050070800e07109220041e032005d001c040c84001540700700b00101d076003485100c0d40c03c2040d68a9910b104100c080030030340882181c104123a20303004400100200c4280c10240c004990745840002c108070f5408a60350308056064a403c07814504100400842078486070050b000d0702d100e01035440b4140c0300c0c2c405000403402000c807980d070810404002400810340c03c0001c1c4c07240944038a00030880c003042d001164280d0304444e40380d0050f00c2003ca8484aa9a000055406070108450051101c1c1c10305400003952440d2440030309209100343c0c0c02c0b0b002000307201e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 625194856 1250 625193606 625193663
    0x17040f0323010f0509152a0c0102211015030b0d05060702070f0b03060a06181e0311010e0f0f040e0625020f0a0b2e03050f0a0c03 57
    0x4030003000f110181d030401e00702401c0d00b01c2d060406802142d4000e4a0a2507140025000c1e44041d030f415904c0c0040c42103004106404140f03000c60b0102d01713000c0344041c104240010b0400d11000b03201030710180c00304100041450006031482d0050003010310705000c946035004c805a023a41e003914012401c88458004030700c064001000c098807500441040040441d000101e00702190f0303203201d0041c80740e07641d0030a0140a000c2620810340c4451004410000c6030b200e104480b030b02c0400f42c00c200311703051354031003c408030380d10768011940d40c030119aa0b00700f0911100c100f02d408024000c0c2444030951124000091055a10b0102e003840740100c52013001d103a4540740c0c010600100441c0482d1501e08003000055640c4405001c1041082c040f8000750005610115005140901d00b10080c0f84411003940d4104901034002c08010303155a0400c41044a8040700c6501810070703e20703d001042c001e065080050400f02c00d04101c100750b612180b04c02c0d00040600b0b04c034008880e0130038041c00401a0b011114512420310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 625196106 1250 625194856 625194923
    0x30506071808031b062a09270402010e04020702010c020d06060b040303020a11010f0503070c0330050703050c09040902240a0f09051e040b1002030717040f03 69
    0x130800c150034211801c461004592800c00f113600c83d54658040001440600b60005e90311010710b855a00035901544c058554058020400d40d403d04458040441154001c0045465600c0440901c810f65802c0140044880b1056500750300d0110b0382d80029007086804a0004e000d02040c0300414244070300350380f000c40500240644140d4a41c1d403400c000390348214040050341c1d06564000021a55802111410940d031026110313181103039242c150030740b00c0803a009425814441d513150030042c0c40f034540d0704414071403012200d0401020191804130382201d400030100c5090600d420188201e294003c0c1c141c41990004540116032460107101150075a00f065220804a41040a40001107403a98015012145d601e0355141880d48000c07a040307419141c1403003910f411030004031000307440014441d200c00290300c015002042d800a048082200342c128841040c00503000481c2030780070070440c07941d00c180c03020301480000e060908055250452103210b01c40141f140f02036100a183c621074204040040091 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 625197356 1250 625196106 625196113
    0x10b0901080705010e040606091203030603050d05030a14070e120f01111e0405090435130b09060d050709030606030f210e0f01050f0d0b040c0504030506071808 70
    0x94400600d42c0c0c1c2c021038081c10b80410102e00408000d81810b10600007181c2040d96400000c40c50b10140b01140c04e60b90205604143d25020044003069081103881c4c061007860343d520b40d50349490b40001c01120382400303e10590400c040c0a000c0c4855000040d88040c400440e4425088481e05808a00d0800c82480c50354441d420583c0d440111841e042c0030b84552906180c5070001c0000f01220ba0525205074040d00c0d900486240100e000702d40e50f0940f440720740101d0b000080c03008104945044104400035003500c40107200194480c071152416511f0402003440c0c070f40b454280742e10400051068003800c28500320b410350380c01c00240e480f84500c82050046070003c1080141c951241840280e140ca491001d032080c80c0c45c41c1c41c3d01c004070449400500d05034690b41d40da0012030340300c4041011400b1000d00450400c0f0090105030b280c030540800406403041421000903161890b58148800e0383c205c1ca62040c10f2240c10310080000c1000410801d40c02001490440c1c280d204011210449903503603003001c2154030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 625198606 1250 625197356 625197359
    0x109060501181b0c0b06040b0904120909060815040503090d0305040302010f0942170105100503070503060114070b19050c0901050c010f090308040c0602061005010f02010b0901 77
    0x10040c04119000b042e1807106004401c00d0003070b012040301d030311800780300081c46801c0302502249200c6509500b000c4010400324001c04400002011880c041e070301942d241203811009200c0a8025008100402d9041800e201e81498010507503140c1d0861060f0b01c100c03500c110001001c2003c14000c4030b41d4074030300801c4c00d0000307803860500400e990418001240841c0810403d07c0300140940742c01e104481c02c00c141d2240b4840280c854a0544030f409510014080e0f21401c450100c41190701250081e40e00707503440d80c05e000101c0c408000c1c4e401040c1c2c40280610003180b640c25031107512000b1660300810310b08209507603440b00b400407a40c190030007001c50038804010a030401003050445030705005040c82c0080300d500424540a200445400742c80d460b4403e0002c02134120b49500440140c031094102000018100014400e1032042d1481c540b011000240c0078800c000410141103803280261030170344000c00c25454100712800101c001402800e05009002e4084d02103180300b50802c7c820300380c0280c070030801c95 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 625199856 1250 625198606 625198619
    0x40f1202060f2202271812030603031614030313030f09080c0d0204091a0402130207020102030a1b1a06031b09040605071103280e01021e0109060501 65
    0x8070070a5400c0c1d00510784840100d88680750031040715528501c809003000024003640e08100700d03d40305000e413080500301c80346040001d030a40d806052040705440c04403e4500c01442d0458203040b20340204101c03004041c02445070750785000083d03520340a040098205c903a059410480c595440e2045014081e220000800000104446000701103900c6a01c3d40e150503154910151001285d500502c3d0702a8090409032009140184802d20154005000001c0b69000f9846682d030070800304460b80150420030040c003085003030203441040e11000501007141040103641c0000d40724412181c031402000082000c03c507184076003a00b061107260303100c030b0201c14640300c006203000c510400b10303141446030041c1da03149190414007035107a6004020042c03405171a80d440755128030060602401c1da40400955101000c40c10000b04001c20403c03101103002070f0006c1a9806180554a200c02c140c030030002c20074031100041e600050300a19120f00302c01c440843c2c0792543d40403801800081000381034a4200320000801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 625201106 1250 625199856 625199863
    0x30d02030406322d010f2409090203221401060510021c2c040510051c060b06070308011403030a0207180f0207032d0215040f1202 57
    0x11800c04090700659400640d54103e0203035481030320141001d01600050105019a290840c141000f001c820111840c841d0030302000c2d80c002d0700254901861050184010f50b110b000086406203401102d160002d119000100022030700e115040c411074020002c508080415550721802c20001c600c2d044c0080c0e02e908014a440804d0b080041e02ea500c0e250707002c07810f800c180e488104940d1841c0c008083c1e1842c0d50f8040d60103071105954503003c02040070014043c0b11001c418035808000e4a581c002c1d005013003101040202d44010300442545520a581045036484044080d45004e043d01ca903511f2101450824034042c0c000300c620303b03520120000f015000c01d900100d240d4181d41200c03040840b20301164007407550780d101d01e80d42c04016a000c1c80040268039440c00c0012030f9050b81000101e0007a00c052458410b0383c006550890108250550718040c20703c5c502ca06401c0700d62540854030704c3da40748080280d2503e45a0744003a4241030102c002505000030b4040307407050310754440c07002901c010030140d0003500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 625202356 1250 625201106 625201121
    0x1c030e041410080d2012040b0a0e0102010603021c020102071814060301050402330a09090b010f09120204020c0d080405060901150512010f0c090501030c0504120f05030d02030406 78
    0x80c803042c01c0c1d0104000303800141d00481914161a6001c04c50004c8500b605818001a2100b12605c0b1316151300d98031a40000240008080d028251034954040f4940030b004007c072000000e04580c589141040541d9a55070001410400001080500111400101c1c20031040e50804a1800f01100901c0a000069400f09803565641d01500c002610360008042c2a80c0c026038000c4d41c40062811302c2c4e0707801180030300c1c8920300360800748018604044101c1c4400c640d40001170f583380440c035424130410880c04607000300804001c00740b806800300c00b140310026118103201c3c060140c00d13040a41c00075045407a9581101c592000180c1101c8040010b075030000e00d155412174044519006100c00710f60983c030140612403046c1c4042c031048d409107061a040c840c10040c40d281c4c100d4150340350920000e543c1154330941c1ca1210280d5699001c403814030001505407010425540c0820804010400000e12009607802c01950b10140703074292661581420f5245010b1401c03004c801740e1000041c0320030010158001d50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 625203606 1250 625202356 625202371
    0x2011412010b3406020901170c030103020406061107090c03020d06090e1614220e0604030809210702040e1c0905040908031f08012c07051c030e0414 65
    0x5040c0c5900314084490f0303102c0d180141e6a041c1a180d0310800161240c01820b400344041c034143c0d5400c0510b1451034481d100a440440385000000010b20550506020f0100034105904101c080b41d218019555552601407003804841a45d0317210102d01244a0f80403144008403602c0d00748401a12070440c14002c0c070b1040345605851080810007141a02d01002c3c2c241107810003640004000b82c1c50090082030540e0808072401c00540d0382041c0b00b11040381c031032a00c010428000505e46441c2600d07001e000c11802400c8200d059012007250394006020b1450f038508809903500322519a01c0c41e201140152540040681d40c1e030080040f0107044101c09042408034103507542c2e540700180e48c1d0740103107c1207030b80e440320192401d03100b000040c0c01c1c00e0500e44030785051070250310110240b13590b4951175400c460085820450a05008210000c000240e03a00e2502c50985140030b001024035000000d103642e07074140240303186488142850406c0c140525581c02082c0c0e03000c0c01c1485400c5038a1002210f55000b00d0700308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 625204856 1250 625203606 625203637
    0xd0203150901080a060e010b060714010c05091c1e0b0a1b090b0a1806171e01051522090e070b0a18030c1203080112080702011412010b 59
    0xe4005280110740750b0304840d10030018240460301902c8103005405001c0100420790f49610510900d42c8802c0b0050010700c0c01803900e11084001c00f0580b42c01c3d11030766040c01d000c00c5402c0c42030502075501d95801c41c00700c4102d0f00d0944880309161800134074007101c408020500c000c00014a9050228622855119250382c1300c041101c030004200401b0341105800114000860400040c440c1004030710041140d00c0c4c0300e040c0b80c260104003803045091a400741e00050000b0f041c070804101c4501c100c0e40c8690300318040d04039078420b00000a40c40003403004140f08184c41003c2d83c0034040054880e001c221150240b00782201d6030302c811400907040186185104545d00c0524065400c0a0300001080d2007051b079650000613860081382401c11a11010103031180110030702004000000035017068400c800904807004c1a0303003000c0302030401514124050380101840c01195840e000059110411101c0159090800c20706541d2500b00c1400c5501030781402c1c1c02084581070022030103080103809043c00c00610300d900c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 625206106 1250 625204856 625204891
    0x20601050108013f060609020a180503060c16150603140312071101020903011814031c0f0603050f07050907020102090904120e0a0e040b0601080c180a08030d0203 71
    0x41091044210440401c1d10340b004d502e0001d4409141407071010548070300c502032103440d039a4903100110782e00e0f9406045d5156001850100c0950032040c0018188111a0440707199441c04010075101d0707800400d2200300c9400043e480912500808030440c143d07401c0201c181ca020030080801000b03000600081e110948405140d04400300d000003264000c10300c1010354007441d12840d1007a01e060010f4680c00c0b021f07540034002c3d0b8a81380c409100e142c090f540f00d60038a100090082c10606441280740d41c0618083d0003c2005c101c1d034610f0f084000c1c64003100000c0019040c2801612000104540d800050043c0580250150341c0b0341c0010b03540c0152402281d00c00380980310f69400340d080780f04a205030754000c140030001074040b0700c1d00080002824000d050a061100c8010000b40130009943c00c0200ca2081c1c0b1000c0c001400080500240d0051080c00c00c1522404d107140d20740030fa801070b400a00e20300115104e81041d80c1d20307114282001000701c0c1e411240c9562410314440040d4000316440001a10701550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 625207356 1250 625206106 625206119
    0x1b010b0102011b1722050c121c261302090a020301061407080408060108030a120c090e190606120e010515100e10120c0305010f09021602030d02060105010801 69
    0x35040c028915110050800e89807841c0031050f0000404041c0c801d5030380c2000f007800c0d80d80000c1c01d112043c840c001a2410340d906204100c220300860f502381c40607a00c000f18501d400c03900d8000d0702d000085142443c100c021001c2103104112203520060003441e589903c00d01000507540f0050905151013222401c4140c1d4401842c0f00881c00f0034410b403c009110310161001c80d4004d0310042400745e0140f8a400e26054481c0c01071403901d0000e90015113154000218410035580c40340507c0c00701940c1d05014001c4000c40b490082c00c1d484240101e0206c1d00760780012801040f2003e00840c1407003a034500c14802280d0303d44019040b25850f00b5102c91003403e05948001c10441841024819068410710301c8441d9015400e00036025160702208062200309483c20b00650380c3c00d2101d158110040c2d440c103441c000c01010801c150340203142c130703803003410f080400501c004a16000e104068a000500c0141c03250785803545842040600c0400ae901800358205018809602244c424140e42d82070f01c490b1081d03680da80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 625208606 1250 625207356 625207391
    0x108130c05010309060e01061d0c0406094523040609080d090c030201120c0903060209030c042313031b020f10020f060a090c03171b010b010201 63
    0x260041500418490a22596000b68440100c05006403400168407031101c01403070031500ca030780102810250943c4030b0b4030188070345d202d041d41c0616014a0385040520b4500040d041e6090b6000e16400820180300340e49603041000078059102010800c104503210381c8042030409500e03007100c54081181048d200c20581d00b004845000d503c40101b1301807480c1e0740d890300c0d0a4000c1c82c8040701102d1040007000210142c0f06c160003400c11441c094000304a8451840c40050007001c22600c0400071181041402d801c02600654050b04980d005000580c4d03400e08000040d080c41e00b102145035209241540f00c2d03018908070818510041030f55410f010317603600c80d02c5452185182c1c1d008000c0000b003c101c2c55203134405500400340b902c0c520140c40034205500c20000510f104c074019621000580c008010415000380400c01145c000010364800c100c410101d4032844100069130202500580148141c3c000d549000790031600101c0751600400c84e500080e07010a4040e110141b120f45c0190708000d08807800070040c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 625209856 1250 625208606 625208641
    0x21030203030c0d090f11011704030c021005040b040f0f05120a06230a230603031b07090e0a0303050106021b04050720070911040605040e0907120b060108 67
    0x150019401d550342d200e440c04465029980750708519440b2411400001c04082d400d1854a01c00c0106842c07503e0070384001012401c012908210420a0605000c00b20741c1054012400740e406071030080300540f445500741d51511071350344480003a180004002a0020845e6450300940c4c44900407503a5150390380040000310f181c40a160354164010b0f8908000081c01e41c4c0c40b03c0c404900602840d20001c0206031b1444c40c401e81102c1c0d10b2440d5480d01000c42a0840700c4180341d50343c28400c80c0104160600c800480d50306c0c02410440e410072800c545903405a500100a088000c0080b400184001c0103038a1150342c550040c000110007182c108000828414008140ba0b40d0340a0340030710304094000340008204c0039080103054801808184001031005000e10081d20071200c21903002072840500d07001720541120300c140482154000140401d20041b54030004590071034000e07010b40f80054071841c40301810020f05910078140d811030030155508102c02d813080248269805d8131501003a5841701013017041880b10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 625211106 1250 625209856 625209863
    0xe060403080f03040c1a07060e012a090806090706020f0601080d050714070f0f0e06060a082701050703050705070302070302060d090b041a09030f03060904020112020d050121 76
    0x380b051884250a40c0050b50307115000700314001401d90f40d43c0c4200704030741103d1031501458070f0000f103502c00d000c9540104c0d00409501c0000b005a1044890340e500d003c02c90600110400c60034101e0614094841d0b4841000303820102c051720207900340713001e000740e4810040c8a01005070095142500c08040040b58090481c0c0903600500351005207283d0840c1c9641c0300740001c80381541e5241402400b00d50403c900d001405070001c0e6840c55038201503006080b401c035903206110100001d020004036803031322030944252032507904081000780c0701d400b145611020500c0e40c2d6038400b5440600540356102c1500114051242c1e41c60405c0f880e11050f1040715a07100302d41004d00541d03ca840c1c2000141000e400400c2641a0b003000016242c00caa42c80c0162a0340c00d40f01581c201c1c1c10700c91901601c480c20701c1c2141e04a8501030046141c000ca030782c0310030349034000100024031443c0104001070a6901604211101002e25081190b4403d100244200100800e0041c1402c694821000c107103e610b0712134000c0002c0c3d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 625212356 1250 625211106 625211123
    0x20d02043803100e04030504150f090b130311041b0e040b04051303180503010905011410051f050d020c0114010803210a1b0804152003151c02010e060403 67
    0x3130040b8805040409402142040030411001a10020403003510040490a6a908072004550f0740024000c2456800c40f0304208001c004a0441445c01c0181c841140c0d07014a400d81d0305143e000c0010000e01200c90300c0c0f10101d811000888145902140000d1607000480e03041088010b007500340703c211f5030121a180071000d4480b031210701003805400d00c4c0d0139444032200c900d8581d5441d980801c0c05d540307400760110380d01d179110940118144d401c0c00c600c607807280902d5034400c00140340c00e000955a00c5418840100841030b4101200354078801c50403075800340c402d00e40555440c640c0c0c482c0103008040102d94045003110b03401c00820320400c0441120003403601008032440341491490244074000c00a0000c1030300c0c580d5048048011510001400d013481b01c10b8031880b8161a050901d03c00311032000041440c4103180615519204000c21001c100700d910b44404070703840355502da00c10700c001203040200951050340440071030240309803640244102d034403e0340c94030241907660003401128010390000408085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 625213606 1250 625212356 625212359
    0x204021c140f0609060d120e1201020c1c05070b011202090a05010e1602010e06010e16020f0307060c17010e0114220b010c0f210e090604020d0204380310 67
    0x140104a41d45c100034000d242d55200340d21a0b0b40c4861241e4504000380100b2200408403001d450202d10b074484c500f646030003e40c9442c0240d004161114046507540358040810001c0750296442041680e400d40d52081d5072401d2541c41d41070701c414640750860120b02c03075244207000504000c213a01405048a1129030b11240680751001c4c084894964030f11981d00b150350350024161034a20170003040c0d001701080e041524903814200da800da200b0600c079202d0000e542c0040b15000f0410340000490f0561900725000082d0401c01c940100d9462030800c1d0040c1c0300003070000010402c100d2500129048445402d01198840e201000740700c4500342c00c0d40d1002281e9095000582d1681c0035030040750803c0c00501d001c01104a042d0303038440d0344108582050352059240d4111107481180101c0c0e416500303120b802c1015100103e41d00040e01120020700d414040d0742c0204403088641030507016140034104000c1c045241e0781c654545c5503604d8007042581101c800c0c104480c480b807400182b088a00914006000030b0405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 625214856 1250 625213606 625213609
    0x2f04090309090e0a0204050406090201080603150106051309091505010603060b040504050a0222030c0f030530120906130f0f0201020c0916020f240a06030204021c140f06 74
    0x400c0f00c0c092041da1809414000300c0166514416184150b00c10b00000440207100c1c00010141100100340c940294040554900c400000e86c40d6079046483c5441c01c0350340e400001141c00a0032800c3d81c0726001090802000c0b01c20050301c807a41c002c44200b509010401aaa00d078000c034140c030f0b101d2107090000c02c410441030050b03050940110380d0040e8041c002503d03008104902030451032100d20080b050060300d110600c00c118425260070300805542550700480e038190f0300c401c0d446104101c414038510781020500040382c0184451440e0505e100528070f511541a0018600003042c02c131007250ba80e0054400141b1b41c02c440c1c0d5548400f032030300141201218007490340e94a000d505040000c0c0c1c190b210340752140b1860390b298260603200741a14140e001004190f079034044d1a12440510852168100f02203165030b03a0740c80a117003c024142d08010410507201c0b20010001003034240c0010b50031600002e4140f10381011440c0d090143c1c2c0d000481003100d00c10215040c0744c142002e1b82d09034a20342100000c40c1d0346 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 625216106 1250 625214856 625214861
    0x102130623460c020d0c0602071a0a0c03051c02280f02030904110f0a17100e0403050918010e070e0402180105030907032f0409030909 59
    0x100090244994500e9081244251940c1c00412a8160841c48070018498404402d1501040419032034031940e000c0318584110403504000000380800c00004200f04429503441894400650303070041c1040410b1501c445d0000c1d1541c22a01444200c4600c0c542ca0050f101c0b00e03201207070700001d1182d680340401030950f5030480f482e134828406030000600f1a02000160140c3c2e2000f4804c3c3c204100c5500d114440e090100a201c4010f81c0c1500148020b00108200380d075004001c59800610803907000904020194003a0322038001d82c4050090f00c00c010510341055a000703120900e03403e4100203e4503183d55080b0350070018507403074018225190f0200e40070034006030185000d800070000c000c02100660902c0e000c01000343c0d00036808040041e00110500c1002c03a0002c1540640f00b04c244c5081d80f9266440c0c00d19818013241a240c54108600040040c500400600013000074507840032401c08148010401c4804912442036405403003281c0b01d095184900d02845114001a415141c0100c40fa00d0888980b00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 625217356 1250 625216106 625216127
    0x90a2022031112070905131101020604020a0308090406030501050a0c11030a052a0f0a030e0411090907110609010911040c021009020a080708031b03040302030312060f0411120901021306 81
    0x141e0b4030490502041008075170080c10711404507d01c64018113103840c1801c2c142103035581e040ca4155042441030001503120b03039002900707603500644000c1e039a113803480100d401070566901c050942c5d40707031005102004805411150b40ca02c51035441d5640d180c1e241040365282c0c0706100f958404103204000a42001c2c6000e00d110380341c0108600c0059504c21404512401c1a41110881625400c01046241056080440c0c0c880062003540d08001c483c10081511206100301047c3d42c1c400c0590b84009a03c06101c1d5500304103401a513415254503080910206020f0300a0707010488500e00b9002610304141800e1044407480c40a945c0149200010300703004200514200f02c00303a0f0001c41d07800000c146d0789010484540280b00d42002944d0360440351034804901038103001c489c010f54004200c100f025a40010a4a10591700c0601c2094103844040018a131541a0b01d0348980003802d013510105400c503400003500082060414824080c0d4406090900f00c0c890725883c03001d00d8180101c140b06052044c000c3c02d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 625218606 1250 625217356 625217389
    0x9060b031623030c130c02011401210f020d0b19020a08040f0f02150d05090f06190e06070305060f09040b130201050403152004080309090a20220311 65
    0x140681904404201c160000f0b011210401e9182c006c881d0220f6424460040020040c98900c0d03600e5040208d402d0345182d100701d001401464030446401032140041200480320303801400d10016000c50b241c8641c5104044a41807a030070907043e184d504d82c502d00d0088440480f0207980c2c1141c296103035500c1d0f03607149485000036074410160001c0d900041c2c8a0004200200465600301e070f03101d040c1d0060300c030150f590040000d201500701c51011250500300040c0385811040c4400c00b281c1c40c0004800d100028654110305800c20b110f1042800030054044d072200d0f0043d042a150181200480b0003403068100003561b008019226420014400700629001c8480d040d10500d0302c18501507907a12840745540200702c51880e41a50303840c041c50803441300e1650416a60225607020b05042c40d10203401c3d101e006004a2a000f900714900060a104140d807002418074000420b18002e00300c20b0650f90702c0c030381012002b400c201022000c01c83c2c50302c3c2d80340b5003a41102e5028921350050181001800040500e010006c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 625219856 1250 625218606 625218613
    0x31e010806010f2c0c04090b0a0305061810020a0c110118060305070c050a11011715040b01050c100b01030608121c020c0d050d050f0708131509060b03162303 69
    0x8880c0d44c03030a0103034540070310b9000c491a902d49003070003541400c6840e4800140d00c1146c9407002040094408074401ea403003260740c5911040d0024000b0401e0401801001000c0312a02c0003e00c244078503000341c0081c40d9180a40449400c00402400540c0e04c0303000042c01101c030030030030352040001350320036004181e1003072080c9041c20110005540d010f04e80301d151081210880e1460380310307030103950303025141644400001c0c1840c40f40b0b040c44401d203000d120240c44658003490326001480c4072a4014000c0380c0f5007003010811282e0106800d20312000070500018081e0000382418030002d4800b10001d03a4130740d00d40d100c5a07076600d082040040042c40c5200440385030816a000d10108040360400d01800051080d542c94440da0365448022a04c12260000d000c41d40882000c418080411f500c62070040d17110001c0c802c442d41010260030a06080490401c440c1d91350317401c203007900782006103580105d0803405059044601e140340c60703103188580381d0403401b48102c59000d2180c9054400380407520200046c10240c1903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 625221106 1250 625219856 625219919
    0x90d03030b0d0c080105070c0b04030804050c090718051009210f1410140c0a031514130b0603040b04080f181215060d030212031e010806010f 62
    0x114510b00c007603030350580c0c600c2c4200b0010800c401080c0a0036134841268900b15003641102d64030202c03441c03005403018041008000003c1d0400004104100010b4802880c005141c03800d000014451903144030054203003030036244001164205640030010281054494003580e41c1041006445907040d010b1480c000e84404040c20085096541c10000450050304444113000e04003546a140c6440150180070072460980b40e04a00e1410b68200780c0c110300100e80940d40d400042c40c044001c0d00c030f2940640781c011030072500001c400800400303095008805580c42c83c82f1000030f40e09502150489400590020320410000b00028521800c4d5035000d071107205c0090130412612419500c0e40c00c041480300c03009550140c410313400d16007582a420070a240344020001c03042d01119400c011000602500d0054061040c03079820503000340240c00e090034070542041e0322413412400007400801a8000d40826070055400400c1040c2c01003001c42c1a1040e4024459074145815038007400300303002088800301340c02e80d41e01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 625222356 1250 625221106 625221109
    0xa06120207061506090b030f0c0a020309100306050102101109010e0a08011407110c0f1903140309100906050711280806060d0f021903051005090c15090d03030b 70
    0x2a5003051500c400003c5043c0e81800000f60001d50940c1007031340e0f07200c000d00401051829000725180d114418441030303512051110b4041e480d60281c1e00740b49070300200028404180326856404070049920981c02c940c40c01c1c0700e90403c50b00b2603030b21400f022940942000280c100d5402915009a000c0b40a8092520241d13030383c00c2903003142d0845c0d0710f005400045000340a000fa910201c0c08011001305005803140101c000000f6980e802d080391164001c883c8a0348101501440384e000400554002882d1804400000006d640326408400e11910a001c03013688200c3c0b9a115903a020b0580e261900e401d86801d03015140c0301d01801c10030003030325401501000200c05041da1000c48900c40c810560b0f0000d1102c0c01e040005090050092a41e030064454860220208414880c131400180d01a14112500b07400c580800e0440140342d080904513116060301207010004961165206920714030641c0c04954451040049038081c4070b04011548000380141d01e080d02e4428401000903109050025a0040800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 625223606 1250 625222356 625222361
    0x50316050c10030516050901050a0305040804120602090907050c07030807050a1e11040c21021b060412030b0a03030503090c09010f05030609010c1b142b0e0a0612020706 74
    0x54044000070f480300d05001c512186038174a60110302042c14100c4c240084038000a14501541c00c80008040d1200041000d01c005601210040c02d24250b4600441e08641001070195000341501070040c4592400910071900c02d1040c2c0d0010200100981066440c0da20b81503045d40000100359680e01440c0340407400100c0352403001580715081200c10510580740d013055013425102075851805075007060300020085510201f0015840c524103c2042054000c8070080024004c009101042c007030110035800c0e6640000034403911651103900700c82082c2080450403020380c0c2c87d178841160800c2c0c2403201480028014005035500c88a032104941c0d16640390800900004000c1c3e101850207130743c6403010320850a0900c0003d0b800441d00c0000e11821808400c0100729041c2ca80e284850a0b55500c0654108890035090140c0c03c01042c04403007162031916070b003801b01d410480b08502130800503564014003078001c01149001400040401c00800c0c40e103002034aa05941e0840701d01a25820004000005c1061 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 625224856 1250 625223606 625223629
    0xf031218030309080c01030510050d0c050301020310050a14030a1401180308100e10031101050d02131502010b22060305070e09010b01050f0a0e01090e040f0c0b07050316050c 76
    0xa03503ca203801458140050708103014113034103904050030041004000320b0055101001c5803010b558084500b0810708140170700e03907815000740342d2650001062021000103415001d00342c0744d040344d031002007a03512100c07000d00302088450740b038243e001800d03100081004000c1c425403a205e03100c000f00d10f8101e0460a00f8119a0012007107001c14214001d001a080c030a1604201800074051b400c035080c1002551400076040d5403000901ca19400210011035922410036900d8024840c0c00a43d160003406518172641080d9000740079007618015150070302c240c030501900e1782d03111001d04502e091a07205200e5501502e480b40b2507a4406494100010004e4800c00016000f411240740750300d41424003801c030900b07481e1a16003c41c1040760900c207002c0c2e00d100ea1000c0f21620089410100398840c214001030311030f940654001100031041404000c14000500802300700284108258500310340c035070031ba0070140d00075440040c14aa0041c0300b03507180804c0711040840aa4040c41c01c0720000c24a0100140c28120030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 625226106 1250 625224856 625224863
    0x807120c0b0a0906031503112e030209040b0904030c060f02041d0906010f0305072c04030c1202010c09030803090106030b090a03020f0a0b04030302090a080106080708060f010f03121803 81
    0x902c0f80c10040b0a91500c00e03d12180740002c00922160f1542d1038040d00040a8044035115003a4840701500511140d001954183e540210001f842000031030080c00942122118074011030410ba008102d5242510082d84a180c0c19201c848904446403030f10001494000401c40f40580c0c01c00004c600105020408403c035120700c141620186040325002e03003043c0069000100740ac1004406100158000c20408282c5224440703101000082d24035048045800b6100c892045500d1400d0100349a880800350302c0a600405c940d200315545150204c0c22541030f450b10700c000801d600001d05c0061079810041d41c211201c0780010808075107e80321404840f1003a250300c4c115074442e4800070700f00354050080c6495801c6000c06450344042588950104c1e600c01000101010780c000780060b882c0c1d441d0110b6a014000d400c0007000401e4030703001d040e542c03100f040c003400d4010b101e86000624009804000a0305071050308500445072841d665841d104605460305000520021198a602da4640780d072504005600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 625227356 1250 625226106 625226117
    0x807021c21020c032a0a0f0305040f1508161d03010b10031e11070204020d091727130917030907090509010b01080402010f14040b03060103060503070807120c0b0a 71
    0x3810401361078101a541c2c00865550602c00307000345c601080550a007600301030f41c5015142c8030302c0c007110341d4807590304a01c408558451011030640c240c2301120b00010281d03214a0456118080c03100c425808000c40200050400c00d100c01c20300a0b080c0364440b66820140004c6000c1195100040f48040300c0d019200001340e680d026011641a03007000d2481c003906080301000018102120349801d4461144082c0c015030b00098a080e0548a80c2e001d968015000303012002e5100b402e0400d00703040d5004003409088182d41000072400c42c14000a80b540400000f40300700c42c08502503102078050f01240c0001c0d40da5000510000d0404410300300290704c0707240c1c400040d00aa60503e000902100e6019207800781982c540740c00e85c007443e60011005a085502402c2207000844030140c112054203005928141c2c10b440803030000ba40c0d8409030051801074100740c03000c0c0070b0652248245590b41c0f01d20303c114202e0364046030701045000c2030b0b40c2c03007601c409001d01c4d40ca031100e07511448100321941c010202e0800140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 625228606 1250 625227356 625227367
    0xe010306180504020f01170604020f0f120f16080105040509031c0b01080708060f0d02040609020a030e01060501020c0d06021c020a050901140315010302180d0309060807021c21020c03 80
    0x80c081d0300b0141d0481c001d09081440c24031505001f10800d800034540f5000756400110000440c0700c5006840d034a050320425160b941da914580d00010400c143c03001d4040300c4a401c0807500c101681004031440c42c4980d61010a00d80c645800c200107481c0241c4501d200e4001001240c403036482c44a5a8400ea01c140328010541d0f111840005280e80340c000c00031010046140140f000035a00c85403061075144d0101d88003000400075000150040040d64400300d000c5200103550010035405030400340c131040001c0000c2003069503450040ea00c0c0c2411350141a40028800c42034000111a517010700b240c0d54050008140401c50b5524400480c0c2c4070303e50400105401241d28ac030a50307801000100d141826015403030460a00300c00c10b08403039094101541c14035801180101c1700d43c0541403d1685a040140000c1d81804a424080c00c6d400690061900058128002441c0700d400064101d9030020070b00280090299240d104980c40c03020192070f030b01003940e074560a25014038503001070200d401c01d1002440d0307200c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 625229856 1250 625228606 625228609
    0x150e010605030f010f231815040605180412020a0c0909150b011409030a06090b040b07030c050315120a0309090b030a120c0206040e0112020f031c0e01030618050402 72
    0x4a02c140e03c07400f206414505d0600a660320403c01410b019a00c2c100c010002240400040c0300768403030306c0e80c100301c100c408041080c1d1803200c440c2049503000a542c100b11031601c40050102a5541c0d501d0b403401c0145120104001070084005108a500944141c480c0319007141e5440e00c40c0c03403a6920091806444004840034070034507690003c0c017000707080f9040098018440000e80a00000c00d1858190180820714400c541ca040c00400c1c0201d501140410412405141c07403040b040c001d483c1a40e40d2900d40d80041c2c0124060304c00c090714507902e9203840d4103640d540c0e64001550844230380b006802c046502408030440d0780030000400c00c0d621030745400b8507d60402c56064111092101050f10907842514074801080444907400d1302005a49031101501c2180c3c008160a03201c0c1d903120196840c5118000228030314404c081d00946c0384221100301d1003045403420907644452080800c0101c9424084540041e402464560402d07901818045002e0790742d8540340350140c2c82104548400c0792941c0800086 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 625231106 1250 625229856 625229881
    0x5030c040e1608090f210c06093304170c010e06011415070b0603120a030f0f020f0306010e01140a020109170c071505040b030406090311030c10150e01060503 69
    0x21200b404002c0c08070016174091650b0b41c0303512140506220054003800c2d46242840e104540c100489101107070718030f051034081555104505403024018010100c081200f00342c650300441d14002114400c0c003c56252071f2075040b481458039556000f680c00800c0440483e080078010301c01003100d1880a4a40c81d0b1600da811800346130101420740c8680c000961040c02031204005079035000b500500c0d41002b6a440340080703490b001d24011010794041001ca849048c181e49500010005d203540300b81485010300404030b180507402201003420b0031039030a1002400b10b5200b2691030030308a0052400551100020342c41240b143c0c000f41e481c10050f5150042071090249002c034442d4070900d140046840d04c030a400e800c9440340560f0180f44080740d02241008900782c42442075601400142c00fa0b55034030b007028941140184a0b040b0214040f8203144e915000901000c03050340d800d4007109001d0030507142c140c100c0d80000c20031229807509200f9650740205441e01101c207400c0c06410075032561562400c01c00481d002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 625232356 1250 625231106 625231111
    0xd1e0807055703040b2a030714190f060c090902030c0d05010e07020601060f0903020618030f0a0203060105010c03030e03070302010b150703090e13061a1c110105030c040e1608 77
    0x206510404c070030000c80001904480e9803407031341204461000003561014082ca0303401500d1800328400800e0003030034408a1b040604a20f42c0d8002224019401c0e1542495415120940608941c20358031600d000b203007241d006000c07980d602d80b80c600196501e4400d403200700e0304140d880710380002c000b26940e1844203551040c10b015010b412414130f880e20300008025507585050150804100f080207813880007901a035140f0740030b568000c0c01c06403a171075003018003131500c0040d0b04002e00c280700d40c4038885104400440d02041030742c0c02070083c04081e0308001c010754002588000850801d030703441c1404601c0b500706002a0001c24400d49c000704828803020200320844500700480e030000402001000006074008900100710780320b4441c12250741d80c0b400760401020756981c201134412410303c18201402c3c01013001b0070b40e1a00e000c443c00c000c082031103400c00200700d80c1040c0081000000040e40c5890f580940f000c2c3d50310101d001413580c0b9141c0c594034a80500035056138903840c40322414012440d001d400050349a03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 625233606 1250 625232356 625232527
    0x30e070603110708092220030714030c0408100501030209280b180a05101a09060318070b070c2309060109080d1e080705 53
    0x44a0b101c004610268890504000c01e100d01c002a001c0c0c26884a822204881d4442020002c000c04555255006098040107442c02200344030101e4203041c504109a0380101225030318025045030f040c40e0074800e030b840982440e000c145d0501002580000c10007100c20202000300f80403865514600c103010219501500f500f407403800311041480700d4100a0400c2d1303000c1d60714080204203038034050045400100d44070700c46210441c05400b04904a00d090700094001c080c4820804445690340d09403000c00300038500343d5070114004101c1d900851409101460300800c40c504c800455200b1800154a0b00e00c3c0f40c0d00c060303d1b030100400c0080900c103412000d400103040c00ca040341082484400e481e030740201207400b601d1144601c0c2000c903049074411b102c0000600884400c503010341e501c004019055500c000d01d640207001201e10b407140540d00c01c9035194002d08440d01c03101c3c01c125100007040342c000da00408544150840c00901400010101c051142854802c452900c00720110108a5032070b504904080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 625234856 1250 625233606 625233611
    0x608030d09331b1b06020f0c0d09090b011d0a0e1f0501090b190c050f010f1109030c0126070f120509100e15010b0c0601091407080403030b090403030e070603 69
    0x80701c40c2c2d900405410012001c0c1139404203400000d01e0000700a0150050300072a101003c40e00003128900040c8072200c0c45580e0722002421940e81c454602526000400c10380040c000021044002104009118030b0f458000d2140303100c0d9482c0e103107583c440c200484042140d08116004140707601003c0c8949809420b003032030080c0d40c40303007801d241c2d60440c0700d00041c2601d154083d100c045200ca01c120f0040b140341c0e90050945012041c81d40407a4083c0c15040d038075402e29032802c500c0d40400104507084402c40303100500600f034524001030055441c1d0010052690307418490418086800c481d50009034811001078851650404c58190010324109205001d0036405c0d141000788980088002282e048403a0174810100e0005080713180541001003c0e14000b00b08000b5400102e280b040200c007070194010308070100c0f00d56a981d5540304081c2e0f19016100040d201c0d103480860f4040f0b100b030703a10952150007400c0c003007010b0704950301061850340c045506600081e03840f40520044041486440010300b5a40f609 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 625236106 1250 625234856 625234901
    0x90c0306030706050306030102070c06030f1116080f1c0c0e10080117190c0e1f3507060f0e031c0212030408070204050a0608030d0933 59
    0x119a40c0c0c2d1890203000140440800010450b030350940444424541c04003100c04200e544500141c05031071000c40e02c02126060950183c0241500c02c00c1c0d4806007d0042c00c0b804007030180d01e0b10b00683c0c0c8260744003103082900b00300c000400710a00da180b07a02510043c1c40020a11801e402c0104406640347c19984035220422801d05400d50140081c4e05444400f28070040110b41c102d50145800a0421180c140116110310003041c040d000c100318081fa074105c00e5034603481c0e9403200100519a45050402e41425050b9010301071b064028008104c04003e081d00d1a016220341150004180b100302807030402a84403005c10f1001d69840a13240056407954106020100c2512002a88807a035500e1440c500d10003055040c6a4a4402c00420794540d0000000c00d50b81e04050809003042c0c0e0010714103034003450030000850041c865500c40c2c031003141c000001450070014010580e001420703130f012060f070302003221648407000c6040c100e80a1080404012120b0b8050310b00c0c0c414003080e200d4200004081c80c0080c50f2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 625237356 1250 625236106 625236109
    0x10605071e03030603170d050a02270105090d06060806090102160305070c0504020d020318030405150706060902160507140a03060509010b10030c1b12050f0412150506030105100504090c030203010c02010b090c0306 93
    0x880e80f44134480c1c40f010300c90060bd41004031403034059510300650007145100d04400b8043d43c1c0d40020203503100d800685015a071801503060070f0344102e517441c85c07041e4015011640843c0c421005813038080e105d292040041e5660310001020782e042254400c0720540e0010510000c3c4070f1b14058840c1d604141030146040a180600060443c5101556014101c100103068410004142c0c0540c02800ca800821522548040c0380c009008580c01d0040b941442000008502040e695282c50140d64000301207a8445040d40d031614003825015204038000e6480e90024182070780d40c10a151400031441c0c1d0300252100c0300c202c001305200e00180d01c0d05440680c03240d030400810034564040d4854140c038140705039a018500a4030780307503110701d42c84220420744000442040118030742c0010740c6e600142a00b88580d8a800003090300f00d0b0010b68200d01032240014040040d030a150b0011400d207400362481d0900c680d0b4940100c1d080d10391040b150001070759078584007095441d000150a400a01001c503c0342185402c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 625238606 1250 625237356 625237387
    0x206070309112b030306061b050c010309050c030f0c190b070b0903071a04060c0815010f1421010608010621090206130806010605071e03030603170d050a02 68
    0x9041ca8050000101411040c03c40250441040707144140d200342a0005400c0080050034a0301030000003c28000c1074150720202942082a0142c0040240c805210120015002400c000380119420f0241620303451180e0307402d00002a0307501d4904051f24850001c1002c200f80c1030b18029030546040f622030801d00c000155101a2080140e011040b4540d503181e802c03070709145000d007541c014604102800d00310081150150b0303c90103181714010078400f848101400b40c41403d03040b511100382903100401091598441c1c0d841c0d201484c0a42451070031200c0c0034100044603803044c0048441c030840d0400000754500c2040305280100000d240114007541040d9006003e4410751f00c404883c0300200062100e8005554030041d0f40a0b401040c45c3d6603002c8540801d08064500c0c41010803034041c89000007038660180c01250191688140c071719620b0000016480c030030b03051401c81942010707030301c0c1000720000791240d01b81c40d078100301e01d510980c6510710400d0110a0350f03001441d199200e4011300ca080f0444c0d5228 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 625239856 1250 625238606 625238633
    0x1d030a120f0212010902090f15040e10060f0e061902071404020a0807050306130c1707030608030909220c080601060f051209101a0103060803070b160e03070905070206070309 76
    0x640e03001d031f651f450f1580050004c0080c0c3c55030702e900c00d103244507034400401e4990090089400014914065985046441c05414243d1054101142c80d081011181c1e9100717010480740d02c1ca00611641c248500c03003076450002440030381c8040140e40013400074044100811400031808608135015460070040c807400611181c0040c11090510002201040203503a442d03c40c400034054002080040109810b0b008015007420b0307c0400f041c5400f4400315519611034014202a6401600110f1030420701200b40144000001c10401c1c0e400f0040000d9281010340398012003002e405800d82d80c1d03c00d82480880c9081c083e040c1c0c011001c0c441078082c2c9207079840e00304040d2410740044d861484200e5a80d0600241091b03645401400040d20380507035038090000c030b0a05041078070001c1c1c2c1d042001310340b18001c1c1c85e564400c0c0c1e071300174044800070f400103040e2110528a01028014525004048082d0178010034904030981c2c00c00b0004c80d486008022640364100011a4009110b1038140840b0005888500c0416a030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 625241106 1250 625239856 625239869
    0x120a020a0b0c0c070b0a090e1009150b0a0e1813031e02060103021215040c091121100f0e0106080c07110f0613140306090616031d030a120f021201 64
    0x1b250142040707002c2e140c2e4400030300e00701d01c0c0d0710307110310300048a40b40803c0d031801220807051410402c0101020010341070010384a801103c9880c014500d001998004140150682c0c031400c40074407103a01010000e801801103040185000c001092464041c21300030b104403d1510703a0f100684000341c01070340041d080381101c3d01035030403074200c02c1c41d120300505003082c00c5150b02601c24600c00784002c0040b0a00ea0f041121041401003085403101030340e6032010710030141020390b0540b41c8000d440c04086540c40c0140c100c459103010903081941c509040540c6a2194841411006800300406c102e9401c075541a500180d035a860034541b907955500d0386548011000e9041c000d8162685800385601c4d8030742151840447c12511014440d501c0303082c110341c0c00000c0f0503030380a07000c1d91011821020b0b0000340240140c000c1da81801e07010680c004124010000c1c140c101100c031070742c44c4000e0041e48090008000805480e0b8404c2d0303007a080c00c0428010384101003901d0000501c100294141807280c20f003064103441c035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 625242356 1250 625241106 625241129
    0x114070c03030c0f0b090a200108040611090907050307020c010311030708042a030c06020607080f040c0e1f0611031c060807080f011a06070308060102120a020a0b0c0c07 74
    0x6810991081e1601100041c643d1701c2c10300c14400070000008001648501c02c860010070341280b410b03c030b03256900c030551080c0403508000c0440c0009e0400c1e04400c0c2d0361144010f20f039042007080400500c031041c05a40c0b000100e0f03400024084481e03414842c01c8842c2c1002c0c2014400801c0c070030119a030910008000700d041006e90360101e010001c2e980e0401c41d120415000700400e6040100004828031814481140c0c071001c46840098103500216001d84500003544820607641c0d6056845001000b008004680082000c90013040b07180030000842d003e5240454490340e0f5050405590400c60303690f170000d00912503010881d010b40d4000004688001c1112130b54000340c5515210048060100c9800200700f6001e016008600001c001410a40c0502501c1c000d10282d1080c22030000e100c81c06407c03a030b070001c1c420001d007004a402404900e41004062040300d4600065505102050b001004410010382000301807070f06100c207022815030070943c0c200c6900d00d0008020901603640000e803154204a02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 625243606 1250 625242356 625242377
    0x3120f1404081c0e07170f0303130f050a030504170c100302071109010b0a02070f0605090616060e01230c03040609021801030b060a1d15061b03090114070c0303 70
    0x22980c0d403e03034100d2015030b40140207603000240390a1311251980105402c0b40051980030f6900000041e0101840440002462071074440340201c50100e68400d0007078500600c489800c0002690420a513026580a550784a07203403402c04103400381c100710100000d0341c0d41d803184840141c00e03503607080d0709c5400d0300c1c060400607038880366490200e402080c403c6665500200c2200002518a001c1009112405080d803d030b03440c280c1c503078010220705e5002c0d0007440c0000b2801d100d802e00a052020092201c54980c608141500c0c0c040e0b65050296044101c140d203c40c1d441d2900e9402d010403c000305250002003447c200e649183c030f00408581d0f8080200054615a03c50070304070b0175501c45804000b0060005261400b9035078507414130401500050b90300600a505040000420310102500010507242c0720f481408940c4411401c1207200814880c4035503c41340c00c120003240c90817910401c0d041c40b160b4101458a0f108020005044520460f64100d04d0140420a25000859841d5050280e0b43c0c50f04181d211030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 625244856 1250 625243606 625243627
    0x702270709080c2d0915030d021b01030519020a030606020c15070605041a10061704030203031902160b0f0105040204151427091006020706110c04020703120f140408 72
    0x5550360000742d08042e000717080c080f0740031288010403100c00c400d404031815004642c0003242d40e6010489022442154408019200d611a41050760400c450208001003201d100c14680100c8c0c0c04140c082c80405e0b07035840104006501071181c030f0011641150500c8012440c1c14082950f403242181c0102a10b548500003003c202d9400b07004041e04a000017060341510308074050f034900d00c40c640603400218081b1000c00c20090400500103104944c90350103103045468400040d0380c0c480320040066044c58003480b00c40310b44001807800c480e48900502920001e82850403c1038141c03001071700528026801008240144d28060f0400301d1180528586204a0350302e09084101e140a01e403101c1981c2170f004a41888034011020307a1102c030038030031580505a40c903140d020501c20382c1507100f0900541c000c84810042c44e80070382c800040020b000003d40d0314140f8607500042c00c030b9200f0041100866012543c03211854864400d0b40c110780c4406034104115140500c094410ba140240000c10740340340020f018260 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 625246106 1250 625244856 625244929
    0x50d0606030c03030908100605060f0a090b030c120f090c100e1302030103120309050d110309040203040309080d02070605090f01030b0d0b010617010f0302060702270709080c 76
    0x21900b200020035400d48030b2400a2410783e041c031401e22184070307094000c1500030080c8a860101c90b0010b180e58070f042810780000010b40c1041c0c0c00c20051100680001038804a104000c1d486928071540c11640c400181940005410024024061445004d810000070600004084c490340004036603140c0c1340b2082110171200030251041898003c2c42d5000c07040d088601c5a009181130f00e00c1010700e001c45a2031010210b04030f40002002070a60350000344080b0b512801404500001e03801d1a06072440e104100c03000c1001e81c1d0080e101140041d13a4203104125110090041c8030060001e0310281c04460700c0c0030801021401002080e5118146c28540410940e000340d1040e075120b04003070604407030044103080240b0605402d215010104106d07000c3c0150451482d80014103a40640360007115003030840d020f00a144d000040c003282c0081491000c003a0301d090080c22208111083c254002043ca03000c04002c0070b1000e55841007005038402c1c101c2c960550703900003150341000c0ca01118040d080c41002c028045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 625247356 1250 625246106 625246109
    0xe06090712150c021f0911061b01090503030901200a03050c04120303050a050a0204030f150b0603130203070504060e0f0910090302010213050f09010303030c050d0507050909011e050d0606 82
    0x80307071450001843c0215401260400d091612107020844841c0701d2a10b9400b96803201b1030050540300c80d010700140c18a0000302a1003440049810b90305242807401559007151100a0151595403010040001c80d110902070400c980b82060403140d26811411107000b42c9000d181228024191168002910340c05030105072001040d607400387d44a901610b060240003400251150464a8181030010b541d400d42c42c000c07039048036405504080c0e042041e86503d443c4052010240d00e8040c0c03154140036241d5a684091800750541004111680c8000c1c810180391003444d9010318042da09042e0100090003c03241c00b150300103412407080300d0303d540c0c40f41c810b0b0501c00c815513105442d9180c072140106040e4158090100360900c1c000c204650340d1200204605d0b041c4884035207608c01075140050000174465041070380c2502180c240281403290b100c50301c6058900071141000060303004145805280b82103030000f401420b16169000c0d896100b641031019441d164058103010302880c4244504100c10340d440b460 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 625248606 1250 625247356 625247393
    0x9060f1809070f0806010806240714070906060206040f0f0f020a09020c01050a1503080a09051e01020c042a09031e03091a04050f031f020d0e06090712 66
    0x803075510b042200649000804080240000c030040c0c0050419405510703000d000d260014920503181c0e944508100c1300b4103402074500c01c040c01c00d000103c001510040b19411b645030b4a0050724200c2e003443c404200703e071150340c403120465101105110101c0c1c41040f07414002a080241e03810400319034101039221034a8284000d4205211050000750f00d4542d40c00b4240d9850410300074840d41d100c0107000b800343d031400c100c80c40401c4100d070820400148210000c0a031030101d414854030b81507813440001d00c6800841a0900182825a0341740710540c1c1c184080c01ca080030840d4204404900904a500817a110342c81040c10036424000e15201103000d00e42e40b40046900c402440005801e840200c0c510f4000824100d0225000b20300100e40843c070a01100c42e10342504044074181440c02041200c1c15000d0102141c040c0200c411075000c0c121b00250080c5080001c0300056500c22440c001501105c801d03401c0030b00b0740e0300080240b1010392340200c2e10034101c07005500781c81c2401d0f14905001d6800b501e565000d6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 625249856 1250 625248606 625248619
    0x3021c02040b10020f010c0c05031803240f010b16022701080c09010b03091005060409020d060b011209020312030a0605031608120a02030d1104090216020a08010209060f18 75
    0x2403c0103900152841d0300d84600d0f0000c4c41414501101600c20302c1d1402002021500240442050080d118400b0728018500070b048422507408000000e071181107039403075010046180800c00c0b100f1025400058010030706c50352080e01c4e00058400b44842002c00e0309000380304101002940034804a564601070501c0090445c0008950350740d10b5455807110b6a8480c80e000d8042480005440380c140340540340f08a4808010740760340300b214444040100f0008220300e0788036070b403084102c000d6182c103209071200600c1a000040e021907400c001401080e401c6404441a604040040d401a10045450740380c0080340130b0a20307180d480d000320300b0001d00381a4010316014400c078511030b80058003801c2481c0c2241c0f059016030b4040c1a20200000766071240c0c1d06080b001da8000c12000151006aa00c182d4509220030015801c06031a4684601644c2c441410003104504100081040d854a121030a0041403010001c6240105900c04111a40902c0d1140c508580000c94103021202c580c46c1c030320102910003801d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 625251106 1250 625249856 625249879
    0xd02040905040605071e2f16080d170a020d02160311150705031807080307021207031113270b0610050910032903150103021c02040b 58
    0x100c00800048070140c40c0c081c00d1002007400700703004a2041580226010300b0303c040b9014848166824200c58101110182d034102101104032203a0402d038134a0482580513014106420584d80091441e80e00700341d80391342040482c41160f0b81c01c15005e62081d0440034880c6090f56070303469040028024078103501981400015007141810840a072006018444e8440c00f21002d0301e160303080c0d0340f4560080d005c0c0c100c4800c40e0108650b0703401034000c4c542c003e91681402101c0d10410101c14100a010f601c141001da10104440c821440d000c1d40da40082c1d2101c0008282243c61500c540c0fa21862240c61180102d003241c4600034014403a41080d546046a1410302a9510342c541200603511007046090380c8154000012440394605801c1c008130054081da10141070002c18001c000ea00010703030640e9010b142d80c0710b034964568000000c440f0013821060303501d0024040321038241414502042c4244500310310140040c001030783d922282c100380c0d80e160160170100c0100762010400a21950043c181c1c0000020751 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 625252356 1250 625251106 625251119
    0xf030b06040305161a120112150606080907061115090a0b0403080403030506040e0d030203100f17010e07121b0e0a0504020a06020a0209040f03030b060a11120a17070201020d0204 78
    0x2048401c40388035060206041d50388118419403400340c401802d00c1c6d00d4140b00100401c00c0c00b007440901d014000e02e4201c0c0354130650a0440301300c1c0c04c5680301d10003244aa40400106c00b01c14045c1000521040c2000c41501100b2902e00d0b80f1100b806c090f084162414002243c0d402e1010401c024000794860813084040c01e0070304000e480380e042150300700c0011781448002421410280149401040304600501d0716108441081d4043e40000b060788410394500c0e600015443c42018001d00280b01c841c421841c444046150781c0c0c02c0d500070b2460225581d1060724100424840c070310f141200c03940c001c0d0201031640c050254003d40703018030303a110314444c15900041c041c04112a0f030110340918400c0380c0320145955140410790316170b026004042c1d80502d07000002004961128101030b0460320a02c0d0004800c4000e5001074410740090002c80c0008140c2520418541410000204c1c103a036402592402c142c003180c2c0082102e5101c08903208001b84480100303812034001d405649103905600410b5480300e84900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 625253606 1250 625252356 625252393
    0x90c12040b311502091509030d0302091011150a0f0e010b0f010e03150103151410050409170301060e030705060a20100c050309010c0f0f030b06040305 66
    0x540655480c8040c0c191480d0301c030090220b4010204a1080c5807030701c2d28158598040d1140140343d8480e001d5002c0009a80030364414401102c03010500d89007689030410f610a0501d002c5010503590149407042002c034070507a59035030b0107011001540c901038840d58002e00905052441880034184008242000d20031180c0c00754100a00c100f4442d282040020b481d01c007098240d03a0307010a255000803510561510651041040307104803d030290803101c1c1e4040100d0905c10500f000da01c292071307040e240c8604c407503029414010402902106c0d1800c03681400d2080407160b1048440c429203200301e40d01ca0540d410880c2c0c8140d0858084178490010b512507948440180c41500c41e031120314420b000d0503e0205840c94044295144044c1da130f954803070907081e0311345074a4064038280300168261050703010405591615024540555071640d8070980c480c10a9041c00b401d45c0c24081c100400c3c030141c050001086540708108982d4040989404a462039109002c06d84600c86c5801c05002e900400070b10510844004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 625254856 1250 625253606 625253611
    0x3050c0d030c2d050c0115080105010626220506010605040807080303010e15010c17280e010525060c0810030c090b06121e0106031802090c12040b 64
    0x40d100d4610081c04108030000340c20007040075011400b895182a070010f0b100c4c0015005140003031000085010481c01000c080e00c00780c1d8011030a681d115030050080c10362100d034820701003070109940d24130341908414400015000600714800418012441010503215100300070000360010103550455842e5100100035034800c1c001c1e21028814507000065000c40041107074100c903102c10310032600b03864525600c1d00b054220b40405040018072451440800c51500a02406840d42211181d88d43c00c008031001c0c000a000340c04292140035005080700e2903400c080c2c501091a42481e00c256101c003000300680041417400d0b58200901c800001400070001950302c0300401358055200d444480c2e40b070404440705148140030080c11104420307420000d11030580c0084140da0001801681402460906244c21072070440391300d0110441c84405a0600e054011303014090309035490140800c0d5510300c3c40c0000c4100d0034000901801c410700000b482c41d07910340c05507080f0b40301c01042c003101401c0030b04100203010401d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 625256106 1250 625254856 625254881
    0x150c0307032c160305120307050c060109020d0b040203040f0f02031c030e07050d0203070909030314090102070b06040203100311060f07080a110601050a06050a0917072c011203050c0d03 81
    0x4800c00e805148501603040c500316031744400244100000c0c1941a00c11f90000b900400521409008840707080200380101406050380000042c1c0395400700c09500192207184c100c081c040d83c41041030102140c460340d00446640d810101000f151700262012034079010b1118924100c2c5030342d8480340e500090b410741110b2001e1184804032205580c9500070005041002c0c0c000941c950300c20403040085000e50b81280701080e0207424000b03001d0440401400f17401404407192021ba943c00140c20040120040d0107030b81000307041d1400c60561412240300b803d042d09a00000c1d1010484207002c0707186940c0e03281110201d14140002d95124502840c1c02c800f20b0b041060201e0100d801100242040700700040c0707241c100c800007020b441c0d10034070b00201034411754014440345041010f491030200d84c416001d520b03050402040002810035a1070301026510242c3c801403c18902511000c1c5004200d0032002500c1c103540c0340c1d44d02d0012001e80381c40d09660798461098074030f07840e004030390b0001c102c90b40643c0550080c00f43d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 625257356 1250 625256106 625256113
    0x2041a0f0a050d031107030b010e01030506090d050426070306151508061002010e0a0305040f0801060f0b0309070314010b010e090402032112090717150c0307032c 71
    0x340001004005502030103250f4200043d168481c000c030784031700b540d8541aa04402501e14040d1a0b44812204d44000d80080079007040900041041000030003200ba40301d03410102a04450a510000402c14815845007400c10282c4800400001d02c140550442c1041c010302140c0c0815503a15107180a09102054800c0241541d0b10025071a292019400d01c240466501c892296132041c04001c1007100e00c441d08000c40d980c3d071000d088040306c1000340307015540c082d40741c0c2900c0b140350501440e16490740da0421803c41c0d040000402c203030070540c488181070700d44091299403a540e03441c260a20b404411351014114174291480ca909100040d4495640c465080c1e03074113003020780481c05104802c0420741d4008c0d0113900101c00b81d03502800f044946c1040d0851142ca13103180801c0b0700c890740c160907002e0324402ca03c4c3d0070501c0101f01c0d00300c1c04408014100f40381d001800d039004c0540300c3c10082039001460002c860f81c0000c00070762101e10030792001c40c0c908007a00b00b0b8044900d20780b4941c45586e40d090708034001c910 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 625258606 1250 625257356 625257379
    0x20102070e040c0b21071101060602010903090e0c12041a101d070e4903081504020a02011a1c111309030c0b060108220f02041a 56
    0x8aa9079440b071045400029405020b460300f1800c802c180e2286030051001050401660188055400440d004040d1940e520103125122290a401c50700654403860a6a1502d14034500090300b040348041100c0b01b0382107400d041d580e64001d0203428813401a07070740d0441c201c01c000c000400681c03800c08091100f85000e10035a69541658041001c0014002c200e800950700c00b0f103500004420301c140350702c40b03e1460300b0545404800e0105910001c0701d00e050064500c080360403040a500101d9451040009035085c2c0e02da100480f980754a89010807901030100000ea034001013075103046aa0541503c000a0030843d9035041c2c0c004024020506010702461040d4460f40c681c100d4581808050424003017001c0301e18101c5526610b040070110f03000303011600014003003000003031241d0718803c00c0c0d45070703000c0d48642803c09080e150407244458010122814001002d040c80125030715020540150030000f090320003034450600303140307031404c1030003800942c031030304180602d819000320642c202c900d01c10a03603108a580717 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 625259856 1250 625258606 625258619
    0x90213050301090b0108211b280b090c060906070309080a0c1511032209050108010519050405031204020d1410060503011e020f0403061107120305060a140411031302010207 75
    0x10000031400c40404807041c0828000c04c0c10030048c80c0130420211301104c0e0704004450001401503c64481c4680c07621508900c40240100103c1c1182c3c0504450058844004240b000800c1ca014003103245005050100d909000c1502940b44a0084c00e00300302110959101450240c50138812802980725048400c2c1c1003400060041c0b0b0b6140154240ca00a94101628001d1440e0110b1045e0851880c10b91300b820000b500880714480c2034042e002100000c01c06141211803004040c01000b04918058504400c0202285020058413000300e440c4006041580380d42c00010003081080f10040d0850a5240c6242200000001d0089480300503400c00d200155a500805080351103801078079020802c11800c8100c4903056600070910901c00300104d40c100f5031a0340b904000c445540d81414142040022000148013880d04c64009a017082e1038144a58907000d00422a00005071056105c40c46200142b2802651160005560018200d60864480c905214051802c0854280c182d000d03004404002c2500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 625261106 1250 625259856 625259893
    0x10e0f01090314010f020705010e160608011e240f021203010b030a09170403020a050a0b090d02011209050c1002030c061302010e10080703050a060807090213050301090b0108 76
    0x500805031241101646036440d001061961034410022556a0700b4400b004285280301400f5124025800000c10b4a45510840c0c0b0309001ca00f100309044c1d40280e8104a1079074440f14450549640000980840d00c4070503145480444607003000c1940010706416005c0e03000b882e200301084c005c031581c403900a1000300c5020380e210010418803e601d0201000140b205160400080d80c000c0c03003070800002d5040c9562070389003914074200d080310503600d80024104103600c2c00c690120041c10080314000e0780703d0701c2c0103810a07a40c450402d0003030040001080d01c01c150380c0a0703c06c41404100c0380c0424488880c40d450016120b80300c4907440751181c0300441001440303502c004141d403078507904800103104a45501c0010080758159010480c10080120840891501c47c0115035078201c0302078440380c000c1c1c00c1c581c001078162080101400c030304c2d40c40c14108012000000134104201d42d0000c50042c1d0391805400b5950460b816900140d41541c2009d00803001c000b04182e19034101c0e0900000e83d56084940e030000d0b0725 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 625262356 1250 625261106 625261129
    0x807230106090c1d0d050d0f0801081906050403030b06210f0405151008010c0906081315021806040b0c0f15180109150b0406050307030f03050c1f0506010e 68
    0x250951222090304490204d5005040d0700003091032081e4140b03035561a2504000004520001d0105581d0325040e51300013506501415081010f0440303040030300b2000507200303000b01015100c3c0341c1f00c1000c6001d044c0170754045180b40302c0c081c0c201550b0342268500000300840c900000d48610300b04100189803003d45000040c05258402c1c05020501d2040360101c0f4203210181103080b034803200307980018082c5404d05c52640350400a80302d0f6907031f0030300c0d004010700022001800c400741660591062400070b00100d07002d05216411003070068840e440b40a26124110f010140540c2107040000d020a58560403805800e42c02d5400080303034a40d050000d0426110200381044e64a02c001d00b1020611981e201121820129101c100028420743c031070f11000b90102030f031900104659035800e44040346082500910000e0001078000740b0240f851a0741e0300b000c90030a41405801c021700810381c040c1d80001071107004190780018402000e4101c65102080c010b00055644070301040036544110068144820300e842c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 625263606 1250 625262356 625262381
    0x110916020f011e0903050f0c011a0f1003150902070b16050f09060304110d1b060302040f1701091205031f1d19092906030613080723010609 61
    0x340c10f19440110006085441c03c200d0600c4818465081c01481090240c100441c0000010401c82c0074203001003064070380c04501034050380080390210382644816641002c2d050031132030001600501510074031070360318481d0424446c2d603000140d01003c0c000c45128490040e501fa007100d488510042070161810301c00c50070030540389402404140e041d4030349000134641c494000c40c0c0250803045060005070072002810422210038010308015118815202803a902401c401e082c01c40c50907003402d841241903030851140302c646544060044c401c0d88002e400c04108558004d0b40c40702c6800160034090140e0300215640c8108070202c020207000c256001d50401c08035030b10075805d50b1003002d180e4070030003a1040050003605c090200611072400c0c02410311a0321022030041c08c0c07011410541e603228054422030310001444100c5424144071750b41c2e03408a10ba641141c50140740791140001442c000995018118018029003816a0b200c14450050502a080b90040c50b001300312440e2102000c100302c40c2102483c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 625264856 1250 625263606 625263641
    0xf0706050c0301150f0c0209090307030212130909050a1a0f060a051e181810060807050d030c05011401080c1801060318060501031406090f0a0807110916020f01 70
    0x891300c00c0c01903640300800802850060030102c1550045105824143d070030424550001030494107255043c050220704040c80700019181003080f20030510041100d000300c0c54001e82d5200440e080120420441d214a5403001d00000552507540360b0446c03414040300e0090034030309200b00242c06480c10920000c1031354401000400d4850000c941005141041c0c3c6056801c0146020144e5070700e0181e82c01c0501c5400e00d500da00c0f4000c050100c0d02070504910720112002c0394103105060000d1900840c109090350b4054910119200070b0b803c0c1180c2d01001144090055460078810313551416100b000c00d41a10900c2c1c0480d84544540c2040c094200392a448414002221a0050104907ca030304030901010040c200d03c440c410070b80d2118002c85901703a10890f5004821346001e4162081030000f40e0740244040e0181c9000805001c1080c3c8641000000804c0041c00003140b00401105a42401d400d1201410420081c504614401030066160705010058821410444600b220501444036654100c002c01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625266106 1250 625264856 625264889
    0xe010e0a0507020c15040911030c0708070f0804060e0a050306090d030f060b0301350312060a080609070504060f14120109020306070801091505010e01080411060f0706050c0301 77
    0x400040002524400444c0540002e6002035a05c5400941d148071900c0c00c40750f603e51615030050205d4811782800348080c0010300401482603007105c00e0743d807920f0700101d0496803110185008110303240c0d0b50070700a100101c0402c004c295141e02014451074841705555076032115884004042e82c6070811107200d15107a004c4011003580074440d420207040b8060203000401d100351640c20b0020160000d0b001004501561500260000c2030039015100c0d03e00c07800b241d91080601d0080540c3c881c1701e840d640700300318424880801d2003500c07000700b030a00602201058503168104141900c0c0c40f1001481003d00c40d80c10110081003e004070a03510b0f007180c0001c00c010402c10010b1040c1310b083c07070114200004a543e641e510001685061100f54484c01044d41c4401032076061000820071918500d40f040302400c520081480140d801405032805882c003400d00040c1580c03141741c011801c81d050192150003c5011034440800c404800150507500d104640601150b80c0d04041044140001d02c035240d00c10403150790 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 625267356 1250 625266106 625266121
    0x90f100918121b03181a04210206040e040201030b010203250606092d06140402031503030c031c1a0105070c051c030e1008061c020d03090e010e010e 65
    0x100128010003800c15450708035008020140c0c803043c0340020341c04902c1c00e6100700600042c2e186200d028003240c03540b842c444504020b450b5000d0050b8007810640c0c07011080d25450809003035104094142d03001700010307980c540390160310750407840581e001c902080c10140400d0543d800801620010781c00727800c00d00c03010100416141ca085070800f03c261040b41c1d0710360000c1751030381450152100c45110f0410081d5055603803141c17000014101c4c1541340145117000340600503c002500354940c2180204c2d0056165116181d00102001d500102903034507100000e9005c0710f6882c08006458608882c1d01a141e20580510b144429940318079025401401014031490031076000d4406050380600400320350400f2a140c0b4082a020801c1c51410111100d00012a81c00c1580c405004143c01c10180c91030b1600c202c4510300500b103000c2c0035040c50f20a11003104c0307541914101c98100b0518640040c8440742110f079030306015000080500408102d540900c0c008124010f0044690b81200c2e101050840603a40b51704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 625268606 1250 625267356 625267373
    0x160507060f2606041d100e12040303020712021201060e011404020403080f220b04240807031d0a060501051801060203070803040c0b03340518030c090f100918 69
    0x5d114041d9a18265803141201204100700e56540081000018045e00101510352400101072405046c03200108018000298042420f50440c1c2c104100a4440303401480098803600d01c42d000d00080f03602e48500068140303290780f0309178101d41500300030150700c89802043c04140c1c4030b50b000140c4002c00c2080000418207a4800902ca000c0b00c0d4840804512104110110081c84960260380e9800010505110703c1548014a1840da41d108054811002c2c40c61000303040003c009103034005040d6500b02501c0f41178100f0803641c0c3d001d801c00f010360341c4e001003a140040c01407900b80512070260400f030810888584840b02c041c1d041e00c1064004500740a2070b980d03030170036680c401002103d00504100000502014540195000d150361809030303c0c5151468140046403503040c5001a0403a14a503902d5000641100c122074003048030710744003011441c1917000f007480e00c50b074011020340042c004030030000340c80c03c10b011080c001c10060b42000d5070750ba03540000394140c070001101c3c070a030301c0d00c2c40405030005609103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 625269856 1250 625268606 625268621
    0x313290c152d0411060a030b03010b04060e1602070f08032107091a12040f120206060a030314190f0e0102280525060801080f060705160507060f260604 66
    0x6200b04c025001d141004039250f03820414440b400b00307842c6c0082000d5440c0a010342c842d1260181c0d010080503240c2214410861000762444219004070408040a14400d1040c00d01810b0058041d661941d92203c090396607520003d0034103030080300300c412112200010064580078061a036510382004c1e0600904041407459039000c07074000c0400300a0401748200780c0c4c40c041d201da0b00410151900020760b00301461410052805d071011034000000304002c81c1c0e20f642a880075250035140c241020203c0c40c0c0501c0c19407064000c072620902404c0c0112281943c09103210018050700e543c2c5001608206005a942d00d400d400300340d00c51182400c1441d01c5200303000080030114092012282240940c0d80703c020101c1d404002414030301000401407107400d821200450052600d6401017003141c0b00c4003107084d101c1c038000d0014003c20200180e04041c40e03610340003800c1c0303564110003900c0c15541d50320005000741180307842e1040412100300c03414070302c807904405241c00407030741565528041d41c078002004000c1201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 625271106 1250 625269856 625269863
    0x71e270f0e09070e010f0608090a0503040605160b040b040309090b0901090906020d1416020c211c02071d0610122004030b01080313290c152d04 63
    0x500000180400c5006404d034020030080798030214150501c103006107040c40041c4105810f521100084d00003880c004115070880b11945021074941c6c1c2c03290341e000111004a040604042c0c20903007807006010381e0401a6006074484d45030b2a440c4c0b65510b11541c00c1e10b180c0d004a6071701c25034010040011b184550072950b0494801c8500501c1c0125070100381e4104c90b520411460342490b46000c104119844a851140900160005040450300c2c040040c00301e010301c0c5040340c45564514003009598030308200384110f810700c05481a0500880b804025602e45161080000400340b882c188814401c1d9151401d01032a000f42007480800b551310020754060304451441030200ba034420f4012002881840000c401d061440c13003035940c580c654280b400c01c180041e040b018242d04100004001001c1c0e105006048440280003058564001080b001c0b00d18404400124494070001d2003960200001c0740b41d503005042d0901000d43c0c0d8441607101501810300c040d06c80214503005c0c000400307840c00c801031580c0c018030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 625272356 1250 625271106 625271113
    0x20c1f1407080a0207030c0801090b06040902031f0f0b040e0a02090c1e0d0e07050a12050c040513020108100f03032106030c30020603071e270f0e09 65
    0x2a0b595440c02076215855040c0103801001c014020408144000f500030700c0480003d0203031022a03104c920038401c014211031710950740c40210030215103003070000851141e906440e100403080030883d2032000d03124240840d0111840c22000401c41d04e094031901c00c4c1000141d00034840302c030b120342c00d0084d07113200980081c690318010301040d0000c01c0510344078007100c0c400bc48a03a80b031fa0324004c240f0080e11402d20125400b82c0241e04148000c0c0c85407400e25040b240100d03404902103001d424800d06041402ca031064200e0300f450100301002c0901c1540b910164401c0e6a103800c6036541c21100c07492480c0d1802141030050b4099001c02c0424030420404c41c1c071200752515514a003402e8440e00b82200c03201c0d8012589501c840d001044605806801c42032000020b100101003030724805400700b894151450028455071011011034a21445032401c1c9444044181424607c13000019000c1d02003804d00f540e810f042d12101c181030701000c0c001c05e103170001c5501c18001c5119a40c00d19040394031448009008429910 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 625273606 1250 625272356 625272367
    0x201030b0a0b040906080f0a020d060902031005180a081c110403030f170c07031139010c12140c030415030b0f0307030303050a0e0105041101020c1f14 66
    0x70348044080004040c0403100d90350b83d83c80c2070039000903941c9a0740100e286401104002040d03000c08179241f124180e04944081560600d0b2412500074141a0006509440303941c288040b101002e50081c2d01640440442100030503800c1e40706a03468042c0c9400602c2d010080c0500321085078084c110700003402d55203001050740c12800550000d43e41040d402a8001392070102c2c0c900c05180c121118400b01506080311712080d240851080d45284582e074002010414022000824130340e00388a61048100e08500101c00b81c0600b000140303081000d0800c410031048400c139890610342c0600310003011140e000c0350f840703c0307006060000d4480210301000070482120411012040e0320003400140050720303103d918a000640003020040481d030320200400e00851403001d01e19040d0b40c0002c1e8480c11a0b5141c13038041611350350160a1780140c0041c64104c120b0758201014030081240083c204640e50354282d080380c50a1843d5020400c881070100d40c1451400c400c80004034001c0d10500000e01c00f99194421301d803501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 625274856 1250 625273606 625273609
    0x606110a05120c0c03060906040605160e01231318200c010908030924070507060b1513031505010b03220f113115030219030b09060118090201030b 64
    0x2c4040300d40d5080c6230048400c0100700030b00d174820740d90018031024000681300c0194001410864050810a040c04000100e816014422030b00c032004e070000408510741c40360030712040901303c400d907270140010002804000709904540e621030b000700c1030400e154800180407500301c4501294041d1940c0c06841d52103032400d20100d405030f4021030281a424008094401941441c140d855007504c19030045610801c3c203200360280d015050f1080781c1d4005e84000340c203440103800107620032120080070144000c08035150b000c80c0b848806020403240507280103200f11030056103180440e1001d0150b010118000d00124108140d00c1c0079101110841c1450f51401e51b0841d26044414810360034225008040c058040240f801d000c0d2a102020302c110100324400403e40c044014086404200400899900e80010500c2d8428901d46002981c015024074000f95190310003940c41001804181c68041a1101041c94000c0018405040390060070707032003800400301103044006e0031002e54160304040e00d501019641703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 625276106 1250 625274856 625274863
    0x1a0102100f0b15030114010801030210080a1506091d060d03080408070807060209120604081b0304050d140d020f030901120213060305070f23091908010606110a05120c0c03 75
    0x100c11424680744c3e00d940c5081404161800f0452420341040b01003c0104010380782c400522440b440c02c0e041c4903080c0c1e614007100b0001003410b44400004040603103c005109504404100c058510340184056041030b090f4110784e40c4401036803004e400004601c441c001291190400c150011300c20038929250080c04d8589030a00e07003002d10159220340d40000c0d40d0b110361500d8413180e6000d003115805400d0f94078054a0b01a968000d07c0814083e042c0160040300070782c8820300c00c07500030f404000c00304060382c940e43c24500d000c03112400c08924030384160804280114000078140c0c02d21242e5100452400c0000401181d406a00001c2d9000c081c1d028004481c2902ca031001c840050b100d80c1d940000e0b5440c2c00c2c44014441300800700800148858481410341d120614110700d07501c8402c40415030342e40c070140004509054088110520030040010000c5210b0b041034000c4812a181655094841c003120946a40c4840886000900a5105010301c011140c84c04010300400b010340340c1070b0f03000c1c0151400400d06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 625277356 1250 625276106 625276129
    0x10f02070f08150906061302090301020c031207020d0810141215091b06030406090302030f0408160e16180510170c1e090d0c06121a0102100f0b 63
    0x1294002c4800c100420340d503c043c00c1c1d40320605100a25140c20404017068540c882c001d03204180c00c2d0000785011698800350115018a88024100ca5840041e80f00041c52102d0598050740180500c1d0308103004240325902043c00ba80d03001c100b5541151600d604a19108038001c200b40d004000711555481668041c00f0005035541c61300351080451500d030303600310300305010000180c00c810484249a0415200d410650350301c0f40d8400e4000640b00041c1c1010303403a41c05610b5031004103110029001c00ea14001050800f80c40c890700d101c62402039101c4000702502c030800c40d00e000c02c005404540c240b8141c8203018000c144d83c220317030505050340d84520105442400301c0f020b06001c107100381c6410401d00c0c10030340c045034844034075242a810211609004650580c0100810301c1d00704000c1076005441da06c8030407030b8588507444411005915a00c082c06040209042242c15240f4608003001c28001c040a8051080d840164050100d140030308100e20010245d03055200042946d1700040c00241e00c0351a990308 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 625278606 1250 625277356 625277369
    0x50a08071b030c15150509040606050910150e060a1b020303040b09090a090c050603180a141b0f15040f0801020c0d030c050f160f0809010e1e010f02070f 67
    0x20305403c0340c100b420311403000320020010300c0e1a0a1546221159200510080c0c0350211400542e940300e07814000c2c080d2803141c01607680701590030140100203003d20315501c12545c8000ca580c00114201500340c9010309000c041039084101085074640c0d040c4207001400143d007900c1070f41e0388000015004240b03580c01035040044580d0000508e00c0161400703004190303002481003030a0000740c1c02c60792400c1d20300300d481c07040394001c80300400801c1c0d00c020340b20b50360340d07420a0040840310700035650308040344460307581e0312885103034040d524102d10016042c40b500651002c016009180c83c034000c209000802030240090a0400402e110200d460b8000720001002001101d00258848824507029403d000065641c1c20903d07280180c18901703190401306aa4101084490442e240c10518400001511916000402c1c211100c101a01007040c4203010380f011000a9881200301241c0e4011300010711400b40481e80302e4006010342450315031150040d0106040c10b8410b8428080e1b981c0c0404810f409140c101c3d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 625279856 1250 625278606 625278617
    0x20d0f0c03020a0e120a0b0903041505040509010b07170f091c0302070b030f010501050703030e010f090c0909030801030b0402030a0b010f1505090f040f0b0a0e04050f0706050a08071b03 81
    0x340100350303221203002c88004e404c440301014001c0c0f61000642e21401820010101da0240740082c991b250140151001070801000440d00c4c0705030300b0f400406a034007070b01480c0d00c42d10980001207052101201542d80c2c00d0f41c80110200e0091544501c00540c0c3c020020b2410020780802550895417902201050b418110070080034404074549006400e020340303078010348080f070024000c1165181d0610b41c1141181c50a00b4410740d11020707070800705c0107448140ca0021094ac02e001c80d14410743c0c0c0c07a90103444c1c40d600480d03102401235201e86421081c0d4040c1600500007500400041c00400d40a0541725002031004044032410189a510314640c4c030320907070220070070050444041240804c01030195140d101c0c1403810f41d2600140c680000c00e90900c61400c6070244d507880c4007a40e20142a03900c1142c1c0c9100003409041d00070741e14465410015022142143c00e0b0050b0282d060750440005460030545200351605030600038682c00031242d00c04018034241c02c1005071244000400003504a1071003041c06a50b69 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 625281106 1250 625279856 625279867
    0xa080a1101080403020a1407030605091e0c03030d0b0d120804060f0623121603060f06050d0308043002160501021f15060306150302090d0204020d0f0c0302 68
    0x3180380118819030690600c0754220400c00026404111175540310ba00024803224203000091041c60010b180d000100444e01d058140301e910540050b404d01d0000e42910883c43c4900483da190b41c482d00701f44160358040d0300030f00c604040400c40f40c20a07003203541c000d40b0403c2240c0c020f0300d13070841c1032408040c050b000c1001d4005003c1400520f001d44904010383c080300b8000740349440b0142c090b0740d035203c6107141d0340c075081c0c01255141da0b0b03030590b001e020304a020100c64600101140c0468608a1480111400307890f101c0103203c603d103240030f540100c0b4002004a5040c40b12500c05840700540104122020082e1020310a8001403210031120398800525084039801a1040080d280203890501603e1003c41c0c3c030300030411030781d001031030000504040710401c0c1407012100c0d5072405004030580358003030012843c002040565059101000719a440a04200080036400c0305400300d1140918058005403280000000350a00c0c0d0010510102c00060024034043c4005040303040f56020501031002070b400055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 625282356 1250 625281106 625281113
    0x7080f0705100b0d02040506130501031b061e030507050c0d090509011202031011091f1e050a050a0e040f0f06080111121f0612060b0403020f0405090c0a080a 69
    0x1820380005501941084000d10301c07000034114000c0050003e02c03c1f5220340000701c0c0c40e22524020100704811580a100030358592800c1565000040c41d119010b140f000c80000d22070744505480b00d0b1350749030040003403140e64100604a02610340140346c070741071220800080040581c1003010711442502641c031400ea81c1d040004104482206038054000c0c10524001c3d1401741e900419034400d01082c1501c0001e4041c045100c0804a0142e40e5000741d00015149402004a45001c250075110546e640c1d140c4911000b0340000103540282039070b4100051040c400880740f0380c0150300407c0079445c141010800c00c1c4046001070207032401c260a8030104c0782c480070100c03611102c0d40a49805400c0107002032182142c42080025203002d907880b04000c01011201254032a0040c448000c103c20071190140c03441a203549004e403244000410040c581440c0c66130001d6102810b4040e034058960040c003603410854200c041201800001d814206d26005481c003142040d07540700880c800904400025024403025401e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 625283606 1250 625282356 625282363
    0x507090b040902030c0f040b06040e1b030412050f04090f0902030f0d12020313020a170609010c08130c170c0108010803070f0f050309100503010e1023040207080f0705 73
    0x10340d40d0300070350070000d010006940c08980c0030f509010a480c00f000d1a412200050f001c4e0a00e42d00300394001c40300141c0456121881c2450510440b041a803c005011440203130b0720092208035000342034160059103407000c1e1881079000b040c0c09842107101600300b076152040001116210640014580c3c2d40701801000c50409000c0c0071416119135010344541c407100c00001d000c204082003014140e9038004006120641e0f1110314070740b020f80181c8554416a00c401121031694620a80016540720303040001d101c070300c4140103400e00350769645d40300c0300152540908104074054000c8100c07050a4000008218001482c0d800d83d40b400800b00108000442680003401c4a801a007182c00c580c0c20404c05280492840b1155421056200d543c40c20300d14800d041842c11405808002a4400344802c124500e1940c4400614161071116442e18856116401071031a45003283c400c5005030a2807400c40780c600409000b4400b01284003410151070900c069440280590000d0050051030001003541c0b0203010041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 625284856 1250 625283606 625283621
    0x181809020f27430f1e030917070c080d0c060b03010b09040c150302030f0105061e2802060f040b180a05030d14240114070f0201020d0e0d060b150403050709 68
    0x9080039400c01c0044c1320024104a441d02c400c1d95400301c1c155001070507074401e1740810750554010030041248030140501c0101c0303a105032800d0358440200700021400c40004a00c0121020300380d1240a040207042e61000c0242140c4008250705550351611400f913074584460291145100d2110f03c0a0742c0e0400c9000c3c4141c10008403181c04141c818810080d0103207400c1e443d01d054800c01c840060301c13400c048104201c1ca464000d03103040c65550104048214502552404001c1d00e895403800e080c00355031442c200c0c1c1c0c0d100c0441d00800302d100c0d0040418045038001d8085500000c5918040c041e4110705a01c243c1b5005440c0c40494441e4400120400d0807101441101109204480010394506041c04102a01c10414418484a84560251250030380c020041d02402101d6a0440c90710703503c5904010b0341100c082001640940103414100402038400c48540e05c01c40002402011400210348403d801020145440303600020990140305012032084c2c00740004501c9100106803550802440400761041c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 625286106 1250 625284856 625284991
    0x9072c0111010c09030b2701052a0a0806120d02161406221a09030d0503100e0a1107140f07060906181809020f27 50
    0x5184001c0c3c40f80d03074840079500031a6004000d2191a80707801d220f000f88201040108044507101c07030103a800e030101c1900240c0c800c034100781012035070302243c03150072009401d0002092a010800c024229030140118052500300c000a01011000031a21664511f8009003d103060701591102c0b044c9000d04800f080f510300039052100700488450328101c0420018000e80540d000c200b02080348803401108003200c07941c0280101040c500140500001da1032a40d8403001601d4060302400c0f6035484071602170000c5070f009240d49080c1c569014504001c1188216002e001c41c0c0000343c5524070a01e80c220844050314a65015000c044a000000d0070858640544080c804000e030f0000101080603c1e000ba801900300c981e6424011400d01d903681240d02481910381000724100070840380711006000e281d100c547c64501c241d81026400290034101700c03908003101301d4080d404039110510b900c0800b41c00b52294101c128040c00f00a8204c8101c030403010010240e85a407520000c240c84026801840385110340b02c80103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 625287356 1250 625286106 625286111
    0x507030b040e030f1204030302131403060f070504050607030c1a01080f1b0d02041407030e0c0d1211160b03040b150d02120a05030f040801050106110c09072c011101 72
    0x381d00303a40110718080e5000021148400748005028140032784c04555242c0c0102c04000c2c0c40b02d0700c5886d5a00159650802d06010307114240001c0c00380c1075030380099030103600103841d450305003071500040002c03a40c46030904508211880301c0c4000001c4e24030010884055411031400565030410440740d19103020f008840c0c1040c0e08c107100010020a240404540c05a0f0507100e900b0041d0160002c0380140542540700f0310356455a00411040d2640340d80110781600c0b0b44000e46400520000c1081500d00070b00d5000391198412118029683c2d0180741646202200340c2e05550458801075002200c4c40d88540c03210900c0000002000b0421036085138465100c00c1c00040c240303c0041c4900031943c3c1120400000b8098aa003c0e100907505000700014000b290780042181e82d07480001c1d00802c140c2d0002c0c03003100c500e5030038071001080c1107000308000145403040c44001e00001e01d41030304125403074502500100602080645034103540c4d2402182d03c000900300792500b404040400d0004140b0999045800303113a91 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 625288606 1250 625287356 625287367
    0x1e1801180204110f221d04060b010c08030c131517010f06120902010306090e030d2a030c03020708160510060f0303030902030f160e010e100519090507030b040e03 71
    0xd003079030b0540305520000d607070704003101c5d4441d5401070f540c0d000e603082000408000b5081c410000e1a60813903030300c650720070601030001c50085401900c000039940b00041481c40103000042c41410103002503c803811500c90b901110594401e80138208080081040d000115042c5680b406610800c9420303004042d8030040501c10b5162000080c503a82c401c0101513142d54443c0504030542e80300b44c0041c2c5c00360000303420801c580100e4104960796640800400c0d240d5030300300303404040b1040c25040c00c41400100c0003400d610580150100314000e005110240341031650034402000421500e1024042c007409410303074608848028144a071a011040c10300c60f06041c1841e50901c1810004c0074001c0c2180da05080201d00310241d440042c1c02c0c000088075149207880388070050030980c1d005105184c107da0b17035802051402c0e602d5540005010b90100e602c407000381d106000c00c001c1e904100060180038681c0d0300601c1c000700d445642ca5400e03100e040c0c5078240013a803201c1c0e40d00300514092040c96101e00c4000019850709 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 625289856 1250 625288606 625288627
    0x3030908210a030c0e0406090207020916020a021309120906030b03011b050c070905090102070209071404170c09040c050f010309050c0d0c080109030f080c031e180118020411 76
    0x10b1052249075000c0540701d2110396a01405007400701240c0c40018070a1040988032a0403c000750400c14090307118203901d002280c2921400380c1c1c0d000300505141c7c0a001d00740c540d03409000204001c9103010942c03a681c0c03082d035000702e420010211380007519503940140d43c502c1c0000017400d41c1d2016656074860703450082c281c1c504490604003800b1184607030074000d07100e8818202507800c1c80031544c4140701d414100001c1004c501010350040820078404c40e2a02101c1e100c10b107003100e04200031800c018102204002c02c0c081c0c80d03c0001c00000c254441e60440e69030f24182004688400d006503400c444100e0408800d110500e403c841c075400c404028603003044103501c207886050b41c507070f20400c850b4011081e2665040c00d1140d00300015010701482002404140f4841c9401485d007802924810001100b00010803000702007501168020040480110401880d00461101e107200190141d0002c8000031041c0c5c406040070b001c1e24620010300c0c0090b030303401c4125005210650b09030300703401c200d01d184c10810a20308 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 625291106 1250 625289856 625289923
    0x130c0b0a030c08012102151c020c010e150a051012051005010b130b160203030f03070e0609060d110c01060909021002061e0405100615110c221503030908 67
    0x1c0c1d0103c80b81e4a00300d55800d5880510b1081c061258412310030500854002e07817481d0000c3c41c01c42028002084065403401c801500c0c2d4500c4509407285544506c007044050641d5001140c010741c8104452034a1960380c14010b43c16688118111225007000c48a8028000c452040a0041507540702143c40c114005041c00f002103034501036001c03801408104551207a41110348400820703030282c00c80765148170744001060341d5002283c400002911100e1401c1d401c2c203008043e90f54001000e40080d003800c1c031007000f0001070444000400300056092055441d1048240070f03080050a02400c0014005440e005002c94104000700da1425075100d0300920168042c0c49c05045524000b000d030400007605c4a14156003024000303002d013001e89080c0000414080744042c0c1112600559444010b00409110702c92134541105011403a4001d02208a0454100c154000c0f4030740b403031720b5450010f0301c100074080b5107070803082070740058000030340030241807080d044200001601d0f60b0f07820050030f009801c06000042d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 625292356 1250 625291106 625291169
    0x6050405011b0507080723041e020703180b0c0c0405070207120507030c060504080607030905030a0e061b03091504050d030f1701170d050306030303130c0b0a030c0801 73
    0x400c0840b802120140b28040c440000640308880503506101ea41d1003e10003911a0300021180510480d0380100883c5003034030071102550507580c2031203144a21002c40c8070003900000da0a13410b1051402c20b0340322100144d6498806403126002550b10344031101c0c8043d141c00c201d01d5215014a20384401d000c0683c2d0001440012104060362040c00d841591a11604080482d8001054155040d6010494541003409401618100c0040f1107042c1c1c0c40760000c400b560003945001d00030790000c00c21100960311400090141c9200540380b01d1801540b440c43e15124000c0313140d030900c03903040820141c0162900c07030a110000400345070214102424030001500045d100a002000c1c0148c947c022403038036001d214020a44460084089419070307483c0d00c0d240c84050342410001e10750203400d001071341e91030140c03041c0c90054074062b000390b06607950f01d09614140200e102c0261011b04441100040f108110801002c0222040d607011030031281812000d0030f101c506030030200312905450527052036003000d69940c08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 625293606 1250 625292356 625292387
    0x10f06090506151c020a0c0605060303160b10050a0f0e0c03040c091a1309050609030a121119020106030b06100804030c060b1002031e040e070e0f1003150605040501 72
    0x40d81c4401e241484c25114058010014216002103102010380d504004070783d2140380549030900169585100b0903417a0f10420401031003020a8035400c0011450a0402c43c0c3d1148070317041c20110071500c0e100000c001408560100c3e0300b0a81480382807019103c1501002c0c1c00150f440005425410960368414034021a80200001103a407044641c0c51ba00b981134000312400c0b0040d010081429840b0000740103003403a540d064030b051091201103012440000100d801000244d40d80c501c1c81404040740001810b0502d00c0131443c410180f100200c0b40006400c614201c040c16000040c032640346107030004411200424491260087d254000e501f20340085040d41d0040d414a401d1403200c2032464485d00800741008c416801035a8044064200c9030004010078401d2500d07048802c070300081c40c240e801144501d006000c882c10030000812442d50080380b500094100050401c0030b11003010011451056400c900240040d403038043c540038200014000b0740280c60203142061806003801c0000e0807840c1e01110b2070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 625294856 1250 625293606 625293649
    0x816080714010207031a060307050f0a090504020a0305010c0f090602012918070f1403070c0201140706021c0b0406032a050a0305010b1816050309030c010e010f06090506 74
    0x1c03640d5a20034072440010f15801285800419031041600240007812034113140a48100306011500780340c9054034000c2c1001c010050044142800d4040740038142c05070007240c100301904800300025800307010f44100c1100030750342d030800b003039450342d00902c4a4210391058013503901d0815218520070114140d04084003100c941c000001080d80003265440260710205a9600030341014010920b50100704c880074060140d441e50002220080c009000e48819076100000c07400f100d000c04010350040b0300303000c400da82c0d6601081c2070a210f500c44c0d40503a8042c2e960944400c0d9a4411001101018464200c65200580f0100001d50441e078850a940c01c3d500c60710ba10590740c80161a03002d03082d0300d0b80e40000c2d103c09400c1460156903032805c1f038041c01c0c0404802d8850391030b484540404c40740d50080a031081c1c10341e46000001e2000340000b46d0f001d0b40f01400c000c125020821800e038010000f40074039040b10101b88000074001c0c1401482008541140d08180e80460400c0280034040d542c402e03443c54903041d60050b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 625296106 1250 625294856 625294889
    0xa020a0e0c0f0f090d0b010501030c050903150414060403080712090b010b0f040f0902090a05030a0c1e1203020609070801020f0306040b060915070b010b0306060703030f0b030f060108160807 83
    0xb00c502d009a41138207074002d0503440301c8010000b90181240c121902a01c05018100e0074000584617400303002c461076056840810311140e149407200d0b031181c020f801145800a40ca054441c0c850a100084809401168405042c040d00b2036002c0200e24108041400c2080343d6401d036500c86007002010b105815000314081203c002c0c84c2c0d503101c100d40007440c0c810101500f1541d54100c2402039046122098451400203c001a840c00c0214001a10703580c002c680c07140003800d0018901c00382c1c422000c0341004d00800c110126131102e5420121a425009030020125841e02407192803900542d50840c014590050040b17040c86d55014007582c0c4c1000c41101c1c040703600000480403a0b03160056914269100815141b0aa060504038004051f014082c40051442e40c3e29550504510310080d01c0c80307500000c08001c020701085c0700c3d602411042140f20000300d0300810b60000240380180d0300103c69400e0300b1220042126120800032984080c588903074a43c02189082401515001548901507003501d09406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 625297356 1250 625296106 625296127
    0x3180506010815040b151309061d0307210507060f05060405060a0609030809030312161b030c020906040603021e040b150a050a02070803070c0618051c050a050303090a020a0e0c0f 78
    0x11061608447c07590104680c8a885c01e0070005815810203201481001420342c9940703d40100803034841e503801100308008050000c541e212184200318084040040c1403220b4000a8000c0c0201d40c100158010301149505107541007204480001c1c120b18442d0365006170811031250001a04d804036a00403031001c0e1607080c1800480e0a40c8920f1428181149200c410460089110b5441000140c0140d58160170070003c410f819603140d4200b1030180105203264800030051072f00c0340c031240d4407030405403020078072942e41d0b40442e203029000814584507181d0807400c5003140c10b1078810442403200c01c440b4030852419820080c0490b00c21081ea00c420060005415849103000300624002080460708072a950403081c10400c4c0791462501030320000820503018200d28640074005801a60002040c40381c0304079141d00342c00c0301800310941c11203440c054001031101142050029500c642c0c0c00c0405401036803514410010081510303002101c0303e1540c2c1060140020580b001d943c2d8808480103020350790010b911 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 625298606 1250 625297356 625297369
    0x9070e03010b030105180706050c070512010905011b0311160605040206070506040503070c240f11060f01050f3c091602010e0a0305070206090103180506010815040b15 73
    0x6003041d0b019802d003411b0002000c0c1c07843d42041c020400005a038510382c0c403040200d8141c800c1d16101d500c11b611050003401246813405143e000030350440000115081240d8460703080d0744003050702c042c40a14050003040b049030140906101d1801c4822498038280045107961080c551001c0040c1c141d541d11400101151284d000b100c0c2e500e5040300481d403075490140380007680c0342e00082c021504200d10410004030510343c440040f0348440c8540c0f84825142c0520412111104442c40d40420045000e080e20000102845090b01901c16080001c0f000d40c1010309000400c271500403a01e006405100c1120036030765072154914940b00701c4c082004c1c04080c0c0440300410301e503903d10890f6031000444007031101d8005460740401403810300f900280b21001c3e600c10001d480302e0805401401240003086000010f1900c0d2000f4200780130141400034807100342d42c00c0034040c407400403002c40703c3c1e5102c0710060010100030001c521a0304134680c0b0500d0300346420782e1400300c400000780a8401c2c448603113500c6070b200d03503801c6e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 625299856 1250 625298606 625298621
    0x306030b0a020702100e010f08040c0b04062c0d030e030c04020a0203030f071b06050a410417031302041112160816020a020a0b030a0b0f09070e0301 65
    0x4800d031507007480741c0340c070000307602c4404124032440c02010b80e04130315806420304c02c20416050715250f034102c1d03c644041d86c008100800c2190841003102021070034541c0d14015001a00302075842c100360750000d010007007602c50301802c098103501c0391004480003175032140089007219504d4500310318120984070100b8074040c26040c0d0540e1181c0003158800041c0c1d80000030314440c841040c0c0308481034030f0701101605c91200321001c01c00c0c043c402d110604045030050308040e800458680b40020014107a08840100400441804c40c0e0b01d500c3c030003614248006011704c140f801c1d1603040445058202941c405403440315400c007006144001200090001800380784003c11140c0140c4140440d0040d91a074070300e00d40c848540909110041703000305801c80c4030f150100407054020b448100c100c2e00c030001c081c40d880c140000540118811886d012005072140c000000080030751100340c80d01c03030600c2c844a106558000803d64007450a080c601c151943c2c500d10100e40041c250304041c800b40919502107405001c19 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 625301106 1250 625299856 625299863
    0x12180b04090f05060a03030207060f02030702030601080a03090b0a08070c02010219030504080f120a031515030f180f0206030c04120813061106040215160606061b020a0b0703030603 79
    0x200e0009203403400c0c1d030008031040c81d40001c1005182e8070042044810072580c0406030041c1c4c0000428400203008102001701054140100c038140890303940080d01e00f01c1c00360451040746e000703420401d04040e003248104020b000b0f0178410505180c00188000d00c2141c00504200030001080240419a4000e02c401e081e40c0c0141a40c04e200da04040c240a4550b07030040c460f00241e0b11034007503001103034103010862511000b00c9080541c50103c00078811400341044002c55a00b00056880014401e0350303d0400c200c0e888800d49010807041c450650202c02c5420741c0c0100b0301900c28002c1c603103000403104a0749840150341240c0558480c2c03030721100c0041c540155000407080e40800d40001040c0900c3c00302800b080c0a500711103018060b100d44c0e044541c41c0101201e042194415000300313006142c1003120341903990803003040d00e003401c075400505109803c0d05103003070b00c00d80e0351600144409039208030341c08400b00903a8840700b06200ca40e40031840d403c55600c80c41d0070740038010035861304242c848d0300224005c0d87c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 625302356 1250 625301106 625301129
    0x102030c150c07140c0109081207020f062b0506040c020d030c02071203030f0608072301170a0228020d050c0703210f0305150108060f0a170705030a1218 67
    0xa1340801c40f0f42d10760100708018042405000002040000003a01088082c2ea041da800e0800c2220b60901060701040020294056424007259403810100c0504d003202500d4200c0d21b080b18103140b00c3d000c08580c0060100d074000d9052014050320300b50000b800e0a1042c0d401d06d030004020011100890911045c2d03005522580c0c0008600c509169050300155107407401400204007030390703481500c655100f1040c4680c03032044052059024455590005144499106050180c85e4181c10409060007400c21204c0c001c02c4c0e039005c1980721008002c0081a0b095109000111000038000007019585408040e01c9404201e80020040c1003040e0a001e00c0c0e005580c0f2154800003407070000102c0205140e02d03030072100050301e221141c4132001d10a01901c0e01480720005d03c4841d0803580303001103850750002080140c000e02c128a82c806151200e00d081402025022401c11048000d5803d860921001380d1205200303601c030003034440c0450345900c0211040115810303c05905140713035009414034407503944800344100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 625303606 1250 625302356 625302383
    0x151106070e01080906060306041b0e0a060905060108090c060a0908030c06160201020304020d0803041a0405210c070e100e01080d030c0f0e0103110f03011d060102030c150c07 76
    0x303800040701c0100c01c00c02d07200c1c0500c40e038a142c0d1181c0d9452007200c0040e07042d403000e4042408183c46441050080a8000c00708541310788414003401458000d6540b40340c6d10b03540e004100648000340c880d00ba0001d609103082002420300c061a02d41d6405070800151240c000010f032800e1040c09208810002d0030303180142e9880d001da1011482d210881100c10008000100c44005c0c1c4661040c42124420350b0700a01c008400c60742612a0707051070300022301c107c402d44541e014041002c202104030380d1055200c1d01c002c00009512620440d1143c0314040c03070a5001c03c00348103001003030034040744403016100c11640d03e1000c0daa0340903050700040c0a5131f2250048150610010400a90218102044e1030b096241071110401c105c5045400702140100c85000034130941c1d000c51558400d80000c0e600711b844201390340c2056001e0342d0f40f0042d0b60003070703010182c25040031400703003507551242810300d40c000800d001441c10445800742c42600c072180d0080c1c0c4607150803407e000425a904040070f0b10100c64000b4100c2c200038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 625304856 1250 625303606 625303621
    0x20a0f1103070918060e0604080a0804081c0603020307140f100c0b040506090105010b04060807120e070b07020901050a2105031c0b031501060f030b06040302041503030912030801151106 81
    0xc482114042d43c0081c10710000628029000507c00e000e07542c030054280c070b044024001100c013600082d0041360383c20020481c1d040140b10742c0048034140c4059100c00a42145103104044ca0704640c1d51002a40e140c0300011280260345100154107680000c2d203491601141e02e090454034900100c80092008005506100512100181c0076115441840007004240d1b00c0c0e030440f0301180501e00c544000540b10f0300015a0480c40744120813041c5040a01c0460b16980b1503100d2800c1c000603410040801d5004141c0c0c006603d0602d18030f82c010081070320b40c9248541444026200000240c505180f01d610030a50078040000c10001c0300c01101103607042e036440e112004410000340c050f5024541c4213216201110041280c802c103c503040741c182e0340300e00448001c100b5059014152101c040759000409001c0080940c03601c0c068401d034180c002640f0340c60b160035072034041c02c18110340c3c0000604140910b18070780003139000110641520b030b601a071150354840c460021100900c0c20b2044040900840701800550b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 625306106 1250 625304856 625304891
    0xf07030308040b0702150c07060e0616120605030c060f0904050a0203010305150f13110d050304180207080a0804021c031d0f03070618080601080a12020a0f11030709 72
    0x1030381c4140755003406a2201d4000b02da5030803401010786034200394100400d01341c000520040a508e03100d198040340190043ca0702d9402c02d9002c0320072502c0b2500301d00700503103c954041d18141000d920800100708460801010aa40d684152403250280b00300080d40c04000c079140040d03460300100103006010503c4d0035010540030f0f40080c03004403014421035029400c0c55000ca0f004034070504910701c16503450f079079021820084000c4000281d45546400190b403005450303040d03000c07039414000c20045685034034100c101200c2c403407030804224805205015210024485004850307294560303180c08525038489000041e483c40780740300c8862484210103000c00130903400c0808200680c4031500c04105078810700c824040f2490166112a52540141105005035406080c0c1449403401500354991156100c10500e440e05030280c00882c180d81c0488084000c00001d0380340c02010003800d2001e040c0d4200a41c0e100b070841046200c000f44020344107240c000f11078404000350402410170150501c1105001e2411108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 625307356 1250 625306106 625306111
    0x70c17040f0e0105011b1704030b041a0f01060c060b01140711040f020408060604020c03090a060809071a09130b130506090901061d04021c03180602120412050f07030308 74
    0x2141c00b040e400001c0c041d80038120421410540d58000c80200041e0794481034860030000540154110521000c400b003400c03802c641d4820761060f82c1e40c041d420b081b28049803d00c0710081084900b28000030050040951003032041c030416a1280c404910903001200507100c0ca0801c0050f51651403001c40c82105100c29561003c04045c02500c0400000d00a00c5441041c0d20480c0503d00280c1e0005001c120f150400e07900a010f504921020340341130541d90000244814025444080022018018800341d04000c0c803011008104d00c94003008004406001840c0074080e07031b828140f04000341c1d103c01e89110f686400c0944041c1c00140241d50120594032840c0042c03a06880881c0103103250800140c29081c144500d0040e5103040b503614031040301c0c94010740003105008200b283c00001c0e4071101c903020304482226031109882901d07540300c00681601c401e2030003030181e484002150720500a540684860804441c16203061140c9600313079040d98100300d442c11b442001849041e10482400106050b88070805070b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 625308606 1250 625307356 625307369
    0x4060f0f02091503090709090f0302010b09190905150c0a080c0711130207171809070806010c17040b03180703051e0a05060708071205010e070c17040f 66
    0x51800c4240200049000b030181254100b00865020010b01101c0300c041e59100f000c080031100e0302c070b80301ca810009031580c1100403180d0408480c81c2d01c0c109074083c02241e901d4a400e030b504518524144808100403541c410401101ca079446140b01e080c05001c0c0300e000300800e02d00003540700030f042c101d004030407551024000c00f00240d8041c01049061100034200c0e030f01030303402001c2c00034610184403c100c01500e201142015155080086000041040e8030300c0c074848100000903501c41e591189091060111055600c1c0b04280d224100b0100b1504240c0b00c42c0c03c4503080c40d003050001c11515000701520b02c0f142016604500c08100085d01c290700c40000e40c4120520f01e40c09801c049009a401e642d80e03803030300000307286402c4401c840841043c10620715031098510310448002c00f01039141c1608114050314580005144441008405504078100210703160204000304100d41c0b5200c0b500c104080040e05801c100207541c10844280904421101c0d06480e10b00c4c402035445a403065074203401c148078850003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 625309856 1250 625308606 625308611
    0x1611061009060b03090d051b010c02060609070806030607080601050f04030606060905060705070b0a09050613091b020715020f150a0c110a030e1219050c030d3504060f 73
    0x3081050007502680e005c0c507200790040451480010003030750650848603510b901000a1030800d22012000d0107540d0040d90349030098503850400d001808200540100f105c4117002d4141c1c1486055100092195030100c40c46c03404400a480e550012501032003840b080000615002c9800b005021056208104498860725142d040c40d13598800c0c80303802d0003500d42c040c166800680040000501680080800c0c41075440c00c800b210391100f001481ea500a80039401752030f03000351003e100c00c051030320a00b521224042c102e107002c0414814025524685070046030b0762003407000c00756944c1c0c0e4020000881c0003241001540c00d0425241400703040080115504c00703100d8203045410011500a603884614100f1800c068420443e094809444814003981c03002e421145425042c110300c0d1081c0140d9030105181000b41c100c0c080d0a0074982d1800c4070001c040e51181d000050f10700c02c180d0b00001d4039405150160701c9850040a0510000c410350030303070034a1041c0c0742c0b400020031040140c2c2d81d2110140d004151001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 625311106 1250 625309856 625309859
    0xf0a0909320a0303090c0306020c031317070515070f0503072d080318060702070f0f05030604031b05060106030b1809030331030f110312161106100906 66
    0x10a203003910628690101c68101c40c50001c0400d1094108502c001d0040340d011642681d2a030701c9400704d91000d900c0102a8001181140040c02c0c1107400c1d2000b0000d4000b10014500d9190006407210314a00c9171511807207800d5604800031500340e0558104a800c03507071540300c40c511400c02c41d40b00d90004038103d6203401091040a0300c85106443d002c2480204050a21030507001e0759250010f90024020134040c1e0800000030940ea901003119610500b0f007603024106440c43d00100c031480f900d4640102461040c030100c00c0c0029100007983e070f54419013504e881c9280740c0b400c00f906650100c01c00c40c0540103005030727030011803420b406402030200300c00e041d501500c000d01620407100e1500c80c1983d40d440745420400c00700340110000302000c00082881071960b0070450b164038201401c1d001000046000c644040c09520000313802040195031070f81ea80015519008416400c02c01e900c600415050540003180b0245980701d1240302e44140707c2c900d040489056082070501107552582a100e8468401e003003580 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 625312356 1250 625311106 625311173
    0x90501020a020d083714151002060c0d1113090203061f091401030f05010f0807081504080a12090c0821030c09120a080705010b10020307020f0a0909 65
    0x211309490585c100844409034004244000380701908038029821522103032020041c0c80e04820f50f6001c1c030b4101d804080f5032580041400031a81c00401d914041d5000f5904004a6621620440e02c40340000c58002032403401c0c4901c43e0b84280118034072242507006048001c40c0400d21540110300a60301128440640e121140f0016644200b801e074940000e40843e104104005072080c03101402507050401062002165840700e0803074801740e00072192031301071100030407441c1320511269000d071002c0005000003120703594032174a40c0d10f0082c0c0001e10800c400030350a1103061098041e280740c64481d000a0220204504080482080f82d0181c004540900c929020341240d10b20095020351117500c90072400e66880603012541904117420803a00591011111654010180041a1500d11844089450b1145400c201742103e107a80200d601403d0080081290749800100756841c071581200c0c11000c00c100040414005d035031507807200c1d041c070b03040000c00000c01035006003480320510945000c0d03015108140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 625313606 1250 625312356 625312381
    0x150b0405060d020102030d110f070506011401020307051c1403010e09011a010c02090a02090901031a0a0b011e090506160b06030307031707090320100816030f090501020a020d08 77
    0xb24000d015a00820541c441400290001a652040d680c0344504014040b180d0b0041a44000f108480036040900140700d01040030818805510003803005608004850f900d0320343e0707480040c41c220f032500c0c00e280d0b114064601c0703034405800001c240c4480984030759680411210642094503040555401c3c41018440300241d0110306104140594543c2c0d8040465000d00035412400750103100150f4081040d180a0340b030304902d0700d0085108440001c00c010425640a81103d0702400300c00e40705081c8052644140c0e071242c90100303807826090043da80c003031200c0004e41c0d6030300351648410f810040100c0da00c4440e0710301c2d040254920740101a4802da50f5185c0c82059141e2007074040042c080307030610040c2e252800320365404682c403642c04e0414588a540740d0b150001605c002001c3d8030889600d80e0b680e40c140d8201407021046145e024100450300342800a20807051001004001d010107940d10545180c50403990800ca01d400e42000c001c640d1240001b50007502c1c1c500c0011508045030301580820f88038440c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 625314856 1250 625313606 625313629
    0x118050c0328050a02040c26010303080f062e09080c0303070813090f0218010806010c0b090c130f0506090115050a0306051201151d0112020a03150b040506 68
    0x15001c03a4000000b0303024695500040c8002a03d05220306400035005031102c1c03103400c0002641d074448500d21030903021b04100101440d040301c904040e40000400c0042d80100100d5005044100e14001315901e4401251007105c3d0000701841c3d030501c144002ca942c90f820502040a6034813540d030007000710f441d0a07805641e031061a840c140c1652040000c040400d07590006460021127000198142d00d580b5064041a1402180311210295002941d5056420040007034544d26100b800c04c50990f140000021b03105103143e50020b85948007080018026038418001c00c0c070f181c5001015078868021406521000341101094080d209181201107451171620183c80d5049445407140a80189a1004103d400d6040060424107141d1221070110300355a42103849880403815a00004046a100c42c4030a0490b9140e8000d0780003541540b040b40d20703c80d503009028156002d050300106d6544552000c82d46261880d44040c149400d0603504030703648000354103d440794007400c44040c010346c0c41d4078042000c4555007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 625316106 1250 625314856 625314883
    0x27051504080a14070305030a0f09060f020d12020426010606030b0303040611210904141302121207080301060207140a21051c0201060f0e010501080c07050118050c03 72
    0x82c03280c2c500041c404000f004400c000b64001c1e2038007240d995413140d00d16000658004003091a01c80000d003416070002484006000b54a48009100304141e0b01030b48030030030340c06980204048a6100f40d00400690100d400902c1d4800b20305038118081e01d500310010940e0400c0701c40310750030408001851446405001c54061006000d03520741864003400f699590b92070001c2081c18060106880042e200040ca540c100c5400510251341e5918010100802c982c4003101440408071401e0500c00c00c1041c59114510301c5906079803018400424200d018030b04801820540d902c00800210502000346200c0514121980d940840d2441e42e100c1c41080440700d0f0503800207801a0011400300810015150440c0640301c074bc3e5040c0c1074648164403102c0c00c000300b0f01e0000310460400307034000003626824800c202c002c0c10402181c07903441e4206031842e400010103110742e5040008140100da0a5910541202e5907603900000030480841c064810041014507048180c800d4011301c65000010304012601c1c0342002c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 625317356 1250 625316106 625316113
    0xc10060e0c0919120b040204050f010807180f02041202031b060d0c03090506010807081b03190203070f1202040b01020d0c0201030c110102210c040e01090c2705150408 73
    0xd04060203c02a022162112090720310140003422504807150303000d200340035920401507031030b042c014081650700107021246080c4040004000048010441d0b030300342c070a1685207494441070402c5400180500da0f945103072584c4000f42c00940141802440c0c40c001d0302c25010759000030344403101039034003140300541d0380d820060411070500200300a80c4800340d2541351307003400101001e15844451510900740c02c121665032003110180480c3d1400c000c50741b60703580b46240b00c5100c502c0e2113020075124412902031a4050000580001c1155401e03c090805000c05201c0e6481b002c2da2800541c800ba402d40500782d016504d49114610030354070206003030f081c102090b21442c5011016074011402040c011202008010030f00c0100e41c001d100a000501d810641c90b0210103004c3c1405205810400700501000000b007070403c002c01c0010103980741c2504440c0c0c400c20001c1c1006585030196250071801c80c000550312a14500c2102c0c6c004c000a103074041d51029254402880700c0c46000c0242c0e449030f80508480c80d070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 625318606 1250 625317356 625317367
    0xc060f06013902060d090b04230c191206060626040209060312130504051303020706121d010903020705040e030904021e0406021b04090b07051303080c10060e0c 70
    0x40031400300002c588044d1a25107805542d090500440e00ba041040320005000010b000502c01a240c00d6050712130240c00c1d0302c024010100e6100c0e42c42d01c8062405000300850805441100b002e8400d00e8010b0a41d420407a041001e2450680004e003154010b01020904041601010025030580203030900c0c0901c60f20803580e1240d80070803180520040c116a40751180c0d0741c03412210303060107014008003e07800c01c40401003814001003005540c2c1c0101801040841164400b0200f91f0001e0301c0cc08840c0103003802c010305041d10044030040c00304409044003007131503c0e036809044c04055006c207081c40c3c020750075a88030a80342c41c108001e84190b40f0040040364001d010180107483c182c1d0081100d0240000d00c45da280800b070951039801d4000d40c0c040c4015803c8590300c030401080707500c00410345c080101c800300000d240556902e031366414003510060800c0008201182c004600d82003031070103940c02140c60358540342e1a1350002d607100c40044844146074280040000d0b00805119868081d07a81500101d0500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 625319856 1250 625318606 625318697
    0x8091f1d010c0f05011e090209180d0807180b073e0402130305060f070c0f06090f0c03110a060e150a050f0f1e0702010206010510050c060f0601 63
    0x1d5a2107001c4e01c0395561040c1c3c20442e015101304040a80005103404074200c60b040c01085110b84000b0310001d16031106000016525201186486a4400794204070261f80c441100455403029000d03910300c0c0c100d1107464045041d10b0341202411007144558a0118420104590303c8103d40f507480c1810070044040c42c2e0712040e082208405680b40304064001400d01ea444000d1540341c2e5190b078410380e0039401810900c080c880c0c1140c0010307402501424150100b040e965510301ca62000d1580c040c14456450f0354680402c52820101c00c41c40e6000f100c12050a926414611703000123154040d40e1140d5001940041d001e40511103e0301c40c120014020010540c0d80c001405180d030000b400e0b2002c10038104121203810301c844024188840c024004d5940320b000300101e000720550000708402c105001031040790010303a400140941500d0043c3e465010f00414400c054895005440d5500000d01400b002c0222a4030390108181c480c4a003603031100f449680099600c084040c07000d5100030f62100800d49184107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 625321106 1250 625319856 625319873
    0x30706060b07021c020d1217041103060c03010f03081804050f0906010510050708030a1b020601060215010503061303020f010c020f0c220509191b0905150d08091f1d010c 74
    0x485024101490b6408c0c0015076002c203e43c013110102c482c00074107020f0080e03e007010402c0301d5120200c008480d10b503506284201c28030340c41c0d80c0300007000110300042d8100d408103002e01490100001a005001a0525041191243c00c0c21194841e161140d039000061a1800c1d00301e00f1706001858442516040454540b000b81360b1000b80200c1526469200900380f000c00c1700e449003c0c1c0c0e9080d6000d050300c0d50410324000c1c02e20990300e00809070715034410010f00c00d643d0042169030308420f0b01840ca0410080c40d160a80c1481a0100d900610b07500c0c201c1030203061600464404403502c407403415103e01501c14420014881030030300501d100040c44052642446c0b072598087ca0300b00e2104011070354024580340c560314141c084144115002400c49000401524a0101c0c91300500340c842001c2c4441d24200082c1c2a1091074030300d0300d03032051030f22203a000d00b4041904100c1c0c425420240602c1c4014841e14940c030001418a15484001680542c0800482104c0d03c07110744c0d040c034165581460f076038480c1c840451 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 625322356 1250 625321106 625321133
    0x3030901120905010b0a03080a080c2b2004050f030a0302070509090f060a0e0d090b09010c0602120a0209030d0c1a091f1a0d080912030706060b07021c020d 68
    0xc181d175982d03000350ba07195035030010207006510402640f580e03407111004c0284a00009055005640403d100070607168294441070342e2204440c1c0904e0305201144503800025201e1382c190300c9016412181c9003000080180020001c1c0c6001780d03082d01200a404050554911044402800581202da0180000d1800c82001a00403203004101c902160903000e01c50b0500c441614041030341a0380d0000340c1404202801014000c80b1f103803d0a41c1d0351361401040382900d125002441e41040310417074005040088079416149441c40c1d071844252940361051b0440000d40c0614a000d03c00d21403a40c080403001d100e902038041580e0f104071006481d448050a40d819410040e10124060181d1041301504900214003007880000d11080450032100940481c40560040c00c03c1d00e016181c3d601422001c50114000c803062035030180d0b5004980c4500b05580c0b411030080b82001401c10b420000d00007001402d4030302030300d480e5000f04c41c2c020050801c40000341d4030500c1c1f81c00080d04480c500421700f01054190304000c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 625323606 1250 625322356 625322363
    0x30605060301051e031e0604030e090907060f050409020c0a020315090a150b040c0201061e0608240303071a06181303180e16050901090b07020a0b0301090515030309011209 75
    0x846240e48100320703200c020080180311200d039007c90204001c1c1a40406d00800c24003040d513243d50300b820245a4240ca40c2c0e400d005c0d5809201d40b0070008420300e40705004940041c480801c0454850742c4544025480d6041d14005034402d00c5101051512251240c110714000e00d400b0780100708064403552481d41c0491920808000650748000c071600c140c42d0f134000c44c2c03114035596000081050811070041d400c0410b0290007039840003240c109120305500881c480d600075030044c0142e80c16840c081d4aa65150055515294060001040e4881000000000303102c801e03003200901c51059640a041c041a000b0035088004080e090780e010607000241d1a0100108500030702e8012040720449550351030200c1164400400c49a5030300402a1131508142906001d180514160f880c0180c62800241034a0341d03030113490501000060300400315076501c21400000c000034010300d6200d6039100c0084008000443c0d103c55034201c111130b1904640750101c110354880c00140c480682607010765841100404510070200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 625324856 1250 625323606 625323613
    0x3110301020d0203010b19050901050702040b0a09020f0d1b08070c060e0f0f2503120c0501051302030f010e190c0503070b191b030309030318080a030605060301051e03 73
    0x40b52051403500003580605140001682c1d618102d001d41c00c54404081c2c21001001414000280d00b680e10604031880039030111030106038a12800b0004644004603441101100d10000d42101e0040ea44005030401c59541102041540007808518000340d0f84a0712680006080900145101e03015004003460640100800505003101095031071410340110309455883d0f010360515a20b40000300a110f41c40c1c40303006d5010440c1c04c0c0711081c20000307a20a0100401c407a59040703061150500c945030004206810400900c081e040c1110000120100040c0a90007401000402c01615070140180840084080024511180910303107045100d00c1c01e071401c80b5001d800300d80008066070f00b0007260b00a0580740d017215550301c448174542c00c0243c2e5100b03003060034040341d080e114500444141803802e945826080210300014180340441c01840401c1d02c6580ca40404240001800740c82005031070034a1072030710200862030f01c034410481180000d21480b0ba000012412007080f2600701c50452a84c010094105c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 625326106 1250 625324856 625324867
    0x1b160e01080c0a090f020910090515070c0317070f0c0e0a0203040b1906080f0c090618150a270c020102131715180705040e0c0108060a1806080607030b0303040311030102 74
    0x40c1c0346030856503080c000144270880502c110310b8807040000e440c0c803880c03d101c0d20b0b101150340c40100001c142e00c0042c1a64220700e4954103202c240008458200364060b80d01c0d169900540752080240c2c161340074002240c07c02d14002014081c692007103078050764025000a10b66aa5032100c04801d0440700e10101002d900e40e1400903402d8010007044004013404005400322505003c24006620703070003045c0c40d2040d0701c440c0d250129400030802c81c80e04074024124124007c0c4400c404152003103100d41c0a01c0507500540e10801020040d0002d2000924008030103020414078268100c0c01c1c0c0c0a440246280009506020445a20030004100c441403001e405d450849000b44c0c1440300301e110840b1900c8460203001b00c8030000400070b2090302701074801160100304003da010794140d83d0301100007906042c00b4002d0045821990361000490003080d0960000650300000c4001d10b014000034032882c80e4502c20400810012402401007021220010300210b0500d465521039200394800b8040c1c2c00d4155508104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 625327356 1250 625326106 625326109
    0x902060d0e03090405070e01050a0c030302070c080a0b0a0501061b0c0b030c0a0e0103022a1608100e0105070c1b12030905030d03110f1b160e01080c0a090f0209 70
    0x450898400c90380c06141c8030500f403030600040c2c2d1402003001e002c002107998480c6aa80e003081c01c0e648101060300e40b10400c1d0200e860305034003d22415102070307d4405c410000241000002681c611032503c0b030548001103850381d01c0c96405484c1e081c003075903002c1132048000344007440815004040440c003c7d030300002001c0c2d1340c201110856105a0701091440c00014040d080c40307400c00c0704028850f0080c41c0031860b00c0c42c155001b1089030b007040c004a8550501c586080a9154204000c100ea0001e446e2900b00e07083c0c0d10b0510300e41d511050410240e01900708505921104010300c540c0d40309881d1038940416480e8941e44200c0080c103440c003520741001d9a50340c041805241c03500496046071098649224480c100410107281034900c50200f07040500f00ad050500c001e170705506a0b030b007043c226012540c4452006450340e001c0d01c1c00584011142c490032400b0030781504140c00c0b41c01160300003540e084c42a621074003000d071142004141282c101c00104000c01000783d00da40400c00c0134282880060a2000910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 625328606 1250 625327356 625327361
    0x30a0209060f0c07080708072403090b09010b190315020a0210090813090b1e040f1e0501050109031e1e03110c060418020c03041a0d060e0411040902060d 67
    0x1001081d413a0f22849080c0450541000700c50040e207007000c0207010076446c1140714040b041b00403502d802050207901c80f491900d4069040514030031350091710a0b03141d05d0000b0034240240f580724021446103070810390070070229010050940981c2d8000810351941c0358181d142002a6000103281d200b10700c035804001c5140c4146105d100ca060303118800441d07540c00c45610442400400360071444480c1e1400e0303203800c8142d030790940004412810a001d4101d00c00c0490009005000a400200c501410000020503180c9020525000715922070403c100300c0c1d0f240c10044600c103400d8000101080c907480f0301404610204008601c40318469050241d00d0390095010140004050703000b1400b040c4004a154600c001c148070010384008251490350401e03140140e0f80c0d200d03529645458404130b0f40003d0304842408144208e502400b035009001260504180e0f40328065409100c8495401d40341c8040410900308141905024640020003504024807903410800100440001241e20100030403079400342c00c0e480d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 625329856 1250 625328606 625328617
    0x10051606020705010c0813020f030f030a0201061d010608190209130504060b0301230a02221d01060e120a02100f020111040b0301030b0c130306060821030a0209060f 72
    0x34800940c50310900c0c07030454255400301c20f418061100420402c00d200440344840c098494046400c15010841d006c0468100603504103030f0719560000042d034030302440c1c0542084044400c00c402607008545a4560b10301c3c10701d401c0c01010700240024010400d820729440c8102d44803040c20340010b2804450a00250305141d5500c44e4119483d202ca040205003d01445a005030380b03c10350080c40324039980ca00340100c280820204e142c001d910301020690b5445954150340640d4108000000003244068000b41c081c1054850504046c582031641d8a203d0070101d4614101c80554444010f2440c0e03600800100590b41c1030001c40c50301c034800c02100565190752695039103207070b0b0b51a040704031000030200034251071242d200c0c43d00c000340802080040b80d00d04402c5a0440350000d10084480d05c601c00014124404d81d15900e401400319130001c414030059501c1101125400e004440400000c001110840401840080380c9250184000b03000741e21150001c0c241860014540381c941620305000c14501d8218 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 625331106 1250 625329856 625329863
    0x60504020304230d0807030f020706090b061003060b0306010c0f15050a32430315050f0609040203160809120403060b010e120c04050a0911100516 64
    0x82180034035400f1038a250075601010104003400342942c007540c0240a1200c05042501010b69902c1043e86070161681500d00303003580040c00384104500c5042c8054801c03016141c140c802c0b0784004801c80c0141c003a1241c801100c03018030140e41156101801510790707141084040d100e0095000444001900442200344011864180000e00d42000d004410481d1000d00d40076900703411501c0400201c01c144035115484100c2000e0718000f599900c1c41880444240804c0e48a401b005c1c000540004090f11000d5200c103016200043c0310003040000480c01d44544084120b06807209034018011801c100c0d44080244401914203864044924040382c12130388100e442802045022080a005c02d078006065600141954000d128841e002c0b109103010381700b544001451a82d83c2d50300854264003413030001c0e1402800401001074035149060301e44d1a01c0c01800c040c0c0c4200d103882c1c00a9027503221481000d1ba42c9400140012080c0300440500248101d201650b6080c088240003200070780d021000c041d0240da00c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 625332356 1250 625331106 625331123
    0x1b0c11041b0c050d03110304060f141e370b030a2105030402011403060312071b211e0f120e0901050d111503160909020a0f050d060504020304 62
    0x50803e9810188000346410805042600200c1e114030180d058a030401d400000028210b400c08840c04000c25060418016000354101003007410170480c460281c3c0c004500904800e1903a85206481d1980000750819100c0b800042c1d100e0210111403202e25201c1c5166140000c2200e00c07a00041d01c0d2020200b421102c1c850b400040809a070308030200b02034802220709005080d0309155001900c2c41c06003500341c0d00c5041c00400028001e40e030030040f03580210a400070107956003d681c10311503d040055841945640c05801c0e0000d16940c1055140140744540d04004514105030369030948544290202021050901c4140001180d1140780f164200c900c24607002c40b40d2548190050500c8800c2c001c01c9104001c041c2c0100020344840c1c2414104a51142c0000302012031180000c1c041c00d5101c9041c2442c51020003042020f0b00c1c1110102030310501c0b0b4545000c600d86d949058030592041e0140c00000900f032070803011711280a0b002070043d08101e9880810035607145d0012a0890700111004d8525a5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 625333606 1250 625332356 625332377
    0x7110724020106151e020703020d20010c110120030301080307120f020a0303020a050d0603060c02100218040504020a0306020703080703061d07050306010905150901031b0c11041b 78
    0x1e0302403040000400c07840d04143c0b030100312000081c00c034103c90660040c0b0034290182d07541140d40700f0300c54079005e1607004142140036095410303c074002110580c0c0380c2d1191008401810701a601492811940075400040160090038010044854030391001a10780c00044012464900d0302041c40518080c0100100a580701d00290a114204085044038007007801941c81c3d882c10440da010903c07640302601802c0242e5600c0400c541210144100480c00c480d0503d010000f00070406d9541003d054000ca1b54225506460001580e02c00c0f0300c10301c10039803090400d10343e03d0000d80c205a00150ba0050009110300501666034840d40f09a0f0311203c4206c0004910100f0440390b00c3d01445004060400c5251100c02002c0a0070712040120300500241d00707105d030120004410f81e210304000c00c0a46005400e032080c1c0151460703c0c00164014154580c003190600c0102c806d040d02c2d020100305540071070340e200f0254000d039865422200c94406d4001d60881d0b220051301c24014000402d43d0103488603665200c6508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 625334856 1250 625333606 625333679
    0xf0b040e1b1002070501032c0a0215041d070c0b09012003010312030e030c010c03090c050d210c060c08042303090108150d1b05030303010e071107 64
    0x81e801d6140c254440c0c080d2885201d1455030004043c020344400f0b080c00100b4502000e49542c4078070601075401d5141a0b100d83c44050000c020070304000e014403d880c041c16441316005004024000c80c050811081803c0c00300c8044101c1c0408195003014960030064002d10b295200c050078464100c50f9100103a44511840c07414401c0041900c200c040820081030465045507510f003081604100044100742e103982d1080c41144041c41101c0302d065580e402004084203118019026250b0701e8019184141c0d144c80000b10340c00e00700d20315990725a00a440183d0841440d207404075083d00148000708200000001d400007403560300c00c0c10451405078640720842d02d080d103000384488a19130304820803800360500003404540c002058071200035007401c10155a0790784030902442201c0c00d81320340d940a003129840505001c0c003440080d240d6290340480c00d014903250390505a07680b000303110b00201c040380c1d01c00140b140c3c0d1195400250728880c410603582003c2e903c000304049440024414800401d0107c2004001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 625336106 1250 625334856 625334893
    0xa230601120b10050f090424060603050a06030f0209090109170910020d091512020a03050130060c03020c10020d0c02010b0f1c0c08030702120307020a05040f0b040e 72
    0xf400754401459220304020104150b14000c1c0c844030300900c1208085820422030304101d009031440300b2041c182c00300c0250826005040c051240c0c0022916050214800c10318600803041500d0b00041c81c01c0c456015603083c071070603a00040c0568900d558072944c00000400c0c228580305841c03d20300e060b50b03e07160410104010fa4248030082415540958035808095401c6110715044a11000300110144c101d21025106d20b80c1c3d621a400c400f500c0000d140c0442a01940b01c641615041c1408104558070f804100c911808a0040e6503c90302280303e4810001d40030b50401c640a500c5440c0240c1441c458020851a20503441c040c1101c040d0040350300380085600348550f0902030b405d8030081c00b9060b8030101240416048100d030500440440c0d0500540e0413101e480e500b90180d001d400c0441d900c0c0d503440042d8894100c104228031940315154400b800c484000180c80d19580c00130009034a181c50001004002d05900307000005450310f0b0b4011001c19911489003152440846018103011442200c00c1420f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 625337356 1250 625336106 625336111
    0x70318120204230c030702120318060702031608031b27010c02061204020102150a09030e011d0f0f030a1b0902031b0309010603061b1806020a230601120b 67
    0x4032400e5000c103c0d5088010400325004400e8810396a9244c071100001c0f0b0405440c1c80e003c0a5625000043c0201c3c000da858105420030115803d170b5500c1d44404d00101c1c0c6a01c24100c070040110b0894014401080c4404011500109002c582040d100d14005220100e0303005010301900310038a465011081d1408000c40c400b02100c246010016441e4035400903041c3d01403560040c0c000f9032406e0005046900801071250348001855000307e49203040320f100d40150031843c3c01140003c81111400c0540e500482c20700ca11820800240c034405200b101c144040b85118101095000320b201c0312281050324184002d810381c5000782580d440c0c1c00100008454070711810b502440e051441081049850300820300005e50404c650006103603a5103c1d0304601d070140400340c001402092400402000000982ca02d9009219180c3c42d50910001c1c4011003040000c2248242c0c4051b0b00107038240000a1091002d042e406d041c81404640d120062090715480c12000741c01403081d21a000c3c3c83c4c2410b00448a52003903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 625338606 1250 625337356 625337381
    0x1e090f0d0201152304021b0d030522170a090f0f03080715150e190509071502011b0c050709290607061b090e04050d05070318120204 58
    0x1100701035103200c00c48900881c4c4150710144518651800070404035104c40d440b0b800e03008000303540302d51314072080e07040d401c00801207900140f00f407c1848a0840c0240521032040c00ca0b500c0010300402080018110342d03d4042c0c00702d4411350004840711b10012150041c0244da0295a60b5214490508420243c5101107800c015509147c1410030800507001c141200c0046501c680304004000200403134a020f231006034800c220f9000d240d1008100074110321001c0b0300c100c48400e000204c084c90410f5030790443d0410760b205242604900c109004041d05845649060b5820344000120080310340310b12010426002001d0000034441702c4a04280708040008a0103407100380000c1112441d4805821940222081c852210030034556240b00d05a0b190310560308095004401404030581058549601042c0165208081200c44101203110f5441140780352081d9409401084102c644100580743c03600022002c504000c0b03001e0a6904034100d900c0c8001c000e00582103140e29003003982c070411058450100d07184 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 625339856 1250 625338606 625338611
    0x160302010e0708071a0a0507050118201305190203040b060a0b04060203090112020c030a020a0b01151b11031e011118100302161109011502030a05031e090f0d0201 71
    0x14400070003403500201401c00c8201d021942c80700c0c502c809840c2d500071404054940d518bc000d80e0706044c400b500214242c90f204294040840704003c59401074801c1441149802080700e0907510411a402c0e4003080d006421103019031000c041100d15074050740e004990442d01e2404090900c1a6414030350380590185c500d5081d12410107091200003075803400b880200504000c0d1400b000301e10800c40780d0490328503e929601380c80e0ba90300f03201406035841c101c07510101c898440d184c000245d5400e4100301e01d00bd403c1c907581c0d0020301c05000b24070001c900301110426100495409a5244240c1e0104051020038142085403001d1a401880680c21a48417040a08400c0002c10511300720041c440304400101b48102c2d0380c1d0460b005412400c800030300408486107888032418160000740407801e4044034945004880d00030980c1c0c0c86800001b003025482e00504007691041c0299001d060140d0003a40e8040280400003075112002010510f544009480d0307070880350000d44c4c0c00441044c0c140075600242c081070009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 625341106 1250 625339856 625339859
    0xc020a05030a030b0a0e0106110c040e120d11030709090b030c10081e1005030f0309010504030b1e040809010e100813080c030c0f0f070e130602160302010e070807 71
    0x1126160712480070b2403400c041c0e440740e01140d280d0f10611100b016000f03800300030a0b25a11054058203d0611000c0000c0c24820b10300d01d6007240c42d01c0e010ba072003207004900244c0a00000c1060380d0380d0750b4003e050984c4078a0340f50031411801d641980051845950039664034204280390001680c00c80308034410550082d00490383d03404080d21040c07043e8003461500c2ca000c00c0c3d640e03a141808072102c42000c0b101440d07103e030300043c44030100c00011182c050301c0c4114203948203007284c1122603503207200d001c5c3e045010940600c400c101248900140700c0d4400203e0001c0b00380b035445208504940c0100f11011100c03280046500c220b2540e0201e4210003150065074041c80000075035102601403a0014401c040b50424403655030100025081a1030400088a08881e16250380e9040b0303d454110300300a019a51050000d00000c200001589004076094411a040c86440d408001d00141c0280346090724165002c210b140c6540110f103191480f0180294000034000003c240c100e400c1011613800200d469214800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 625342356 1250 625341106 625341113
    0xa03020d110117100303080a0b030106091b02150105090606070f03050d110703080c1605060c0c01050c040b0a030c273f03031b0507050d050c0a020f130e100c020a 71
    0x444c1e000b03503505802d050101d0750f110f11030704021f069852a800d4155080c240e00080c0e003587c41e0080303419124096031a010030001c00404a90f50b00d51026242d000c190504010040340c242400081d03000b1001030700c4203141c20f80c242c46004040c079561404400080700051741b0030240705c0c0c6110702401842508295850030100e52001845501d0140001224a100040710180349101c000202007a991003c1903a0342490080119002d40d000100580520350070040024013a00b01e9000b02c0707094500414505090400101044008120035142c01c0240f0547c05201c180ea510b88486202d5040741c105071101c000780c10002d01c9101840710745842d0002c00c600180c1c0c1c0b190450800162031300d03150500b02000d01f0311014107044016158200c00c4000600008442862050b4820004d00c0d00b14081e104681440d0b42d11070003250305104541c003403602d582100901000514110f915059004402031503c4000c00c40010079901300c0b04c0200456800b940500c0c0c000c0c1c41c4850134010760414212500161100018544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 625343606 1250 625342356 625342381
    0x703240c17071101060f030204180c031b09050109020a0e03010b1302090415080303040302010c0903080d050a140109060305100b090612030c06040825021e0a03020d110117 75
    0x201c110305181c0e59240056841886907081c1000f801010009104040d50340c11003070040c950700d00059000c1c604162071858440c0010180c1e9040a0340720b6081240d0030b1458841c000b6854582841e140c02480008000a421010f40690b42c0a40718100006135621100078010f000c00c01d02542a50183e41071082c00c2d00c00355a1011240c0d43c0300040103015a035482814002002440c5d84503c04518920151010441801c00009544580d201c0d400800c0300c85100701069030707100c22901c030050005070204034030350400b8059085681c0080142c2004201c00c03d001400911001c4240c200c2034400ba60b401c0100203000d810008484003521049082000411031400b164000c50014445030080d2041c03446074840d414104110b5500c00c0039101503840f6401c0614111925a200c0800c1c007030b140c00c03401194101d11502a00c0680d003103070b00030710300b03003482e02c80104c0425202060b10125901c40840c0ca0008050380f501500d03501446e219440c0080e44000780400500480c0c81d07014210701001c400381c02c11072400c80a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 625344856 1250 625343606 625343627
    0x810060b03061905030f0106171b0105070807060903020c1e0901030f034d0604110a0305030310080105070f02030906091302070c08060601050c060103230703240c 71
    0x1d44041000e01d0024990314400c054a522131505031003103c00d284000034041d4413010544911031445100c40142c444415034809000803040d20f044070b85580300e0500d601400007030001901c980481400c0003219250841280c43c40042580940c211140c03d000c00d00d8000c40f2000761002400e002800b400b01d0310041020a80140002441107000c04910018140250030b81c10040318058000140421140d0800d4400001e8038901945000600e12500c10800540c0b03801d658054030030010301040c0d0715600c80e44500ca6903078001a801005048002c008500144021817040003080114003080f484e0240032821181300800c501c0c2002246504141000d0380401140c0b1034080480b00d6a4440760b0100001e003480b084c10702441c0000d0701c0041c0071002c21085000706400c80d031700c0d0340075525680d07240302c0191424400d600030b400103030b00000d00600002d02800654038081c00041c0780d110b01d42c0d00f5031101900d080d9075a001900d00c40307820650b50341c800103114107070414040303205d00611031a031000704040e0801048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 625346106 1250 625344856 625344859
    0x16060f060509220f03021c0905211f060b040902070210090b0d09080d0204060e0a092d0902090708090c0105070b150111011802040f050108122b060810060b0306 70
    0xd413130005251013081841c0e4040b00414034081203a9990704003925071101407003000c1c020010280b0716140f00c071000130701061207080440903007400880c01c0440b90f1101c01c0d40030b13281c404075668034010401401c500060000303050b0084006031740d04054010011340f07400b0800c100c03003009070b0300c88240001909030b0142c400c213840c04640469041c0c100d00c0e103c00603014440c03c0b20b0205101080002c0c0180d403240010341e0b1500142c4001030401d843d40b28000642d15042180781d52610a000b400301d5034a080004e5404c1d81030300110004509540f903000540006050750744000040541041c0440850305008420303400d14242012407030000c803561545010b074002000d0003103a81402d01d2904040c1d020700c171245503260104008111030100040c1240c4c0c05540c040e000e0340901d1411101c40c10000300c07481058142c40c4004024904d1080d5120540705070b9118101440000300400d645911090303402440142c2038140200100307505003000c5015240903400414450504d0400c03108012118482048a4000c0c90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 625347356 1250 625346106 625346123
    0x8010b2b0209090c0d0e0c0609060703030b0a0306022101060c030804030e090412020f07080717240a05060409030807080702120f030105280b16060f06050922 69
    0x400d41000002070140e1440640c0142d100d00c10810400c445400404c03400c0c030750803006c0101041150089680b240a1007109410650030000c0c880da91604e007000d0f2036914480d140216070001c40c54040749031a4200c1e0701c120b1303d003500890002c015161541100c9840402d86401151540c513207078001380075008801018060010400204007450710428100003030032000341542105050130300d811445c0740b000b4402d100c0140a03584280559403030107d8808121a102d400414100d030400d40d110300340c10f4034418228594401c60034230320a02d866101828440f076882a003e013181e4074051980c1e00a54034000c20845c0b19031b00d40036105000a07040308950360449464070784070a285c0d6a10301c00b64540114201901419640031540705448562580214107072001540e010001103e0f40303e20345448003107250f542c0d10031038a50005014042450700680301d01001146511032454a035140c000442c0d0321101c00c015516220641030045042ca000c020390032800020b0000e8152248a40c1c2c076021600d000310080c142c0b01d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 625348606 1250 625347356 625347427
    0x51c0f14030a110c031909081605091008120a170103020612040303061e0f061b0b072c0103060b090307090207060b061605120406050a0806190906030308010b 69
    0x14000c010b4a11300c42c06041100e5440403000d51004d01080d911103ca0006540420041060003011500310039181c000098410010b0900f010840240c200902d003d0400c0c1001d440007580140400c50615410702c1441c003240d6030707498a04020b18003401055060100c50702c075001000140c0b5180d04454100703095544400310764541d80b808030040c2070258028001103c0949500c030000002c141408105d42107000d888100540d0f422083c3c84400b503a60048400c0140900382c6c0b404500c12a42c542c1e805400741c0f600480f6801c00311900052000d05c1d4054154614162030894241d5805124a2000c1c11204058505100007900003039520f2100340600c001050b004a034200400c041038000b202d40c600020705880d110124514240300da4034020b030090b40c01d0300c070740e002182c000f0300404100c8040c2c030603c1d5101890807450420545200f00054182c94000e00d04041c0010000c41b4030300004064082054041440ca24505009041c3c0d541a013115030b00d10020040c61008140c5418222048a6030445007800d81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 625349856 1250 625348606 625348631
    0xb03340c05070e01090b0a050d0f030f020a0219080613080a0e040b06070b0702071208031617010303051c02180103110d020c07061106040f0b13051c0f14030a 69
    0x1a019401400c41980100001c05e0103602a0401c00c00040191601c1250a136a10100404140c4c5074002500000d030032141c14000c01c1c85500840d07422105030040711202d40300c0e030740860241307918017900c0c2c12000c02035107080c000039000b440003a40015508640101102c11920382d44800e1060507a0001803154181e040a43c0391074507000944070740d4000f8243c0d5202c0c001c130b040484c5280c9003142e401c4010700a20b000403414441000d28071240382c0d04807200705c0c11940c40c010441c0380144039014080034484161004485480f2141d6207a01a520079540e8544800885200c1d05280082440382249c41e4010302c00300803220b10b484c8030458964824a00803900511002e07103142c0d0fa100d4a0301d826121800056003084010380042c1990450f159503481c17030b0100d07176842c07840ca072030f04019680104080c0c0703200c00d01c07030100d0440404190401e00481c40300c0e20408199442c50300d024203021009007040d003c41c0c41c2110b203c0d0807010540704002542000404004a14541d520f01d201c0100058042d0703641d11503d5240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 625351106 1250 625349856 625349863
    0xa060f0b122d01110406021203100e07110109110301050603030721050c070b0c0709050f0a0c021606081806010324140114041a0a1a130b03340c05 64
    0x10348074000020051300790030145014030355110b4054a400761080820190b00600700c00c040300d00ca840c2d0740c0003c0400c50f0a00b40d0307029103594060202401c01c480703883c403141f00e900288501070505d44034040c040000014101410300791075000301901d01c02c2e00140000808900180519002ca0240c08603c0c000ba506e402000d13034050007142d06a910521442001181c1403007400c4c000d2010b001000e0031200d0840d0369110307490030340c0d00446810720f00e9190b8401064580c6503a0300003210708040e0740191001c502c000f121882070101d0540c05140021150020b0254440241c000040d50245d44400740c000d641c155210281d07584480c01041001941281c0208034010f40c96200300c207901c40071401b904d91565242c00d6610303030b00c00c5680050b10541c0360000c84082400c48119820300c2d000d01a01c101c2c1c02d14500201c41c05038408041106040c807400300440310101c00502a20800b07418140341890b200e003000051401c40701c01c01c585142c0c00407101c401501d0486000700e4281840417031403402900ea900d0916203a4207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 625352356 1250 625351106 625351183
    0xc0e101e0e361f05010318030c230a06060b091f0201200a0306090b0a052e0905010e040e0c010e01030e0a12080903160f030c0b070224160e120a060f0b12 67
    0x13542e140074602b80c0703c0780740082800b03910303a03000700c20070311000e900e44240340704c1c0b44603036100320303902c01d80e60f40800100101c14280055246120300001940000d048031400340c1000c11582c000c590300000800c1c1203180d03010310443c8041c001c40d960400a840301500801d240381e500c0e01445100316070040c2080003e82c58445101205000c1084019407404002005081503246001f12404240703415500400750419100f000c03013000c103440081140288000c01500c00c44c242100040c105511140c08165140c82085600b03d454481d095a468440852200801030340000c0d020702d0f038540080081601054900c0c0d0003209464008929401d128040c2c607055030000121a002031070a810322007000281d0390048ae10440081c2000d0b64032400c400000c20382458060200d50715007140001501c0084424130034504565050301c06000c408030000500207261a1800c0404100c400781d44400d00080e501d00c490007003135840d00d8183c505803207111000d11000d85440d08180303070915449c2038900f4505200101e00c40c445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 625353606 1250 625352356 625352393
    0x90f0b1e09061c1a0904030804110310180c05090f01150c02120c03070b0c150703150e0402150a0c060c0e101e0e361f05010318030c 58
    0x2242030b04003d80c03c070160403c004207400310252910303590154181510440c0c840d940c0f5590320071241c2d03100d90f98010444c0e0682d41441d05032140c107a000c404114948161413400300702001c40b141d0180b00d86040300b481484c5400c440e0107500c001080c408003140c0c0c0f0a801d41510780e200701032503802c7d04411303084a49411801019610032481d5804800d035582c04500400c1030714040e020b40b02c085440d504541284c0c4900320300c0700600d5001c17008840b14440d4090341280c00145914010803404001900c204a0b40620742101040440950074001145440d00400c0e1014600d01c2e041030501c56103060203020035011007400780000e80c80d03280e54605244581d00d0b41d0303100c0741d00811241007011020401040000184415441e00240c3d50303001e140c0c01e0282d010400c900400811940d14200c41915082007040002a120302d041607105256801e549405640ca104800d446001012819140d61754500c90000d035010605051030000e00b01c1e0740400e00d0f090080019007504180700c0144052505030140c45048050707a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 625354856 1250 625353606 625353637
    0x901050409180816030207050613050f0f09041b240f031d03040608150d1403041a07030e09040c121a010e1e0c0702040f1b090f0b1e0906 60
    0x120f84200e101085100003d02036030846400d15158418408a4031a0b0ac0c0c031408001e151801c10011841c08443c000389028010308031030f210301d00ca04003141d40342030261001c0b00d440d20f28448501406480c405500018031070310b01a080660034021132081901401f8605104000340280105c0030710b80650040b11006400188016101c1c1c50341440a499030414010100041c00480200b81050b0644d20180038040e0000c0c1000c21140184d900d19404004a00d6480c5041c0001e00c00052114000001710fa10f000d81c205206a55504601e0000c0500200026141c0319940020070320002c258480c81c640152580c0c06c11015402e042418031030410140200c01c114807201840010429056400c80d9501803031a44540e550f80119245c000707207041104517500c0030b10f117605101300005484c1a41183c801081002c0c800200e518026103803c0003200800d50000110316000010008070980c1d5810900808468250030704111010892420000f51842c62200e074840228a14a40b56110403c59141c5003543c01c80c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 625356106 1250 625354856 625354867
    0x100503120405370f090c03020c03090609130212220c090b031005010b070605060d05060a1107020301050906041b0b0301030210111603110609030d2f06160509010504091808 75
    0x144d0041d001d03078094081c40a083c8107440002c80e01034025203130a808840b000c1d40c00d103a100d505000c20b94110400f030542c012596002071030390300c200e072000700085400310310381c1c0c0f0441c9085401c0e0000440c1c030340d11150803c071019030b00744040303002a0f501405076840b18102086d841c6022000a24040085401902d203918110000a001c4142002810309510661084c49150384070b02c10040c0300c054004000d400c40e008903002900c17460403580480e4a107481c10fa9028181601e82d0040703400c4034401c84074140c044d03108070b0601051000e281ca074008003048210348900003504124000c003180c041880000e025403104001c1c5c0450700d0007051390b065021402811180020b604c20490b045000780740c032064a150424848d600d00d02e0030800100c500c58a405401010303043e02010085400c1e04405000d40f100004007580f4141e0715503840b0345500e058900c0c40003025a400c004845905001d108a610300501808001c41d084c1640c2040507034088401d105400140d0700c20715421000e001003001c04c020243c410000304c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 625357356 1250 625356106 625356119
    0xd0c080415030e0c030d0503010b0a03020409050a02270109050609030a06050f150f060403020f04110c100e0606031203070314010312030b030106180f0e0610050312040537 75
    0x4150140e00f00b520483e0194401c0506140c0c440c00800e080000150b400c100611402c20000000d0080e44091b1400529196a880004084500540f00c901906400042c030310604411490029440c50079101419401803040b070001e008a580e42c4109409420b0106404c05250341c01d010881d4281c0d0060380c2808a454a2460200f02076011119840030140c00704500c0420309204401030341510000d8a40c904e440d0840c1c0800c0390000036243d00690040e200e03001121030412910241001c501e440c001020070640d192400802c0e1002e031410703d002540302908012680c1c2d00000d1054000480304e103607540c0c0c3d480715031046028058100748400fa4030b007000c2c0008100401c1844c1c22030900841d580c10041c40e400081014280c0301544900a165107078017205082882840d40504a05629800c001620034010920241091411a00c4840ca111582010070041c1020b108811480203002c0340c243c85d080c184800035840003181800765040b4140c58080c40103d62402c0180c90301800014086100c440e80c800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 625358606 1250 625357356 625357361
    0x304090c030e0d180e04110d0203010b3303040507142404060f1107061d030a06141605070f171b010c0216030215071509020906120d0c08041503 63
    0x3078100b0580034550000603085020022180100da10906207005008100c7c02c21042c2400031724140c1e0305541e00c011980c407650b80c0f0000388068a80840c2020100080c50380998000710403c10942030169080041000041000c00c2420540e00303201038001280100c2c4020913081540303862103600c0795103a074643c100c400030141d002c1d008a90865440d000b080c0580c05044403c0a80302540070000d071702261040c800d06004a1725290342c0c0121400f4006184509400240b5100600d601510500d65a1032092622103a008584d42d1116416a070122030078001c2c0e4004110744102d92010f40f058070101c102104001e002c1c1c1d8480c0c808900001c015482d80c3c207180700160001507504d01d10307229600c1c041d0311008903800441c9130b8818606650680140d6441c0d41c00b402400c08504410f081400c0c001c22003400065950b110324480c0450a0500150711100d62041c04001840902900d02c544140380c030321117044500058020b160000c1d49800036100e452842d000c0c4940c021030b000030158003112003819050b107600d603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 625359712 1106 625358606 625358627
    0x270301320712020a08090106050306070804110303072405011a070609050f061e011409061c0803090f01150326040504060b090f01110304090c030e0d 65
    0x4150b018200e030300101c1c140c8081125041441450b01c02441808060f1400f80d000700b00d281820503001c0c00040303000f8001460791040c11540c05aa841c2802a0340a103035111822440400c101400709207905241ca510601d4280751900000740c0000c6040d80c0c240b817061031624540f034551039440d498040c00c040c0070141c50b144144901c102c40035404120307035445198a06900d060828190020060031401079100c80c2003c0242c2100042c01c0d5241c030000e07034003c85d0807140c0c8d215103400d240e820440d4101151020f02520004400c2203603641000c205284420b0100008100d42070b490b14594030164100d02014008001c00b41070045980ca41200d4843d04030020481c1d00c1c24103a443d8001004c1d0380310342d0081d102e03100011a0110003030920360102c19251070b0900305000320f0b1013606101c0782c0d00e004500c10b03007804e90f4507200031440450080d44101140340c040b03426917013200400e0030054500c4000 = true := by decide +kernel

theorem cover : BRFrame.Cov 625179856 625359712 := by
  have h0 := BRFrame.cov_init 625179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 625179856 ≤ n) (h2 : n < 625359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
