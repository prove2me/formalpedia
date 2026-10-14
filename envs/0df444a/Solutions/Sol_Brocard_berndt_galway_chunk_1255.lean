-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1255
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:01:29.537776+00:00
-- url     : https://prove2.me/submissions/a6d2c917-d8cd-4faa-8db9-2cfe15428e28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 225539568 ≤ n < 225719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 225540818 1250 225539568 225539579
    0x9141608030c0627010c031d010b010819140907060e0402040311090a02130801060f091b0c050a0f060b10021204030206071110180509060d02040b0a080d0c02010306 72
    0x8900a8411001503a0841e6021a1050ba01000c3c0c90100e00901814085505020304ca070b00e084404800d15200401d44840e0310b551280010010100100d241400900031081c0d07001c00202600d000074a401d4810342e482c0886190005980d010600b0301602d50724841c007034100f251100380c0c0c0322958401d0000042840741d02d041e00d82070a000787c50490368404150b007200c0c3d40410402100368402032800762a107509000700c410090910340504000c0c49100c0001030050308000e0394104003041d80d0000c0455500f00140c0e000d012074958040ba0452100303103014240c1c04018544541405818240a00001d000726419818031030709a1002c403810104860580c6502c104443c160707140c140c1c055041c903074860144001c102500b001001803251610079000e0503160700d00c5c0c0c00081c2813513810041000018101c604c0e940c135040d00c103111540203420704584000705460900f0014040c1c1c540fa80000b8050341e21080e000c0d4060319880500006000b10030150f98400200002c014030801182005074000b80c184500000ca = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 225542068 1250 225540818 225540823
    0xb1b01090f03080f1302130b0135010f0f0e1f0902030f0f0609070f0e0312030f0f0c07080d020d090b091002070b060613030b040503071a062209141608 66
    0x10106d501034020400c0700c184920316001046d140700524180008801d402c1540d040d1800104000d03015106000305008020486c5144090145c200340e03c40d52000358140446000030b440f0b102120800039141d082691014800864a00440300d14201185551008a082c44c400e0700170710300c103811940146040795500e00034141c04030700640c0c84a80110354640480c080078400d00030000001d0306420054412454100864548404102d4101c007906021080c48110f80b10841400d400031900343c48040702d400d2401d21540b0382d20400303178020f05c00100040c210b8500c410b00e4060ba0800c015407281000200c94900304000d07064800c4444044500588038041901c081c0d6109560f800d41d04848004860360b070305014804d42ea40400e103140014104074000000060318000c035288940e1203540030310341700d01041c601031940d040b00c40b9142c24628560020095a6141c140340300090707909035004401625503020621300104100d2030050020350b10b04008100d442800100c1070991661001902c844940c2c07030030700d2074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 225543318 1250 225542068 225542101
    0x50709020f03180d0c1203020903060405010f0c0906020d05090d05060a0f0f180f0f170c0115030305090d08041502010605030f0706050d0509070504020307080f100b1b01090f03080f 79
    0x3d0101e08117a00c120003088180706d4240040606040040c517154000d00020315007001281d0807a441da4440c1c0d15400c0c52180c80c0144800f003003090408502142c01c01c44007035110302040541030304010011541350b02d10f07500c403035003a182680c009060300c0c1e1071b0074180520000341c00f045038121003040c01c10781c034180c10a08510071000c0642c0214050784100b5200d07600c40120700108842540c501d000010380d04003054150307040303c46407c002d644040e030701c03d8104800c0d401d6808403a0980d000c511041020070200790800102c2e03070007000846d108000d1803005e10300b00002d402150084000c4045201c481c0381425015400a42900d504800700d03001366440c3c88585a42d04107a000e464005170045c011001d400380c03aa0401d51b0060a080d041d60450364440c4081001c9030803c5070150001401c0c4001c1c001c400b15810f02d2107403c042c400100c50802c1e828001c07414541c1c03003040303031000515134000c0300c1199028007036109440ea240c0c00a0890040c88441c20010005907003540c01000382c3c8014004100c4d084040740360340e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 225544568 1250 225543318 225543343
    0xe1f03110f101202030612010203090706140a091814091f0510030213020c060a020d0b010c0503030c070507050901090c2d050702041d010c030f1116050709020f0318 72
    0x10f12800300e912115001c0d400140007103420030314640380c552241800307001451040e04810000c141c0c030342c42c00034002c0201542c01c45003240c1d0394041020003812580887c800090f0741154600002c004100042e210090203910404c00c0b02000c400c080c0308450b040402c04503501101507245e0040c02180c1034030282100c00a58580d4a08230b030402d81000103060070b0761040b13502d02d01c00b0401810402c0000e074442c14190122100420360b070780015460b03035192440c42100e44c2c12000b8600525050410781c1c5095032880098814244490b0100d180c2040200811030b41d400b85c64043c1401c0e82c0b13560f4603400d40c4040c2112080c0f0700003103640420603003101d601640203200110344428025603446000102510706a0100d0307400d83c1c1241e01c407018a008031a011030400b625000301000021011040d580080840f035880c043c50104500301801070002c01000e000b5544000c40c0b0080000d00071040d4038240e4902209a44070140d602d00100da580600c0c072100001c0d510611842801001c1415154003440c2c403141c03150b401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 225545818 1250 225544568 225544577
    0xd0513060806060d021612020613060b1207082b2309040c1713080909060a031a041b0602151503010608030702030c060408070e1f03110f10 61
    0xc1199074440c1c07100541180d0060445032074013000110301010399115003400b10b0103c8007802518204018102840484c443e64405403a007070038802c100700d06e80307200818050700940d210807a034101640e6107040312030a046070710104e622060340c4031802600e0300c0c00100c030800111010740740d10b4186411a0007030b16028010b90b442480e513046180d000b160680003500398030500c450520030603503140c541c1c0c86001801d00c2152208101d218181029002c080c5005101d0301ca19810f14610100103900c0c40e041d1f803004102111121070f25503601020131050701180e031001c2c01d40710ba04440080440030424460b03020307038003071140c1182d004130f03031140007803008100d101e070304011707403001c0a441c90382510004804e80048030301d14465403054003036001909403071590700007100640000800800314034007003143c500c0000003590340314141860705c8540381e210352161042c45201d40e1200c00080c1034507410401c0c020300300243d10b08048842e4990401040341c000c075184440c02561039034041c44003440e0040d20fa8941c1c070b4140e0744 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 225547068 1250 225545818 225545857
    0xb041d0105040c120c0c02040c0c050f0c0a091e06170601080307030f050c0f03031906080c0604170a08070803011d0c032806030b0702210f091f0203030106020d05 71
    0x39504000c00904205c2c20030042480320100041c0d869000e2040c0e188201d9a400d0031099540c108241007c2c0d540710883c02c10390182c1501000ea4450440b9142102d030140400138582c000104840003502e80f4000c3c28000b246885004102100d9a0038121a5a0001c0c021140c10b070380c0714803030b45589124020300070f4045000c0c4a90301840c207200f8001007005400c41d1301900d943c022101c000710318541041d00c4440418988078403600351f58246118900082000400800f8010f1041001c01c0c000d11650040c040b03184070340e010b14502d4035010014580d0300e50307206104a41c1c4640c0c034201011075400a02445981c603007148255112a040c0d01400c41c054201c82c00050701d50740b22000c00d81891440400307081c20240c600c00280000007014031900d00158000c00c0e640e0040e1901c503100031705004100044107004042c20340320606850701e0034140c0e030003c8001c0241c04d5540340001c0015400358485080d441904215442c6256a5070780800a14102e4400347c0840d003103425004010742e1180210411035003607103030340ca0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 225548318 1250 225547068 225547097
    0x7030f021b04051306110a02210316050c030f04030b060303030609011701060503030d06060323011401050c011a010207091817071209051009060215060a0b041d0105040c 74
    0xd0010341c0002500403207841e0101c07150f80381400d507603001c800c0350004503000c0359000c8602e1f01880b09d10318218070f041d420a13002c6001080815540405802860000c015a00000c0001c0c002d00480b4050004482265201c00d0240500c400320b500c140800c848415a40020030301e982000001d0307038090b51740200280c003260301b803010236260b010200c1d02c0d2680640d03c07000002806d44040c0010618403220180c0441c000d41040e101500b900c1141c0542552001440c400d1210002000d0109064070b08401c50140701d400b00c2801240e2034091001011200e5103416814512140032075a02c2c0035070310081c1c0075103c0c81a40c8520640855181103c241901040b8204400000d03040340720010982450540d15420400c683d228103241d02c40c5440743c10040703103194609100d40e20340960500d90000b00d0382b40c9861000e090010003501c4804031038200750100b0405020440c6640c072550400c001c0c0040506260711a56500a800c01402d0810441007081b00010004140713820a40075080000c5080e4440a01d400e0551 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 225549568 1250 225548318 225548321
    0x105030a0f0503130e01090b0f1003021e0d1b021903050708130b0d0f09020a09050403120203161b05070b0d0e06070302030a0e15060607020103090605070507030f021b04 74
    0x1d20308403110f000c104104810580144a40d4010f00442c0718030000c55070406802004880e034070480548202d542507100c01950786d80300c061801030340c0c0500c0c001d030f1200e04541201500c0d175450300d16000040740c04201d5901d00743c26580801030b490010304150030b9441d400f0300180d85a4060540c003401c0a03007941d5400300070a01480081034441c1c031a112451400c40c0d0f000349456144e4040d08007500311480000c03000c01424090090102d00c3d21044410000e00e1b58079400144090003a12941d45515140d100090515000d4040c400b80041c00f210155a03a20302078640424089180c100c04011510000c0b10740c291800030000840d0703040d407000003041032a080c1780440e00c95810000c2c42400701ca40352065036991881c14810207000d90320680b000b6850b818180c59a905481c4022490001640002408810031004135556038100310305560b02603070340c811400104c0c00b030142e040c00a015141421305000000c0e80c058010903100b8040d0303445034503d095450b412a08c0e1010f2407480c4c2000c0384068007020062070325 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 225550818 1250 225549568 225549593
    0x21e0d050a0203090307150206090d05030105100509040c0305060a0b09030d0503061c030e040b06130509060607052d0312190605030a03020706090f030314031509040f0201021002030105030a 83
    0x740c01241e0030311403503074000391810403550012010350484000c0c100340690100496a000103542d000340c441103040796030003807040c0814401d00d031080324906d590303001440c0200c1c110780949001800030b1014801280000e00a881e040c1c0c0d103680a00070340c030070020745400b030a02a158000c1009019159410412104450319000500201e030711505910b001040e5910003444c03107a81c5072007030311088001035a81081100b107448180e5218050a409c01c00b14824260b000078070300a80d002191088100e031510004102d0318010800001c01c17611a0804400e517100703005080965100300f0402451080c00326400040d2030380a504091441c0b400d010000c10003801e00d480b401c0560200c4001c00050079a40c940009103440150001500543c0001c141448060750003601680540400403c0c445540e165507001040b0171000c103104460542c011000c03a00b500c00d1511a034070500d0005000020509103800d00705444d2075121001c034054480e02000b000000014004d881c125800180500031a101680310700500d48030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 225552068 1250 225550818 225550837
    0x9050d060b0f10030c120902060a03050a15080c040612050d08040f0c18051501140708070b0c0c0c0301090f0b07020f011d010b091003150207050a06090201021e0d05 72
    0x1104265500c4a450f058240c10182840c0c2d5000300f030305d403c905806071403901c00d4200032688a041c04a0040940c076080c2c106d03444458140740c00a40b903a1144000d100801880c101500303068200c5000040440f000031300c010748043e0840d020403045a4a2002c00d01402d444c0000801c590440d04080c8003150251010340d9019000b650300301860071041e1b940ea51a4081c0780c220000101e14400b1802c010318079071040daa4807450848101090455040029044000d48408000801c500280000402082d14140c40e07209500070358088131400e012440211542180141081c036208088680c1104d107414040c54840300d401041018507040c45850b403a2050700000c204109602c01c29000c005840c03024440c0201c07003030942e0025800101e00780c04441c29951102ca5062050f030140341400307c414a00010711046036070200c1c400b0b030074100380414035000e03004d01c0c0c002070424041e1004410074001141c00260b4000d200341c5c240c508200c4411100311550218680b451070550000301e0b21501980904024404100c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 225553318 1250 225552068 225552079
    0xb0f01030c0b0a05120c0c0606090f01140a090e031e12060103111b0c030706020708060f041e05060f0a0c080402091009090804080d0503010e070c060608030304110a0609050d060b 78
    0x40d900010100118001c0c0d9024800d4a030003d1f840c0c4000d0414081d15411441c104d901c500c20381483d6106091514040c029000843d816806521240d40e607a503514000b4098403509000e54819020b925480f034001025181d1607800c040710884064481c901102d455111102d410320850310303440011030050907045121401d503901040314600c00304e5202a41b501c4154005c0051174848503400a250600345076600034015035001c00014440c900d008104217a004041c50510398031a91181007000040ca161810148000d20919241c0180030000c034400d0f00c103d9a030105140c043c0c42c0c0d803401c10119410201d200000450a1002c5001803034082c2946800071041b0380c1c12182140c9440da204100c1d52031a500301c0701150001800c0054950501101807180e225091050131903151890302040e0810040c00c01c0204082141c40c00f08000c1a41e00c031501915400c01200d84920b00751a082044a4174410400d2091104580005520380300301c0001069400180403925440680c0d03860398081d090310780c15a42d102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 225554568 1250 225553318 225553327
    0x40905061305011103010f0311150c0106080d0e0a03060b0a120c05030601061d0405061f080f070201060f0e270102090a0806061302090d021c110f01091710020a0203070b0f01030c0b0a05 81
    0x5090103025049000d400002e37010307280800c1245000c582040410500c10301c98612849a82d40c0c40e1003d003207d40040001c50408000c0c4001500b0801c150014010b44404030258424031001404400079100f00b98115407050341c0321602983c071108818085510716090544a161a003010b40049401041c054030300d03200e002250703001400300c250b40e02952000031400c804110310600b0009540d40c01c034a407400200991070030140c48403590032490042040600100c4003042552520624001c22040d10041c802c0207241004000381c080e5009130b80c050311502207680045801c0d40c01068690107188010008110b51100740c404101a420198800b40e000040701c28a03000b43c0c488060030140e01104039105400c2c6403040ca40b0b6040d000604500d540922914032102400780d07002103c01095170001c403120390b1005803103d41c040c9452104080d5400c06400840c415413142d8000000d840b80520944580c00302c1c0d51060311284000400340f001604001d0400303000c014041541000300303d005010b140c090700d071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 225555818 1250 225554568 225554599
    0x22021012060f09021c02070503040b07170a03091506080d0c03030b0a03050a140102160b0604090c0311040c050930060106080103210804060506040905061305011103010f0311 76
    0x2034003503c1d801041c186800103503181d14100d000801424210b0348034021030030410702c0c0d1595550f80c0143d0048480c0c02d01d002492038240014402001b00c03040d0400c0449595815000004000c0d00c8004011220b0503540c032683c00010100e802441c05840c90b034401000501e43c241c44c100c0308445c0c80d035800e4044c1541c41900030355944030341c07040c84080c1d80540f004241e14031a80c0b40055241030000300c60035440e48107020300401c180d0300e03822503560303030740c010221100c10b4079468001001020703000002049810003502c0001003000010b41140f0f1503034202c8040040c0b501901c019281c5200e00d03081d0306c1d8050300c50700714102d06070b8105141c0308440c01c00684a0030b6002011281e40e203022000c6e00210301040000004008104826403859807520720356103460605a078269010b41401c2c4060320082403076840b00e0004681d80c50310780c400441182c100b402c55005061621880340007450707855040d2129401c1c00342d6440030034018001c0300d0480ba91920030705200313491920744880101301445465407000401500d100c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 225557068 1250 225555818 225555839
    0x8010902030f0610110a120906050f090f0a050301091103010e0115051302070c060201020d150302062b0603110f0d020307030b0c04090e1c0305100e09010b0d0302062202101206 77
    0x1014403e5042c80c001004e6021f01074910301c40d0b64008000c0140c2040611039600340e42040c1c910291003912084405c0010000040652103250030032a01507207010030070024440c0c0d11840c140c104000350000c000c02c17918400c000b8280d07040450a1980b16000d01000c100c98100440d6003640d020003850010b013005561381d54901e407400d1660100d00140e40204917070245001c1403150021150800352042c54103461540401c080e40603180c1448040110040301130300031600b1020688003030002010130403015071a454445101c120014015001d922001c2c501c00403424041c80702d400c4c0700d80081c0100f070014030b9640c0b55070120030300529510b9091010700002409003014042c04a000c0c87c04c00107400c408100c0028204c0e40c1140350103100c00c0506140a0105081d00498910300391010766104a0803966401c141c1805407a2164203903410140c0c5402110a00d5800300703049002c0c0804511917800d551152050388001300c682d12010b90300140513400c404019010b41d11865009003050310104116545411020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 225558318 1250 225557068 225557083
    0x5030c12091e0d0906030519050910020a020a060608010b030303040803040c0f0303080106030c1d0112180b01050a060203030735040501150f03050706030e16080102040608010902030f061011 83
    0x14500c0c0d01000f00c4501c0789820840d141c000c0e000c01d207000c0240e841e101c481d608002c4105002050301540ea070001c01c810b45000e01c00c50340c1010a642081d076654407001402981d07030108103410741f202440c021003c0360307030b56060042e44079458004000f035095803241d441d604840e81c409042298400107110f03002035501e007005000402140039441e041701944c0340100c00b5060721318009200e02003114401c20034410f60103030034060320080350030310303083d05000402030302c02004003416054074802101c03400c0e001c0c0030042c500300c09034142c440544440c0407540c1d40b4401aa42c0380415140e031008101041004400c0c0c2008844c0400004030a5004e01c0c040c200401c1d00d4822000151419103559440385141c00581d0800215107004110000802c0b1080c1d255889030341d1200c4040c0250400c058484000304401c0704100134444889c3c0ea0070040045555640c3c61442c001c1d0302510071200864202c0000051411462003036901c224920a541000d598ee0b50042200c4071001401881c10b204800e03642403e00c2104100e01c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 225559568 1250 225558318 225558373
    0x5010f06090e0d02060c0a141204020f010516020f0a0504020325090311120f0708070806070801030f0f061112010f080609030415020319020307110105030c1209 70
    0x30103a04122800d03050362910300200c42030f903010780c00400c88641d0001da07031a4090411007041d501c07902d01c1d0170f04641441089484180c1400e0100715400000c0044812a0243c0c2c030884000b4801c11851005598902441c01800d8120f00040e08403805400c1c0780340341c0d1070301d414024044001140c55100240880c0c0003505c11010310701080700705441c0703aa00380300001c4041c0490300701080050720710341d03c1160b0450322041d21401880e04160070199811b04105050042c0440400c1d164004c2c1c89548e581d640e4401e82c49a2070243c031600002c10a02c901078144141602d4001074040c94084030754461028211801d1001c451040d030781c00b036800c001064400034101d40d5034420003c41d500d501d80804140b143d5540c1e04041c4a0f90000010b2101105c40041114110781101805001401000390240e06501984003804012440f01d0892040e00b40d0100050180b58442c502c10a96141a8030044500d40001c4441c020442020000403226251002c2d1455002126408940010420f00d410050064880560 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 225560818 1250 225559568 225559571
    0x30d02030a020a090504020405150708040305010e060a1b0c0305090a0302041109030c040b030a020d0609020907030906050a060b04090f020d0e010203010518070f030e150c1305010c1101051605010f 86
    0x2024455a04c14140c000401c0111029407c0c0350605000407284d2202404950031080b00081500820440c030381a00c000f1034011000f081001a200051502c1e044100c62080040c3d10b011040907008440c5201104441030319643c851101405036000e49803540f15800c03c1c2c0c0d000c05d04440000050342d0300d000c3c155408240d8a0607640f14400d41c42410303d010900c102e4540310b182881880803841e20000742010650350111690f49000b8098281307003004000c81040a07400078451010000c0b4260550403041e5400e03c01c0b2000c10550366801c0d0346104891b0030707014821640c9400c001c200904681e9810906031042407010042c68442042d080e0011507002c9890301c1700594010004000c9490055a1141d40245060440300305282c1018002c0c10490031000303c0c0c051684d1a40300f049001e10800c108580181c03108a0b50341541000703c85001142c003c9146944031200341c01000c504e03544501d20119056900c001980d6826440c20300540d4540c004c950200106810301e2a1074010a809000e200d07001644042d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 225562068 1250 225560818 225560827
    0x30f02101d010f0e0303060f0a0b07030305072a1202030906070f0201020606060f03041709032401080a05030d1a0d0615060e061204020609060d050f0906010612050405030d02030a02 79
    0x24480c01c0d60b07015040480051300c0c100000c1c3c0b800501004595021508888098503000150000394250701550800c44a10b803001c40c5000401d605580264080c0020ba20383c200c2c1c409503880001c1d0a104200f4412b03880c06440305500e8006982ca03d80485c003079401e4010703241400b10b02c2e4045004c1c1c2e00300c140c0a0310444081c01764203082d942c0603c441a0010b2055600354035080d03d840c9811020b1101030030080007110b50b00070926a812624058a0710114002d056070030030345821041c0088119826511140e0070101400002c6404000841e40c4000354408061410600910309400003410070221181407204802500031950391400c540d104854070456000500812750925403170100710b19007150050140100440d1651b170b50701000d450110b58032a009440555031031000c0340c140d0040e050520381040010500070007221194120074840c802a44242003503545401da0310b0f0b940e5800b031003a5008580001c0382d100a0310078507007245900c035000303904a0345400b20f1088550200d03030007140d1810643c0d41c00314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 225563318 1250 225562068 225562121
    0x3030c030f1a100503131104020f18100306060f120603020d140c010509010e06031005041b110303060117090a0209070905030d02010c140a090302041103161803030f0210 74
    0xf074a140c480c1d891609074250300e4001c180c40c42003103100d00098030704204c01c213002400d41d40d07940444c1e1640844808040d1107040c1b086050416a62981800c0d20a4048506102d0414406d100e07220440d142ca96903a202401107010964505988811015040340c40344400f2015840322040c40c4265486400c41208400740620484c0c00c2140515480d0704002c020004152280e0b0300c080c11400c400360480340c940d0b8984460200030140d002d940e00040d0090306000c551098540440c0214004600036211402c620f024200550f440e03201c02c8640300c0c049691500e07400c0c0340d0215011a40c1d0310025034400c84204012640015001400444214001408003401403080c0d00f0700307021040f4206410300003031124210501001c1c060b07140341101001c202e00d001c03a80f03100741703807046004100443c0c02800c10490301ca81c01503a09040d52040b42c0c0c2007840440c41184101d018480c00143c1c80c80c0c1000c4111191607402d6540444040349042d01c00300841c46888040000b00390188a044c1550307001400890340f440340707917 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 225564568 1250 225563318 225563329
    0x1b0b0702031903090506031f27110412140313050103060e0403020d0e0d02040f0203010302010e1207090515060a0207051c05060a0e1c261303030c030f1a 67
    0x90503402d0582410040001c00a070b00300048500780c1c0c07802c944032178680e950104008204c41c81c1d9201c01c03460107101200064410510089510454460507200d694100135060050a85400c5c050a403c3c04104000c00c0081291000d00c02c0d0303041c2c1c444c8000741c0d644400d80580c1440c58001a20740700004a0b83e4000308010740e058803445000300354000d0345502915050300d001e500c1310070454125003401407108010a5607502e0707070b50a0440c194002c01c100a00c11540010500039002400708a0211314642c040c03003034a10b08420150701e8050800c0080071450704004040380900800b4101d0300003019403043c008681e44d41ca001818459113640e00410040b0300d09030400c2076000c01c034103000380e000052105a1010801c040740d110761259200d4000b14860741400c1c00185050301d6400c200c680241042201c1c0e500543c03000440030a8450818218a810307010307011765034040c800b52a01040300000303121582c0000d00035001015900c0250800048844102142c44241c40d900d0f00d84080c6800035070080c05d02483c2c40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 225565818 1250 225564568 225564583
    0x2040510030b0108060d110a06050d0f090f1106040302040e060915161d040903050a0e01021204090506040b09010609051206090606010818011508010b0d0507060c1b0b070203 76
    0x3035140500580c448400080c10101c00504003a0003080b202200c2010302440a42201118a0203000c82c0c0a6aa4460380102183c00c200900741040d070400c004125a00070700c0c021090120f4003c12a000401c01075a503201c0c12114100c1d92a170014428400000980d40e41c1c0f04680039079140e00040c144c28070703001e8103050900441035200e0060a0070027043c02203164021501846100032400d00048610390710a01c8600003402c50701e004e074454140942602010743c800c01520030420035880d00501416001c005a8407296454110311a0680130f000400c0107180503040250410b07409403000440400038008600a42000d80211f00480c038501403c02843c1081c45280b6803104800c40038040a062034141103491340c001601041c100310b094408200e8413840c02e00c006068100000c001c2194810000082510750f01e03034411180c0b6946082c90340325681c100030030140d12055101001d440f10710304140040d6408180b0b100c0c20342d42c0d14100c0700e040070850000500400a031116a40c86a107441345441014940040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 225567068 1250 225565818 225565849
    0x301030305091f120c02030d0504060605150c0312130203070305010c0f09050a050108190f0b0f040c02060c21040c0f17030307120f0c080103020102100606021902010309080d020405 79
    0x40100c0320a0f11154400c08803904030728491004181111481800c03840c41c002c01030401769a6180c1001c2c0f00c10014030b07910920840c2c2c41038442d85d41d04510094418114001c6030360b00c50300d075041009600f02d6280c008980b158044d201400220010716241c002c64035014a41d00202d920380c0d903968003107840e6500440c0703a82c1350500c40d10b8800b2035642040007050720300704207219150500c203882c00401c0400400c04a440c07074920b5030000070015160568091400740142c0b1441da0f009003117012080040b41441c1c0078a0308240001c2e00205419260341c0081c008a502891102440c10440250f1240c070b501c00c249010b014a010b108120806800c1c40412010b020725039000c02000d6024189a000c615004000d030f80e480111030030110444c84130600c0c1c0300080c0255000b41c0c101c00740303840c0c12255519004151981600e000780e00303e6187d019425110406c0740e8080c064900580d21160f08804c1030b4030404104d8540d41d00c185404900f410040d40c0b681d8071a000224090b420030340202d024446400c0c400c3c40c0000441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 225568318 1250 225567068 225567109
    0x81207020c030f0a0b0a02040e04120807050306031c0e190f0803090901030609030302070c060203030412031503290705030a0b0f09070507020d0b07051209120f0c12030103030509 78
    0xc2d50f42d81c01035a0310b0ba403510042c10000c5001c001000494070f94180ca0050a03940e900c261310385014a060514082c04a4421002c0b8000d0000b01d0540ba00c1801600d200301000b8005080e1913090118020041e4094084241008004001d190046d156503040e14101318000700d200b9090b508203030b180b0f08841c10f81d41002c4441d0384148000340380d41e0b6445001c04d044a03008100020690702030f040440192003041d0024003540da48206c0043e11b9079000005500c02d40c082e1081c059900008101141a0b45107030b4001d51858200c08401d00115038002c60002c503c0b9154000440d442080d8200e5000d4001d0440b0440007040000c010002c20500310b009a00314400100c071029110280c4400041d000c010152015080001c00700e00c0074215219403004402803034107d00c11009030724141c07500410715400303000300b0200c1e507881d98040b44104400050b4bd8214540b84158182042c40d8240214001c0d00315000036183c6210b40d103070b814010921700e001140030754003da880e00c0c2c4d0fa009400a000038401d0306640542c104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 225569568 1250 225568318 225568333
    0xb0f0405030304120c020a0b040509060405040210030f0e010f0c02060916060c060207050f01061703031003111c0503040303030e0c01020601230a090e06070203070b071b081207020c03 80
    0x40c4000c02103940c800c1d0b102c14214200b504618044504450240000390070468082c0042070384000480500304030b40d0308581884041d138512050006450090b01e009401c80c500070003044a240c041d0700030008041c0ca036100080c1d440b40150085003501d181c902c1d04442c0b290340e1054120015814800681d10900c1e00000b030001035803041c01480c00a0b410700ca29410440c01180600c01c1001d50b40488426940240844413440c2d201c0448038000d20043c482c1112403103490300490380400e0080150380c4160241e0302c0c107820040c03954503502d265901d186a81035014580030305034003231402d03102c2090b910140540c000359200c9041d46005030487c1c5500810214070303032095582032060380c0c0c009042e0b41984c07148120780e032841042c0c4010602c1e070b007d1f00d00340365030090007401c0c080b40404050703101115662064044550076111a202a45c403031198040245c0b0b00f000d070f080041d031598021503954222050200b40b134003000c107031600d82e68546c2d017002d000320700e2a99500d418000c110354100041c0b500c82104030041c0044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 225570818 1250 225569568 225569573
    0x60a050901030b0d152a0507080f0702030a0b06040f0608060610200303061c02010815032e050a060f091a1906020d08010317031b13030b0f04 62
    0xa000d02200c050415840e400c00140588484040b03444070365205007041890700400520b10040c001c2116482c0048180d5014404c0b400c01c28080401035a80310b41f207182c6840095159114070354001c080f81680704000300501c1006840411254107418025aa2105141454410070003503540c51890501d01c0c0c0d003130110034862039101040c1150000b074121000c1100440f40c140582d8042c03221403842195400c00380002c0030311803000c0001c0d4418202116103841800c003005002c030004440c0c900103030009110f040040c400358038900c60070b141e034600103080711101001022548140701e0301e0800540302d04030001e00b40b0990700c0315000b80307030700300c2042c600c2070003628141500d40200501784d2150300917084e2545290660380002076542425410040c15142c01c0841d40541111800080e10600005104541080d0251881407407114140c03988000d803030f07902084600c0e0507025a00050080140d105040030051140341280c0028110901c106402004403413540c1403003007283c04002c04101d130070160003041200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 225572068 1250 225570818 225570827
    0xf020315010c02120304061d06030408160512030c040e062d010302090405010b04032d03050705250f0b0c120a090e0a090b0a0209151c02040f060e060a 66
    0x50400a103065582881c0b01d0000a034804030219004049001c0040c022504a6006d0441196800c824071241035000d914814401c1c18402201d0240c1803150900030411101c1103007990000b414055400c4602140c0c0c1c420307405540381d01c203807a41810302100280c1000031000071032880da070250084580c0c0102050b01245c2c401400c3e0103940d0205402c1080715200c0c001c6e8001d5050354041c0401800401803580c594a042c1241c0e13226000c10741d1400d8400754024014425070311000c0e4810340c00300800c03d2000860368203481da504a030608036445e00407030000e00710151403c5030492a164103000c0b209507151800c01980c04000740f580103402484002c1020b10182c83c1c00084502c0360000304c00c001990386000b01e800b1951a441604400046000d05050201c01905074029811150045002c01d240740c888082c0c80c0f08034030801800e240c2108501361101c04200b10303440a0040c050355960602440000070144404991268010318102104144288440d681c81907100d100c415094a820340391004804020300b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 225573318 1250 225572068 225572101
    0x120703020a11010623120a02091915090f1103060d060902060d09030219110904060b031e071a0d15030f050c0916050406030509070510020d030f0203 65
    0x505068000400d4406148100c0b8030640d510072a00080188035100e0380070b00348000107500960580c2000d508040e0302c51500f20104610080414000d201c011280d03405d1120221006003040104101d40649070344108150143c60800e607400303109100c06c03d00b4540c090f000c59802d0002c0c0d1030305d545081c416101d40860402142c0d04a4800c072111141000381d0300c0d00f00060074811790025008031000c06d40044001c1c0580100d92240d00c2034081d5610507041c402e03048070740d29003102c02420a0400c025450171a003443d034591038105025281c0410000030f01c0c03011914002da01c00103405040551030411000482c14081c0802400221542c549260000c0e048d54400780181031261403041e03a520440c0d038030829210043d1001f1603005c3d00c0354284043c1401d010f600c85080d00c2d100d600400c12607000428004250b140684850300c55200c0f1070030503041c0442140141402442c644061003801800302d03043d43c2d0810403515440a903030080c0300e40004580000e042e10300004891036100e0043c000c1c00740c0f60301d084170b501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 225574568 1250 225573318 225573331
    0x60e060c04210804120c090608011b0e012f060a0c0e100504090c09030b1b22031403130e072c09010308030a0b030f0a0b0c040b0c07090b040212 63
    0x2082c034112504110446218640c0500b40590b24003000c0006c100a000d6088100c0b9a01c02c070411080b551484881c1c240c52802c914411280914a040c445141c02a100400360386418504143d1101c000032000001c400c1071074080bc1e000d00502c10b04140f07050b0400c10643c0c420080102403085135509032011f4001c2800042d01849022040340c0c5268003849101610000c1401d403100b4019000c00d04400385c45030285000955404049000041d13010100b408801841080f00e0f162074501202080d419401401407400c106c1e01d0300304080300101059021010b00c1c420444440a95501c1e281c0d0040078aa20351207a11030505180300c40b0810030250740212002d4848100d0154000d44c02c529100c20700c0c4015198003402da880724600001001344640600130390300c2160103c104214244543e002c256031003500340c0e152041c5602061100c000202c503110000d03008000065002c0c1002e03113400308244940c00007035411f000c940c080c1004002c030030f0b801e0143d4058280c1c180e030300714580310181046041301c01009010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 225575818 1250 225574568 225574619
    0xf06090503180f09010626250201090b0612030f030c0d060524030a0b0904050a02010e0109030f080d020c15060406050f01051e0f04030609061d030a0807021009060e060c04 75
    0x620407401160340e26001c541100f000a0415458030400d48490740d1a1000d51403012304a2501d5110f00074014440c2032038660f000240380244e0381c0c4035810049041000f0241c07840a00041c82030301c00620411000e03501800240e40000d8640ca0072000701d00403030b56180d120520404401e1102e840280303060101d011100814416281d0704d645015181000e0140400c01d00c1d00442c0d41e1080009000021814030310046c800d03a40c0c1c862921111700110f502d81481d00014001854081d81c0c000080e070380d0001000b002e4100240981055641c1c103185090000c1d146408030100307651001c001040c135003031040ca0050305003142c0c40c3c0c0201c45400002460341c054903040400000cc004e0500680a40d0300f4192401251031a0803159a40d881c1c0c030f0000701a0056400850320b1508201d040b546581c1e074859000e845900d100015414000c1c104411288150050952002d600078404154070541a070300920b545240a41c40c00700360120011044c901e051801001031414400500c004e0000700d1503501002c40001e0b07070390003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 225577068 1250 225575818 225575837
    0x4020f0607080d090204140916060206060307060320040308030108060703140a23090d030e070333060e090607030c081b0412051f0603020306130f06090503180f090106 73
    0x4a001004e420414500380701e089030421a081034000350982c000c0c1c00c0304504014481c0e4840c412f9031360b0007040d11485c1d4140c000703201c2071094501c25844801860344070000101000c25400c024080d03035005030404e4441a60000051050030340801029401410781d290400183e48440050b280a2201819201945803a103121081004003000c10000600c40d00243d42d145041000550359155071107071034103000c24101a913008504c0f2003c9001000c81e03030041c9881c0113a40000c1585130a09065801d400312100189009420764400d6110b080080c000000304201c3c60309100401030b1410b100204950109400e000d65404c3c3c80341d200c0c00f81900031024840c0049000c410310701c0c7c4011805039810404c002d940000048041c000c0000f1301c3c0902c001c4410380303241c0700030300640c0060544813640400b03909a442140480c169103012000141030714003406a180081d8200d542d2a8103450203140c0a0352103a0011a040c0318100d200104e10008040889014a1203107a00c0081442c4030300501c07880060080c8101d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 225578318 1250 225577068 225577073
    0x1050d1104120c0b18120a05010c0201020a030b220e1002040b0403152f040b0706150602060405060103030f120c0801080115030f06180203030415090e0103050303150a091404020f0607080d09 83
    0x8407007c00c59100d402841400001b1900034001d412020003400080d0030900c0c4450117003400c0400090450341c3c41c0e0380083c100c81036040721000d094500601a520310031844c1007902c03d070350b51018001900118906036529443d5081a942c0b160b11940c14010340c505d800e103100c0384404c08001c800404480032010f2481042c002c0b85107229806030b41d0107850b0b0790400280305e0341045a035501102c420200c29007100d49846e1100700890351617600321401011030303221702c005002080c050004080280100c3c9058070142000b0103200c0c065410035040c28010903045401403006540030b0050200c001c132921048481c5510390307103c482c1110803100c030191405a545c103040501c0321855183c4446981c0160403a0f58840e650520010884140c0c40c0d040000350032404046042420360035168100c07500030000b982180c994003003003401010704420f4242d114070305071400948201e443c00703150588400009410140e252a00501001000b2000994800ca500f041500005004607081d29044407440100190b04001c61 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 225579568 1250 225578318 225578323
    0xe030304030e0a09060902042309070503041e030c150c051204050712140609010b0d060b0307050405090c0415030f080d0236090f010501050d1104120c0b1812 69
    0x5030049601c140c101100486c800f0460b80082003110114254540c020140100b20311808120075402c0340d01000030000b203001070740308074081c0d5001405665208003800d5025030b006c41580c02e9a42c00c902040d42402000e00344011403c1103003007449e030b0703000500103201c1d480030040c542d04c42c500e6050101031610000c034003800b00402c03a0801802032400d0140242079103040c501280ca42020a01c010344c4206800500c1d030303c0060103185001000501102c0c598441d503900c0401902e0694581d070f805100d04e400024a80d9658040c0c7d03030150b00c1c1e14015083c11500030b41801705581d1058018140404c0d0348100300300080341e0301e013a540c05d40e800001071601ca059440c0800302a102c5c0401030741ca108600c03900500c1c18682ca6400c03042240720003400400d900f2802052005000f000c842208400104400400c0254040d030003c00c5c2c80801500009101902007683e40d209401a8200326000c40840c008a400c014207074102002400c0c1c880401410402a01c0300001d90501420070140200f06034007900250f42c808 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 225580818 1250 225579568 225579589
    0x20601121103030408011b030c080109090204022a07060c0c062a2004050f060f061b01140105090c0a0f0c0803090a0c0b04050906121e030d06090e030304030e 69
    0x3029281d0344c6668041e04e03070180c0704103e00c50b601c80f2203038010940482c5c002c1c400c00c1441d441c01c0c1c0340c0c407510368a000b06550050503540001e0380c2168080103650f403040062580d40b103190044c005040303800307241c4240251a08900b0b030414028414103030030003000b03d00c034505103204071102443c04040c0504110300040c0c00003815500c050021005100b8002040102d220343d8040e030103c05002020740350031074200002d40d0016207903699140c1c003100120f65141001507078191308a0020b81920b2a1801c0001a03d141842c076401d0009223954404a185028030890412070040004803400092420f000e8404041807148096507001d200c00c100186241c03a004100c5c4111003900010055103d01d0311420442c1c8440031640c0442e035854059401003080b0106009440954174050008043c9a940c0350501c4040d683d202c1c0540e90b24400c20044444c000d445400402003401740d20051500c861448600800b0784891ba000f5138a628141188030085520000c2529032054051a2181480400e600860050b204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 225582068 1250 225580818 225580853
    0xf020a080a0302030a0e0a180507091e0e060102160e0402030703020612091c02030a050319020304030c03110703021522060c05120a0c08031005090403080f0906010602060112 76
    0x7070410041c14141c000c40507025100451301c901e034102e4465010090005402d0056009480c110000b03a00d40b87c04550046030f1203001428005800d41c0c803a6246401014100c4111521241d140001c2c030614496895882e00708a003800281241d05184a0840e01c0c80c401d400390b000c6060b0890000703802e65074100010001550090300255846000c0f0191682010040340c06000f244594804004010180155603107502615809503060009601045509500142030f00c404002c4030b1809041e065220300c0107500a500c6511041a400e44d1494050001c00d1a40080120ba0708802810005620b5050f84410419450149107954000001c0070b141200c240b225545143c1502c0b82020420f540c002450800c4180030302d048a0641c1200d40c0400403d00c40e0700d01d0400083e0313180c54543c00140c1c0c04400f542d0000641c0310b400460544450120710780300012a03007a00012010b0041c0160801e003407643c580c00400007800b030002e660600401950740c600603c80c0e8440f030414402c482c4240b05100b6615250680c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 225583318 1250 225582068 225582073
    0xc0d061d16021f140702060123030a0203010c020705091b0d1107050d110c0916030207020102070305010f020a0305090d020c01080603070f0b040501020f061005010318022106060d0305070f020a08 85
    0x1e0183c00b9071000f80035a0240030155403e01000c00d031038a000190050403101c1014681082050315036580c03807515482c1c0d498a40501c140c20f0030034010380e028002c00e8040f91a0303074010711000c1d10740000c000c0e00120280c4a00080c08080440c1c440e0300200c2e0086602c1c03000e030818080754030024198134800e507205d4014081c10602079410a0301500764454446c82681403d001181c03031031081d01c1c0420132030032002c1d1980d02c1c1d1580c00301d00030940b4070b0180d000348c03ca05005005454000369261102070030b4a0030800601c150307980c00035810549030b805104450308617400c200140304280da00600603548004441c2102d0610012900103500d03a070302003062801600f9558006d1581594901ea0300005401600401e40035025002142410140c001100352084800c202c0890b03180f49440c0c01903006141c4c141200c0300b1004031010600141e101d064a031001c420300e00d0486452045030640d0a81003a0010b486180b08800e000320300c2000c43e034000c0c2030791a000e4000d4603031194030311b09100081c5101c01e03642c041c54607030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 225584568 1250 225583318 225583363
    0x1203051204210f05160516030b07080a14060906060d06060e12030343020a020a0801020301050f04050a02041208030709091104060f170c0d061d1602 65
    0x2d20784500514011082d144410420b0401001c2d180c01d000311034507600007a001d112001c03038241511300c10490302e40100f09481d040000501c0201040b080b9400580c0c11318070500900c10125072011060fa40b050901c0d10421000d00f40101002011401600c12880f613001c031000b25101d030341d64404440340154101307010085213960f800003901c8800c2c1020510701c181866135000701c60b024040202d910030304e00880e0000c6c01088101c58504c040910024080c011501915249041c040b1640c0c014204c0c00b1540080c4070140340c1d4410824001c2058119a84c641d0042c001023020f07403120148040300803008c40c1e01003026951030890030024012a8084030f41d4600142c80d000520441e000110b0207299155110307098030b0748440b007480903142040001c075000f4100f0071003000124824a08030014001c2443c0604003040ac0c2c1e0010a509441694074641445000403508a43c1c40d0b28450b00c00108010324048110114101e5403c0100780000c002262614604124140003032003032000c40100c83c803d5546d039480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 225585818 1250 225584568 225584573
    0xb060f061b0c0402090d0f1e0f1e050601090209060712051209010b0603010b1c09050708010608011107030315030b0703020306090a0b15090f03060f040501150f1203051204 75
    0x25401c0002040c04a01a150303080c0602d007014000c40341c4580014106900180f01c0d1b6861140f900355201c41900e401021a500304003100e21181c850044c83c0c002d144070034200106003040401240009051b08407061a41c400000003480070401c503045541650006881d1041c440100740203124009005110204051340a1030154012000e082c50481403c5417000310b9540911840c200c0e001e00360300d160f002e84117000401c08110010010202243c4284104200d07010450030181078a00c3d0303400440e15508090710038019201c0034800d600081070103000034031a0500d175694411003440f640401808150f2190001501801107101c50f070300a40e442102d14207145401c0300c0050007908141e4016109228210106486040e64000e641580c0c50003004c5903010f10700034010945ca50b00ad100708a4006001d03c581c0e0545035024088240300e8541691005039502d814a401400c41e4468480f018020701040c009101420400ea00c010594001c1d000020b0142c81038101521503024110341c0005842000c0c042004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 225587068 1250 225585818 225585847
    0x10e0a2009010e311203180302070801050a061208070f0b0a02300703090c12030309060b0108070f05030a060e070513050105040b0d02031b0304030f09050306040f0b060f06 75
    0xc41c45901d810b404c3c203c00410030701c0c1210503000030451021680d5041e03c5010a290588299072820300d8180000c514280300d1245040c003068100681c0035821110707080260407828000c00b64044241c050030000241000c1c021907210001c070398060500d0002098030000c2280200c0f1a070940c3d50401c095000b03034602040c50324080e41c8200c5005840c0500c40c40c03682c09001281030f01c105d5000200001c4442a565507904400408003a00c2c159a413003000c3e04001403152030050303d0b030b860b00d000382d81c0031500180e641080400d444102d4480c1d81000940406c0005072588140104c500c581d1034078010b036403921501103080c0a06040d4100c14104116003081c002d01c0b640007001484ea0250740171400c03000307950310b0005407118000d03482411001c0000b0002140c4000d890b80c021a40403401810914515180b80300e10100f42d0002c8500328081400c01000f40b92140d0003145010081404400510940c902603860b0071600500010081c49600003001113503159803200c04485032404054102030312020710201089 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 225588318 1250 225587068 225587071
    0x123040b0a03140c04060e0106051804110d05010b040602071710060e04060c081b07030c0812040203070b09030d050a020a0b160e0f0f0d1a0a021b010e0a2009010e 71
    0x41940c404d00b58111502e007003600401d400c942403414020440d83c41e00fa0241c0301940109002d00f010780c11540d1a07807141d9031303a01ca0800450000c3c400c903500c84244010788405c0795010b81181800000c188800c108503a40010048281c40114072520403114002029034a88044c4100b0f0302c280e0313803c040001c82c01c1d2032400078540c482c5004080c03d004007070303111b0420344002405071040684011900002d858001d1008000d1031420b1080ca400b00d903202403a2210007054000103c0c912400134a00705220a500c2c3c100601406403000301c0c461072503c0301c5100002c1c0c0d02c3d80c5040300d02061000120703510402034001e0115198a03900582c9500140c6000f0414002d203101100c4250003250440c4802a16414038075428100454050080c04042c0080401c202c600302c3d2545007201c0c40107200058601c0b4054105c00c69001d0600c048000d0388076030750a402d42d07814a0400090740840da251100180c0701000c009030050708035412103450f090000100d4240d41c2d800820720000c903001600107000080003428001d03444e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 225589568 1250 225588318 225588353
    0x9040c0c20061306050a0e0105070b04170c060906010f0b03070804060b040b030f06060102010507020d050717130602010606080f04030c0609170f04051e0a06030225060c170123040b0a03 81
    0x40c1c0d0200051f005481d28010360030041d01680c4a84005000202d0501c0300c00c0500501d401ca490900b001c0100c200d240800c11580e408980d04604010000a1003003c80709018101800c80c10f800c41c80d00c66402440e4440080c40601400e0701c0b0308100340719440702c0e800304000900c06003e4607400540c6881442d61140192205401503180000280d6800e2000c01d680c1803100701951780c00c0c600195030311100410720340d00141d20180001040140004103c0c41519001054a43c00100e103003454058054001c20b03000f1f06010000024004010009610811040c1116070100300010b115400e824001440044200d0724000c003070bc0010213071170f00708143c00a0822180301322414171401c1041d0441c090b00e6980b108034a50458074103d03060003814040c0c5c000e0b10f5841007140c41e00400c0c0c030b901024042802c058940c141c0c0c103184d0f2291902c1100b0791003442044810100e1901e204030b549040d0b1803400401403000c50220003c1e10b0002c3d00b20b541da90342c0110341c011030001c0c041d1941caa10303428480d54015007400304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 225590818 1250 225589568 225589577
    0x50d0f060e190b060714010608151008060708010302041802030105100306110c19050c03030304030c0501050609160302160c0e0919030816050702031209040c0c20061306050a 76
    0x3010b4008680d00862800d040c02030b250500340300761651403010000c000d504040d80d40d52101c1c00400e20107420080c13000900721a00e209c190301d0130507202c43c0517042c429405c90700b000e4002c4000c0100403074104c0f1100341101c3d8107030340004584103450611400301940000c025415401c0c00d003030259015030202020143c81c0034400400000d460380d1400c062612031100a440746412840311020840e1000c08040c404500400c25100c0d4030300c0e1980000e00755401101c0c200c000c214644451802c0c44824401c56a10840903114400306040014802045c3c8025900b81010541c0000702750b0070400001019840107039008281e481c1964507060680e400c081c2c11140310403113209905075500780e00781c60183c2e00c0119400d91a1407645480340c40100200541502015050201c01c015240050701c0c02c02504008a61121910380c035454100f00b004162800c0e2101501004480269040440e162003900c440055013082c1d10520b507010400071540a00603030040d850b44c1401c03240000f400c541c00c0310040c50202000d544 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 225592068 1250 225590818 225590851
    0x5212401080906010603090f060203090303040b18070b0a02070b0417060912040e06150d0905160e0c090121050103050d0302040806060907110a051507020d0f050d0f060e 74
    0x110741c5603074100c8856049070b0003600100b00c507602030340c01442e105001c2c01060380d8070003260303da2400366071003a100303e82160f000100b0401030200303144003150000880c8aa01c051800080345241d5038110314054818503010010700055603500800c20040200074100b501a1a01d5a0703080c0500c1c2e03140e05590102885c001c21f8005800000040b40045010341703150002c0307084c103051107a10785044400030012900320340f9044034188119001c0c406020f00d03ca900c5030108894120380b40c000d091007a403241210300c0c80403010303080c80010460703100540c1c040c80f019845500c2d4041c11004a0b55000e4820000240000041921711760714901d8000d541a2401082180c400c89143c00d412000c074801e6100b0008260400c10115441e07103401105540c01000313520300091080e03400048181040c80c0d24808803903079880b510050440516160207141e10210701d0015113040c404240c1e018207810f02d69105101042000105000c4000c01030340121408042070314100300c0c0326200c4082d140268816604401000d05400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 225593318 1250 225592068 225592141
    0x70908070f0513021e0702010909021206120606031002031b0301030803091603020d0303151707080c150318100519050a090c14040f020703020c01120b0307060521 71
    0x84a03050044055240035001700700540c0d0103e9040080201e04101c001c1000080d80111030000e8006001030300d486121500300041003040c078405040b1500d91a4000d0800c000c49540c001c0b80010104124540240c1c0d41e66542942140100000f41e821082c0b04010002209011004000d103104d96481000c81d40038009010f08070507000e46030321000b9440034100e80400d00283c4642c1044081d010880707015038240781c4030088030580080900c03414009034003002c800c011603030382003211003205c450a0703c500126500105002040f484003d1100e800441a0440e82c15020410043c5d030300d1000400c5402c04c002d04001d901d00764401940c2d00a0040b1909020102da14a041841040d028507071003d0304511003131402c888007071805400008a6030080d40c130942480303044158002400858800d5011b080800d0300c0d00c3c0058031100301a00c2440b84030b440d111030154540c07000551a03041d610315041c25501c40c2c4602200303202c0805100d082c0c02502c440c05050000810140340d204e4151203696a50056118242 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 225594568 1250 225593318 225593321
    0x31e021b15010b090103020a050c010608100605040203060d020f0a08030a0f030b0111150703020d11090306010605030f06060d0e030a1707032d11030718090c021005070908070f0513 79
    0xa0084a0300b0b107000300800c132000d6000364000d14003003c06040443c100502040c0c15070859a480d4800400c0c0d402140d10042c04011070300c60580078120480e02181541003074400305281100b0103400034011000c00140310780c643d0395045924020444401141c1c3c2d1803410a00041002d40e003201c0130b03c0464100004102c80d903010304050b081440e00003000384000e51b801c82640907801d1000d0001828103a0800c03024420503018020040100c84450401c0da0707a400b5001803601d4580164412800c0100c144148450b0007400da01c007a070850350840d20203480e9003110300c06100400d01c00304180384c0c3c2d200c0014901c07540c94100000241050051841d003000b44e0f0303a0300050301902c0b02810407100d45001101c1200440c0700c003403988050303041c02d03000004204003094242c0740c0c254026615072022070100e649503000340c40302072015000f40079180014040d100381200702075aa96010b04506100d9900c41002840c194841e40c0d100c40281400c50899000b1542c03030b030402158004034040c05019060303600c1c4030700e100f280b43d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 225595818 1250 225594568 225594571
    0x110405060a08030a180b040905090d0305060307152f0106060f020a0212070909050717070b070f02010c0503270901030237181a01050a031e021b15 64
    0x40c0b0024610b880d040705000c403004802646a6008280e910001103100344460001d007001c0d142a40c40007a031800d203001d03414900440d40583d9410107040c04208540d945000c0748507000c8440d01d803d120500035103903005845100d146c4007031010f40b0351460303004820302c618174003507440001c030440003005255104c41d030071a03440c0186604080980e000800040041c01d02071400c100e80b00ba040c050301c00c0103407104c2e80e100a80f0100c072010380e00c40d841644148020b10500500000d4800d0400007170189602e003403407100301d0b8051144042c03d080340d501300107419039000c0c00500101640c07120641ea80daa030000a8000e451427529640c04200c0a1440620700300d040401200e0305a80e00249464144000888a0440c0d40381c01403800c0404042c4403032030341110316500d040e180602584201c00d41a0080ac48824085170204494136000024030f940b6201c8a90700081194000100c03440c01141450020300350041044201e8000e40c0c5003440010300a89a102d0080c1981419480100ba110800d80d059036015034107a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 225597068 1250 225595818 225595829
    0xf060b0f0109120f050313081c0f0818120409060501091a0304150906090b060d151104180507110a11040207020d0209040f02010f020f0613060209060304110405060a 72
    0x8800014000b00340c01140c8000510701c01e400e80007504c0e6841e9500c03411908603860011040e03485590610040c9028040c151080220005a50700b155006030020607c0098002c0c0d0020301941c2030100714510080613059600c0785008007211040e100b281d5940c0c00c10b03031241c80b6004a1034549000031449620800b1903d00321082c0103064288041802c130704030311503403000c1c200b2141d45100700b44088091042d8043c46070f03c14003600001a4040340c501740002d5019004008600c00c0704206941000103518000001a11544150011f01c20400c1c00002059108503000b201d840c11141807501541c0c0c80d25041580329001a0b510031203110070820601d56959018403000f40354455100020102e0304159020b0601d040c001070502c258820541c010592414003a602a43e05a0710041d0f40e209558101c0003814440e0a03d00c0281081040c2c60040360f11040b01901030141c0c00c004004030020300c252070f01500e00000006288a940381032520f840240c003049038807010302850820000503807074985801007908544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 225598318 1250 225597068 225597077
    0x405012004090e15041406061503070311041205031e0405060f090f0a0806150a121106190c120c1a13080301090c02060603010c0207030f08040b070f060b0f01 69
    0x1070401052402901c0003821a4042d84030f014801c04400d41d500c07103140c0c0560300031408449610606c009003802c0020003848a401840b01c04040d4841c040080201c80e40f1120a20b00080c01b010400030700e007264403a66201e20b41088a00d00000c05010000c0b0040060040003134400b03030802c5594000d556980281d100d00d80d0303c10818040d021510342d00c00c009000c9800c00070001d45007481a4000a5501074040d0051703002c9500280402c00c141c0d210f10304074900b9090854201c00e02c1032030301005081d000b0300010000d00d0030302d401d031091b1601c5c2c031014180d170f0454036030040402c2c200700407100007010410100404e80350800014018080140110b0000c401940c1000b8250b06101291050030b482e480080c04140261031420940c03c007052140e0b0185020380016140400e4030031203142d0003031800300e000e011070380303e40d00d40344003a1201900080c0400c01c60fa40020700c003c0a113075600345880316000b103601c0022001c00c001040004c00ca941d62404544612811040001c4100c0303c05101249070040d0f070003801704 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 225599568 1250 225598318 225598327
    0xf0c1806090f0a02070614161d040c120203070c020a0e07140918070503060f0618040b031903021c0201020306220b040f050f010509071b0201091d04050120 68
    0x90b4115207a25511800c4080054500100c40e901c4104580081d5602d45000b41d9800601000c81112181c0000e03580181c038144c074a1a0340070b24026041c11840407054401c0d566441c0390744c0424081c540405590140000c119200d03d040103016045a002d048224071039401070a02090004441032402d0240380107a0361103841400c0045404140c7e404103042c0d60b8000480c00d0851021042c14161f00d00c80c10050341e440746c0700c0c208502801460134840ea241d510507a0144004440540b0340e664514a1400071600450740030141c8000c2401c20088690b2484911072219002c010b00d138001030070407200803411603031080030090350781c00300d080f40801d072001640b11820300c0e500c1d101d02030414651058000200b00c000340d120b41c08000981100c400754031040c50581c60f2410070100d00000d01e02c072401444d059600c070900b031411079001446030796180e01114102d4a031000000c01d5922600681024000002e13030305100b884604058030301b500080364100c81a60800c2d03014207015581202d002b01c121184898282403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 225600818 1250 225599568 225599581
    0x60c0a030515130b010f05090102031806090a0617060a03020d031101110d0515010801120b04110a06031e0c17150307061206060201020301030803010302040e0c030f0c180609 76
    0x50710024002c4807044242d98031091099441c68100500c00e129460f00186200640e00050805013a1281800c04d1020a20101050340d03000b208440e10004001500048090aa8000381e03c6000350110310343c02146400001c924150022034504d0380e09851010785800e1b6031584100b0070103000500009411500c1e0b01000000a03015601c14a400800d050001c079440034081c80061f180d400c005540180c83c0c2d11602880304040b0311300c002c105107c1c2c0c28640140d03198103040310008a003030442c8004001030841400a024405181140130280c80c3c001d0407024501d0303407884000c0c0904519241c4002e48040707034003800e100c00910321410003100880c0c1c6a007500c22603d003050030340031180106000140001120755042d907a60610030040a0000c40d01d4404500d894120050708488141d004081503a00c10001400032072000000e80307044076412180840c501e0742c1ca0710700e981000d0030a03212a425108403141811440d6011900d41c20780c00084d640c0e0100c1040004040200f20000c0d9581e9400c0070882000c54036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 225602068 1250 225600818 225600821
    0xf0a090203060117071d1801050d03050705150717010509160306030506010f1505030108061302061309051803090d14070815040b01081c081504020d0207060e060c0a03 73
    0x340440c0504100070701e0000c950807800e82c139070211501400241c91404074010301ca80396026041e01001038030040003220b400c80000046400601409110700e0b6000d40d422b04042c455801c4401075903002044c1c5114840855a901521000341c13006c03004520410412401c51110084081c12a103000300110156140c629150405442c03103544d0004045e162503001c0085202000480d000b415000e510075a02c031b01e06511345000c880842d114100700a01000100a82040025415000002019142da005509200251091140d691a28540810040001106001544528410040c0300007281d4201016a8403980303034031648500070742c8a545055a4400324004443c0c0405810341c20303088414040d03c0e00c6a0920b0a440200d4060800200004000c2080200c0e4849401060b044c0001c4c140c400341250300e06818000b02d00e04608102e0494005143e40300c5580784446031440260046588a6070060040c010790311094050780c0040c1010001c0148503400585548100c050110350342c20310426030b00440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 225603318 1250 225602068 225602071
    0xf050403020d050706030b1c0b060414090106050f01030c020304031b031401090213090302060a050406060b0f180907120209010c02060a2c062d0c030a0305060f0a090203 74
    0x10404284404001600c4107200c00020a00803001449154609a001019611001052401401c56100e0600c841c0c1010303240b5004503a001201120030b80d40c10010800410312050300400032034400092080201d010b40c010401d0b540180c880402c080040c0f8015401c0c2c410004030000103900810082011030903088003c070003003c0007101061542da81c0e8503001840e05000b201c4843c50396646440d0000c5103048009804000000039040c40280c100380c4001e52079440007409402c0c0b40b5220400a010008a41d201c0c01c09000f4480507141c4070400c8000c41c00e155004140d60f0950510f9030b1000090900d4402d440038885c01450355000b400501100700c2c80061f401c87e80c01c150511040750044001a601c1d0b00103420b03400044c1d960155004035014903840606140c002d0300c0c0c5000c0002d040005039803500d9084481141860009041d4461100640c00c030030055922084a854400308400100440110041c01c54146665060045403078610420961140e0003041581c440000502000070212503000346 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 225604568 1250 225603318 225603347
    0x608030a12021b10060e01151101060807062c030a0f0503090d20040b010e0d14030705070f08030c0a0204231008010f050f221a01050906010f0e01 64
    0x1600b00304042c0e02500c1c601007481001010f0f5000307090810b80e8080c4034442e403001031524030305402c1c1d507524280c0414406008c003070f602c000b0400580e954070030402c4250003c00041c1000380c1224615950b402008103c0082507601551001a114030010131812020203030522240081c0544084100780e9914074121861031001c4469020034005000f8070781d243c4211003280390060400c803500c0110040164000526080f0726440740303240440c1014141d92001c8928076055080e12040020f16550800c0803108003c100381081d2448000f4500c4208140032a01c0d004035031001000ca26200c1c1c4824049841c0d00600b030300755201e43c1c800709a040241c6419000001c140d8942c09407050101000241840c2100e02100c2410601c041c03032004104a0000b41714900c5c4d0303031154440402103420410034034442c01d00050812956601c100f01000342036034500c0225000320b9401080d000301c0c14840118151103c40074451548194681c5001640700d502900445c00c44ac0e81c1a030300e507103030b01c04500c0041d92150700d0308104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 225605818 1250 225604568 225604571
    0x12140f060d05030a0e15030f0609061c060f0e07080d05031012030c0512070b0a0c141c050105010c0b04030f11030a030203041502041203080c090405041101020c01030608030a12 77
    0x440300410380070710007482450744580d17032131100b140310a05024135140805143e02200b0010001c01107254100d206458010204a40c0320600b40c80c4c010020310480c040217030070340300428144119001c111260707100c855048080071007401900350b00320b921500c070304062040105c15000034081c06a5a0300c00c40096500c2820102840d0000c0c0d01c0754480d181c03075502e40d00f048002c01c030850004824001d0070070050b60002e1000d40e405251840e079a5801000c0f49000c2e10031902641ca03805040f0030030780a0002c80c0403884194401584445600ca1010f08800001000f6420540381400104a9500c01c14102d900359400048101d500e803102e0303608070b681240c2c0482c95130802c004140d0340f44480d10103000401031038059603400740e1607040c079040c111405400c0c0c03050032107101e10400c0200800c200c41e02000840355014101224690707035411000246101d05207995511600c2c02c010082080064620405284020780c02c4a045008520042d01101d4290091030200c0e44240a03054680340305c0e002c040c0891005003030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 225607068 1250 225605818 225605839
    0x506032208070f0f150c020c040e030909190b1507030c06091209081b011707020a06060e01080f0d05090f03100207080903060709030b0403030b04022812140f06 70
    0x3d840100c1d40d90540101c0708040c095101006001540c14900300211107044100b10213031510001a50390002800c2e02c5020380d40b2075521482c0b141d0144155540240d002d4052001403420020fa032840c0e64800701030404030307454161540e40c9410410380c2c403071140380701100b03291030619151025600040c00e444111840c6445501c01300000e20700c0701201404a246d0b858422005040200d8641080c0b10b25003014106034003114091100e030384c40f82c1400d640c01c6405407011219120307290100d01345075540202900250400c40002121020102c0c01070407681504140c0e14242d650323280c144e403121900030400c00080c40500141003549044d038000c1d1044407004003120400610240c11805a8010490503a00b180700412910b141d03080c148542a40402e813494206452410b5503100d01c2e8040014001504260759440d14044a0b11940d044031025441075080c12114000b2440c0352041c0c01c10300440800003808001c030031810380b0050003202403000b4100c031041c4442c4d07112003500c036803040d000b4800c5901c4036a645 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 225608318 1250 225607068 225607073
    0x709090c06140d0906020a0f03140106032304050c090a0203060123121608060d05070911091801031502041d06010201110d05040302071d0609061302040b030f01050603220807 76
    0x46104a03e45c0300380c002607120400d414000e891400400d00c2c400626040440d000000c01c686a079040c1920181c0c140021018480e001300c0300628001314034041e11a0b81a8284000c1c00350018946001140072a03800985685074142103099010585006000c102c0030050811182e0020400300c41c0b84000700c06450615880e6148524440400d03a10020b4400f0f1807802c804c82268441115984100140d03140000720003181c0d030b110780d180c00b180301c2d0702030480d520003142815914000c101d801c60300000740480c1c1c0204a05225504c182c2d401c1c84200c41500d603444c84680254003d0090724101d42f096070080b00402d0088800c03400d6490018400c1d8115540d640049080c414560041d1490326001100024035203003c2c03801a01d041d40030b1700042c1c42c2e0070f400c50520040009010b406c1da030180c1d050341e01728400e488110103c1c000f07000c0141d4611055002240120382d41581d0300140d13108800c0c4001c401416688c590a020b128842a01c1070610139603017000c0d1801c903180c40c883d480c00720761290706903900e0510303680c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 225609568 1250 225608318 225608321
    0xe09011b0c0f060e0d032c150702120c060a0e010c02030d1a0409120f0228030e1f08100503060601081b040b04050108090714010f0207030501060e090709090c06140d 72
    0x3c03010100480d0344c5111180c0460b130042040010413010510311407800030181c0741141c1c2c8488d01244450744101c141c0015040e140300b4414920002c51180c1c4182d100c0a060109984a0008aa401c140709150481d010100c010500501e24a900345030042e500d48541c44030702c1c001800603d0b00740d44440c400303511400038075250f13440345c903916a01400300c3e6076400021300401004003820568a40842d032000592001843c1c0302c900006c2007452000c6200c000a401d4078003981c003030b00e03c0c003251640004191030030030148011084500b11140c140d550141c4075a1000d11004280d0964007950340c065009600066441d40141e0708140c000c4400b00542d6034022000c42901c1040c0d102d0740000c1001d40c0040f0b420003080d6041036983d500302070b592000d0f101050805540604d070310b000060b001c1c100035100307000c444054001d21880c4065508000207104203926910380d4507101c0c1c41950010710780d10801100190b400090f2041c0c440390b55019207000907840ca8500300f00e52036010748a420841c48410081600c3c8000c0d103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 225610818 1250 225609568 225609583
    0x204180201141b030d060812040509060d050a0f0302010614090f01030b0c07060603031d090906060603190e15010f031a0c0d02120103110a030b0f100503070e09011b0c0f060e 76
    0x414404542d060420010382e00b400030540c16011223642c240000d100960300c00060542c0000241c8120114608504116107418207019010703010092480001083c076506402c104191406411506681942c035400d001308044122050b240054205005000281c580c00480d038100d2600a5400c0c00c00026842c2c050843d921948100c010650300500410084006409004200001c840701045071800800894940c6030080c45184180c20000c001049400f00008800e52007400760010003040b94006170b000c0d60b4203104186424400059000003c1a0001191400a0300c0d407200e6140c00c00386118020101c440409050706410030000e2001000c000f205101401c25019070394020651545541030618580c090f2080ba81e0244000d00810301c0842c01c1064219008201c035051001c0c190f42d151000070340010640c01582e1b050050500004540600d40d440a02a00e44030700200802c0480307030032542103420381548540115040c8007941c00403401c0704a140292500600022035444c413290003c60601e00d8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 225612068 1250 225610818 225610837
    0x9020316060203040905060904120804170c01020403020913051005100e0405030a1101110723030a02060403020f0a020d1101120f021c0627020d090308040204180201141b03 75
    0x1011a0400c01803103d402000d420180645232440581895101e01180703035894110f00c01842504008941001440c041d040c0307120301d81e404619283c0c001c90341058080d51003403109070f110301415404600405a0f41d1480c0c4507040d4040d005014103881c0f2040e0344c000d4100181601c1082001d101d0014540c0120340400e0700c2540301d40041e545e9a03c0903c0f0241021458400c0c0d694a030f8940081c1405841421080b9103a403508901f100c9010046103100c0c558080c0400e00412007400003298078600c00d60001345040c000c40c40b07074080e03400c0200d01010041d41c86c07840c40360296110044c844150003003500300c2105041d0b4a41890f085454040c0d509041c029070700c0d1454158001ca500203000404000072408402c0316000c0d0503001e1025a02e0b05c086060000522209008030030008101d00c45c035001181c1c100e03840c0b80f492a1062011407500d00740980411000c44081e40540e0401d4240802d9450901c2c144070040d505844014403841140c40486076034200030034449001218924510301010108064940240c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 225613318 1250 225612068 225612073
    0x215251407061415010801140a090608030901080708360105010602250f0e060105070f080307091202010206010b030a0f0905060a060602031801050d0603020622081b04090203160602 79
    0x2004503401e06481c0c001e000b030415640342c0504003031300d80e409269a4112800141070030030b103040503030001d079201140d85e0055000d0b6240030750002d41e80c1c9002c8064181d10320262190322596032501001d0f0385c0c45101f1aa00c0d19901760440b4030880c130b40d1820030b181c80b0b1100c1c00761030303440701c4101400c086007100d10a07000980135034007007002a100c074030400807401c0d0820310500c04a04c0482c6807080959010100d40507810700300c00c540b40012040e0b440740b0107581c5a907800c00ea500c40d01003280e05051946902c00e42c0c071040000e4040c003020400d500902079541c155641a0300905580c0c4c41c12409443d6500043c00d2a000c0c0c03910f51100030310301d80b80750007400e4605005202600d00780c201000322134100c0303806511110540d042031150900c03040e541c01c1e00a000031020b0030030a41d109100800382c0d00806903504020750050b8042029055803100e0040049018100c42c0d4142000d071712903480703a41d00c00180d0a200307140c2c14036404440250500d600f040d2101c501c050100d82c140b41c01e10a04074407242041e002600140d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 225614568 1250 225613318 225613331
    0x21e21091c050706021b040e03120106030501050a14010804120306050409030905090601091a0307022b020d05030112140115031506061b02100216060f021525140706 72
    0x21209000540c010013207400108134814040345500e00c2c0c200004040ca116698803122017641072010b00440e2500000600850324944c3c4611020307000307090030302849028007041a000304070100089001a452001612602d255540b10b40e40d0802501c0e0803144441095243d0000240d00e0720f5600031003032020300c2a1100c0303a00504103428400203100040c041410440700403420031405061007a03101300d0308540a40c10342e890392800400e0313280c91009541c0501d242411103030007c881c8500340c41d510b9080000e0b800e848829240c0c25044545000a01540c04450160486040010641b0301c02d801d801d0607040011401c61441200144107803031035401642c040c0300180450030b042400388904400ba01c0541011000710b401d1040c41c40c448800c4503002400344284144a544050081160043c621004030110001545a040c01001d14550000f80d2025118403140c0c0340c9500f4000d01030034800c0700c800042d103100040c13401058001c071481d0040c14081c0701c00780c00e0a403170300c801820080034001c1c003500c4089400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 225615818 1250 225614568 225614573
    0xc03321903050c03060604050d050a0c0e0f0f190b150309010504022b0201080403051314130e030a180803041d010e040312020d0b0603010e07021e21091c 67
    0x540740014000d0f4001c240400c00c100d078a5994038141c0b420340d0710035209034841d101185445480c00c54840d002500b915461240091b00c03103442c1989500c50410341c6035411842e01c40d914500c105800036103400070001020148a144810b940c2d004803040b24004050703500d050f06014503201d1a5000b5140075800781d440d10204825410a110704044014246d40c4004a000850341c0c01c600c441a9110f00904110844c4081800c0c14840c00a42d400340518501948e1a03503655811a03210b5016800600d00071111903c1036140801c003449001034080f1b020000c2c1d8941941d84204403074444101300c02494460b120340010461402c100040c001402d030084103404036410812b020310580750160f00c620b041c0c0d0010402c11000039400071409460707046988000d41c64440b13030820031014084121007150007603c080000a1280d0100d104e480c020740e000c1d001c1c0c40945e4000307040c240c2c8803841c14880844075070050f000c500485100c00065220355044e00c1045080604450002e030050601600041c20b446801501809 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 225617068 1250 225615818 225615821
    0xb0a1802190c03080705030c0408030c010f0f02180d02010302070b010b2214130b04230601080c03190f0204090902030705010504060905040218030105100602010605010c03321903 78
    0x201d6041420031410070012039030000c0010400070304c507000f00080400810441104002980d002c1d10104086ea6114403524030305078000d00c01c01c44002d600a00b480c0c0c80882403140b0384202c4400481c0600c0c9482c941d00400180040842c10002c100e040540c07c000e401e000c503c0490780c1d1406030220f144842d0762010301e900401c00c0c80c0480200880600403180e0204a0b4580c01480c1840c0307142c0a541c03207040400c29240600043c002c0c9a1344d19080760400c4010300208050781c0394103d4807090740704194016201c900044403851400c076203401080d20b040000c03a401410b102803002e10300001c1e010210b001c4c0b5200c440302044e6007040d1b00c030045050f103800d035010031840e0030311014000e03100a1070440c5c201898640020000a103501c280da0144e0350015580c180d2850040030a0700408000d00240810304052001010560b43c604c40c150041d40380a01c0400c040d881504a07991841e0180e0702c03003e410040c0c08010406004599046441500c801000700000c440c485c050440200a43c5a80405240340e0b1409030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 225618318 1250 225617068 225617107
    0xe040c06090f0e0604060b0c01020405011404030b0403050c101a040e01050f0105040c020106050d0b01081504030206070302160218011d13080310030f080a110a05100b0a1802 76
    0x40074800120001c0c00a2018420003500311103070b0002c681601e44600740460001c0580750440d04c00b045c40000d603109620310540040c0115002a6521b010306481c00c41c010302d160095001c020404408000490f0100f841480a01008001c079415a8585040b6621403003c0f20085443c0065021443e0080e485500d02032144031801e01c80c1800034041c900c1c201c031185040d491b05001b0944101c0e038480700d04026503c01d51020001d0301c1c3c05070400540d54618101030000860034858094603100b00e102160900707031403405c428001d69140d001003040b03807203104042d0041c0d00000710100d4400500d0b0051409641c41500c00743d501407103500007000c107505000d8840051109010042c024034080024805c14030785580321443c0c481e070401421a00d9882d61600ea00f00400d40d580040e100404a5542406001c2c8403001000464840e0722440e40300401000443d072a000e01c1040506160030007444005100d040760050b00107284001c120100031a15244c8005041d0101c952901c02182c2c00708040f40320100000201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 225619568 1250 225618318 225618329
    0x14040506030a0b070807020f06251707030b060d050a05040c06180515040b071407060c110405070905100306050301050612030f0c0c0604082109060403060509030d02040e040c 76
    0x1c025000707140d161400d5002000c2c4c045410424001c002400e898030034041e070f8000520300d009aa199041c60400611001e522100b2408010001d407040071680d8020114003003150740014076117100d43d481c5d485c1640203000c00f402c0703e43c21040230805c00e100381c111441070600c40c1200d000000348505190400c03070101c0340e10f5001042031003004940c01640001202d00a02240c03011a081c412010005c45602d80e54011035100c4208001c0c0842e1403401c1000040c2c83c05401c1c0022800c0b55442c60307403220201c0701c42407488000341101c000300c0c0ca0b0100b24100364000300e0384001541054250241e0700d40c007180c0c03231003140003140000035a217035000d001c189000e004c3c84d50803d800703d541900d4a907000800030b40f64480c1d0340f14041ca080340003a00c0c031108102401a21014400200001d0b03c2e140d65103100c507103403205003203400030003040c944864400140c20020348a07e02c0c005000385041505540d202001084040c016540c60300c0184440c1e6510350b040d0005001810380c400d0f0703200300ca0801e03160040015245030406e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 225620818 1250 225619568 225619573
    0x705031309060b0409020c0307050604050f06090d050415020a053403170a020f0d090e16091404200c0709090b040605280c0905060715090305131404050603 68
    0x8100c0c03420f14905440a607031064400582c1c1c0c60f02500040c8c42d600c44e40300000c04602032101004203005011560358003000c03500342510000d50300c51302d4040c0ca842e2103c00a901040082c0414458114860386118007284107004465064106441d61803410340c00d40c1c40c0d960a401e83d4485c45000d05458182c18070442140294a40040d040d561120398007680409902056400401d800204d01d200f003240c2035040c3c0140c4147c54811080400c011301074080360250380b10040c4070401040411700c90415200f01c140c40d55a0b800c41a60420200303400e0075030044012030744282c54008505d4206a5003104030402c00032103100035542c25007044214105039103a0300c0321700900e103494402d0307001c17400144d40e03180c0c0107501180018041ea109406006000c0090b11600d1a4900c0000c2d4103408a03145c0c0d00c50382d500d0b03c094a9004c105c5544d8400c1140920030300e07000411058500341d10780036207803141d00300401051103030400d241490b905601200c08103050f64413110120b100310590781007a0816100d1a80c04c000190b01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 225622068 1250 225620818 225620831
    0x1504060e06030c01050c190f03030b01081003060e032802010e06011421030a0e120a03090e181606030501170303041713090519020a020601061805060705031309 70
    0x2948600f02800202e051040004e061042e0150070b03ca52114040c0c2042c640484100f20304044140310703c018012004070f49440264505507000e400424410305c03038005400d081d68107544d6040050212002160490b00c02404005c40140c035260504864503800600d0490540717030008001c0c01e48501c0489404c40d43c00542c018070295810f07901c0003c2ca040241d81009401079504000701130040040ca10040d60700006c1000880c0541c00465071860700b408032020b00b054081f00100d1034031494010402408184500350408c0f12a0700a0700340b90344000c4800394620055004070541d810301003d981e9020046000510900c00250035100b840d000d810031490302c518100070341c1202075991002500145c8541d00e51a071354250759058804030b805c2e0020419100c3d2419960b4500c0d40003901d400d03541e06103005103a42c992145040d86100f42d86690340c09900a082e03691034800700360b507546440c1420507251450648041420389a007001000c07054819030003507659940300090f18a20300125040165690706214 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 225623318 1250 225622068 225622081
    0x5010503070323070c1704210c0503062a0a0e120703060e0706030b0f06071205090d1202010c0c05060714040503010c0507170a02071205151504060e 65
    0x142a41e60040182c10001980c640804031501d01100760740b00102080ca80400f08540359600c0605160401c2c4251010101c000703410715082628060350180c14000c041c440070781030f0000011030f4110004d07070240c500c060720980c440020a060a0045400c14001196083c10174008400881480600d1008010041c24440d0624000b043c40c4075086800e403146120f0080040c1140741272240340300445d40010204501e4841d0688140ca40c4680d104450201c5e181c014110006e051903030200c1030b0750000410040c80c141c1e080d5240700c4100e1020665500f0041c2c24070508001d49c442c10010200c450040c0901c4804011068000f400e4610300301c45601005000c94081d0300041c4000b03242070b0401164101200d40014500d200c250070300459100d164507600300151030341d60641060007842114011401c14078994044651040c083c490300c4030704c60060344000c1d410000944030400c142e030400e1040058500c0010004000040e901043ea08042a038a000d240090310b4035141c440c220003000e031605150701745d29060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 225624568 1250 225623318 225623327
    0xf0a02031f1409250b0405060307050f0a020303180f070311030f070f0f0b030906070e0117072a0809060304240207020405010b27040f1a030d090501 65
    0x800e6110003100408048404055402062519449098403981803509003c0706640316124820301c1d80b045a00c0703620407501c000c03e48950055600c1c0c604454989450801409a9503100516010811009000b003117030200d902c50041c100016507500135078682c00c00400c0a4094842448007a00340d030700001c06820246d0001c5103440440750007112014071448645c0c0804c5c1402c41c1c1d40004500d80c001e482c0f0101c1c264252a0a02f001c0d036072180e480e01003254441e40240014801500c9542450f4060030000f0746c4c01d84510308007098a00c061405500e007500c0008042c1140304140d41e508080b80d2103403014040e9880034101d420030b400c00040c2605000c541519803c1191141c0504a4000d0f94000001b900303210400c1c1c20b000f200c451107a29070403000c1c1e5400c0ca001c02904401022440789040800000c1e211200720295040700c404903042989292401001800c500881c81c10150025143c2070340000a12840c490850051a44010700e160f00701800d0406090070345e20f201319018400e03a0107041c01a0b0344d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 225625818 1250 225624568 225624583
    0x9060609090a05150307030311010605101d0102010b1507031101020f070f05070b1902121305040b0f0307060c02030c090f0106050a0504091a1c031b020d0c1401020f0a0203 75
    0xb110341c00151a00e03441000e0301c4543d005850300b60940b18100d07002041603449500020241d170124000c10840d51508200001802034040c507600060a540c80380304026240c00d01c1c3d51500505000020310f803841c07803000c33500034408600381d80707002e030404150602407681114031200d00b0700e4040021403414113044a55a583e01951402401d8038220005407000c00c241000a04058450b9940c0c3d19212070340e100042d840340181400b0000107001d101d407001502001c00c1c0507900d5031b01d14251161a81d0703091805100003402e1800b40660701246c13610700801103071000d004c0280602600d544443c61840140141032421940d00e0146024070924410440b14280c05001a81502d5041c508260703503447c500c0040f81e03140120740001c0c0087d840c0020740300c42d0403d081c41c0124104001e40e800480e20181001d00e00e221103c900b400703004510075094071040144050001e2984920040a80074100d03000e80f590b299007092508070500a034071000c40f82d0859a010015903d03042c081c0310080018118a80c00319882d8400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 225627068 1250 225625818 225625831
    0x30c121915180c0b0906070213150b0403020a0b0d0f1506200a08160501060806040b06060705100e0f010230160804020a08060f16090b071106040f03030e0906060909 72
    0x100419062500e1b95058225441917800a0480320703000054400c000041000b09a000c5a1086820001070f50b1307011141a1000c4a4006080030300a62504881703107603541c080c4014441a59072040780c02c145008a108094600401c4400780d07020320f04080000c0c001d074a442002d401c6c0041d0f000c80c0314801c080000b461210081c3d00c103044680300d561800d41d0824035100c8000013040e950074010301081c101000a0601c0c400c1d405901044020f07158441404624400ca2101800c03d0300a0480002e000b14140c100ba49045013185c21222004848601c160882c0c10140c0c040e4440390003000c0602505003c840349000e0007031170b9a41c0039140e052a00b240034522040f650650148245031000405540e11001c40c280106908003c5d2841c925000c1000c54034200122500d24442841401010150f8415190b4000f650442c42505190030a40e4542d0108a00d4400d4100e0344030340100b001142903d51034031988000c500c0703030725150f41540414040100e00800101904e0040d4000e106604107a950352503c01d80114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 225628318 1250 225627068 225627089
    0xc1218050406031e0f1e021804020904030e030319110f030f030a110d09111207080d1407120207090c05070c06050705010e1c0206090a02030c121915180c 67
    0x1864905043c0e02402c0290144c944510290a0140590070f0b12028111030310807942c0b1031045140b52a01c401008c0280e40207904500120300250009000d040c2100e2100d00080032a414510411082908510554080c0c030000d00c1040070f40348440313020000f04070710b054090003031428500201115980307070100915800c11503884848c00b400400c01c9200325600050099014000c0c00414100610f90300c044202c0c2c42e0040c00d00c80341c1344200e050081010300c1500c005501030000c4140401d000c443c24400401c44007008401040070b003000402140d03064007508426000b0380701c09481c0101c1101158002207a4109001003001410002402c24213141d05452244c01d00030388031280c03410000c1c0100a0354007210b00034401c0410607070403155400800c2e1410740c840c0d400c8641560741d800b015134484100d0030000f9003682c004403520303142c1d183c19a41c1c0a411440b2070100c411070b200f9070482001e4000c08140c1030310030411014001c1d0903901c450060344010b4441000d00d03480c5002980d03a6086010942c410582c642 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 225629568 1250 225628318 225628373
    0x20d111608030a0f02180918100917030403090515030705040612020903010c0905120f0c220903090f0b09090a0c1403040812060307180209010c121805040603 69
    0x280f03aa07034007450316440a132404649031b031110000703600003201401a00344640c40c0800010034441060145041010400e8080c7c1075003003030a00e584018001030700e0201c0ba03c012a0b5802e0b0010050b0790091841a070080e036a03261442d00c0c0c8818010a108081004902004200100110160040c08482c22540d4234502039410450031030340c42c03009020320041c269055007492880c10034281e1000510080d110119045d14002405112081e525004096042c0454101c201055100c1c03034034046202e40144031100c6a2184551440c4010440f110800d088010510501c020301c0392802081e1140c024102e00524903140040c110000f0300350f04030040080038541e0b11000160400c901c81c0001003100740203004d04945a0500d850001c20039048241c00c00d0b4011510000200d0911300098200125034000d6072441d1a2070000d200900654041704140e4140002c0b031061100050b2403c0704041c618246030b98004901c0c80c00501480303802541c4e442540309a0500c00207001240414410021030441c846086d13101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 225630818 1250 225629568 225629581
    0x604060e3702030f070e06120109020904110403050303041b06081303200f0d0201110a080a090f1a18121b0d0f020706090f090b0121020d11160803 64
    0xc1e00c5601001c42056030021062000c83c403081c14140d4000ca00c0d0b501e4070026491554180f1030180295002d03601c00d0840c1c00c004100010701540140821100030f400450b80d200d040f003d880b40e0b50b01540c0100d5181e800001040240b1018040c061050f40104504403400c2e8034000004050160282c81e90010300b1002030750745c0800d80500303c10354289a40c0e0104022260034056426192841040c0b100000d002d02a03060240c1c83c03046c03044840340007003201480e040443e1420200d640010042c805515582e6529991020413071062048034501c8c03040f42d0f0a000e20351340803c0d02c0001d2601074895442e00d14460f49442c0c000310040369a4034112025801c440c2c07a4425440c1c0028112a07a1403540341b1400780b4440004c881d03500181d5519006d20359000c560ba1255216800c45170900d00c2d00c190003c04414000030701c1205540d402c40c04d400e2405140c40c3d43d13286190514000710610790440c500e003160340069440440c00c4103004102610b400040c03517606109004040000008590300010401c1100000140f003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 225632068 1250 225630818 225630901
    0xe0106030e0a120207080c0a060206070807050903120306041a06040504092604030b01080c090103020402090102030d0f0506100903021e1f02060109060b0703020a1101050d020708030604060e 83
    0x1415074011800f080c1c61041c100000c4c0d110103043c000c006040c007038588a000c00741810b00031842100c0c3d09074014191a40c0c0c2c404100c3d03100102034001c0c42080402c00c54124541d0b420440b54460015060201342d0341c0c10803d04200031602c0603194550340c001c000d00c042d1615542c400641c0c0071501c003546c0c0030130308420301d1070402501ca403050024298024400801605001100d0180080c5da104da031103650241d8032068800d03030301d00241106661140c2c14200610041c00c26170054800070030107004807030428001868820a440201c8021000710350b40e242000f0042c030380440b1900d00071055044c0141400d01315000b240c2c1e40454000110303e9149036681ca54540c0c3c440d96000010352046500300340c1b5102c1070500003502c941e000c1c41803c00f440c1c1003600c00704004000700121462aa0b06400500b00b0085a0791009002102541010305001d0207010042e003141e5103000401301b81c1c0c849c1d40c400ba6240b03000b60030401283c415400040d00413a141d01004030307112070b041da00400404802d000c055240300030007103550f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 225633318 1250 225632068 225632083
    0x20306010614250303110304050601031506080f0a0302120a050d050c04030c0306050a0f05150415080106090b120c211e030304030f0813060216080c15100e0106030e 72
    0xf01888901d60f030542a090b802e904600c8a40c1c425541480100c1500070300c1c0c51140000d4038040c10b5078010400410000d4481e144000c202448100d000c510305a40d0304103181032040c03026111a0f250484a9103100300b59040c0b144804030361448480c241000402403009107580600c490f004146991403002c60040c0004200f80c40c000d40d8800185c0c08010344038035042c8043c100c180c469480603420850009144001d41c00307654801c40300d407030003084a00d125100f000060000c0304080b085c1c892608002050b00d03034080c0619000340c009610701280411503c1c00744104070b1041034001c4160342103882541c80d195111424000d05d0f118200d4400a0841c2e100100760810031402c5036140c004440450202981c0d4001c4041c5d48034500a4480b00c03140d0031101e000f6900e81e1812201448110344120303000c3c7c000307019680903107400103014090764201c8803d036803200f040d0f40c4000181c8002e640800035140c45602c020038034551002111000321422440d00c8829502414180100e0051645808580409100800404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 225634568 1250 225633318 225633337
    0x402030c0d060803070809011d041a01110d0c0836030c0d1713150203070c09020a2a021e1002030304050d1110020d06061b020306010614 60
    0x1155a810090050358480c1d01c00000c209180d41401c60000c3e5000c4048251844660030503c0f0f81e10b4000140d004581c01c05c005401201c0b0002000305c14229611903100351440304089604180b130002d26000017400a5010340e4a598056100307203106009594410441c841d041d5001c00929110b0102c0883c04001e06588903041c4044410240514141d8091120360b5041590075810307203440c0c444c00028081c0034291410094581c5280074401010400e4680c000c140004411032080c20b0f158541043c42e48900c1002403640042e4004a25042408040c205003001007294400c214030f02217007488080c00c00d0754640e588a000c6030700d41c1464261650803403683c2400660040070990b4036600d64800c804043c60b0080c56901074444860281585400002100c0c012500040180100c1c00005021184001180502c00542c0503841d011101002e8900151400300028180801c1d03482c14144000c0c4078541c0700808036100c00e0f014040c800561000702c1c9250540f6418130f0540c864140400307c0d00c0e070342d12440641 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 225635818 1250 225634568 225634571
    0x612070804020a08012313050a060507020105060a0f0501050a091e0602010e01060e1506090d0c030611040e040b0c0412030305041a0415020315180609060108010605041206060504 78
    0x100966564041862446244212481000951249074140c2220300552040699500401180103000d40d442049680503040f90007020110300c1c181c0c1c440b41424032074241250b0050b00c1c1c1090004594080c0103080d4880c106032110601286010180e078aa0a80b600c02c441c1840000a01c10050300c0c40740c6480000341032600901900c8525491010074113070110b12481006510f003603054100d0107010700030f86003160108078480400c0e0300c410f1810070b4041d001498817035211108010300c061680300d02543e004600d00400700d8107880361039401d1110646200070010808210100818080747d03502480307540c0c0103a084003904520341c5e55001207146500c5030340c1040f0951000441b40108240e815000389226600c60100c50002c15007041042c4201682524010065800022104c2d030700a09a806998404111580309100b0342000c0049800c0101c031003c2983c1c002d204408001e128100310007040d0b0000020328200d41250314066009066004a014040e460380381c102c02602481000d801410140c24000c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 225637068 1250 225635818 225635821
    0x71a07090b1c060b030405060a02090f0f12010504030c050105070c08030703090f0803010f030606050301110f210f0a0e0610050409020105070b0106050408060c160b18010606020f1603120e0612 84
    0x106101c1c2c3c0d070801c0360121203600c100740000c9c10a28090090b6882c0c200c1c0a42001c00d00c8207040100148100154041900840c0c00141c95405072824000e4038061070103070321024089151800c220f402c2da038000f40110103000c42201700c040040c4140c000c0f26484521858002012500c0b481d09141011752050084d00d000d2005c4008904070300c076600c105049901c01d43d4200a41940d03441031500303968600545c480401c0c024840340780c104092070001c0c60700d24401e5211031801c1c5582400e11a1001c0107441c140c100d14000c01c1046150b60040c131980140ea04c40e1402010180b6040c82807040043d6039000e0207000e1070b218006041164000c4041d20303850b950211a0442c1d941e122103000f86240c100740701d4900c0c10301c18040841c0c400c50f0302900b12034020080116480344147c0c41c0c3c0300caa0a0720400307426004088405090102d10300d5080c89500702600300369000d45084440000d05a1902000600c07072000041c51043c00c000040030032804040701a480e0070030650300103a010016a00f8040c480203030b65180c1c0f5010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 225638318 1250 225637068 225637079
    0x15060d0509100b01030519022a030d23040206090a030605090606090c03190c0c080a030b03070b1206040c050c1c020712052e0e03071a07090b1c06 64
    0x500c0391031100c008002000030030b4081e00114140da00644d10087d900c82032564010258072541c00903c20a800701c211127a0300144c60300503030010b0f41200900049508041891281403c003806008032a12400880c480d00044801e14643c02500c09400240300f071000040b009003584684901c40001e54000c1c2c02003001e45884400e035520749034201c4084e48120a0140050703042083c00081c2d074041e00c0043e00c801000110b2905050040c1241d502c41011710114490302800107100d00020910341c500303654082020306008003071502e800d280c0d0704607040640302409413480c0c4043c44d00c0d03250f621640c1100c0101d90101240c60955580c4540e040f514003900540803401c0c444050001814000382e50740d8202e0b000280d4684509198010303100c4010324642180031916030790344904040c1340150109081364200d081012800d02c0031550701407206052504081105010b000c0074010600344099110944000c034a0402c000400390b8010307000311085000c02154007100c0c008841203481402c04860020440c040d05c90 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 225639568 1250 225638318 225638323
    0x100306080706080a140f13020d02060a02030d060f060f0309081b0a050c04112b05070e0f03010207080703051c050f090f1c0e12060c0a0207060903050615060d0509 71
    0x4c0755822449803c4c4080c101d0b0140350540b00c680b1854a0051418058035400c5120100710178100040c0d80c0260104840c1c005695a00000c0c402840e598000f9079a45110451310001d540640d4400b14101c0d2600004001443d0010159000d1741c00501e000109003030f241c500840c2c0c0e8020f10210800b1006d201d081e89010300000114444004e01550450b032006107030104100558010a00c40180c88500303001c1c000d902c440f11240480c01c0e0303052442410701a004175504404031785084440b40000b645214000b291401d1640314081c00100980003503161172415294526144100c200040801100203804802524008140c411405140f0400e1107581820101c4801445c03043d80d40310f0403809a8094201c0d0240001401603d10019812801800c1c4c2400307004d94210411841c0c0c0358000034101440f800c4071500f806514440c680e28002c443d00c0b100301d01c07402860030500d50003203428442c10799410b0001c2003000031041d501030842c80301c001c0c0394852400400c449010b101786058041782003400f403100b001d201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 225640818 1250 225639568 225639571
    0xc0303041217071b0501020714010507030b010903120806030703150213051e120a0f1412132c160305092407050702090403050d200910030608070608 65
    0x320340e10780c0b64204441c210710b01c0a041c242c8900c0301141092007062600d40b907140021040ca801100018103000503034803440d0b601d035642580709085965070001c02020681620807c50307185e03401e01e40303202000d0840d610440900e50426001c01840301d08000030700746035003c000100156074410021300502da030081252019402545034400241c049080120b900c1c100038850001088107a1014000c02e0f06c10002e01041c183c2400c03c1c803d0030f0052905140108400341100c0e080326110b003102d902030505c0f0384091800d000c0003c4103000c000c4010041c814170b11000c46c002c030040d500e50300c0141c50040c92041d4201044641139910039076400020003040000f01d081e1102d0308610845440a002036620018040e444062421081000009800020000d40588098258000039600701103142c2003c03500050700c104030440c2c084001402c000384c03601302d036009400b801d1414214460104240405100301607228000c0313203610360242038035007031440b0031521a801c088010004d410655070525143c00700100f10301700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 225642068 1250 225640818 225640853
    0xa0f06140d09051903020622060b0a0f0f050a0e25020c13051f0819020a26010b010305010f1e090c0906030b06031501120209090f0f07022803050c030304 67
    0x10307910003d40c5803205400d0703082200080c1d4440000000850360782270010448441d840e508180c4070f86010030f0400c0b8180c02040680034104e00400d880d441e140400c841c910841c1c01c07002ca9141c945062000b01184040081e04d03802c5180141203079003d1600c0224642644080c03569442103082400c0380a41c0d480f40d018900036800025031008000c060441030070980300c0c61081d6600380c0d2000c82c400d11850001c840d107041c0a0310003802403602540c0c40e505010b071502c90b03590314513041800041400c50160240300e5148080740c05e007418085503260000c40300071940c3c10310540b01342e8080764100c405c040e0001c500082c054030054504001c82c0103440401807580703241e0b00541010a1910000c001145807035010380c1d200e03540444501c007403014a140110b80000324610002021a02400313044403030380c0c0d95403103c0e1058a40b03001260303240c540250754042448000e0003c5065410564080c4458460003006440022a065a44c3c40008079480d00310f42a10030358402c88440c0c0808001e100c100105400315400300701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 225643318 1250 225642068 225642073
    0x190512070206010602100f0f060305010209030d1115041a01080106051203030103081801090f060e130c020a0201030209180c0301060809061009180816020a0f06140d0905190302 77
    0x255012801da80d654002c0c000c0e03401590101e400c00ea0790101e10f800811009200700c1020036205841e40414003694401e810480e401c0c3d4001c600c0810701e0134100700032802c5000c686817840340030484580141c4ca44141d019080301c072480d40740000341805107211222700103404190b1000c00c15030351051003074000c0c0320a00505106007203018008378551000000d59040e2608030035030700c2c540b9114090340510500d1600b2140d041c004103080000340b1098010b00c0ca0300802c1c00b521480412803c000410038011000030511615928009400c040940d0005c0e06c41c21080c0e080c02d00582d201200320004c1c480c0c0103c003001c10044a212020814900b17910300185041740c0040d02d420300181c5480207455203c1d6422502d1036080790070f481d01000903050703640108003500040e0000f00d40e622001c4e100e850f01a8000d0882010103030800d590041181030002848004004150303c012141d401d06100401040510150000d03040c000304014481d0798581e031220140603405400c4904840100382840c0404100002c15000350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 225644568 1250 225643318 225643321
    0xe030307090524130608360a02090901140109060303050a1d0307170c0603040308190f0f0b1206060a05010806040e0105011d1e0403180f08010b0a120f080d02190512 72
    0x102081c14122000a4441241c0340503140c40341f403071103c0c90f04481d5080310030344a4a9043c40168468040d0980540161000454420a041085120070314180e001c10032003442c00d81c1c1007021a82c003206445004c207131031500f20110510032076001507010404801a0740b5028888002401c00c001c402d84c1e05415826905882142220400b0801c450004880240100d66182c0010700c1c4038403076101e581c00307441040e000010b40714081003001c1c08481e07070b4002034881207554089000d6107103000080c01240c0c1c0765440c0100458a03007140410304220007441114180000e0300302242c01552150050b00c01c03900c4a100030407096039140754818103908450301c42041e988a0201003010382d40c0703002d40d009503d80c442850760b8498640390303000c44040008a8041617044500500031031141c0391142c070380000304074800010650301520b504205007001c0a9000e6171540d50300a40e210005031014043c0031049401c01e0441e5111444000720102a01c100403140111f030915007441100c00350003001a102084070080782c40b413075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 225645818 1250 225644568 225644581
    0x170909060a05240c070e090c03011e0e03310e040b04080306130e031b010e190203070905040303091707020915010c020303070609060e030307090524130608 68
    0x54485a00419810400c109810032804911104143c4150741d68601903140400200040d81002841d81144400c3c0745200c007807054041d070410607442c0341c1c607088008010962001f480c1d042c1c815511000002401d485901a05111409100341c6244040c1d0049180c000c214002c2c05c1d90310050341021244103044600404205003640d0002c15100310351044030480c41e034440f91101038058100502e22603019181601c2421100d0140c0120740148009900440d1603141e2076503100014417a40105000d0ba85c90140030242c045000100705442205124000c50540294000700c1d04042c071a4201d0300641d82480c00740000c155141d804811800d00607588600800c1e04c9501e004194400c0070b501961046201d000320300700d00070413010a07640c060141498510450303164082419508071540c1941d800d966820201d007402000d0180240c0c04a4907409549140f4107210040c100c407005015441c0603c0d461007500c010701404113210080c03501c00c00c64080c5c8131010781c04251407140250151000040300e02c40414003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 225647068 1250 225645818 225645829
    0x3080c0d090605070b01061b0602130e0903090109030209092404110f10030e030c0f01020d0522060e07180e011104060c0206160605070503041709010503190917090906 73
    0x3d11740c000401c9801d81d191075400c44142d03a0000704640c20410303558040001809510041075007540d02804400503078605050891600e4000b0580f101a40007009501c03050381e8003050340026603604503045000c58030b904194a10b0310354020394000f45140c0601400d039003101c002c40e400d8030452080fa0540140c1d010b8405012980e80c40d8505103811000246a1002d0700340250000701d020161801100d0901d01c2480a031841c0243c0c020440b0140d0354005080e64401100740076182d44201c2d002e00350b00360041c0c049244113000b14050409011030b5600c0000b0b140c00103041c0150002846028a14035000c1c4400e0034407801801d40c0280406550700e4947c2880307800d060a0203817000c9070442e0304c904a480b50150280051503002800502004640700e8658000640b944140350141e01141d6a59031a89040c1c075285207039030704e07068050b40d50750014400c0c10400c1c0e9101080b2030380a4418140400b800f032250300b201c409031040340e0008010700d50303a40c41c50145030b4120000e80701a10301101d0203845900e0311010b014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 225648318 1250 225647068 225647077
    0x2102030a050d050a090519030909050402030606010503100f03121101050f0a0b030f1014070509060d0903020f060403051305040e1005070203070b100e07030507020d0f050403080c0d090605 82
    0x100c0c000b4008620155042d43c0019030261500001050000407070340c500c1e0805003030f2403103c07040c0d1404030382040616500c520b601010340030b009001c11880c141034001940d2a000206171504102002000be4144948080c00c00002d01000300c1c852426522890b0405642011038030180001307040c1e455000404105005440c010301040e890f492aa84031201120064000c150a250300b45c400c0f41000da0700030500b0080d081c0464581440000c80113840d00303502d602d080b0b000d0807880820100340074503505590f07040112480c650b40c0040000d611040b9103410790812042610202c22800340e00200700c24150094004c020804032904140303030f0303240c0f560204030032140118060070050303003d80505114040107030300a03500320b00700d03004480c244421962200b2903008100c4012040d805410300070402c0700c0d58211100c0c1c10480504040c44a890030b0b44000b507035441070008007420400f509141e4020b0f540a44120b8000d560014070080d075415034201c01c00d607200301280070480081c0c001c0c900000d0180c40340c000c0e40e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 225649568 1250 225648318 225648337
    0x209090705030c210103260d021606020703031d010e070302240c0703020f0f0105070f02040b120c0306090f0a1202160905040302010b010e030309041d0703210203 71
    0x5900d03180c03810125820b4000030401ca00f03128080041c40c0c0521009140141e03d000040f903104002e41c1549000604044070215981c0f4a61242454521003084030003510b03c2e00031102c400684130400201e24062000c00184003070300d41c5100181440c01d041d4583c0060a044503001461024000b0204660307080341d606401000b5a41c010500c02c0c00186400a0001900c030800c0004100c49554814080002d622004440d681d80e0300c006030400450031b125165001505040741c100850a0409001a01a100c0d840c0000d048403500c8610000f15901e03640300d4519204c1c040c08690050503450000b030350303510000c01014483d124020018900a0340010314084a0629101507c10ba24881e40d812603005012181107003136001d032404994020300070010150040114803004501707428142800390840305400c030010704001291205101544000044900401058074000340324820b00349034541e1f1181000c0b1080e040c0c050082d0001c2441a09007090400c5d9101c07400d2040b2014131100c09a039648141d000c80b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 225650818 1250 225649568 225649579
    0x304060c0803060f03150109140f04060b040603050d030204030501050105060702030a080c07051503041a270a080f03010303170f0402010c080712020d12140402060313330209 76
    0x340400548100099908990302a0150359120501c0000904054100b5003980e2414540f40042000c8465070082c0e40c861985401110220306003a60600da55410007000640880d8451103a1290f0343c4171940304038011134120090358004d034114107008000c1c0d0f00512096886609000011406250000484905075030040c01844215010399850b880c0fa040001c0884060042d840d0000742e64440d00c044240113040000080d0340c80c5403a01e060007409500302c062016820000c2d04001c0c01d60b4080f4100f1540b10074a080303100b044150424110b2400c0c0c0c1448000f044031070b000c61100d4000d01048040c5059921075220203070180090200a00c212030304440d40586800d48030081030155004441070f00d0914003c100c118a07108441d110807200e584e000100c4c0006a002e20003041e00c0302d6100c4005820b01c10003080a010400c400d036940f000c89075010b00b01a2103624001702080e1940035a02000c210650b1291080c9420b00310003a42e4243d50f040b0b0034040b0700c0703100100c90058402ca002c1c030845001c100000d02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 225652068 1250 225650818 225650837
    0x10608091b030303150604030602030112030318020a061d0d050d1b0305091504030f05070501030b01090e040602091915030506010908061306241403030705060c0d060e091509030406 79
    0x4800780b10340c45c0141501c1d00060b04200110104074140001c1d070182c01c94481c2c0c0c01100c1c030540b40013000c85905452540b091740301605808016543c9480c40750880303074645882d0300301c0d444040100c4a161040b400030380d4000206121501045030129110b01145036540b2030a1030011034040210681d5100303540280090401c020010051401039943d0f03542005801c03a10382001e4984d0b403000c4040382100001d85541d40710103420802da6925000d443c41c0d4180030300c0e00012407450712041c158005009003004110a03004101450542c40b07120a00c008464800c404c200600e594800c5404036603203030026140040e0414000942c9940100700c1b800c21a40d1503002040c06a40e1000080d8403a012101c04507140707525102c00440e021035104503441403101c180d541000c420f2030b0031988482e40442c400c01c14041d400611080e0041240444c2241d032059000d40005e40d104a070300c0000e1f000341101d41040c2c084271070050030b2020044000400710074003840021024820b0302e50200d4250307680079920501000031440ca4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 225653318 1250 225652068 225652081
    0xc05120c19030c060c081b04081222030308010603060b0f09060a090f14030601080a02010c0f08040801290111031602060c010f020a020d0302090d080a1106010608091b030303 76
    0xca04240702406807800044104882ea01c0f4070665102210704400141c0c48804d2080c0310000b40d040700b8102030440401884d007450a0300303407610380c0f001004040d0200d0300404ca8805401552181c40e8140144540c0801d4031510380c40d002d051232500707000325400a490701c00081070303084c4208c0c01ca40f8520301102c0c0003820301d650641001140c0d80103003100070420219001c0010700f880d100d01c068004d00554480c80c8840003008040c50301d0100b059000c550594071085101c400760b60003a03115414150484086040b5203001c1c180090340b88110f500000381d5602c2c0c00e98041c42403403600a002110403902d00320340114400c4100441c0c4100010400403c02d41040018170460000c01c00742c40500c0f440900b038903060010b9910000d007100c80218404811540010703098004513410300604030b040071641411400e01c40c1440115001813500360000385001000543c0141c0c0c00c2c010703030350305000e00a8201180c1c6c3d03035038440b200204050015034401c540d81c8610144002030a09144101c80f4180c2c000e0010350441c1d8480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 225654568 1250 225653318 225653353
    0x12030b0307090221180c0108011a0702030a0f06061401020303070f0f0c02041b0305010b070f060c03020f1305150c0c100e03151509070e12010f06060c05120c 69
    0x1030805183d00c0c5000e50013584500b080004092065980b0349941c0d414054042080f8144a6441a414104140140180840f03208403446d00640702145100d10346414052010070700c1d080c0b120b10003404500d9000d0280c0100030194005074240c2c1c0f040340604005a03804001680d0300c0c04180c50810200b09140c41d00c1c549244902841c040c08a524075001c510784a00b60040303800c495400700c0780b00000d01b000004411164240c0200e80c01056107420b050718202c0d8907240c140381c8078050040100f910f6251292100d00621a406445603104c06c1e003d1940c0c0c80702c070086200c101d82500e1140c0ba0080203541d03081d403c2401c145007540e090750403490190142103081010090f8005c002c01206c000e002030a40415001d440800c4828010610600c91841c28106a5881e00684440c0d0015620609050041004c21030344000c0402d4a01000d454a10050140280381d40c0503041c003a020028444c9008400603540d82d00501340d600c014002d500381c80b18008802244860b6100320508040b443d4041d080d407406a1025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 225655818 1250 225654568 225654577
    0x608070c020418081308060c0409020f12090a12050f0904050907090e030307030b030d0f0f0c080c010f11032e030605070305220c261912030b03070902 66
    0xe0001480a16880340d12000943c245410b40c0c036a503000c5201c001824200b0100e0000e442c2d9617009200a1410f190021814441c0e400740400d403c0d0003003850b140c1113415905842449506044982c024501003680e103580b020404401d40c1e8140040f043c03000858002c0c02201c0c4441e40481c0f51604e064000401d01c40a0b02001d003800005105d01c0d60b000510b11040d224040c45c031400000915134a0421131030040540d201520010320a030840c9401410481c1c0110303152640c1480c1e0b08040c1510b008540b02612507010b59180904012000600003100b46410b5102c2d02c9050380c040c60421258800d031443e80b002d40401c072000510b0540380c03d02806012880380701c082c104030409001e42144d5860360b50307003c29104240d0312500401d441c2c0c0f007800180202c80400030750404408000a4500e403040c0c503080c4851609104921400c0c00140300034061604c4000520060400700003251449070700014451000c44904000381e41c844003041c103400c4050700c01d0080c4c5e07000180c010001c054480c103010384100290310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 225657068 1250 225655818 225655823
    0x2d0a030c2906150d110c060f0f04060c0e120c01170c03010504020306030a0c09150b0c060c09040204121a061816030b190503120f07260304060204050a0608010608070c 73
    0x405001000c0400c4417801811103041d40360782103d0725140328228035032070004050020400754030900b040000b114524071801e907105802c03182c0880e00c080d40c0c43c030075070711480300350746a9820140c0e09000784215000044c42e4074807420b00b07a88443d40300307023000540036242d041039840b078100c2d05007000104018a416005950042d500405603601c03100207a450200c040055800620f455442d000c000d150b000407000f030030004200e510541450201c038503041e25201c690040244051600100f01c1865a807103a17030548010300349503140c10b82080300504190760f0701b0860490742c030400c050301c40c00540c49042c2114800a150756203007000409484c0e402031802488007120040381015541e0050341104d0366a100122035200c50017003582809410803041c0750611017005030fa280400410048115501a940c00311200c640d08100c4001029900072503440ca07526000c001050049004010f0000784005580280215031040790b020107002e070f90301402e81d4080e034244107290225460100150000e400740880b040c40f01d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 225658318 1250 225657068 225657109
    0x16090e150405062403060403030e0c040906020903010c03020a0c0f06021201120203010b102a0c060f030e1b040b030705040c05090901080c032d0a030c2906 68
    0x322029190120341000c0350309403007075071141c0c05211980d005124040002006610140a03a4030782d800440e5450300701410090405545803002100d00005001510305880c0c010002d1114000d142015006034104d00b82051195280000780c2c519a40640300711020041180c48805e004640c035102c0c03045800d00840c00762002d603000c010114881031034a6016028000542001c85c104c12107005050840c0c81c0d440007503000d140101c80c050002030304a41526680b9840c03a03031140010300020300ca0200310340d00300310061400108000202d480e54111108941524031540c040000101d0ba9056607502c4245882c810845030504100f00010700349904a41d600300d0015040320601030740c4602040c00c551070391241000080002c1803100b8a49440411140100301800003441c65101510029841d9010030180701c600303200864082544110300100e4000003000301054030101c030400d040150011a000320201d40d11420440c1d20300d41c581c00c09000301c04003e228200302d00f06503107603014800c445a0320740b01c041890 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 225659568 1250 225658318 225658333
    0x9010b0a0323010806070908060c1e03010e0f130b06060a031404050714030307050c09040c080a051c0203190f030603020604091a0321130e07090609050316090e 70
    0x108a03882009150034a0780b964482107624004c0c401d814414050280810403403d82da040120030300000f00c0d1a00500c51080082e51204204121004a061003070299815003001c00005990b1004080d04d40c4a40201c1c48004034640e51f00381e044605801007000241581a203001040c55410140054800c5019078140000c80b911551105201d101c0203d0302101c00360701410301071113242e42041c206408854190300550800c02c641d5a01134840b04040b142500036041240041c045c0000c4403c2c10009046607010b8410740c0c0080e00b071040d100c055000003440c040031020b0b410602c0300d1000003166110f4480f00b84607030b0302821202c402c5a450302c402140108146d00e5020101c0940c1e00d003001000208104000012500020b60304181d014180c42c107134920a8100d8124510040c5030342c200704540710101071071a5900c440a1a400100f1f24a035042000038140b0a8108034565800819410984800c4d40751080360641e213000305990b80940b00e68040480c45409801c10842086401c00041d13002d441040d00d045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 225660818 1250 225659568 225659591
    0x402010c02041b14040302010c17090a090b010206060d03080f0403180b09040b0409030503070305130c090207030207090b180c0f220906030f0f02010c02030d030917040509010b0a03 79
    0x180c1e42a8004102e91402c41030110150139000b40c0400c01800e2110b0071356052602e180c001078800507690f140900011009140c103262a003031035046624941008241401d09078650380240024602583c05074054455074021495a181c20071855500943c5681d40d02d0041d940e42604003500440038008030280000706180c0b0f843d8010414150014081c1241c03582e466540f241e081000382c90800c0000c500461814a0341404654000100d83e8454000e05000ca000c6d142c01440140c0208641d43c05029100c1140f404034100055400603c1d565000c3da00300c0e1019a00c46507540100c9803042200d41d40aa9040d100c03d039220000b0701c0c13580c0d000c83c0d488030480c105218a0f621390706a038050000c030002041840f421802c105094071320320000e4500c2980c1081043d055950380c011004000c4030241150b0044401d0504580c401c0000c214860740c06001c1c3c902c0b03440c00240140281462541c1150100b0100706070420312072801701580d0441d04001e141c07440f66441e15058607019809004460304054450010240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 225662068 1250 225660818 225660821
    0x903030b03030a0f02070b03040317101a090118050a050f03010b040c02150a1401090f0b030a0623190b011103070b180c01020717011508010608120a170402010c0204 72
    0x210f543d19511106000d501d407400090418159400498030600306100344004070754888a0070355514a00325005031103840b104007504112003e0362140c259140c0f8000e0308a03a1441c018094080c0503000c0c0c8406c50802046d100c141607070f8280d40074a40c0c0141a41004210300d18100030005e10802010b000003405040c03800c00703c0c003030310b00b001604070141c0d10001d00c50311400c490300751059024221900c10440034000a10f5071404071418810a56001e03141c60100007045016884809007000c001c080b100e5580c100d01e4140b028000060704860080ca81d541c405080c0700a4404080c07040d02c260100f0241c0d40d0421007108000c0446180313460400c5940e081c3c1e504c84403020030003020010b0042c40c001c0f420303243c4094900d003240c800d002e1418080d04682c1c100200c6980004aa03001e075403140b030705c2c46210002c2082990050010b100c0c04500d0394001c80c40040c1030300341980220180c929050a8494a8400d41e0b0003010030320810501e50002100424035140205001000ea0f812903c140f500250b0304102c0d800140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 225663318 1250 225662068 225662077
    0x203120d0f0609060806180604020607061e050603010606030e120c070e040f020301060f03080d0515131a01020606060d0f0209101107080f0d050306060d060f140a0b0406030903030b0303 81
    0x1040c16504c85050241500421a182e840910980341c0c0000143c000b00413502c0d0700e40500028000d07540031070080100f052541040195004443e840483d042401002401034081034401131302035441d246001c0703175052180c061206001e00a0000f002c0c0400d811003284411361010502c1441c600940001181901000607910b00a03402043c0d0000141c0c001d00401d401c58510307038040100c2c1c50490300208005032920080e25a92100b891001500f5525410201d880040414099510075201018101d00484a41c4007407602c40324001c8035581401298016a1346540545469038004001c2c020000000c80d00d4000c0302000402400240c1812061008501005030002281001c00ea42c1c0c040003070400e404011000013005982c0080143d2042c806105803104056541d000c10800d000001420b01e40b200000c95403810311604080040c0b03641c0d03245074404140d1034007070603800c0360314005403c4483c54003104c500207654079007082e5440d16282c84c3c1c081d0010110032004a0905484076400312481e5010710140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 225664568 1250 225663318 225663329
    0x4051e0a0e0714040302090609090a0c08030a1d1c240911032802030c1005040e16051c14040b011401020109050d140f0d06210203120d0f06 61
    0x1c5006007040c50001e0524985041001c402580620041026981d950401ca410840940d1414450303200d008007103045c0303491000003501640d0710600000c0e0f503d0340080101400079031940c071240d20914440d18981c6200040701350540c0101903000d41a840c0310300d04442c2078041d124250f42d96086c600c0400b00b03010f504c0620b07030240711144d80b4056603040c86010030320020004800c9014081c00d071941e090b0919014002d0740d1070140b82182c1101c1c0780454a04004e9100b01d402c0042c0142680c048020000b403099015002e0303280206c0071a0301040c0c4c600b0101e07441006040032500c0e042d0901c10b12a4004600345800985005c3d950f8503124160041c1c4000b00d03030240554043c00009900f503040c885a01c0041c104c0040450440e0714040401d0302240c00402c0003a030400044c504182d020a100e6030361001406617501c4900300c0c010000c2c01c42d51910003a071148045407a80209001103c0c0e210030356071004807041d0406074040e0041044075850349100e000030003911520070f00020b210030f891070510b4111241034005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 225665818 1250 225664568 225664589
    0x30705040806131403090a1e0305010e01050907060c03080f151f090b041a160503030c0a031104080604060b030708030705060f0109110f090105070b151002070b04051e0a 74
    0x1141804008030241503a1542013004515156000f0b000c1a5801d00d14444e01000e4440c140d03c0341d1558030310321480001103802c00020301a90315151320722802480f042d6448030b0680709030207002880501543c2c041c0c100a82645608060707550308048071007200f000802101e207095a200c8e0100d500d039242c0100001860a0004502d2036003901c40024107001f0741b0340c00c680d0141001b4442041000300d00c5011060080c0f0700414107440e1034180100e0581c400c8200e070024640c1c0800b00800c0907840800d005006242c24599052058040e04150030003148603500410189030409400500070561603004101b50030b1020382101c4500350303190002c40c1140c1128030101d5260300030070244480d807010043c000b400340042034000c014502d80601d04007410700c0769080c640019000811100c0c416800b410549111640104003034440d0b244c150348420611001c40381c001d1140040c00d1003511410300c002004010303254010480c03440c060801c020400d480f500b5403201c00184450100d01c2c001901c0b0311009100030900c207680d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 225667068 1250 225665818 225665851
    0x14040803092107020d05010605031e0622020103180804080708100c0905010c0c03170a0f020a02010e04150503070806010501120b010801060804060e0d0207090f0b0f06030705040806 79
    0x80860410541d54165005042d03000d9210308142014012501000c0d030440d0300d04001005c03441c11601609680d8030003507241c01030b4883c00a00d281581d80039020205054291041d60399092610012000401c0d04102c1d1b125080e11641c0040d4041c1e44040c0c4504400403108400c1c808560362070309264800d41006065801c000404c0121038810000c3c1952140c0c404070600c18024000001004550b03540300300381c1001101010b410a20000f2000b9401070b50700b05110f850203c2c41d0039403408007a442520741e003000030500d201000078030340701041c1c140280340d05940c0c01000540080410001d01180d40c40010008001c0b0790004265808104100042c1810405845190f01d01030015084420101c050090036080c6080a019030384d02c40d207050306560490402c4001d903207603410020000d22180280b043c20348280104490f02c66000142c050031118000c100b480141180120102920700c4a5070b5940c00c40b0090f40500550301c0c02402460b0701c210240f41c0203044c0340c0c0ea0b200591800c4400d40c0c82001801d031100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 225668318 1250 225667068 225667081
    0x20c0106091512120804032312090307151109040f060824190e1501031713150e1008011806030809090615040608151008040305030a14040803 62
    0x4070080d00510000d1498034141016841c0e0158800a405131202000320041c009010503006104000e010710360302d80c400d01980580249125217030702050000080c40c01180002c1c4051800108445090b03510561100841740da800114000c1c25402c0c0d84040380510602c5241040d456070f1150949420412402088039480c00e0000c40c141700d5600295a41901d00f00803c0f0b00707107011440169000100903651254441d440181e800c01010700c4103000d04c0c50700841040f0310040c0d040201d918140c902031804540d0001b00c070b07080c07801c20303105a2042c4803203845007620801461403013140307290291010b8100740c07822140100010350403203140d055540c0401c0071310006000881d14600100204114502c0800000c1d0035074540045a0103400361040c423640800700000c25a1702c44800107840540c06605450302e46031100070240c40c0c2403080744c17181c1c007209103a00c9444c0a85000f2800c2c052001321903d4422460311580c0b000c440303540c401400303403e245485102e1900c0f0114001c10483c4264064480310713850b803c1a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 225669568 1250 225668318 225668351
    0x7050303130e0f090d0503040512031f08010b0a030f020d02060f0703080c36030d090509060d020603061011071d070e031b0a081608070902070503090f0301020c010609 73
    0x941103c1440c4012400c00140b0000061003042c1400a03080881e00c0350317501d1501602d04007106010441c0c41d04040144420000160142c00c1d0803621030901011a079281c0c0030003400c079809207000d0741d8081d06042e002c001160272201981801400a050039030080e04075000300e6001d51205000c00701c040c10000d158014940d01c01d03c5142c0044088845600c0d001030004035810300115040c0d406001d10301e140b1051a400b94260742d014048401405031a007101c500f15025044442d1031080c580102c81800000d0607500c1c10303200b4400c2c01540103019501b191100c10601c88101e04003041c510a2015402d11b400841c1e80c10801c0030018410300001030300f080b00791421101d610740b024249505028030790f03013490b50990780400d0f0704a0344001010008501da00c0784001036403607041940040c0c03140c001c0c0203c80790102c140ba0700c07030015a1010300c11180d10983ea5000b04049104504e405013858005000b41041072402c0340c0303608000500100003509203514501d03010b0071240164000000c05985410311403121604 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 225670818 1250 225669568 225669571
    0x80d0501170d09060509060319051005012003071b12061b180b09030c060343050a0e1002161502060103080d021b0703032003091207050303130e 63
    0x5900c0c2103e07081d40b81c418040c10038043c07088480d02ca01004400195110f03c1c00c00c2c14034050070b40c114244010b04082400c80c2000c2c0090050310300160f4150289200520b1031500c00412490071001140b0300021a01c6000c02c0c410900d0250020006020000610300410b100c0d200d6501d014040005a01800d01e8074a144204400d0b043e00038002e805102e40007164211200000305c400c4070340400d982e840c1080c002820075441428003a03001c00080709000301801200320341c41095404480d510881038041007845524a00404c91451881d41c1d000703101c112a1280016044d1402035003096400344000324000f4040c017214410390001a800b04d5544051100039009401c01014424510720b04900c3d00a4020345403481400003400742c90b00051000040d01342a811500c190703614559080a89078603003881c2c0d468904912065002601d8403908ad00f070016074a681400800040b0025841c02540704140503522010201e030301114007989000081d182c030140300805282d022000303800c00d403e0400a2517404000b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 225672068 1250 225670818 225670843
    0xd03060f09090f0219210203010f051003030e011806121119050f09060310031106090f010f0c05120408011409030f0705030403021804060f0c0f0507080d050117 70
    0x1007004000100742c011000000140c0c064866000039543e05c04001c0a50905601103901c5541c141c10300c081481d916024003040d10310031802030088103511a014000c0c1d800070b49003015840d80055040000a00170015201d05070810b04296100c03c510409065540c8400e500c500b02044204410281001940c07041c5c002400404011506019a2040030281c00341181918010300c01c000580c0d041c021119410b427107400310010440355507407070250a80f0700512024403045481c100780080d0242a4900a8265020b0450152100c0c240d01e0400e801145c0c003040e428a114103102d0760b03242680104a080c000106454a10b06160303598614001100f400c6943d076800c007002c07241d512810300003514804807c490301410851102c541750b54241c01c0903400c500c11648000c0d401035203002024816080040c0c1944a240105000c00166080034002c50561315110300d0340c00015070241c9901820b42c02840548040c3d8000d0544509003404401c0708011140281c00103001a104103d0511201c0800c001500d41d0701c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 225673318 1250 225672068 225672071
    0x306270b03070b030703020c070b07030203040e1008060c0702190905060f0102010e03030a020901140c07180b010801050114040302090405070e100b0a031d0d030b03010506030d120203040302010603050d03060f09 92
    0x70f103020411912400060451410140c002480458070700080140354050206800515511920b130700c1c1c080d5690f0b1040c0300f1b000e00c100c401000284688005d035000000c4130315560181c0520703500c44c1c84146540e840480c0c201d0f444058156040114400008490301400b45d040d0f000915080080800040c50040e00b1050304680c10314090100c451004003d581d0842a04078015032070b4100300005807014940640b45041640000c505000d00c50700c0011203400b02c644085000c00826001240041a1046544164042540c0030700401c800c0d4443d40a9000044501c002c0504041d00e0341c2c0043d5140c8000d64041d2a107074829881800701b040080111600038804000026188d8500800640c25004107101c0e5802e141c0c0e15494004180d00c000381500c0c40101c110180c61002c2d010302005002020542d0b0f0302030107980f8040020703501d4100003400900d500c696495001d9030701000c0e450b030300c065400100128119502c0d0000003000541c02c002401d58485e2a03200400c1c028280007500b5990700b0071354046440c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 225674568 1250 225673318 225673333
    0xd0503072109021f0c140705060705060a0c050f1207050408030403060218010807080103080309010609050f040c0603020310030204020d1b0206070f0305070804020904212601060e060a0306270b03 85
    0x407034019018040c4641d001100100c46e40c5030000e15801d0046c0381e0702c1183c116070300180d541e0404c4008144644554050001000110f142203011125805040165003081004102c1050344220304220582d02092925010740b03025100c171211070941c0c000ea40f08072041c3d50085005d0072040090b10300b4000035070003031809075a2450106401080c56806100140c0f580740f000000c00d02881d000e412203c05000c40c4c14050150b400c05a0b608014118110740594200925802c040340440c400d0003100c0c0181151004800f1450a42d000c0100030740c060035400ea01386a8400159101c407403d41c1d520301030791b0300c2034010b4180303172404c08000703040c108500c0050020075150034200400f260700a40c42c19089034058501c090305a540b403608418140e0406140001c807910b062150803601c0e07001280b50202107401000d8800b1056084d04040401c00a029200220b900d15500c8021410f145020b84100e19040c81c01140e0b056550b150311000c803d8106461130b080b03800b4050304c55580340902071482c071400142c0007041138 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 225675818 1250 225674568 225674629
    0x30305011707120f080406091511071503020c070902130b030c070809180c04050a060e0f010309021906050711100818070b0f03040501060f080d050307210902 69
    0x3110342c40d000d0b010b003002400300c103d000c2c041940c421000c50756005201999a0741c070f41801820306080e1380b14801d03425248021507450030f4491801c141e0324507a244010f01c1c401d8107001f00242110315841c440410160300340001200d001c020810035000b031400a100680c2d030300444003026070032302d86500016200c1d80e08205100c90514001c1c106e84400360440305c001d0b116004080040c4400b4002030410494003040700602840070403180041081715811a061076081e036035030a0942c3c640c0740280c00550700440c01d131003e00c5107502032340000f0a218801004900003200141856907010015001000022008103c2c84100a2140c01c01e0365412000c440010f0044110f44006100b55402032402c4082c0400b6400000009000c105003000381c00382462a940b90360950b405544607810843e0305640c41d40c205a80003982c481030643c0384060314451009410030340a049001e5642d81d001134240000c000c00d400001184489059821040013545017000c513484c1600d004004802c064a0b010a00340d4041c170055501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 225677068 1250 225675818 225675823
    0x18060807061e14070302011a030a0203071217040f09060603090f0204091401020d02030f0610020616090e0a0219050a05120a0e010516080f041a1003050d05070303050117 74
    0x10109108550b44108500c105070031070368000741c3d01c08142080c901003212410590103421054540c0544644540c0071001c0908250307551006003c081e40503004208180403000e0402e00c1e1141d804d008021200c503959000c40300c001e2690041e408400c080c0042c040500ca41c00e01c46c05004001c091b40d1509020a800c141c84003600500d103204020b10540d0b85000035401c0101d046001c1c5c15041a0400841d01c92220210742c0020b0350040f100d4030048410381c80010303054a07044200c0c0001c2001c0358000e00c8290f444100c4e1604070701501010600b40b2039825000500d2408200b802031080401c1e120158454944c0048030012078501d040b25030a20400307001c1f03540358951190036120351006400c1200300350b032185604040107100c000140ea001c0d508090820440e000d004507a01c0660203940e50b26500c650390154440984202903074024860364208580484c4240c00800640d005807402c0e0b1181401c55581e81c4090c5090a02004a03000c41c40101d1000f0616825100b400e00401c10b4032036800111400529071038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 225678318 1250 225677068 225677087
    0xf0601030b0106050c10051504240b0315100c05100c0519140703080414070503060408031519140604150f21020d0c02010c09210209011806080706 64
    0xf010041c02191165001c0800c120760b03400300071403400402c0305060981545c8103c9043c519418041c0d401e152202ca508801101446811004805400d46c031a00b030003900500d07944040d060340002106080c2848003681e50403031491910707050361150f01d0440038610f07006091003515005509550715280c0f80b20241d0f900300c41202d11042002c5c0001160324000a400e407942c259004102400c609d0209083c410142c100422502490060050741543c1d10403003407041c0c1e611064003400d034060700034501003000100210041c2d9000701035194011001c0c0c41b1a00401c2881078102040820881e503200d04000001a00600c400d0303104003999502d2420303041042c0501110145100102004801e0781c100040d240701b0181d40d00c949240c1c90038451074014007030001010350402d11601c460149019040410107005100b41c1d01000d03096200c000342c040c508928006070440c40004501081101c094240042e5111311446000c0c08100c004c40008040f07401c1d03444103c5445030021045a481810148a07068201c201c02c1e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 225679568 1250 225678318 225678329
    0x115060503180f0a05010b060f1c090210020a0c05030d0503180102090a0f060201181e02040f0f060e070806031002031504060314060f100902031f060c050f0601030b01 73
    0x1180d03a42c81e0000c400e04a1004107200d40300b0343c0184401041c0c2080045001082240200001d00000013400204070003413040d103208488401c02006840c0ea1a0604203074030813208000503002416000b1074010071104400b10302d4260043c0c200100312410008628001005000294002c0c024444003450103412440301034040c40c0150103014100950103000d40449000360070103001880003680d00c508050064641e806504055401c180ba02c802d80040c910108100750f8020720030078003402d45844145140840a682a6002034903420341d1014041d06008019400e07010400020740d561611008201031240904144100200001880705640d00003612242051a602e00180c1c0c03511224200c028442110444640203400c224000091090b101c4624044035684019101c40790784000b5042d0444200f104c610710b10011001050001c460298041c0d50311900c0382c20010340ba405815200105140c05a2040c40020080c1d00110300304802403003240c0c0020070305402008203506643d9242d00c1440140101d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 225680818 1250 225679568 225679577
    0x70207030803100807081005150d060b01171f0906060512130c030b160c170c030409022b0b060409091109270304030f120507080a020604110102011506 66
    0x1c83c896041074403030100103021481c1100c0000c0d540f889045d44611294900c004810b1a10300001c06061741c20700c81c90109000141a242802c0160343e03100005e004070015281080281280c0e40518000c0814960041108108251050242204c0c01f415404503030468041c4604000c410000650400250f5103c0d00e0000112a0545c1d0f50302151684505120b202610b040070303089d00003003400004e00300e050191403542030840100340724001c1640e5018071600e00030001513510301580f17840c41040020703144950040064901c1e080c1d540c1d200d03a00740d0308801c4100582c00c00d002680903071020b10441c1e0f0200211440b42c14000780d060500056803601031489692107040e26507079080e04010000d21078400000c8014900400340c10004010100b102c2e044895001d04050405001d01c1c008000007134500700c0f41e12800300c48265000344c3d5850102400044c2902c00e00005114180008808402504c001e1616600500716403800782014180c22580c52071540c10b6900d02113200281c03405209000b800d94149041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 225682068 1250 225680818 225680821
    0x5010e0f012901052805070309120507030201081f030c0e06100912020d020d0c080105060d02091f0b18090a050402030d0e060d0207050a02132d020405060403030201020d0e0105070207030803 83
    0x104100030300c01c85503d0f5620700e0b21085e2440c00c203030803030080c0490a0003942c030401c481c2d807601c285401030b0300100e802418a60240f141040158032820105a12450781030f00349445402d1121510600051a04200c81150408005100449401401d1a840142100d0035440780c03001d44006421101c0381e002ea4001d031019a440d4109646655145503881c1c1d0f4060000600d0b414a402c0080c1c1403004d5024241d181c1d400e003004103119140100002d103400da0014825505525110815480050166043c150a0030200c80008940e14040081d15601c00e040b6118181520220204040c0000080c814003855141c1400d000250701c0024244107481c00718103140f121780400310f00040050041905801c140383c0005554020002c0c08a2021482e6100f500c102c0340ca1901c40c403401d030075543e90100c6c0300309881420310f00c0240c01001c018070003807552452500614190321a004100f059205400540150307400040d40002c15003284504e21400090400800140c10000d000a40721061407002030481ca10200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 225683318 1250 225682068 225682087
    0x2a171e120703140406090c0b0313050705031b040b030106050907050703020d0216170c1c0c0e0705220f150206070e0303190905030106080d021b010c0311010905010e0f01290105 77
    0x60444001c0c05010048c15101d291021107000d08940c60201110386004425001805050005541010301032011114210b00d54550500000308150305d40b2a2b450742d01c036500042c0d10348824207038501a184a50b1031035903907516810064544001c2c000040f0455000c0c00484001c0c0844003624025200f103201904040d01c00001524506003500c6d550720350140d80b480700040065241310b100030310103212f030320343d2088181e450901200504003124004003140081140c9841c1c41c070201c00e034a11a1503400340d8255055200c611582220080d600199048010582d054084940420000d903201e4114908132a1011084011a880e80504001c0d8540d0310035202a401402d030103010008040e0101030b00811910380c0d1085103595420740407030040054050310f407a000400302244402d07015268180c40d9000969801d0707508440c4071101c00144000d41d5a038512501c0040c07030030b0143c8000031521a004060301d01c2e50110203030840703544d510310344c00c20600b07206404403410128025148a850900b401600c1d4801c0e003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 225684568 1250 225683318 225683333
    0x801050307090c050904061e29090d050f0d030b09042004020403050a080a090b0f0f070809030a120f0203043f122a171e12070314040609 60
    0xd05203103a005040041c04a420605036a6840c120b42807403805081c85135980b441e004003500309c003150340c013421040c8155400c95407101d401002582400780c06400102c50545901d070500c64810040703101500420010030b50317181e150094009801c5c0403184000142060b0307640740c00c41c2031102a07a0351600c40d5840c641c02d0701e036a03950681e00116008030550b01403824500c6d014089a01810045000c60f141090104070b901150b82511600d001c0a821640307040b103102e56400907500140c20480e505001000421442d48040c0400340c40948640400035100c00740e91300c003401882c40014003208550041c80100030b0342c25485102001c0769258900013404940241200c00e0f4208030188418055408115550402110f0101c000e005183d5994911108525003082e02d2803500e02180003680741d10001d040342c04600f2520a6900e86542d09042d0351410320400c0c0c0c03182540c0b008243d5240c20280206000e159020421009940212149810088100c44400404416001410113800c10342d480701d4010801000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 225685818 1250 225684568 225684577
    0x1d04050603190c090e010903050d0b040b0402070515062704050307050105010f080c0118030605060f040509010905101b1103131203020d03050f010b090a030c080102190801050307090c05 81
    0xa181e42d141020f08181400c2c203160304c02c0c0d5002e0751400240b0140c611040c40740c5041c0c268199103039403400d103030506841d010b40642c0b0b5255501955580007805503a54a100416925118001501c4c10380c0350700c001d00084400082800e405000302d40114804100000001c55060000140c0b0307041544843c28410302e1802074000003405c41d031902001151000c0021754142c11540b001c011104c005038104011581c076411151040100501c5100500004626800c400d52008026260b8114580d050340000c081c1c0d6000d84054010b0307555035407003805105042c0300305803400300c2c46a0300703012150100c01c80c00f0310003403821412020440000f6048040d04414422203551001d85e0903400b00e0140c40303000020715884140b80880140c41441c001000c2c0c01d000740641131040c2c0e501c1884905a07868404118038030703401110540e070b1100058a010000a5540304c030f8501408000d400143c0311360305036512740305800c0850220703802d016000004001540c1c001a15000f0380f4549074010030f16051441e03003510035008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 225687068 1250 225685818 225685843
    0x506090a0207081908040c0f08150601030b0d0605090c0402090303090906030a050a03260702060703050a0b060301030501090c1e0501032316030c0908190507050d1109071d04050603 79
    0x300203084c0d2800340d840004c146c0101d024021044a0a03035501d00c10081c40043d1284c030140360419460f100343c40410360085039020b030060602060609400c000514034608030002140c16a589000707104880c0002c0000350359030350085c0c404500d0303c60040d00203030780c900508980710b1213411a2800203180b510709000c0c491609a202d0104d030901c1890f80383c081c2040c001001c03240c0c03a108281c142d42d400048200300042c000d91903034001d030145ea118010101c0240c0b0004014520a07a00c456100105403240c1c0c0055008501510001462200301d01c3e00340a080060360042a07802c04000c50003002c0c0f004282044200c0e1400d00340003c51924a640b024807454806600a01c6080178030100308407841103c40581c10201e00c0d680c00c00c01da201c1884281c4c0c3c0003480e4012141107030701c1400c0e03031046040e004284094450040d01110400d0303036100d0004099038103c6000300e0741da0300c0400080090f42000e10100740c100040d070400c1d03041e801840c3e50031030045218607000c921803920b410229040e40c50a01001081c00d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 225688318 1250 225687068 225687097
    0x51209012003070506060d0f020d02060f0708030f0c09030304140d0807030e0102060603060106020c0d14030f0715050601050904241707140d1428150506090a020708 72
    0xc8400c0041c03a229005103505403814007070040011800d15007028007500c080c2d40000c4580ea0150700c0c7c1c003445880d0101c454100d0b00300000f08805007005182e0350180101c24070407000f4590320711307201c04442e0440a000d000c1039a20031003402042040c0c2d07004070070394080c0e8000704030b0080c00410620001da20a1a0514040d0042d100000c0100525030b0000c00070350125420307001c40342c0740d84500043c9541c40c9424440c10005800c60001380ea05442c0c1000c403410103030300078000000110070b101c06050075544840320720380700c0342c60000b400303010004450342459291840403006c20440c0b80100c0043c090f40329511201c2d200c0e983d905d006050400d465405980d4004070400c86902d0140c96110031840c601e4680044611480356240c0007901041175451802009009880700300089030a64500d00d81c001d0102124a00c5d0086c1ea4a461445000000c10044c0c443e202d00c4101201d15242050708070840b000d484d02444504040400081d51030700c40c41c80e80c0210142000683c1d07101c00d410010890300420241c0141e45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 225689568 1250 225688318 225688367
    0x2250312121104090b010903051209010e030706081914011208071401050105040b060f042c0408030f0a05060f270114040606020d0c02010503070318240905120901 71
    0x2c8066000f40040d0b4810100c2001204106001502c3e16200d9110041c02c681c002c044445c241c080340c101808040c1c00604002480524407800242001c00a4102d140005c6060007080b5003101d0400c40005010098036040064010300d000c3c006002c07005020720031074203c1481004041090f4001110340c000d8215115000040c0c581150314041d110a1281510a40c1802c02c40f094618204044901002040c44404c0c0b03040d10b45914061080c8030204803000c044004120682402241078203248618030440070203549240c52198002015006000d1135034081c54002000001d40f038181240311f04840403560302040001e204840d0940b2444140c0107042111030b040001010600391003000440402100d0900009403100c4007245c0d50405000781783c00085028041d100036501620045400000f185070100e1403104c15030480810055600045a52404400c0020002410701c2c03112003140391036950500003e6220f0315221750f52080004854274200c0005405903031030380141c0c0442d82548400c0c0441210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 225690818 1250 225689568 225689591
    0x10e030a111002010608100c09030503030115030f14070804080d0e030301140f0607110301020403060203040f0c05100507030503151f08130309180f02030c0702010225031212 76
    0x8580001c1c104500404072034803414100760040c00303020150340950009100454045121802a200081e50700061141849011010600600040d4041d14030a0311250500f0000c140c01007c451001069406407890b2820706074400404a94040e00851145880300d031544a40c2415015031280710009000c40b8540780319000d00000c088041d504880c0912203080d0700b05860070500100c003140f02c40d000ea02c2001003085000040031141d1100302500090001402e20b500ca030f450104a07481694162482c1d0030004d01d4108100ba00e40729500540300903541188420310884c5c0250650060010040901c000403000880c090011a250201903000a050b002074000802c141c0002342020320382000051262000600b10b54188402c03401200d034569208815a0f10b01443e545034500e0503035030110f980e42c8078039003103490110341d001070350045140c41d811030340c1d441061001900e40341030b6884a1907242d1031400002001030780440340800f12504407800d03d28035150380e50b040303400c0302d1001c10304a2118a1700e81d80600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 225692068 1250 225690818 225690833
    0x60114030115080105090c030606030a0216030903061a010504170c03060403180b041a0c0a170c07080a0506130309030b09010f0f0902030d030f020708071a06010c1e02010e030a 77
    0x2c500c595803582c4985903211005d01184640c119a0348165400c01c0000c2485418000021940812101030040c01c1100c51481d01d040146107050a07000114100740a01c14494a80718404400c0d0b600c0180718607180441c4001f03006800707644181da604003001c00424044560034420203071042001400c0e5103c0346400d02d0b0140c00603104030300d02d00166220000118403407020300100c800352003010309540c0603403142e64070302c1e18150f200d01b94003516801001e40c802c00103107204452a0340d800041c1840798448080101c064504540f030f41c800384099005200c2c0601051020541d00d41200c80200002c07a50300b124241564408019480240a01c408508101c0100019400410303154070200b801d1100040f469613901c10703520301340006580341d0017046021004038080c0c1c0c068003410100d4000542005240c0d103a00c6440e0304200001e855aaa18034071400c214881d042085170b011000342043e03c1c0b20321040d00c5920130401119501e9886a40e01502d103029a8041c001160403400b00400b00c400346080c500d49441d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 225693318 1250 225692068 225692099
    0xb0304030806060a0215040c08030a11251701020c030c060a050f070f0f0e0a0f03050f0a0b0f1005120a050d090b0f0306040f090f1b1d0601140301 64
    0x30006448580410464030f8110308075024140940d0090010980420b4020440d01011700b086807224802038000681510a00c007034401c03028580c0341c100c910b100702c890090518080303501c50801e10703c8022080c0c03031b05041d4140788070a0b035901604260480c2a41d1150600901c10b05020189030701c40411030300e86081001039a10700c29001d15030300b40b000380c0f14401c0110007100f040d03d8030004128401c0c000c1040921504d0001c03002410707031034141580745504001c501410682d03001b104d061140c0b85d0b418000e004041007600e80703020002c0010304070380615450b0100c03016000b4000c01e0a44500402080240354200c4030b520240000410006583c280d402840c0e580d030a02c2c01c0300703d0b403501070320140302c0e5140c0c09114900d040707400d0030010b689030040806402005500003003c55074029070f6001481e1180c902d40c0302d19994140b00d43c041c40c20445160900c100c0743c17100c3c0d0441c46803502580006202005011079000814108a01c0085054482400684442320f802c40040701101010000081041d180403440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 225694568 1250 225693318 225693323
    0x307030f1401020f0715150b0403140d0f120902033309060a0b0d0503030702031e03011a0f0d05100501030c03020906042d15080916061209020301060b0304 68
    0x161030450450703000d42d0a038001d0303407120320f4501c00500400c07001c6604440212034041d90b040000540760304120003003201c5d0113540c00c22080c0741360106050040013541d055030042c4c1d9499400500407440d4600b002080341c01c80d00212000c000c00b0746144006202242c0120045c3c2c2d0f03009064698004011403c18003440d090001f64414040d692100b4011580813510503000c2d9030100c01900007076540c0d55124000d00610000560410481e02450012440c140302541c01280250701440d40d9008510b070381d844184142aa423800d0303160820040144107100c04004a003882c2c840300f810303110400d2042000a6003e075150881c2000e041c40100b040e40e1510050b1141524000d803410000c840c200b5400714101e000d01000c0d190002e004000511214070541c2c4200801584456203001d1039480c1c01d40b0114100240c1c1c010705411440760480c504c01500441e01e1076005001c903008107090f02c20010034041d180c59034402e0b9014040040d40101180030300c0d41284051580290080c841c15540307510350b45207640100d409 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 225695818 1250 225694568 225694583
    0x406031a01051602041e0908130510020a020118050607050a02040f02130e060303041e050306180a030809102d02070f240c0305180304061202030c0403020307030f 71
    0x61a2941c01001030715600545840901543c500c0c0e03600b0300c4014410100b08110104c075001c0303124030080580c020444c1c1f05103e00040c64895600c181c1e454000b03912900a0741c41640301d80c2c903011980e0741c0042d00c0ca0002c1e8091131701400007806050366030342c2070700d007a000345e50031020010700d4009003c80064803d4100d4030039241000031010b066040e07002ca00540f06580000c1c0b42c404400c0090740303401c004032600b00c28010181e80c40d042d65850702d104482040d2840003142c61103207104019915083c0300c01a800703004200d4403c50001c00d0b0b01842e80b40d020084008040c010124003041201c8020001d4560755174504208019050590105000901c00d4889151480140c2600303015850054026520740b6980701a60850200741c1d60795051110400c0c95460343c080c03080102c9000d1180c040e0081d0030041e10740392400941e0b800c101c0c61070307000d0001800d1f00020b2940100070401c0015880020702c800d40c00341c1040180c0340c3d160210410103e1282d644042e500d4882c0040203c144502100391821441c810b03800c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 225697068 1250 225695818 225695861
    0x1501090801020c03090f040e160905091b1311040b04080613031b0305070602120603061303080106030903120e0105090f0d0509040b0d0b0403020706020c01020c03060c0c12040603 78
    0x1600c60070703441100c20464250304180141006800c11014085031140000c00102d0201042107096151903600310fa031901e004a103031420080e401c0980b24154100c0c2c0e482c40a02000503a240c00010008254140107000d03244035143d5941c401d1296100241800c601c2c15110354035995010341076581e82103405260070350f0085a010030003006070320070000b1030540d15440302d0030348505182080d40e00c0e03000c00d42e040e01401410420440056164030080038001c00d0310305a540389003401800e0515040d402408200c0807180c0b11040400b007508903094904407031103440c001c42c150440e407408554850380c495007069a82e040031200d041900d81908064410007104007250b1000079406c070b403141e036480d244003081c0c0441c804001e244030505080c1c00800540d0b00190280c2280c8203650f560107007004040b5002e40040c0c0000d481801116814050b804e0010000d1005189480b0401c0006e074490501400d6058650000220f0b150f14000078044942c3c1001e0342a991900c44d07603544030240240c0b03d6a041e548442c0d45a42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 225698318 1250 225697068 225697079
    0xc1b07050306070c03050d0510150f0c06050a09060f24031709040603081605071d180f0a060b0324060f0303040f090b0a090605060f070206070b150109 66
    0x46880032190020014a1582c6030508161802081140709500b003010401400c005001c039800f601d070003942180e0800d500c2c1803404c50800000210000301e4020010502400007000e40c0c03210024898070f4004000240c9078841141c620002d0642e154020034040c102101055000c0e400e60080c041c187d8580418219244803690042d1710b1066030000400e420080e2840d442d21260800250003240707009040018010740302d4032500c05c0394101c2c4105100820701124042d04218080c0b00c4d0300014035011800c1c4002c18403005030030a40240007009803040c80d04002c09440030940400c21011502d050b44296684101c180c00c18034060314030503c4060081c40f46582c0341040e09060400300614084c0000006c1990b1503200821010000126184e0703071500c402d11020a5035044600351030000c1c00301c104c0c000b5603809003009101d040754859022000242c501141002542c80e420112500e0303130f07032124155648480520004034240a44900070741514000410041c881039401b0119a140342c003603c5200100f80d450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 225699568 1250 225698318 225698323
    0x4050702030301030213050a06030c0e040302010c09080322031a01030b010602150403030b0d0602030a0f0f0e030304150906050106050301091404030f0f030e010e25030209150f090c1b 80
    0xe2000941141c01139250428000e007d074003054018228201c0490269541e85171200c000038180c0200c0340100c02700044c4004c042e02482240f4454203d400c06064580c90659a541c81c0d000c2c202428181051a01c048244070030440c0544014661000205510104141003d6078040c400d000466070988103000200e0510b0002600030403843c003003c0300e101180c1e1295801c4001e01400102541c111440082c081c002503d00d001030f40c410360748600006019020520401c0640c0d1160f1280300e100c629201d0f80385680f10010040703030361198101ea80800c6003001400e42c0c0e030061000d010060a450315003400404c030203500038025070480c3c950344024850b46401a92051a0740c0050300c0003808500081d11045455010750342490019905040000e03c40c01400d00441c2074a602c8050121240c2000301201d03c082410070504da007001c44081114541c80c116030208841980c0507244070100f00003460301042d0b580d41e0002c03128540201400258a81c202541d4105440d0840803816018500c40d00d2070300c5c14030600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 225700818 1250 225699568 225699571
    0x110102030606041412060a2306101110090c0501081f090c0e1206071701060909021602181503010c090509040503071e0302011127010219060209040507020303 69
    0x418407407a107840c0c0708113a940c2d44182004c10b03410210541118088000500440d44280d40041d80400e0300307000c4502e8401000001000c5204044040c4240b1444d07403120740c6815151380721030415615a444036611280740400042c41c0c580d040c2d003440c82180c2044249801170341264000c1e01c0310902d60b00c50620780c2c164580d40350306403540181c1200741040601c03120b800800d0096407900780500c0700329000c4045104c80d103560340340c111242d01c1541402007040c0e001151204811100c0c13140313216541449070080149402d803192000035500494540c83d1840e01200b09892503900a0070131107102c88214986d0171004040340c00d000d0006000d408152541018080c50301250301e9591920840c608200c100901070101500541b094401404900e00140080080c0c007a400c40507075406040c00c01c5850000d09480c28244842600300301404131452001070200e00350301ca10503c0c2ca420201c81c0040e00101d18200b030601e03e4900e854414154941408000e40c01000194030a442c144850b0780d0b92081680d03030340300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 225702068 1250 225700818 225700831
    0x1104062d02031903060b0d02040302030c010c051e120a0f0e040b03120f0403080f0d0c05091c03030905030f0706180c06210c08060103140103020a090c090f060f11010203 74
    0x3c22200d0304030382840361002d02d111074908000a4050701e80442c6a110342040c102244c42c1940000d00b441541b8042143c804081c0e42440d2000c0030002681d14107803515644206956002d60302944120300e040c00340188500c104680040325110000900000d040d04111200f040100720f2a043c11780440c2003d014007406050f0280c000c000a9003045d1790401e45601c0514101c124280c10300010000854180082c110070060100082c0c03181c8840d50f40b0411690b0804008084c00300030031402d1030344c0d2140300300b14a80a03030642d41e4400070041800c0030b40191103a0f4030010414000020700c60a07442d4581c01401c952409100100081a420000740d02c207000419005402d0a040e4507040142c248283d1080c445918200d00903030301403800a680c4e609440602a03d040414a034204010065038140b00326564540d403d00228513551464010455800c490300880c00196121000322039000d00070050320006240040c11149030782c0c0e031103038024a8003541c81c44e07000001c0d90180c2e00c2060944140284e90082c20b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 225703318 1250 225702068 225702073
    0x406180e0c090105130902070302150402030a02130b0d1b050a140613090203010305010b0f030604020a1a0c0f0c090c0307020c010e0109080a060509070f03030e0d061104062d02 77
    0x122460844022908100b1560703040002c100820303064401c038200018014280c1c40740140e1281c01c10314020b42804021145040310032024001c201c05650b00040c4200096016540c0d8901c044007100450f002e400d4400d880340e000a10b800c0200c041000030705038540b80600f040544004140c17940100280264036100b0340c338085c0c00c0d02e401c41d42c481c40c0284c02000780079009401000403d585803c050260f8100342d2007507800703035500c0007991040e0410250b4108540400c5014002e80d1406a0016085007018010407001030907a10701c00d44100b200f80110b40d014070800c01100d4111401445142e4ac070012101d005000e4034140000c202801c5100080d03070702400290700504016044032004440318150814194100601e82e280042e021405014071442e082c0035460205642c50241001c0d441e11415901c030519012a0b03c1003000803039030168264080300340449404129850600308500038110740340441a440e03900080020381d850b001015640121820410720811205c0c1040348050078400364291030140c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 225704568 1250 225703318 225703321
    0x5040b0403140f041e08060414100b03100903210f0f02070b0705030a06091103061009060c030503090c03030a050c0c0d02010801060f030f05091b0402180d03090315020406180e 77
    0x1210b42003505c10782c4001c1d54002c0e16038641d60302e0740d0f5450207005407030940d01c01412007648400c0c85c00c10700c414444461621014007002c00440003095070b4103175a000021080780d8980440040510500c030f8130020b03070f100085100784080080d00300c2d001040622548c1ca00b06141010031441410a4020f80b4506a00a0714100700d179038179000c00741e8240d071005066a851954500020441c260b1078841c451644209440f1241c90b85000000d000e0701010600341d880600c500310b141080890343c4614030f851036a07071524215450781c0301c8248030380c5040c9200341899410701001c9000105c40d6072002c0508010305403002100c6101c0c1040c414003401000c00d400207400114107100600c845c0b03002c0c607a1101183e41524000815088820302c440842d941591100c605030050525400f20021401081f00105000c0350b08500d800e483e11015200c040a141c0101d00428844503450b051501400000001710b4110f80041000b0800100143c001d512a020382c4022071462010148264921044001525003040852045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 225705818 1250 225704568 225704579
    0x40206070212010e07030f020f0d0b0615041d06151c0504050a0c0e01080f011b111203010b04030b090c0306041b080304180506030a050a02010e06070605040b0403140f04 74
    0x614509200d440301542d04c03000300d44407502e010011032006600401d5a040541303128410072a0381c900072a0036520800302481c100c008126203022140e008502211001c80a1210103c054098083c5031301100010810382c4240b01c1c144509190f00340315040450b051194511802c0c1c0d421264040e0b681d1040c00c51080c0314140741018425404140c025002c0d004482c2d580e10559240b07080100c6903088100d20a14070001046181d17000c002c48100c00c88514000e02440000714010504101d220603900100105c0481a8600c1c0c4024040030142110704010190350b5a1206140d581c0341d4818802201c1200b071480c0010740c81000411040440000140a0910b0f51943e480744516600852801210015812000102120f08000800090007118013030001010341600303990446000810f0385000350860900c00002800116054600300d5090030b0450348210300001160160241403c020040c41c944400e2005100c0a0140c040c8654805c0c2c0e02c000d104a00000440c0060007003800a45034540c080c00305029 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 225707068 1250 225705818 225705829
    0xa08030f0a020f130306051e0f07093609080702010305061f020105150307030b01150201110f1206191205030f070308090714180907032301140402060702 67
    0x20064181400075091a80120f003200c490b510040021640025080003082008594001d4a612040c04030080c880180041c405e4940004001c7c4004110305a101c00106558001d20b5050b01600b4071a40526030100901c0c0c0300d0500440145203480c04489849000e04140024000c0800d000d9001e04035070b0030324030690300540160502900e025844803103038131511020034440c2c070303800608001c540c00410242003042030076980039408044030b8002e400c0550144007103444005014112000e0448036600d40f030712010102c0c01440300c05080780c40500b00113440e510203030741200942940c0d0b81150900d40f1588030102001804080c480c9010400c40e034030310701007003c242c01650a41d8002e008500707480c80c00d4200083c8409550112004801242242050241000c4100088405018851440d8444c55414070019001b1480b00b00c01d07008450240c03000411000c070600220004692100c048400c3c0e1102c0e07003210540b098043c1001050350b1034000541c4c002c2d41820342086c00f03640c000d80103c2c40c0c0030068080c4031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 225708318 1250 225707068 225707071
    0x40e0901060806070e01090909020a05060a030f11090102060709080d031104030b070c140c0f09041a0c03180102090a060f051b01060f1403100c0c020901090209120a08030f 75
    0x9805540c0c1d0300001420440900c42c60303220354407940e184092080400d0024184100c903812900703202d40350003031520058032025440001e8420880300c83ea25810459411000780069034034461065040a010003615043c140181c00c01d81005d8003500c1c22950742c5082260761113410b204e8030210741e006031408000035019510501d000d00204851515050312500c0354118a5000d4900340000741c4500d82510502000c0154880090240d1000d0640b0441d480001591600c4100c2124072844400c0301080401441104dc001c085140403a20031042c5045800900c1c107410481e450345080c5150514240020b9040c0302b11034280b0310090800c6481410700c1001c517044038031101d4a034103020f000c004900c0900040300c140700c4031829140000ca280c034148086909100e00c0b9602460206000300c02c0d035141642c022400c0304403410301c02c900060090007144216618101c0e0000a504500c3e903000108440923680c008101012042e143c0349015090b19440b150b032440c104101034026030041c40841c101100d060040c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 225709568 1250 225708318 225708331
    0x5030d2912010603170306011e0206010e22031706102f0a060b030709020421080f0a0e03010e030304051b060403080c01052a18040f18051c05040e 64
    0xc010ba2280e80340f07050024000f80710705c00100c010007003081381c1da07205550b01210007220000d02180e4107500742c00795a805040c06a41c0c2c0e484200000588036800407280c01d039181d94281d410b403007402518240a072400c440c85003e403000d1100c180019040e818a20381d02281c0e018035a031040b54042c200c002244450310350354040d500303800103890809100041007260b108003d00036200055294100c004043c1b5002d50f6a01002c0c086005200421984807601800310640d49901050015619036182180f001d2040b054a03d01e21403021400c2203119078060a0884a00b20a8000f00f040030080d10720369503640821140180300f50300c0912b00c0015040d64004400e5004c1018241c141000c0d2a5a40c4840d2078000840c1180f01d40c2d0b480c001c11681e519503500c0d6400c41c0021000c07102d503540841c9140c80c9903201d09008038001102420842510b61038643c040030310b013148401708110900c82d154200441d000058030546807442903c040c0401140d0045080d210711242d51645072030685410254001c212009011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 225710818 1250 225709568 225709571
    0xf060e130e150108060a050606190c29090715050703111f150501020316080904020c031c0c050304020906012706020706110604081b03040305030d291201 67
    0x1001c4040c0c1e010400c2d004030340350700e1a032549507604090440745010001494002501d00b064240710690310384004485c1010b1030003103082507010304039000f521954088031b0000c1c90076074144200520760f00c1001c06490680000d840400361078485c1c22100d903a4421500850340040380c00004801614040c3c4e0091000030310a04102e148200d944524a040c050f0295082c3c03900181903144243c410410b2203a22008451113000c84d2289080000013540c81c0108542207520440035503040c0240130402c4140c601c0e00000410a5542d500c0d1a841d1a032690030001c1007c10340d0f13003614a050303401d5400d8040c895541d0141e41d0350904540d1141c081000c0708074050245030521821040807002e104d00c11035000041010000744401c41407400100070301d040c803568001c9003000703a41100c2c51415040400d00541007074112a070292150081e6020783c81c000091036400b1458400090000100b0030701002400c4500c0d0340c100100311000f8a6112038803030b01d414815200301e070b61074000035000d2850039001d11142903118200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 225712068 1250 225710818 225710831
    0x40312032003090a0309061e110118050312010e010e0f0c07020303030403020d20030d020309250311010c0503030601030f020903012c0d020316110d1b0f060e13 70
    0xd820344694410303641c400240d040444c82d01c2c185504070030500d009040b40e1a1100100a41003166801022800b402c10100a03042001091800c42504100b086254007128051441098541183e899000307083c050032000b1f00d40700002d450604491894100c6201051210459845240c80d07143c24400605107082070b01d00380310b0400583c030304001440c49030b4406e4008099a010030500504403a040c60003200c04041201401d00c030317128011040d6244080d02c00e074056202d49485600ca8148407102c07174028190344120b8481000464281d454800312409900149059501203004403414150484054402d034010004503586d540310341d01180790307441c8950740181445a07180000c1e0a440070704c0c58072010680c0103180d980351004411414840d51300c0290080011611166010b5220701400748808440040345103240140401c0024000c0e183c4c000030150000c682d036030315007000420a5044541c61070f07a50720001090300803202ca020b0b8240c83c0c550f12010b95101d1a0340401c580c038007001130500f426540b40d06 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 225713318 1250 225712068 225712121
    0xf061803120103030512060603010b12130503031006030501080106151211161403032e0308030a050a0e010605010203030c070303020702031b01120603020919020c120a03060602010204031203 83
    0x2807024040e500c02e541e91035446042c01c00c581e2141c40060400c41c40303244100300411a07003d4000c00c842800800e035440d015a542d0f1000b008603142d901440203003441c00b00004028511410080ca5425200c290310200410798840c003240e4225201d80c01004010501c00b0030200c00315000f01d200001c01510b200004c20804110748d00107034690042c1020940101059888800b00941c1c0948010704001d40d400a505500e4041d0851007400040c1029020381d040f0901d40e02c002942c5000300c000a0340d0042e105903900d0401910600003803500300c60041c4c030709103480000000d4180601a14003180da05034021400c6403504000321000d0361282c4021410b26170300f0803480300144c40134015400704415181c0880d0700704d11000300241000d1f006940c59540e02d17241c480180b005070390322040c0c25040003440d410b00c2040c40418080354020301c03d68051605511843d603060790b102c40d0380780003051801341d070346e070f0501c04541e44003c140c2c282d02403400010001c1c040b505030880203d103c0c1c3c2c042056121450204a040702c03802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 225714568 1250 225713318 225713347
    0x40902030c16060b040e06040f060b0d050f06010e090303040b040b06010e04110403021005121303170a0504050c01030905070b03060d0b0103050313050a0501021e070f0803040f06020f061803 83
    0x107072080f51000c3c0ca801002d1002d02e000d200c1c00107032940c1e04002d00424640359440001e18880804001d01199595100100b261550001c20303003000d9100003294241040410740c3e9940c1d040c2407044910070f000703410005140c40004025240283e5100310317010480c1d19545d0301c071151010014542410450403c8160b0016a146c5c00780d0f009032440040307002e54450035070040c03090451a0400c0341051107000c2084402c1f440f0280c0100c2d42c01a1003203510300e05400d0a14048581e02c181c0720159807110240380038449000740b15805140901c1c850412074101112220056066552000000d02150004081040081e6200c001940e1001c1c0090441010483d2503881c0c200c440020381099840e64004154190444140b56804000d40411603080701818904030000b59140306036807204801c42e02c2d08040e40000c1c0d100704440c80250440348459407000e901c41e40d10aa49810038070400005200d0450b00250290000c10b010018000c01000b1f8189030392480c0c00740c41c5200d41300020f41c0080c0b104000300f40348550032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 225715818 1250 225714568 225714607
    0x10c11030a06090b0601020703031b02040f02030a020d0605010807020d0c210504061b0f081804051302090a05090a12090b030a0501170d1b0804030602071b1406040902030c 75
    0x1804006145945800d012184104c02455030781954048030301440802e0b00421840914514441444850842c61000c10080c00480003201c140c2d60012060112004c01e94014224030394042d5010003045030380e00d0045a014a042d00d200015030060000003000134421101c885455010303890ba00d00411000041005080c1610032150000c0c9000c1028005a948001d504400001500c074406078001580c071041601203281000506840c40010b00c2c0000c90303000c0880038000c0038006d008000c1c626190107a0b4100e103050b802d04034411301001d400288800ca0600c2200d009144400085c04541078554403500e51103800014482031000105002444c0d07e400e00003035208040801c8081241d52409020b043c0301041c81c600c00b24142c020b24162240c9683c081e00c60b6441d8501846e004801540c1414083c2c2280b08070342000d0403d60002a440d0140980580114110700b0700003001010030ba55443d4038500002c0c0b402c9159400b0398108004c0190941c1500510341206940030b01d203290200b5031600c0c070f400049 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 225717068 1250 225715818 225715823
    0x61e051c06030c0e040201120b0f04140603072103080705070503181503040512130b040806040c080f07090902040605041a0103060b09010e06130b040608040b070e010e010c11030a 78
    0x864000038400c02080c0c4039240000e204102c0045034a0401ba40080c22200000c9134a1541e82c0c2d0702d42c448005d80c1d5840c10301003140c29026004105452092480e1076010030110f03003883c000c0c424040006007459080707100004002003000500c10180c01a5011200460041d10b0342d41048002e006441c0881c4040c8000c05400d0f0341d101220800301c40c0c0605100c066960b9850780ca42800040c000c110216030089450480d8101d00040b1039918000c001c0d8801003002141c100b2010031030049004140c0c02000901d03035008500900a0f0307034150f61344205081e6110707504c0c101144103421004082020500179041a03031014801400032541c240c0300c4020508031800c041c08070902a008910300d030710f10358061207440c003d0030161000c1e610702400300001803d136007202036405004d960006034107003201c98810151380c0504880c9940540d9075542d160000c00b1803034103507130990fa104800c5001c96142c07030059040c4280d1030010b0b15000401d4085000545444d08521810344041c1c0207007030b00070703c5683c060018108052 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 225718318 1250 225717068 225717071
    0x20040b0c0705010509060d0b0102031c1d0c100c02011e050904290f0301060f0b0310230904150608011424090907051f030f06061e051c 59
    0x3503030200d1924020455010505029040158002c40e483e03d01c00c5030a2920802000304005400c000100e02d103105003251060110011840318202d2440750704194a0314103003244406281424804445d1130b10545602c6943c0300d603046005e20700250203401c01c4407402d40141054201d40d0004030144880503005500100000d00001e114651445d0901c44c1488801152500c010f000b0038001d800e103540e0030195025489403001d60b1020030595000d402c01c401400c2404001d001c501d694465800e2181c01c141c0700c2d281200604800882e40c11290400341051501405103d130303540300e0503000e100c001000a4002c0d13130880c2da101d02085101c001d6000d500c0040c8041000050307a0341ea540c10840000c500502061150708107400000c42c125a500710007034450b44115a00d80040e20750030a0b2a1800c24240e01954022104507440381640801e004156001c0105403000c2c0700c245004140c110071038840d0b0060802184981620200600025540180600003801c20624000a6500701501071901d140c110700401e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 225719424 1106 225718318 225718327
    0x6060103020c19110111030c1207050a060606021015050f10050d090507030204050a0e07031704030b04140c03060712020a1e03140c0903070920040b 65
    0xc80601c3e140c000441d000c0c500240803c1d041038469022503031101940d00c4454000c400c480080c11440090084d280043c0200c45494220403c155054455540010009a03561003001c000d0315068000f0001c0c0220230403041d007611500301c07000404000c0c001041086840d00c061a0240150459a400c4000d0000c07004540c1d0740902c0b62645ca24509000594050020104003001580e0003035a051141b0785d44c20098105072001c40c00380b1940395108010030400b141c0e00000b110a801205400940340c1980c03500d0700c41d040c110684082d5056240d003074041410403000c1081c0200140c09501230500d900d400d01020f81040640e10122400c0e6400284c5103120a01c80c0b50034150341d2011040158041d0007844006008285040c6880e00d202c503960081052181c500042d10244800140244016818101d03801e014010805181030031081040098024100b03000103030015021001206855 = true := by decide +kernel

theorem cover : BRFrame.Cov 225539568 225719424 := by
  have h0 := BRFrame.cov_init 225539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 225539568 ≤ n) (h2 : n < 225719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
