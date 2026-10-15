-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:01.31939+00:00
-- url     : https://prove2.me/submissions/6db40b5e-d894-4609-b112-f4e81f1ff3a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 909892086 ≤ n < 910071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 909893336 1250 909892086 909892099
    0x20a0e060d150902010806190e100323011a0f040b0d060f0c0908030711060304060b09071d04050603060103020d02061b4b03072901080307050303070e 66
    0x210040b412101012079480c200e603000264803c0d039400010410000105014020b815561034201d0307680e0400e1200080301d004800441e0380b0744841c00c40d50843c01d800d600252116200b5010100091080e04a1140702080003000b000000c0d1195030074404409001ca01350f5100d44c03251042615402c29420852407024010a000c0b0514202d03942c09080350701000b40700d160156511040e8070309c20741100040d00580742c82d4005505100039035861701101d00a503d0f425000320b9003c0081010000c46030401907804100a010800c980703406417005161801d000c948082d0403d4000c82c1660a0800e44143d03402a1000303000b5029603030071902403000380200f40800301e1308a4001c00060703201007003000319544541c980401a10800b009000540c0303203000c55050102d09140d540d41180041c2e44040c40498400b03154440b55140403030304d44c0b80f0908500800c20060400241c00c5d850191002c462507014142003902c01c0d60989071390300d039002d055132809686401010303030f401000440c45090041485502003800240710 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 909894586 1250 909893336 909893359
    0x3030c0309020405040c0303030c020307050712020f212a040207080c0a0809011202090d0f031110022a0d030902031e030a02060a0e0c0409050313082107020a0e06 71
    0x410f0460f00c0c101e4080d661400300000500426a1501405081d0720041c4000e50420701c6035142c80342c071880b00717102d0340fa20341030f03001c1d02002103445610050340741da28001d2217122a001c052556800002c04810114001c1c080e00d030800441040c1c104048051b42c203028451551120310307000384070003580720102c1a903465406211040403982c081001c070044070700c81d05505484055510015200380f404800b0f1014450044c06441701613100c03050185001c81d0403910805081d11242400d54052142d0304448401c0d011b026224050b0410700c0c0c00506050400c3e4070348440105812504116010345a00703001e030036400480c1001b0005121340c1110580500060a070340c0f082002d00038a0b0a06040000000c1d06a0004290b08080c2e54060007041c0d40280c02c00028855110480d6025071030303a9240e8281032207995100410b1003440b00400c190b1b101d494545540040c070139100d410080e5506020800366100c0701110950303290310010001612201607002e40305848850900307034200120400106902d4119807942131 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 909895836 1250 909894586 909894589
    0x6051b10150806070320030402040902040203090a14030307210608010c030504140706020705011115070918110403030f0302130f081005250c12020607030b0409030c03030c030902 78
    0x7a4058a0040c0080042072900d080511410194000c0c030700024980342c405103850115035144418040c07041013110780c0d943d6440e4800640100707120700700030750028404000c0002c29480007506082c8603000c0d0301c51644c4000001c10741941d900c4202c9a4800050740c01c000030300c0041c0c644440c44000035105801080954554111701e0845010071030000010ba02d035000c4c0b1084c0701059070703011001400349005c3d02e074260804001950f07400341449041c0c10000c1200041d0070181c4188003505603525029500c1c80c05042044e40100314044500968021001540c1c0381c4070444c505105408407040c1d0000294140707459a02c0a07500a454000c0d6542455020080104215070348079000f0007600700703803014130f45107420315099519003501440401005450101480343c43d1260b00c8095038039103101e070040740c1207d0035540222550000da00380108071b075900060f42da108540100e8543d100d0485968100f2101c2111400c1000391018510044e000c00c0034002d224000c6480ba4000070b542039813604010800c1b020650 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 909897086 1250 909895836 909895841
    0x9150308030c0d18020108161205040b0609060910031b030b091011040f03150e030301080d020105100b070f0606050d03020f07050d1e02010c080d0515030706051b10 72
    0x31002c201c1014001a50000312116101d1600400c1540c1c0c1c819a0b4600b0300d42c0084c0138168041e2410f0040199129490b4245110301c0500944040d050b0042c02103080c9450108406181550354600c00c03510703100010a9400c00f1a0711070b119001c060003480300c1da4659210089841103079041d0b0b0010303d0182001001091558103030500485812000303000300203000d004902201d10391003242c5d1043c481004104504080303d07010f0302c181c9400c480000d8040104044607401004040442807480c00048000291034901050f01d4000317000a4000380100e50b14800402c114140320300a91401c013130300313000050210306040400091940706441c00586c050301c1e40000703504182c144900703d006a001c61300034501c2800034082d00c4003c00301a00c1c008010010307656590b0202c100c68400d0001d8031010301e0020300303581c03140b00c1030a10036803c082140d0362035100b04031110180c4030495000c0c103010140409034030107007400a102c1088440030303a40c2d103051801740400f41c4460016522142d80a01c51040c21160600e501e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 909898336 1250 909897086 909897091
    0xf13062a080411150a031505030a030923010518040b120a170405010f050a03180602030f100b0313030e33071509021c06050912070c0915030803 63
    0x903110226035251034541241500c0f884644140507044803c1018405407540050340da013152242004114103a02c80000c46842d030660781301030782c1032080c03590178002d00d608591808159108280c101c1110019002c110a0100203905802c0c00030f001040311098407038140c18a0207018000510119660340040006445007000c2c508040366600710381e59a01c100450145c8243c2d2080d0250b000d641001c3c58100007034a1524111a0359091100c0055004280b9219038044600010381080d03449045899060201c004c0d0002c442c0402d540455a01040704c042c004000d99040340c0701074501c14510795030f42c94807038049513a00e00100e040c0554440c02c01815601d1a01c00000b010b00b05a0419040b070607030340484c06001c2154180107042c2401c00446020a00803406401c2840c0c10600c00f25049c0c0b00c62000c01c950b0106076002001e1405c0100c0705004101241d04140c0c0584203c40031101c1d40310a046829200e4030844070010b1005940b04401c0001403429088404520031404600754126541e442e040b141c3d0307104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 909899586 1250 909898336 909898421
    0xd06020307030b010c050607051c060b09040e1506061c0e01021201060f05090d031713052406040c1e0e030d09030b1807050402070c0306050f1306 64
    0x4420031103080c0d41403240814115003445c0a15081c95a40c41d59501c03100c0251411007003010001d00001d601c80c03210403050703a100710380c00100b00c0036035103c47d14960b94104481c554807450608400320f5504000088400c880c017010200c4483e5038850030204041c680c0400c1c40b001440e0700040e01d05141c52401c0c030904401451110004d0b0391682440c41c003101031107050f0808400d01c8140f00c51080c903240c0c0b00041d00c20b44041a2113982070f81103103041c180c664844205c04d02600d140d422042141030090b0300f207042c000510543c210340107071940c004c40300b04500b01078a984150a960900060b01403501c2c1d0803445402c2c0e49803c0030150362041d5603c80450391003030b001c058081080c1c0107841c0d02d1821304003c0041407502616100540c1402e540d100d0501040141c00c040c51480104840d8103090340a0216030300801d801001107580d00194a4141c00c445010705c0300343e81032460680040c0454689801e618461240c1180c42c1c1d03040034007139880b00014604ca030010b1182045103c50b5207a444020203088015200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 909900836 1250 909899586 909899591
    0x170403021c0509040b04020f070303050a2d05071e140c12031503010603020d29010801060905060604061b06061211030607020109120e131a0319050c040b0f0d06 70
    0x400c03030920045c1c4170410b900b0781c0280e01c108010403020f03000905a6034829403600d07011074a900c5202c0c58201422207404154100810b4800040d030480d0b4241e004150342c42c508600f445160b4a1900644a461001119805005401e500740310454811b0001d2502280e00968080c00c0170b004c482014944034495881804c0e1001c000b06102040c990040301550300c0004074000d200c50750865020230a0240390741401021b40400c03603000070500c6400e40307091212030b04080e0703880c5032507a503084554044c09a51141001640c6030601142c014105002210305840d180c1d01c82c00d400342010301090207440d100400c1034a0262365800301013503190411980d10344c0304c0c0c003840000002130b21070300805092010142c202410741e0b1420b036144000507680030840c28080780d2810200100100343d000f207041001340000081c0c540d443c02c0d450401806040c0300c0c0114141e0254111003401147c06d8a03418140140780000c1c20341d500003840f0000e00e1038550400112401e0203002000c1201c44034021684150101d00116101354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909902086 1250 909900836 909900847
    0xb0307050c0714061c0b1002100c020c030a080a050c12040609052d040209120a0c0b03011d0a09021008010e0606090604030209090102070c060f12050403170403021c05 73
    0x441009040050b0100d1072003d20b0112210002555500c610105881041040440035200c3e000a6000c00d134518009041195580340b00f1a00a44030591004030308001d518008914524610004498007620005030003070151804984400c3d141e9000b07004e00a08100d81005400d60081c42808240d4003004484404c544039401c1440240c50104140c02c45401100e00f0fa400c810946000d582e20001000102100b6000c0c180b0f5101140107482000300e6142c02481c1c603000b42c00b22100000c1c0c0132286600403080000362684a003107100c0740384402e20600c840c0a00c401c0c0d110031041030a59401d070308980d06690000f0300c0e860035800b203080b541200404801203181d400c010046036503001c004070340c04001119080d144c21a0540002d0941c0101d000203806429400f0009000314025411944001e801042c1424404d9031030764003d02c55000c400b00303100003540c030741590b09404010f80903142c000e592584417040c0c86208480000440070300140b040c1c08602c503d18034070315039845000d40368020300368943d2130b66a101d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 909903336 1250 909902086 909902107
    0x60309012a022406191a031f0503061603061520010519020d0f0204080706030c0305060f0d0203100f02040611070b03040b10031203051f14010507020a0b030705 70
    0x2d492260507151045040044407011800f1103074581c1300c142181c581a0600d10b0400040740540b041d041402c00030074901d200c044000c0040051880348800c80000721440943c0250000f41d40d02500c01e454144c1e004a000c900c24900c010380c1c0803a41010303444c0c00504540d44020314071050b01c5806108020500702c130540421301024001c0b41d401113109074001d000d40d003400e10903160801800761060400503400f1403201c20441131600700d01c1d8001c840a0095407190744803000d180e1078015034450b52000c43c0c0b4020100701c1e103d0090085504ca404c0081910903112000018040f0f0051b40d440203d038580900f22404000d91201e1040c06c3c0c009420720001610f441c1821b5000c0e01c0f0382d6107216031110650140004000c0c41080d4000c80ba40310b0791102d42110140c0b1000d40160682000d034000500310308441c85080c4401c0d0345548003621580401071556200d20040900000b541124001d80c04e4619800405031384e154042d80080421038070182281d60000d03580c0541080030b4000742c8136080010070009504010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 909904586 1250 909903336 909903343
    0x30a0f03020f15070324060f02151b07061d070603061a1e0708070305030f060910091a030f0604050d11030d111902070608010b090d02060309012a02 65
    0xa4242e28001042c0f00d039000390a0782d038000c030004c0c8158205502c4260340300d03810300200348440007200061034402540b900c420b0302900c505084901d40703006204102101303200003000c0003524010602e2000d171005052400701d00900c2c070f43c00002c05454403074076208aa864148020803560201c12000083c110301d1b4240782c0020141d0340990300003518045580c21090740b51103800111030100d4007040509034007115080fa25851130003260000340c940300012400209064201000b14412004060b400c1d5440c1c2e1414100190f00c0c0f800e85805c0031010560750103004210b420790040d0156061020f10320303011400000028504406141c0c004200d030400018401003000400061071f000100e41012811407011000644d9240500303814454082d0711002d620b80c0f5170f800d0b10102c0e9402094042418884044014065076079101403159400242d040c41c0001404201082600e0b00b1400051015100b1aa00c1d001c02045410241508205550b5801d00345141c0c0b200e4080c454404d00c42100361204600002c801904 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 909905836 1250 909904586 909904603
    0x15020613030e180a1d0f030d09140601121112030a03050c160f1a07050d200d0b01020d030c05071b080f0706021b010c12120231030b0414010209030a0f0302 68
    0x7a1a802071b0501e1110780b00c0841501c02c0014119000196140c05040000742000484125102030060800200d0146900800054814081d002c0400004156414000c82c000f440c011491aa04144010300f0700501c250045a04915001d001505001064002485c2c141901c07408131010024146c803d0304010041450344480c2d01e544413800303010303e80382c0c03000303001032198240e2440b0180d44e50880784603035140744500d4131500b0140b41c20316840d040080380540082802103c4640580b2a18210341c912502c00d00030b11a40303234081e544d25400c005d80384e603c2c08807040d2080e0004407402242407000ca181041040340f030074010391071801032a0052070804040c2c10720403405050300000740d06450304081130f40c1004070410007c1d84040c0c3c594982c40a4001200c00c0d040c1040800030060000a403a140040c60148003003140a40582036062011000b0b00c81000006500c4000c0040035410009404145c0f24140381840021040000d40792140440000c0d0815015201c111880d16880300780c0c000f0f01d0782c1040900d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 909907086 1250 909905836 909905891
    0xc090509132a030614180c01020319050c0d030b0a090203010e0c07210e0f0109030b0a05130c090507030e030a0801091104091515020613030e180a 64
    0x18100441c40d110740e10046041a01407081008a00c0000300c1c420003103040000850f0814810050a00707034224190311001d00f600d1548903c00c140c1242c030f020030404601c600c20380a058000318640840182c10034007101c400b00e8090305000b828808100031031801d10010307042041039a00014005c0545040140414a03038200841440c0b040c00148810007a000c44507030041e01180c0c0698031015075291940c04840380c05920803994501140d9024025000902c040d02e4010480d40706503601c2249004483c1100c60b41300140041030390f040410a80c803682e074403044c0c200d113255800006000480d02d030740408617107a074420b940c500d540c0c904022000364944503070340d1881c00f001e002c1c41c036016451400030041c04042c008c10308201d9072040300c0c0031100c0d80d010880c0c0060441580603c1001884880c02212449601c02c0c0140c9002c1c400c81c54400a20124400d03200b0003110003000c08042c15034808503280344145044541048004041030144007035000709500c5581c91200114445248054003905043c0202c020b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 909908336 1250 909907086 909907111
    0x90c0801050711061522022b090c030b0606090306010e060301050a061409060a23100e0904031206030602030f041208070903080c01020403140f01140105090a0e010b040c090509 77
    0x2c94041e17440c07031428014117011074401c29103c881441d0807041680110440c4e951a1000610f01d076208000000c070038940407608a03022001c240304640350242c0fa03103035078018440e100204041c40020503880301c90f074102e00081c010b00e0500b00741704086807501c14281c01c041224200076040082c0b501d0240242d5510080c58841404131034640210026524019843d0602c190f00500c00180607480b0011214020456030032f101d403c2d6010080304006038441e035120b280c021941405510001c81c0111030140d8080e8001d010158550380f1074a0031500c2d649241070031108070b43c4502000000c501d0900145006a01c0a07041e540103003018a0040070200307445800505003c51001080106a0401084022a17070800d000030b0742e5000d0704000c0ba0092245401c000c0040764500000340c80000006040d162580a040081015071101495a22003500900c9860351101100000524040c59038110003205111800041081040d5400080c162102000500c00041964004001c1c61034a040c020303401c271200c003a1a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 909909586 1250 909908336 909908341
    0x60f05091507050f0a1d13020d05010506070c050d11060a030b030f06070909020711062a0a081b1606080a06090e0a06021e0301061d060c1e01090c080105071106 70
    0x80d55503070300803500307900b0510421040c070403003104420411001e8000e00600312a801502c441c074510081d002740c5502c0031002d20b4107002184a007070400880f40003d8003d03020100c0146480100941925103070412641c0d10724105000d02c140d2180e401400d8004002d0710040703031649180c0241443d100e03003811405030580c82802030010700754001c0d002d107040e11841c0c10050382d244d038603007402c04036414560510382d0840000501240844280500454089000895081c0320018141c0055545054890203030400c101000002c002c108640d00c010781540d00c08040c0c82e40c2c51200e032042880e480c02ea03802400402c3c40076040106d0b04103940b290703402800c564202000030800100c041741da01d00622600500d0709500240c00301c19103205011181207050098a0780340e5968503140d008290300310f5810940145003203140c05555034a015410b6030255201140105a88202080e5841d18203d1744003110216550710501140032036420707002e030400340864030300104032800c2c0b081d00140801c001031003c25180c3c01510030f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 909910836 1250 909909586 909909607
    0x60c1701120b0c0a17060f0d050114130317061807110f1912170115090504020901051c020f0708121b0316120501030f060e030a0e0607060f0509150705 66
    0x20031856000d415031060780346e85140200b00d80259048256078040c2c078142d406000c00005410403200003019800404031504e55400440020000550040c04a10700300b10501d10303101000c0c0481d60120008004003442c0c0910410788143c3e032403d503442030000d0500c440030ba1900008002e43c0707410504c030f28000c000199145281d4110100c0200700108241d10041d040e011543c461880c0c1c0c020f0140c08007038406256034039100880140035000a103400b08083c194001b50f40c0c82d2520030398500c4001a1140c1d882c00b5032800302003c03210004101d189900340c0c24480802d456480ba0041c087c168468520903581c0e02143c10600003410f00100950880c44c0d240540b1940a40f20300150380e00100c4002440304c0c0c1815040c0b05071f400315850003958890501d00310000041c008150083e116407401010200035088410700346a03264490200c105001c0740b49a50b420f12a810108018a0340700e01890300040c0380100f4040d5a0141c4000b0340d900c075810350100f2141d10281c40e080000d103800400508219260500b40740 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 909912086 1250 909910836 909910847
    0x30604270b090a0203030a180816140409140106091d0a0b09070905040f03030e06160c29040c06030c08040206090d05062509050d060c1701120b0c0a 65
    0xd00401504005001c6010300104000180d074460303004054903100e4102200c002c00c000c0c001d40307594003402c1d1200e4000503854004510307140504a01100003a400b802d00c0fa5800002e028907000c00c3d000b40d81c0b000340c807000c5031b01d41c41851200004007002007210341c6045146000d0320401d03020418403000d80c00d583c070811000003400007070865004002134043da0360b618a50b030034050a0f90003a01d6003400c0100300070802c000c502003009094880d880810400d130141c80400c0da241c2e412202d12001c403500080c0b01201a0095102c1398525200323860610101a80120680c41c402d2000c4807200c1c0c4d000140140010040720316088406040203180030440192101c100800c083c00c0504007070b0140a0009004074942c80b43c8071003c032507940010464071541404048040d040440d00411f2501d0400c03c40c010764030300e01c6041104101c2e031000b444040415840d855060040110000d4036051052200030800000a54001d00d4028240084070750500c28a0781411880c041000301000d5440e0010842c0494540d00314 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 909913336 1250 909912086 909912161
    0x415140714190f09080303100e090d0c021909020c0d091a03040204090204110304050a02040c030605130c02030c07060f091406030414030d0f020c010c02060603030a03020a0203091302030604 83
    0x510344440d449441d0482991021099000400c0c06d02000007000856069a403c06049656000a60f011656a107070415181c24a855202c03002498002d41c07a409840c21900d80084100f02c1e42036000419030b10490201280e20056000d5400c2d00600410b02e482038000c5282e40007171840041c4090149410314400c0900e00c8010304c0284200c0d5505004400e5448661000c5113501c28040b49a90b60305203801c1c0655903c5c08540124420341c10300b10038040c4184280104012a040944008240324100750a50f01030b00305124500111700c4244500c4158805c02c20600000300341c0c0c2c0c2c545105004407080c00600503440d58002c4850416074480c4118951580c20440b03a00076080380030704804980103c51581180729460055606904065140030703d01040c0e402071155100b48802044030350507006003a602e0b00000c0350403d40c0758109008041190f400390f0020102c480b0644150380c070f42016680041c40050003a5514031541b5030200401010703041c035200d2005899909900c0d031a404071390005020311001403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 909914586 1250 909913336 909913387
    0x3060305070b0c0a060507051e041a032505041805160f09081e0f0c01020a08183a050d0c0303020d05040b1b0a020c090415140714 57
    0x500d41c1c89800f042c840504500d034490307014000c2c0d00f01310b03400400741e4100c0c3c184000c032088000324980d0800501d0040342e04807100102020060103641400b101c041c1c00043c105078007010003c0b0f014000c4da000005101c1c0c1002c4644910341c5440c10550509801c01040260400340e61a0000b4001e142805141440c0703081402d00e80b4403a01c80703003028116000142c541c88040742c0e10400284940d4022024032010242e280c00084030703c50451028200d5450000c250800e000d600002001404141c4c804004d00c404a070314040b424548144d20041584245103009a111461000c0b40703100f00c812010382405450a6030460020201200362070703550f00c43e068680482c0a1180c1032051100b054004d070150381c868410200104a00d02d05800d0003d188030040b20385241500b2603080020f00300300c2001c10344800c4480ba50007000141794550500414100250081d1102c042c1086251450071241c000c104110034404900e0140b07082407200a055007030480e041058200041c040b004000d8100d05803100000c94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 909915836 1250 909914586 909914609
    0x30f020907111c030b0d0b0105121204150305010518010b03190e010608010e03030709031b260c06040605120a111204020102060106110c0405071e09080606010306030507 74
    0x5401c41c0075240c1d0390142901c082d02e40520384080c0072445241c90304002c1d00c01e00f501c1c144071503110741c0300300003c598152800a1180110800601c00c03414007001d410800030701e80c401c9805040100d5101034040d0040c0e4002009224510002c40d4419414020640100390030f403001068125103d141c40c0d00d21105000e100700210001c000943c11000300000040d51014005003000720500090701e240c060400e901030030302c0030360a040c5152034600002003180c3c4680c0065440d0101f4505666540140342c0e4001005075032183c41e00e4000c04d050200c02e006543c80755409000644d4407854410650806014008880c410202480100034141e044400c481e248044410f1011040c3d48800c010401058110010790900001145a030303c505a2790f600d0a0085000340c01721807960707a9429044406004500414040303421803c2440500d00b45500f006800c9101410022104100c90900041446da807003001800903286c05810800d0391018015190004001e18040c420030b41161100740e6205002c6c0b01d0402c1244 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 909917086 1250 909915836 909915841
    0xd0f020301020d1505270723040603050f090d02030a12090b0c04030303141b0c0c06030c09090615030718030209430516050102070803091501030f0209 66
    0x550a6044070b0000d202014104104400076110090508090090314012100020b0211484024416542055601000c900d546c0d640390344040303030700c01d0129901c503c1d0744111690350010762180e2809000903040a50700083d1601c1d0604030404901005802c408040d0800040303007407643c2d4003200b1070f042c009490400c803a00660040104008110400d80503081000c54814052000c00c4c0030000d0044038001d907020700101e444e40d9102c003030741d910686591001c1d403805a0007051600e04900a400d940c0300030026684201d4501000c21584c0c0d2040303034803001041c00051144894034141c84150b800480550300407041c10764160a0711280d2001601900510560101c1101005051700303046c80034590103004a906810100b121090030528031024000030800360001600710342d4011505900c1000442545048000c0032900341c070141d00c0b1340c100c0e540d0000c1240940e00030800034002001d030b42e4820b552042c2c0c0ca20341181e240b418044041603090440020000400100d8004511800c640d43c049645542a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 909918336 1250 909917086 909917089
    0x90503061503120309010209091503191109040804181a0f0d170307031a0306240612090705010c05030f16050d0320120c160503040f1802030103020d0f02 67
    0x60003da402940e07800f0020800c40911410740203007211000c01c0d10740c0d603125250142c0706010461a51101ca8140e40038000041c602c00302210302c01c070a10300440080c0007240703284001c20f03012030701110151942800020200301d01010511442120014840108091982640c00c14030f50303002003d900380b0441300c445241000f643c420500c041010360003517502011441407076086915410032281040840d107000104011039105440ca010f10180040c00b620040c0e42c1c1d0607000c6006c020075912074902a0070b408407120a41ca50f0002024103040983c10400e00d4500580124501000f640240e41040743c0503c2101c0002c80000544822106508180352251645114021402c00408000c1c000c3c3c4561040c0540c0e9a8040c0c0c84181c10181004041c203030110381c0704d0700e40098410500400c180c0e21148000072a4940c1002c05401400322079440502c48002c103446483c910340294020340c20340d044a00c001c1011610020b1003502d201004031065080d50b24503000551f144a1050019151200304400c21046 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 909919586 1250 909918336 909918343
    0x51e0a110f0904060509010c0903050a2d0b2e060e0312030a0203040b2508040c0902040e0f060d08070f0c15050d0f0504020f0d1a012301090503061503 66
    0x40c180c0c0500101ca1610f018140000074020580b078908095180400c614100c1e441b981c076020649030070034020601003c80390765841448100c034190701180005103005003c0c0c1c010001d101740d9914043d0b519203590741030060080c07501c4482c02480c0c4143c10410418680180300d855001401c5480f41e0500f4902c0345504030110b82002099441c9201e40c20000017040300000055001e94065070081c1d0706104179694034960182400e01c0341345a440782400c0b110350480d409120b038001560041c840c0c0c441d51410340d6210340d1201030360400d401c55146409454100061f42040003541d0f58492011601650744881076140c1c40100d2081203400342c5040c00112460060050328070600303006001044400c0030ba81860034000745180c01c100171075641300e82002c681e0b4040c245a4010349001d9500100501c2e0045006000c100903182c40482c01c6a6030310b685c40324000848412400b1a0081200040408412000c1d5040402c0308104d039104034103021044d0400c0c0030302c4d10b00045a6910044c84001d4054076032254001030b15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 909920836 1250 909919586 909919609
    0x2150403020c1504090c030506060904090c03051504020108070503010302060307030b1f030618091203051e0703140906270307020d050c120d1e030b120a051e0a11 71
    0x2000a90103c440710410100401001181c0810300100302c8001c2ea854202d0544106603043d9910800510020000340b9050b40400c40c1c1a210342c3d8907410341680c0c2c3d074555040210106245e0034100c881020003055582000d049030340150645841440c641c110340c005011400042c0601c810183e403002402ea9179254080f0101e402c420208500100c030742c1e4400001c1c050130003802a0b1400c5410681048150010f50003000e01d00c0740d00800c0346100d00d1103041c084006000c010034095045c0707070802101010b03079102c03d03805008801658010420303c1c0e0085919000c41d20184c110681540400e0402804031410402c501140c00c400b002030200045200200345180608000a0744c0040e009100c44104003002500d00d01c5c6d1041600c11103544800d03a07010079101c145000a910110354440c10400c03074891940389000b0041c582d410f0000d5030928100204e41010030180d10319159506c000002d106100c020464031a2150304000741180d4030040f40489078449909850040c1305041305900380249980300c100411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 909922086 1250 909920836 909920839
    0x8070507022107080d0518090c1e210f0403030527060f130510090c090e151005011719020a020a0c0605070b1909020a18060e01050102150403020c 64
    0x40c4901c207072100c0303e8941c1124440d00c4164030a82d04660340160191040d200b0010100c000300d0790814680040c00750050006003040c0c03400074100241100c1c40303440300c81191005500200561070f8100b407441040040103030000e81c6182181082046681048101c80c1030340039609d0b10f00443c040d1584000d4910194076944290b260780381d00c076140c8101c00800a2070a11540000540c00101d46804503901000002d17520060025008111100c0c03882d05d05401c14840710b07210300000c056442d0380d12502411100d1440050300c8036088520709076410381010700e0058014800b40619030f9003624100019103d4803088620410f480d0790300e0001503034a0003406000d94a91440d801c155694410308000a454080c0710508a622031582180491498851000c0d1603c140d440003001d03403181c5890781050020740c513031880c4200030ba4907500d41c180103032160001400100301a491292509140303100c8103003922100e810501c200190341d4010049a81d00041c04060700240c0703030400155444508049080070802100107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 909923336 1250 909922086 909922129
    0xd2a0602070507150e01020705060a020d0f1416200a050d0311010e0609060906090c040e0319081009051b0a18030309170f250315020711030a030807050702 68
    0x5084c1d00d50001100400c0110903400d07039400a03140d50030422240510005000140c1c45800d040c20410f010f0700c1c0b0340c2c69038502414410f48040b550b46c45549640c6c0112071000e50b02c4204480c02c01040194054a1212129000800c4114034800040b491461191244e9440340502d03030381c041d040c18001c2c0440e9507001901c9000b404018034600303003e5550f0105480702200340c4200b20025501142c0850b425004811680240c00c01a5001023044054a18400c8104580c042082490040b00e100c84203c03101010603100d00c040351a08524802c8001c0c0554407102e1064100410400303450320010504003106079488070740c0c0d06e42011110459101400d81d2542d10030030781e20103000c402c3c5600034144808480750f030703d480129581780c1c903d02ca0b00c61400200345401644070030707045d0b020301c0038003060b40005011214080c140e136075503600c034a190840c00f8150565815800240401880302030303114100010b200f50001c140e5008982d90080281c0402841c0e00100304003c901c0d5000c55840100d58105541e5410301c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 909924586 1250 909923336 909923369
    0x50f1b2a01020304050c18131109070905010206060f18040309030206030f0109270f05160e0406060602030c03040608100e04061d071503020f0405040603050d2a0602070507 75
    0x1664003d5105840c2038171644a4007017010b4903490a5124074079020a90b0302086000e4491000048103e20031943c00ca8040102150103101512a0301c042072003600e669a5004005140c9400a400e088000d8080c601a1101071148006c517103459403c20309404459508070350b0b41e619814202d0f5520f81580000703510500001c1800b51485650010301d044e00d410001c1040000c0c1d0f01e007640300c10080d009400b1a6200e091081c80e80204000c82c1820540d80e00480580e400510340f184400034001d1a03030052428488030b0f03000c1c807040c0480e038810350f00601074900045240c481d040800650702d024a02c100c408010740000042c1941e03100d181c89500515240403001058186858041c0250a05400040c010105c8010801b0000e400059000c11126035500d1410349201e50041180070394481100300c080e040c42000005196161482081d0040d4090300180107035a40d142401008040c00200540340545040100005c208020000c0d43c1c8690f4400710059540340c0724580300d41040d10543c0400401d00003c00b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 909925836 1250 909924586 909924667
    0x24050306190305070303031104051c020409080301171e060606030901060f061d1e0105071103070305030910030b130e01090204060939081b0f0d050f1b 66
    0x139042e040d43c2c441d440a00c0741e4a5040704614032802a40300742948030303042420203040b9050580303500707a106002a001003649807880e101c640869000703911030384003071031080149a00d0601c103225038142200c20808080c40020070544441d0780d0480075080622640001002c6100304c0002d500c048001e200d401482c0200c96a502c5e40581041e10040d09401a442001340118052402075038862022108141090780a84078070011909900310b02d204581d00510a048a02e182c0d80800441c4010342c858401155150b01da4003d1014119070000c448040c542002d0001209588102103640740700c002040015403214051407141c050b000107003029410034508140418402c070075400007404034461600f1003c00700401440301000107203400e480c100b2410500a00c10400384607001403604000040c6019040f8113015010271840d510880c02d0030312400000440a81c62902400350940c403030924811500c1901e0440605003d405088511a40c1d120300018400807000c00510009402c0f4588016500e11216680 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 909927086 1250 909925836 909925843
    0x18011101150e071b030e061b0706031d06040f0f060c0801060e0d0309091a090c0918011203080403020f030a050409060e040309090b0102120f0307030624050306190305 73
    0xa80311282c01c001001654081c0a541000d4158100c104003110081003074900f210189059109503038080000c010081b18810011f406200340c0c1203000140c4482d80c0b03000400307800c5074032482d44412440785251603034190350004100580c0c03180d0051055008400c1d58031300b29002c02c001003002031582e858000d005280d1a1300502090580301c00e40c0b10641a801606d0802824001c002001000112a03c0c0103000c0185140c0100d02c00440e4404a45503402e40c50002551031002103441e06885140031900008038504500c0c2c60b1010071b03100c07191102075410800d00442040031854040d0500c401500414100344c401c21801001c0410502641d4a0b910a050300405030380c02807203900803442c01d04d400422030340b0001c2ca030a4003460b81034030383d0380c1c40c60700d40b407203910203400744080090550003141000d08507420010014081403d00480c59550383c03a1401d80a4220340d0b05410030101202c42ca07040c0c1e40200204244140070f0495800c01c0e40d103e681c4c01c0c000441c001800303540749038005c2401600104211000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 909928336 1250 909927086 909927089
    0xb121f080618210f0706020301030b04030909090b16020c330406050922090f150b0f041812050301060f0c0804030609032c1809031801110115 62
    0x146442c0042d025070056aa5a181c40303203210032082c090108849210102980240798441e00c10030120305140d03180e240c160498100360f0081d1502c8031844208010958003142c210f02a201006c000c0003400710540316251240c4000381170035001c2080c40ba4044070907001b00034581c0441c0c802002990a410701044000050701040c542080b103201e0103081c52401e1002d0b00030340e0169041c40c2e442074189800b420801418031140c1c552644642c119446604901c00c1c1405403031035860245410b03070141c41381454508035030310901c8882290a0f10b440c048001c03e5030740180c05100c1c42c2084501054000100c8200d4401ca03000442c01030486801051140c42c0603081317806181202c00e1a105d80e10705504103001034480c0306001c2c030014035428003004140b000034425440240312500070b14090030f248003200c812054900f040900009490b0800741b442c101d9152440103106000351500d207030b00031400c100c15400c1d620300440050b000c001c11038031181b01403a440359049090982c134040c000e100001c001c030981900f02529 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 909929586 1250 909928336 909928351
    0x10912210e010614030307050c0d0c0e01062a0c05060f090603040b04021f230c03030405010912020106060e040c05070f0804030b0c0901020a03030c180602010b190b121f0806 76
    0x88007000311091170040103550206820001401c11612000c040003e030442d0010300312420040301a0200314058480046c5000e00290744410034024140d03c0040c40d019524140441c40c441001c40440000b0041c68103201218816038010741c45005840c000c041500030702c400160084000300810040c0b00100c00200e01680c001e0f1510389500058080d520180c100e408550b101040c00d4800865206485c1c1c8210320b0789401d803c4400d0300788865805a10f0441c8d00955050f22140c0d160031059081c030021000d40114001b69000803c41c0301d19000d809001c101254400034070840d80c80c4445074006020700d0807580b8072a0f000d100410041c9080c0f400d600590014002620b454511034006154104210215402c00e06c0580080101e81c00641d41180504119507910341040383c4010242e40c00582c03d01d1040207801144c00124050a17a00140700c4410307248014503c039541c1807402000040d055104588a03003413000c80a90032a50340e40c900e80d00044001c02c54124100c841c000020304420045400d5004280 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 909930836 1250 909929586 909929609
    0xc121115041203200705030601140a12110414070c140c0303040e01030b0603012a1434020105090d0606180b010e010f020601120f06020408030c0609010912210e0106 72
    0x1c0b0000b56685d5003414000d49030543d0010f001841000948407801521203001041a00510340354035072030824020014084480103022444420f10b0318281c0540c00301c031050100103910f1440d041c04c00601d00c10320000080d02004410000d04030206003400444034000c00030b02140d07036803562980100b40b084400d1000303071018048a40410514a818001c60108880300c0303404c0d007a00004054403c00a01d49100701d041030242c01d03042079000b1600c0350701070071843e00c001c42500c60b460381c22070040e60014604006070641c103100024800060b0380200136640d61186c1507503a0036a0b05d00c4c510b08103005119580108170b06041040030121f1141c50342c2c11400c11814203903540d40701045070100540d451011548800c025030046070046c042c4000d41018010181c2c012020003690380902d403500c4040382d005070803468442e040040c61184050f0100329a64000509000030007071b804003900d40994246002c41800100314034074494817130401206118003040c07902c642003007003552040560140249802e00c2000d24100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 909932086 1250 909930836 909930887
    0x6020f03071b05030306060c010b030105012303070302030703170417010c1115010e0c0f0c0604030e0603042001050c010f0b1e090a020c0114130c121115041203 70
    0x38405007982d90601d0744100150308584442c010008240c200c0030000c40d5643d62403070980807030795090051600a094500400e41c034070300380c074075a0001010034a1049001e40d114140c00c10068400080400480b900004480b4a0079481106d0003c1e0741b240f41d00c500c0a950405c5442c0c0c510440640c000c4155a10f0b80e2a0561390041081c001601c5200803035502c1403551840c40100101303044000c0c9158042c00c4e51100c1490100003040c5051140c100501850b444d601c1031042104041d0007001e13219800e402110320b41e08504d02507030707480401e68402d007001c21401c11108040d140c40c1d0080042c1d034024200d8500030700207201c0404155004010041c01c652160083c0015240d5070703001340c10082c00000307002d04204120741c0d80a0850340a90701600403c9183e41d0307038040780c00d295502c41c81100d0191040509604401c946070600014400040d0041c0b40e1902510f0450000503022151911408000340c40202c0d0039084041e260403a0f000e0340e400000c4507107105101c0c0080680c81103141c0085401c0142050030710 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 909933336 1250 909932086 909932117
    0x30a0b0d03121506050a0c020307051005040e0106020613030c050a0c1d06120706030e0a0c080a030801091407180308180a090603170d020f04060509040b01110615030a06020f0307 78
    0x40311240300d442c4c0031480820002141903c1030080701281d0380060100c43c0740d20755400118203956148011240001d10128003846081447c03181a401061544010030700c505003441d20340c20350314080c680101442482e60856007084800e000d850310640d049030610201954901000f50310711141c02c5c425800008003c0051054134120551400707900c0c1103401484402d0074000d040c1c3c003c01c08800c2415040c81019040b070b0006881030040d0700503080003000b402b400100c0e49409800002c0603081035941c00d0405045a03a01020072104543c01003280c60800e07021000501c1100c001641c80d04060400f1100081840f5007426048031116070020903150b03141616900d00d03131542180c3c0d032800000c00312401c00301800300c0808228043c0412001040c0010700e000781020845509500540c03007040841c40100f50b108d018545403180d0309440b0028244201842114206030307446e900300800e59110000c0811584449803403c1004900c4181d110b6001c5564511040e420f0500c1c1d0000c03208200068101220354011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 909934586 1250 909933336 909933371
    0x5031c020c040c0906030c110a0807030f020102040b1207230901020f0c0a06030c14181509150a050d0212040c0f32040f090c080d090b030a0b0d0312 65
    0x604a0365039070903d4003801c041c006c8020b480d07004000f20801800758500e146550f02404a421464032402007aa40c484080c40c3c0648481200804d070010741e44140000c000d40f6a0040403215014030410310006180e460395400c2c3c8281e88a10710010211001c4288220080c0303101004148500c0700360200c03803c90140d69882c40d501d880c1c044c880c0d50443d400441c00c1024500a07000548460714a04009080d81e00400e00301c0c10913000744a00b00d81d103642c41e264048460130180800e0640c000c83c010030034600100f0601003040030703200c140150306002c000a20844403a1280d8160fa1504441c00415560b402d07003840b04500c10034041c0e4068604040b02c4d00e0008507184107040400c21200303500c1c900c00c40c40c500f540394180c48008000200c012040c40300800010303640d85200c0c00c1c42c06c6001c901c0003c0c052440e414881452902a0444e000e2a40404824088681c0089404040f918402d251554039942c4180d00d6015044d104181340c2c000c441034a0103400c0681150030ba03507044982c031008010380d5900403000b144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 909935836 1250 909934586 909934601
    0x1009060f08031b0a0b090d140a0c0f03090b0409020c0105010e0403120b0d060e0318060a02030409020d0e06040c06020115150806040603050303010f0906142805031c020c04 75
    0x129903004000c40f4201e000e9030030301c41031240b2000003034404411068462004c1072104407003007640b6402c01d021650010741c0150111009551100180d410a0310742c0001034541c02940f10b02504115000c1c107080c0030103100d83c54150140a180c5840c640b11907850981002070b4021071001e4075194207000001c5201010481d406110741d805a0b10b103400640001c0c6c2000050216407107a90f00b007003035460400080f810364004d02d1590600840219500c1100d0a00000c286242d41652440740c00e04002c405011030b070000689003515401c40b00181d5800c030a0000000510190048440501460040109104100f0901d00890340242c00034401c540210291004540080c0a092030108030206001c4a040c0b140c8041580408040c000046141d100d4440f81c0c6190400d030b10010050800361000d110480c07070340c02905e0013030058810920048110400180c011800f00c0d81801001c0c42e40004134450381c261612910082c01c015060322400380028040c40c1c10081101c6d010800351040060b55030403801c0a109011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 909937086 1250 909935836 909935849
    0x20a050f0d02060c0c0415060314010b030115020f01151a03010f0312020c09010e1b0301080c01180f0b09040e0c0108160320090120250b031009060f 65
    0x10702020390800c2456045060a10814811041c40300c03e203440340c1c0b250503101401d01520184803803500d04014265204000c800c00468402c0004009520700303201500c1c191042c4a0b000d180040a500b8128504090754585050329820f0078000c0c4018109c1c0c544503019620b22040e810014a06604a003002d80300c20f100f0a0102c080045d41000414042070700901d41d681c0c113106442c002c0b2122000258845400c0e00300000071740041080c4905444000c200e03183c5052150001030443d8034042d496920741c1c02c0c901ca41410310120041c01031050500c3c00880003d03003204960f03041007a450b0100004560081c082e000d0041e842d041402c0384924002070780f000014030503940c210240d07560070f4070300070305c600e0010044061503104c1c008660945448800107000c20000442c0c0e640f198442c600050200c5a002e10420403104110b4100b1301c0c601e0301181101c402c81110750001c82034108000b006924105a42c40660040004800c1c009003180b16120b0a0444080c0c5005101403134a500070500220118407651 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 909938336 1250 909937086 909937099
    0x70206010b040b181206090f010e0703060b18070201050a0537060b040b090310060f0308070f1a090d0527030c15070302010e010c050901030905010e070603020403020a050f 75
    0xc11184080c00014141d1350210b0100340d05581c1c802c40400d0101c1c50f1090742a1280e08883d0410a0041c400c000482d4070840c88402800000040900c040d1207144074040502a2529106131308559100c1043ca042003203400f0041c00b4040c542894000d00810041d03422200590421000c100e10b803180c508030850075014000021225864282840e50042c118400b5031502a00c0e4034001605043c4100640010701343d044420340d03a0700903102054101405020340342d818a00e003010902c5204103980b40036040d20b0340308101580d00d40c014141450b640c80021402410200e640c0c400000c3c4650301140280902c0449044440c030081e55001502e0078041c40e11241d0410015100c0040b10701c61100d20342400a50240c103544103003d2000108a0031081c6a1030018600d100080d82410140c0c244110140042c680c8020800f96075800310041242c0f1404500ca410552200c000e002030000a5120240900d80e81e400c41d180741c0c0d580d1b400074010390004d110582c843e40d1010400940c600380030361022040e990040c0700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 909939586 1250 909938336 909938339
    0xb030a020309010e0304090905060c03010b0307080403020f0d0e13142d0a0c08180606040902040213140a140616030c0f15050c07051c030b0604030614070206010b04 72
    0x48200940005010442c1503480f030343c64070f541c081d00780024005003200d490042110221f034103003c3c0c0740034070141164038a0082000104103603005a402d40c4e81189241c03a108600d52900d060491402c049025403240342c0c003500c1c5950381c550341c10960420280c0300c1500c500300340d040c0784030301a800c1316130008010450018040015010f10300d1040500900040032007842c98055650b0305285030300c1800c484101142d541d90701d000007440c2c0c0007000300340c0c000c181c51000d034540e155013001944c5030007000c0d000c81d00540e1150071140841d0740310307010748404840c10110000d1440d6284001c01444404566080c001d60048801148401082c0b55106010130302811483c0342a040741040352174020526019420802202c2030103000669814924060900860b0700f44600f00340e001d10786040301d01c05043c4118034402005040d000500104980c0d4013020790f0907144410044401c070039805000444142c07036000e1030000d80402040110741c0030460b011007140401615582e1018242c2c0e581c0340a003d4103250300e40a010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 909940836 1250 909939586 909939601
    0x3020c010e120106080102040f0506210c070f051e0c1c0602040b13031509151e0608011d01060e0c03101203031a010302090f091806101502070b03 64
    0x2880a04520150500c9608003502c22032508403602c0790810f00d050b0350001405c208404d220703013084c80a040211286850526010702d0000d10040316410081000c004400140d6202d6040007504e551a40066039019102c0c4145012615070866200300d800f21920000d44654070701d0006100101501f010b014401040d001e500c40c407080022860084a42d55002c1002145041850300505070401ca000d006c0200c1ca4110b15080c0d1030300b40c800c8d0102500301d04c1d110a070b10100d01c00240d00c0d4000600d4003000601600d038581070010b20005002d880e641241010340029058405600c80c074222201c5441a1550090b00c0041e079090b1071240c450100f4000519011803c0c10548400031508540c8100044044c0c0b680c0302042196081c0100781071340400e603981c0c82807580c0306203004409401c00c42442c04515000c0c480001a031031103102d805160041301c400e00000c01c2d540c40c1c4030b181540429440c04540c0340d403038114803401c4d03401503500075071441c020100d5541150700d000250b2042500c480a440700c2c1507940340071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 909942086 1250 909940836 909940847
    0xa08090715080415110f071704030f0b0604020a090501030b12121b03070302030702011428020d090f170120070203120a050307033914090f010e03150109150501080403020c01 76
    0x3c090b103041d9448d21103a1020014480100000d520804840c440d81c449410100e0750300a000b4a950300a50040011000895001414400341c0310242000a9200018000b1403490702d0b8101e040035071445000440d840b04410480a0640705404146001541c280910f1843d12406000310090250748140320480040d0b01400141110406004a19041c070304286494075402c442d203a522022402030440b80f1a0003a8180600d6814040b00d003080c040d01460304c1c141058040c154822210600342040003810741000c290440000940903203804c003811912813043c60115403226008030b1081c8110500c450f0355421080aa500c1d5001d03540f02d10341980e8460740c040d406401d4030b00d00040c0c040c003420700d03910307007102e2840c0007204c1d51400c0034000c1d1080807200b2026290002d10264041041024000c10034a41d07620001c070000040c00386020340d60140240003007441e0205058590601a96500021441e459254000002d03000341259207520560344038015036645206460160050f007100a907807420394041d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 909943336 1250 909942086 909942097
    0x605090f040c052115030d09051012150f0e010807030204020304021302030708060a080f070b130b1b060c030103020d061a031f060501020d050a08090715080415110f 72
    0x141003080c50114020b41c08524281010b04d03061081d55410706202d03510b49002c41e45c03c4505002d80040420b040311030006484421640701e21841889281d2401d010148581007207014a41014000d002401030400c031401c4074001c0340104510398800440000e151201741040740e040710500c8010304010360654080c000030354401801686c20401444501410400703030b00c0194492405a030b604817860a1100400c6144142e80d402658107a002c10300e40c0009007000300d9450101c0351007001090380d840c6080302d80881064154401c2018182c007042c080710018000518884840d40745003903400350354a20b003811406010070300010303400950805500c0c0014000d50f205904c00d2035958140a0018000000131345000c500d004100b1034000740110707022411289015090182c80b090010f40058910780000030900d010b500e828104000c6018003003110b01109000103c0544288031100700d4004210070054000f010644046a50181e112040e60394043e0902c1840d01e0320f40d00740d880c986003034130742e2484881d0742d00b00c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 909944586 1250 909943336 909943361
    0x603060705032a1c0b03030c070b03190c020607030e15040f06090c1205010b0d1a070e0a0e190504050c04111611120105270309090c130605090f04 64
    0xc01081815a040500181c01e06518402d552213403850f41d0340002050391100144903000c0d5006001000d030742c00e008078800e01a1004485581c0d2655030302920000c8950700e001c4014182447c01040d00242d80d40801c1d1030b841007689072020300503004c0306c218650b903c90000e020480c070100c1e40c3c0c0c0800d0014949840d600000c0380940d00100300441262126a550704d040e03071202c064008511140c80c1013000c207000304190808110f030140c0d07031421141c940d042d444020b40d00101c264820000001da42500940c0c00031a07411001d0000001c060704d400d15400e07246025280502202c88101002a00020b18001d40d8032a03540440544204440003003444068841442d040300301380414010b91541d0b142c00c1d1803044205025282c0072000b1003608041c406080c003116441c003110390601d000c00141080030f403860503041000703001d40a04540505d0809007540260034680b948445600c0a000c0c6003904c00002c0d0441c250814007001d1002e5603800160b40390301c241401150002810030940b5000e180c5940450700d01d484 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 909945836 1250 909944586 909944641
    0x501080403110d020c01020d09080c04021312061a0d0320070504050a020d0506033f0d09030e060403020d423905090a0e0f060306070503 60
    0x34410b0005041c5032161410800513800440d20311119a410481c0b03841d140c546061001107507052013201501c2f40000010382d8000c0e50006012075031b6090000e00304000b401302c5118060541041c1c540f00c009407019040764502c68100301015040c0d4605181c2c14007916525072a200c588191903036050b10060310b03000c0442482e000d00c1c1c10000d2103440354021203100b2040000016620303400804500c00b02ca2014017024004d520100760741d0b40d0b4410005050241d210031007030280c02410812a91081c0110f1004050f42002020400301c1c80140f10ba00700d6010300344242c64800c002d869901c14841540900c1c0b102a50105055040c4001320320129108072031100b0000c001ca801050410f14465990b4500744407400349000100100c04403459840b40e040c16003100ca482c0200c40e104040c50000300d1500340741e8684841c00d8a009207000e14007a01c121081e502001d004980003d989900310726030190211094050700451000140c894540170507407600c2250b6a80721642141c0321038948445100700612842034102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 909947086 1250 909945836 909945857
    0x9061409063105030301090f0e120c1006030308041101030b0102031204060b03030705070807090504030c11220c030f02070819110a0b090c0d0809190f03060204170f070501080403 78
    0xd040d00c1a182e04600900c000c1d9665490541082c04407942000d40d09401c1d890146c00c04040340c00070448112914041c081c117500c4001c2d024415042150847c408410070340380c14000810103400400c04d501c035a01603120303803610701c100d5001074051700c01d000d0203180144c2080040182c41d07040144d019030018081c10001817a45014030200c1d14607030000340150342c0c41d03101071020001004100030b040702a1107038440501c0700d0700f40341e80e015228400703201d00108070368230f00042c1d981b00352241803c0501c11411004000a03150202c0c0762a4020041500d0791000641030031400c041e440028022070b80000c6c0d209a02030702d84102c1401021410b090342c000001000061503c3c212806000c0100c8100305006410800541c10300031000c51500c00040d040d28000c8800422510200d01d5070342c142d5240e0842035807828220110b10000484804041d0032640c1407000059022060042c29409042900c0c00032a006100c10290324034190340310034801041085600205050056511520159420500c28180244640c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 909948336 1250 909947086 909947161
    0x606030c1b03030a140a0c080402220504030908122706040e090601210c031104090501140106080f01030c060f050c0a03020607020c1512090f0d030906140906 69
    0x41e8004c1d1642c03840f041d100e520b030400d0300111103c140c0c2c000401d000308108200c480c0d50041d21051000744040d11996500020b030100d803040c0c2e4540c0b003060031800307401c00c81840c3c02e250250800556004030b980501c1070036480701d81202c02e041120002141140011540d00c40d012002d480c26900050640d0000c0080c400054101740d40300c1030038050b10b85003014007900c3d81840d0300340d511000c0c00301da406107181d000d40e160000700701705624040580c2d40055881d035140740b03004081000307030214400081140d0f10b00300705201115030320408070303041e07d00c6603a500724151210003015100279003e000c0038040c802a00401c00506010305504104510030f810309506240031410030030304100c008407056025030005c0c0c0400411035418004001540d00c200c5188180448140c0000a103000b005552102010824007140c02c401003040041320749a0303c0e0040750021011800018080e000d0345404079100d6007051800f0107544003c6401a211b2483c48000300200c2d075403c068220004030b008505200f1120790302540294 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 909949586 1250 909948336 909948343
    0x909031b080715060506030708100812070b09010506100c030c20130509071202120f030c07061b0609061b0f14070519050106080601060306031a0606030c1b 68
    0x254000c052039521005281806590360f200c208401e001d2610701041444aa6205c0d000c1d01e820080718030f841000359842629610312010583c020524610074201780d02500c845010080c038105100316281081500d49091581c2610f4090311490340c002400c00000a00c0b80c803401c0f44c20140c038000d160005a01c00c850301c511038844011108e000079043c4110080003d8109014444020038035030004001d2840c016600743d40702d8803180600c810024100c0484429541c54240c3c2c0107010130720381d040e02c00712100706030250350780d07030104400700528025642c00149850081591030885411a084084401c1c1035940d503400400c8110400c40c0e04035500d50024030707001c0f03c400c0c0401040620361165007102041e0500070f08440c0e0f00d40740a505030302c0200302c210006140801c0c001040e01d41d00c400d0840070350041c6007140c050719040c1c100f480d051048100010b8603543c107812103801c903805850030300030410140341500c18111003110010340021042000c100c00c0f00340d010041c980c10a191360003194000f51035a00505 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 909950836 1250 909949586 909949637
    0x51225050d1802010504090f0b1002072102210a0f1101172203050705030d0510121101050903010b040515150c1911040507080711030901050301090903 66
    0x2640120300c0d2031011500340b0515541001040c054004454a9800209148117a01503c401035031074020044890810340c00440b0340c4100103040d02451381e103403c5c0085d40c0b00c840d8441c0300b8007101811100c0301e803001100007a451032a0060140348442a02d10000c110840308074030394095510600107100003055016854100700d03445900d05154484c0f860b4001044a081c280304000e50002d9501400f110030401ea03000241541114440c04603003659081c00e0300c050181c400d01404030f0000183e03049940c61680d106902c90a00501c007c00c03510b07203c000c040503c103078140300246046420074006880d5030168018203080d510080001c80d00340c16000100e070544409071426a105007003c403040d04185000113119118019030b00300b090600b203a005040307a954526000c141e00c003583c3e105908080c48019240c03200307054030141042c8543d0030640c50007825070038212012800155240105005920040112616400d050359001d0541c3d0806004000500c0001000c0b421311802101035800b00941c5a10380780c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 909952086 1250 909950836 909950911
    0x40609021f021b06040803070f0c1d0109060b0a02030d0b030309030304030b18030c070303050a050d05360706120f0501060903030e030705010c0308180f0309010207050d030512 77
    0x2078490840f11220010007090548588600424401485400800415200341540045c0c0c4c0311811601e50800000e0b194031a00961013841d980c012840b010f4040151a03412142e5240041107802d50b60456001346000d95120f40c00140c100308440c048010458001920b40c0400a094902e066100400246107510035030045810004010401c06440701d80b0002c001c4907110a0061441c00410050070b54842940b40001028000082030403074a0134450b805890340410109410400c0d42404210388080b52816841c480c0030490300302440e00800d2144a803048050700c50310041090f60f08004046d282502c003e41c0d8a2a45981c81c06000034440442c0200e900030a02c0f0b03102c80c0800350541c20001c2030620b003101007500980c8180303c02c10103641c0c4400b8052110781c251400001c00c3d103c0c03030f14004020010402155040c03051000b21070040b10044010001c403070b826001c541e4816582c50600041098025000d0082003082c0140170142d040c460314164030003511010142019581441120071001d696180e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 909953336 1250 909952086 909952093
    0x1c06031a0405100c0c0b010f0e161806030e0d03061a0c16060c0b09030307050a0e03030d050f01060e0307050d0807032016080114010303030f060e0c0306040b09010e040609021f02 78
    0x7401c0c8100e450246c2d000d0080464903101d0182040052944a0030181103840c0e07203c1c039150b880b10784034403807800e1340c8040082d07a14440f00b840c0d48031382c0100034121500f01c980d480e0040e0740e251403015010340306520448860541180784900c58a1240f20310340c103d0b100c4903649010f54400d90f280c460603074410320094030701a260703466401a54205040c0301500141081d9041c0d00c01c01c2407104051300b10041d2404a40e441c030f0800d107510300b150f011900314095240c0307082020f03080505202410142a4195060700c0540c0da801d941000c41c0300030142d9428241c81000d8100b84554507800220b001100209005802814413542601c400a1401483d5401d90101480340d081a0040c1d032102c0c40110242000309200300091055480700c112074185e1700018407004050641d035a5105050314869000300c4000c013032410b124101440c20000d02100c035402113800c14400d0b80703402c1c68100380c3d14241c01441d05035500c035080c0c602c265542da9901402010081c0d0240d034401000000f07415107000c1c42681c03c00c01400c0c0d502a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 909954586 1250 909953336 909953357
    0x20406020c01021516051c050f090109020d062304050604060b040606020c010e011101022701020105090709180609150501060e102001111c06031a0405100c 68
    0x7400d250a04030041d0440d0403140d9440316000301400280d4004848290802a500c01008241c0c0c1d41c2c41003000e00304002c400790702c001c0c11075121075203d02e00c140c00e40d0f80c84140c0765860100307a500302c4903d03000096200409801e5100401c00d030781e1190001c0b0a00005031182c0302e041f20496005074008580c2203490b5404002084108601d81c000e4150121702601c0c1402058140180030f512540800400c50406c0f03502c94884030075038420a00c1180340d40280d0001c40d55800c3e041c0c0ca0440c4000103908240307024080c0c520b40c1c0520351052090600c242240e401070001c032810700c0c41200250001d0b151544590342c1d49410b1102140710340c4503d81c00c26210f4488249080342030624031040c1d6405900440c140200303900145915110071031403000c024513034544424580d04011003128240c801d403c030b80c0d403a9843d064030314804661440046c41e2014150b0401c1d4280100c0403055800d460140c04002c0c40000308400c0d11981744910500030390441d03c01c0040e58120000e01c0321800459055510000c00111881d10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 909955836 1250 909954586 909954599
    0x23010e0304090b010302030103020604091e021b06090304081e01140a05041e0c06030209031c08040c0906050307260a110a0e1501050304140a05070911270604090e010204 74
    0x2400700c183c402820705505542c0355800107260b6000714420301c80d41c5500e03034141240101e0300025080402d0f12142c01191640708201c03036020707480c5000a009015108901c003281c41d60b00d000013543d0480f200034005165104441c500c0c003640360001142a00e1075034130b0f90320350001c0f40d21805040e80701d4018110700007000c0c42c00f400d1081520382c6418040c01c0124846031600d000c59690140d500076903c26080159440c200040031a14065200003043e008410031842010100d6210340818003071401884d030082c000b9140c10589080301d2061285550650000d00100020b1003007204000300d06040c40d903030301c0c035806001e11400d091880c00c1c0740c125000140e084015101d441c0c0002c036100981110707400c000851600441000e5a002261705a41c180480030002a00300701c18142003980046819040e01d0b89030156141c01582d9914034024220b58505101821010080b15400c2e10030000c08095140c1180f07000581c581e0880814a4905801c400204404102041603000c0c201c101d440b20000141d4a918115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 909957086 1250 909955836 909955841
    0xf0303060901091401030201050313020d0503180a12121205160f0c05060a0905010b03030a0f030f1802010c0503040b04080a02090f04021e0a15020109030905011b23010e030409 77
    0x2080f885045242142c500060700f8a40181c40c1504d5081c24807035907030340f10200b2042000c408604000d5000e04107000d41c43c00c109010000d02104402c220401000e19240e00411540d6483d5020360481803400e80c58800101c1c076581030221140c511800c007150070440c805581810385900b21900c0b9003144541041060b019404074510080d0380540c42c003a040520380b0b69a060b1681c00103044601b40356100d803c4203080c40780a5100041020005003181d50701c241c0301c840a0407109034640700c0400302c1e182070740d1581d56400f079002d50305140d003000c41d6280e00303140c40394015140017030103034000da40c603110a210200700030100000030005050000001c20154203d841004010003000780059810071580c8280001a00c0714500014602d640078004103400000402080c00803e1540c0308060f000c40d400c2c05420901d4041d07019800380c60296a9140c0800e45031401554484251404400d030741041e4074ac8000031400340c9030400c4640e0000e080112030003581103c11800c3d14982200d00d4542d810001d01000b0910262 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 909958336 1250 909957086 909957089
    0x60f02060a061505070203120403051e0613061e051305010e120301030305250c03050d0f02100c0309080d050709060906021c03090b01081605010302070b0711030c0f0303060901 77
    0x1c900610a00d030422078804000c80341014020103110010607018215901400b03010440c089910040d07458950b05e00340b40b0340d51405208420300c58559801c0b946103940e80442c0c06442403e03800e44611061180da5034000041c08034141c03040e4660b2000221018601c50340c010307240915440500e50801345541d08019085079406280c0d040194400307084c058100c02c00b02d068904403505801e000307403034584194003000503201c08529803404048a40320442005001411070082c1d034014821900003e844c1c01060301d00c10b0080c603003400541d000c4010090560700541188900d0780c03503840d000c18011641d0740ca84180e07410266201849a40300d00821804685c082d41e2403008004906c0c00c50b5501c5d03d1300c08041d41315290424101c003002c00000240c1521406134220844450380071145a16640c1d68040e4543ca801d090070046581c64000070001409602c41d000780c90025810283c00c860f942c40304503099445100b01e4255022038001400400300d401c0081c05145010391044014580da49003800800c25210f605 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 909959586 1250 909958336 909958351
    0x71208091014040f05070305010e070303110307050c120102090301022709011206020307030b03030304052a0a0e1e040305040e0709240516060209211504020613060f0206 74
    0x14a41541082402c41c280a0707040394201c4594003038401c803414014140003503504094902d41c03c080f2100044100000d80104481c002d0f6a208604d10754801d8103500ca00c21000c01030aa0340c861420841c20749018110340894405450005240080c0c3e900440c0c2660404a000d50300b241c0c0140310f03240010418203200c1c0189004560440f115810034080b000021129100504440d0303002c00094003030350103503100c44d8180c0c500908482d101e1030940303440f50391029131500000c122001c641050f40150000f4519580c441c03c010444c0e41d010b81000c003540c05600004051004040d4810402c00040d0a11030f1040d000e18081e507280390385c45090100e1000110f40c00b810107010480d0410f0304025030303928013902c0c002070901a0b00b1040d4403031062404807000c3c0203082d00140e82454080e488020003069500528400c18169424134000c0b1150314100c1c0c0f800c03c15030b0080d000340c221b05a0010a202c1030031034181d00c5440144100d05103e400c0401450410b4141c109101040342a01404007040d01000b0103a403090700c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 909960836 1250 909959586 909959591
    0xa0909030507230307060b040902150307090f050d0f0515012d0308070204050a0b03061008100e0d0f1b0b04030210050c1e040503100212072309060712080910 69
    0xc048919640e64810345c1c00160500e556002d1a42455a0310f42011000c2600200300700b650b0403507007104d468a64001e641807000300b00340d8400058414082801d40e012980d00034100c0c60f280015445105c028111a5411581d0b4024038224192a0154258190292902c90189031410300d605221880000441b80b943c419020314580800005111f0022201181d50544021030b181c0c81d198810740160902280003035040c0100003c2121803090019a082120406400c8500400e204100181120455040060942c10400d440609640110360501d80e6400c031f8030b0000d01c0880da440900403207884240044034440440e10a00003030560402446402c00c600090410090a0005c4010254070400a080400440708102c0d41104029042990000c00020f03090307582010301c41c1141d000a40c0700b118880380e80650301e000306082ca80304402018507481018666800b001e40590080d0150f08040d041c1c40d4400403c0000c45c001503034401c0c0041181182391244c40590070034814035030600c051042503902c92071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 909962086 1250 909960836 909960893
    0x180a0806100b0705010209040e0d02010f050f010504111c02070b07180312090815040302010c02070e010b130302130b0901120b1909050304060801050a0504140a0b0a0909030507 77
    0x14000042030700701e440e640c0d4003681e12400c62401c2c50190054502c1c16610618008000f810703c840171610381d881004940c0204000341d41ca540c03107001c445095811f11840d40c40d103001440a07041c56400743c5081c000d034030599410584074080b807061300c0c0940108007c00702e4010400d00c08005183d49003607041243d03414a90b240002d860280b455009561001410000d1051904208540a032039144060b0540005444c03a1208030041441c1582055900318015880c203051320a0a074404904101515045171341c0d010964a049184000e5401080c003841210000c0300c00000140c1e5a9640d000c800c40c4910000300d2400715003803c0011108059018070b009020586007040000d00c29a03205074003951842c0b000c00007000c0c40703d4620080015500c02450343c4400074000c219582c01501c07040c100d0340111201007042d5151814002958040385000c1c0d00c018456021503202d2509802070104860045c0680c41200d54459000041d52007041c001e4011601c005060030900488007a00c0e05a417003d4017000720b046 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 909963336 1250 909962086 909962101
    0x1201080d031b21020405030111190906020d1d210106091806020f040b040315060801141303020a080d060611010c08011214030301062604030f0c030212180a0806 70
    0x1090551440302020411000f5014110321503410380740a03040c040c000300701140e90495110800e17800910801a0200d03410f07940d040e154813645605040d00c580c0d84c080e01b20061f000b0019a11111840180390348460b5071800600c5517240c03207030200f4031107000e032031009a61500d950490303003119407030740000c14218107120420300b0488002588840f2158030280040e03445840700701020290055402540c01880001000000e0100010032895410102d01040201503510007040c0c0c200c0719101d01c0c40329040359030300009051034840051944103a0107030040c1c54501281e42d84400c03056004980c840480c55903481c080c03000c03a40c03001e410015108808000c01c5a0345942c076000d084071605102d100c01086ea00403404080040400614010385400011a0389950315180041c000043c606502581111468007005802c0716002646004135056200c03584c4600b030612080341d400b007441500341c080d40b00740d090b0410728650700d00040980540d0458407040944c4424204031a8205c181d0000f4002c0d0b01100522550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 909964586 1250 909963336 909963347
    0x60a0203191b0c030207051302131202150a050c0d090f0e060303121b070302030d0c08040f0b15060301080a170a09060f03090506070f080610120203040302031201080d031b 75
    0x2c55604000e1075000361850105d2504010b0780201d504900b0318412100c2e40500e07034014281030907100000560031901c64103840300036031100d800a076004171103581a01509400301c000b440400c481c0c4c41c0c0a45896030054045107485140000c1600290000000b000034030300100c0041c0242120f00c1801507181010400281d403401850350503100c0110150103d1800003409448190340280c1d000226200c1555003006900c035003201401e03460850410300708220117403040519901c5164011403800b126800342d1600c00c400b110081c11545541541609881c1c2661407002950080980d20000e18409129142400907550100b00b203034070740030052254540c410f41044440b41a0744040c9805010780c15100412170252121a0001d09203004040910402030390001c50740102401c00e03224503a02e511080280710414407030b01402800901d18851006003000d0680095400c0383c02441107a00b007122281c0d2a4250240a0740030350390035480744d02000107981e0103025000d101103180d003403160000317a00b041c050032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 909965836 1250 909964586 909964631
    0x20a020d1b0e010807060810061e030b220b1f0e0604050a03030e0307081c0503060d050d0503040b0601022404051f06080705031b011b05060a020319 65
    0x11106480c0d084075403018500d0074020301d841100000e040d607403905542d40741e5085000d200e0000364004c0001d00e1117a0401101c2040300c00d9a503a46501c0c1d03506d2000303002c205d6487d001c003000f09500c2e6000188907903140e4012030b41842c5c86800101c04401d40c0610801100c1080026a00982410398803150200301c00c03500408030855401c003002842240c1d170000d0720b94410750300026400a8900400b000b4982d00044450005a06608846da01c98862000d10307510400550002c0c80d060360b5114a1130402e214101a40d04070b0400380694441441c55520305050410b0340d120350380000c50120030001444a0f021889070400d20a002820205083e0030040c081c00904001401d9510036110201341044030820000113900c20100d40640145e81c42e01d80c54001d010a8855406c1500c1038a80200e024a008078000c00b852030b48800c01802088818010b441c09844a90110000d007802030b0090b0105000b48a81c910501d0b1040c6d00503a40d18114040055542145000202c0c46240c59421014400c6103149040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 909967086 1250 909965836 909965843
    0x11011802100c020319020108060d05100f0e1c020712020d11061b16271e050c0a080903130924080601030201090e0702030706020a090b1810020a020d 65
    0x1002101154019164500740c060002c0d00340c81004030f080c0500d1418075401c082c5d40d100f6070300e40c03155840c2c100411805224021020301680c04c84810300d000440030b030388510031200302440c010621420340110207003002c14420a506003a004d117084440311617030510601014020031007001c2c0a56189130045000004c0c04840140440c0e10b1190414030350b981c072000c1d83d4103400c0d4408003480344ca40c61441251074454030714880c14010801100440d4054007010709080403109044111100080e00040b00302a000700c0a80d0304040d400a2502801b000c3c43d0b001d658490448009030a07556100044011f00d102c80080518846070818080100403500c0141002c003140c60401d0f0116182074541c0d60401540800b0345840c40340380000800041c00c1402142c141d0403a03000340ca40d50782990750382c1281038038400c0459580006800400a041c0010190390150992940b64501082041e8503a203401f0000c0e8006076401820810300081550325250118019200c503031544058002c040080d800701b501481442c5006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 909968336 1250 909967086 909967099
    0xf051e03090105090d0b0907050906010e06391b010f1704060e010903020c130216032d080411060c0a02040207150c0c1a0103020906060310170c0111011802 68
    0x9804d40d950307504074019503582150001086003400c0b107407103036244800d101d11401109100001940c541c01a16804d5030039030003501440c500351403800003c0c0400c0021001a0305460703051a00820b00207d54040c12880c403010006000c41c141c1d4003900780740c403803840202d10704120807a500d0311030940d03002009030780740001c0c03402c12110f64983c0e2404d80c01a040c40c0c00300c00c1503076107031407100c006065001403403200104060700c0421045c0c046850072410382c03203920500d0540d0780c200b61132000064803d0002004c1003d13070120781150400034981164164055102107000240c0490500051003041c103004000200704940c110301e4170078030340402500c4000085010348100d0340411403c2c10b002c00701d0a64088444001c0d010042e4440c5000301400c0302641c810151211f20003840000411150515554145c94005002c1446a0303100020000c0a62000703001400040900000090781281122104d52840d0100c001c0c1c10824200c6c00010807141009400c82100e0381004490244803102900d002c000c0354055072903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 909969586 1250 909968336 909968347
    0x20c2d06071202090f060d060303120b0307060c0303020c010603110108092b140301060f09080304031a15151c2a021f020d0b0d030f030e070506070f051e03090105 71
    0x30b80304c58001170780c4e0381c01080c002010320308019030b0352090007624482d464068910380424010700456002c00b55080e01644150018840b5030f0061314003505507486880e001d0715003a1120101800d41d6465030040b03ea000410f40b60044560b000021a94408950402000303c005814841071b2a0840500e50100100592000c401090312074242d541c9550314568a580d501d50f5100340c0100705c0c07094a0541d81c0010640040440c1c140c402200312800c60750041040c0f4550035114800c924001005866446489000c40248126880d000c100b00710102a054001e500c4214403540724000703a1400941b56201480c0005464845000702c04e5001a1a100980c0e99505604030f40140d1030700c651080d001001c020440258581e085058008165504205e0402c1c480818000305218040c0b618690040104110004080f00d5a101e54810147c41e2080f00c2160012680c98000c2040d56112103000d441890110385036a01f440400c105c141c6500c032210480d4040b035400300803003030307202c0c084c00182904104000a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 909970836 1250 909969586 909969589
    0x901051504030b090c010216060804082a01050a0507020304030308011701090c0e090c0402191110021c18020a06050703201b0907050409020904020c2d0607120209 71
    0x1e0340d010310b602881c400c440d410311088031551841141d882038010700c101144141c904c5041d014207411100c0319100c21032241c50756510408250001c2600c8010700c0d4401b4011b01d0002c1c3e950f40701c0304030b01403c0c500000b854280414104c00703542000b45003605541c010402000020782c08840310381111421340403142d1400180003010f02424403d0b1340600002034003100810940781c944102d40c09800a2070848405606000a00090340240104d403100100800720061805028070451a84112000d080d41c90b42400c400108040303800556030310a45040d00600c844031030b0b0591142c5032030740c0004401c1402407821640041c0c0e000c00c45000d00401c001000c0340803003c05000c0c56101016000d2010030514001c8002d95240d92807002211401c40030082007a03140321030900c0107505000e02c82580e10700d0301e041d085c101e682c0040d50000001c00e41040c0d080044040e2402e040c020351a1107141400a0b0608100c000a4a4051000031465409580081c41806130311900400c1030104900031100142e182d948000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 909972086 1250 909970836 909970879
    0x1a15090613020d0f05180606010c0c05190b0a091d06030d140403060c080a050a0b01080c1b06070302190801050102060601080402010e030a0b190b0d0b04150f02190806090105 76
    0x10203c2c2c02090034170050118013140c3e01800c50b904802d003401c80380c060352072000450f81046101000f070816048600c0c02e001c0d50510007001c8080c0c40714105d0643c0c1441d542c02d50521b89030f1005503001c0c0041c151042c240701d140003114126207511a00c014409890030220002502d0f25200c071100400d118810382e000388515031038002d4900070341c0c00510400c06640b500002408a00040741e8a2001c249800e0019078481c00300e02c64042481e906039144040da035199040c109050b8040070b0b05490000c00d0301c00c09500076000300b2119220b407001d41d90158031241107061051b690012030241101307010b407407070041c01240d034000b5407164400360910309044180c584d400180c8000101680282c3c040c007403031440c030090000450056028007403a81c3c0c2028841540f044031012a020702e00510340c00441d23b5a40008244c6041c0100c2d0403a004100303006680001c80e5941e42102c1170207070010040f940100d60006004410f85420401c074100d4189101c00b440c11200240c201841406802d03c500186410b07101720b5803011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 909973336 1250 909972086 909972101
    0x1f02090127090203180a1101140a08042402280503010b1c020903010f090c05010c05211207030f0f05070509040504050715170c0f0307080903071a15090613020d 70
    0x11400c1c3e51090609051491405000076495808241c6205880703884032071050803224ac0100c1540d44800a4031950b6842c480300e000380f0030607142041d14481108100c140e510003440000c1102c0c00b044070b204400002c484080d1454051041800301c188010001030210004450714900c2c1c000d000002800201e100c40028003802091540661030880c0700c2d41e924159030b210000c0c0301e000390120120300780d0b6403004552080c681c40005207030340c101610801d0182c0701d600210100340210b00f01a420104c00502c10401c3d100200d82c0d00c00001d13103804003904901c80901c51050201301c244414803041c9001c500161543c8900c06d11103010f0b5031361360700107814410240103a1001d050316a11400c0b5040e14240c000380088100f00158543c01c9404000c103214a101100f12400f024240480c141140d0390740600b40da40c0c0c0d00050511204c0c3c04100b10300c60000d00a1000450307031501e154010203143c02c184100b641842c03120400e2354062142c0c54180f14140e62204104840c116800c0000741c2d4031000d101c59580a80b2a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 909974586 1250 909973336 909973381
    0xb1c060b04090b0a0f050f0114040e070c0b0702120a210510030c050405070c02240a08150d030914010504050409050a1a13020d051f02090127090203 65
    0x3041c0419070b00785941003000e203000c00b2510f044401e51110b290000c0c03c0407a114a0364400101c0030548059401202092a003012107010b0f582820703030700e2000700f01a0300121130303034400142d0103551002004101607106401074560301c02809100070a544000c00ea03c50b241c5070000348103507520b11140c4504009141407082c1400481801142024074509002503120700044030452003c0c02c000c03607181442c0c4512031040c540b5598440214059800b804a5811000c07015a42180040b081c58a000d090000401d40c4080c5590f6488161074000f1800c000108a03a4000b4814109501c0300800300b40d2261010058420401400e00218044801601c040c8141d0b4002500a820b00c8001401e100e0301082a185440c050352400d1421100701402411040e401c840c0e9108075010300074900e000d17040494038032408070320900403110b0f4090800f06844800c290030b055004081d400040552003560b008110b50a01d10340c0c500507124104501d081845851001e00840c01610742c0800000c0c440d0402d40d040c641202071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 909975836 1250 909974586 909974609
    0x6080d0e1926031306111624110c06030a0e010e0a0c06170406020901110102180415050307230d1a070516030c02030f01181b0b1c06 58
    0x3075a8122000d5040710000382c0c29807900d101080d40300d004022041301c9142c0c118591190b44282032800a844002140c82c0c030405074454007101d000c1d251207040d5880060040b0655100180580301400341001c408480c4840402480d4410f0f0b01504038001010032840760101d03407042d00ca40d9400c21140041c01c0907200c001c5d181d802c0000114040c000440c8801440b1300a203c0741740f001c5d0300c4074025200c840c40400c01010300302c03040b800030703000c40d560b94040c001c3d01c00140b502005500302042c507103007a40c02800c4010300d28a031110001082d4034151007885a00952045c116851904c0c050010b6240e004501c51842d003180c44000d4010400040e42891085000040c0b0710b64011031182810310611681c03203d102414218030001c2004940600155101d6040c4404082d040c06203569049078942280001240c03d8442c036000200b2921007070060001e0b491500070090b403080d901d800c1202d02101c00c40c050b800802e00342c20b000c0c0a00c0c01d42c41e049900c1a160850103464208030194264000e20460340302c1c400804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 909977086 1250 909975836 909975839
    0x8031005061206041e2408011104210c090e07090b01020307031214010f03150218010c170c0c18060a030f0312020a050a020c03070605091018060c05060a06080d0e19 72
    0x91440d40c940380c11080c072840e040001e40d11201048d003262a1070b0000c00100501388810402c03100e690701616070908050a030320b805050b00e03940312900c82c0300b50703001070700f041d900c910142e81240004c00c0454000d0040c1c0c00184000c1c50300c0c10002c2e4503441442c0000d0208242c00c2801003260540d6005840d000c1c58510880300150b940d003080400d0003501c2c0c04129003450f8180c12803041d4146d180240d03000c00040d2040701c02407803034140041da082c1641003804c403000d480d69100f11000c110840094103c0140b13076030160000d41d156004000d5001001162000c040402c0c0e0117101e41500c0d0700e0407841c2034903444428000e14560608055400c604c944001000300d41c000038204950720391103006040c00e03000d0303502250315021085003019220103c4c2c0c0580030010301c05121310035862900710781000c0040781c43c2c2044a00d02c4070a4840d0540c54949811640c0824030b03240c000d0b020804100300203940103800903810001c0310309101384a03496a00001043c42040315144900ea400da46406401e100064551162000305 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 909978336 1250 909977086 909977111
    0x902060a08060907021f0207031b0309050a081513080c03030408040e070e01020d12060b0f07230601060e040e012301060c0308160309050a08031005061206041e 70
    0x91074200c03409801503460b0008541e1960001490410404512612602680d0400c1c1e05030300179081751801b5010000c50021251041d00050315400042d4002d41d5008052802e01e41400300488040d80f04501603400303501080040d00404c0e88031030704940140c041d44443c0303c0a081c82030843c003a10740c000321140000014401005001e500810440e47c1d0309040d8032060b9076020b800d0324402c070801006809600561010140c05100e100110348140d07180d080018081d0b107400821142e0f4102d0b409204e08020005122001d202150211398800e004040700b284031490220b0701039844a03810706c12003003030044085410740d990f030369600105213034a07044000b0403c440e4440000807803960050313282c2c850500030000109907284128940003d480d019115443c0c2c80c3c81d810f2214414040340d400e010105940c648170311300010300c103011904040d0f029901168480c14060028560501079030702c058400c0604124070350031501e00075000c0b940541e040350000303105c401c035a074000a42400c00d88903025003403038001180d001e23 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 909979586 1250 909978336 909978347
    0x903030f0a09030b0a021213050f072606011503051003021f110f031b1c05190c0c030b0402010c1403180405060a17100228090e1305010902060a 63
    0x44034059101410282c8440c03003c2e008900c2000c0d003401f000215000018881d42c02c3c102d00c0c203070182c132420407141c0380708000c2242c601b85040380e00034014030254140d40440038140440502c081e014904043d054651401d011102c803030140070880d02c28076848200080b00582000c0c8a0401190040c2011740e40c141014540b295103464440c11002103298540b110140b40310020b00c4041d14440c1e20015854284650203440b408c1700421144051446586990340b29941c3c40704807500d01d0007194441d140c482c1c60075000902042d11204490b410014100e00b0100822000401102103e41002e02c10543e03484038001210424035080c40035040d0500c981c0300715084030300003009000410035003007800c21042d078543c100029503001380d48207a40555011001e0181b044580c15200f10350302da6000b00e6241c04000c40001c4280d03005250b070000c00e040b10b003540c2c00c1250082c40f44c2905651080c0381ca61040f90501d18140c43e070a40180075020104400d10a420400c40250300001d007041e002443d040d00c41500364001481b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 909980836 1250 909979586 909979589
    0x30d030b01022401090b0d05010e07051e030715020102070f140c010e0901151e08012105100b030111220b070c030803150d0309082509020903030f0a09 66
    0x1031240021141c4460000d030f00545000811182d0494030303900c1d0007010700c00740000c01c1c415075101281c8020400050f07824131601e1010b42c900c9020f0000d0f90310300340c04c001c20b4074100d000e20000410703201c0d4428000d45d000300320a410b40d00309003683c0c0c00d040316601e800c0340240500703800240311404641110090180403411480d5044010049900c0c0f1a43c0100442d50585402d0505400449500c011f2240c0003032141144060451850065403c07160b50910b442c5142c0090700f83c00118030751400600c010aa0221000d06020360306402c5000f1036065991700d0343c0c488042a500c43d40310740d00c1c500c0320344030741d8207421180d036400c1d84c0441c0f030b03444503604050f074020700640885804130210564800100c8542c0101980d00321758000484602d51032031900c0d032014507400100080324010318030080030101c0e035480d40502c10081c06075982c02803041c2080308030303840e01c8100d400d0f14250103100000a8201c000c181d4030681540c1d8025800740e01c9069040c0070a03d94011a05d00c01c070840702c0400c01452079a40803a0010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 909982086 1250 909980836 909980839
    0x20d0b090f01060b090d03230a020c0402090310090201140d0b03070609080d0c11040603050604030305061e0f040906060b0a030b0f100c0203070e092508060106140405030d030b 77
    0x210803000107030341c140c01c80e8040d200350f0200c4d8005011908003480c1128441c5280d601074140140250921071661011610400400031109408140c0d1090940e0421442c40281400d840441c41c1c101e04a000a0340c1d0039202224080c0303140c03964818021640f04030102c120344041c40b00410b0b1188032800d01800030f0a00140014000d1003823020005440384030341c100c04101c0d56a0300243c4039030bd00e501000c032008007080c4011340c6c5585034a09811031a444d280b013004c0040d40a08090702c00c44c20503203401020b80d080030b82124441e5a050381103a04951190f500700c0900c40045070908506110400030501074143c0290151480e86000c1002441000301c00013401c0d9030859503400c211a80c00041002a4203810107240b0703800c51400c0d940d000b0f9050080310f0024903140001d04079a0400d83d110300500031602c04440c54030032900140c2c04980d070250700c2d1641c100310980000606106600f130940d250340c0e0b150144514000c0120044481e4101c400307100c100c40240502070309851000102c2035016003d03054001c0c221307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 909983336 1250 909982086 909982093
    0x1020d0f0e06040b1f0503070e15011d0402090f090901052d010527010303020327030c04050601090801090b010612051003080901090905010f030209010509090d0516020d0b09 76
    0x1030a00c41d101054603842558498030a0416444508a41c00c0444e1a08020160110410f601285985d002c0001c00c0090860f80d141c03040c28035203c9010f1440c00d002c03032003240c1400026440c664054030002c80003641c651050714010b84600c0c0340c4000404c06510380302810380140c01042070106002c4190818be02c104118075240000e580449086840c2400c912040e4064050300310040c030552034040c0a21604e8150744601140c2c1d50000305854800300c030282e00440160f400054081440549191140760b2190103c05c2014020704d190301280d22486c10020852290fa0b4890010301c4e039a001e82043c501800c0c2c00c40007041180d0f060300c0d01180440e003c4c090000481c16140c11004858954040c0030303c00c0360032002e110805455955443d6040e00f0103010241403000928001c40c089040303104440c000c005d9002d07564541460350043c804c8030b480c1a0002030081120700200040c5150020b501c0800d08201d1621581d640341c40c58440d011540c1c0d024000f9880b40282e00c89405000b130111500d03020712034002c1903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 909984586 1250 909983336 909983351
    0xb0a0806010f050d0b16050403200906010c020a05040902180a0905011d0a030e0301060b120604060512030a1b0b01030b091005091509100e0a050d091a090d0501020d0f 73
    0xc00c1081c015600340100208401000a00a03c9444814022060b01c50800c00e0600f52241d0f12075648505020062b00003407100540e003d51403420a4410303070010000c0c2010400000560082020503070140038503400385440d824107004540b44d80c0c0e00480a801c0b030740c04d5640b507405e110203540064004400e0980d59503007005400c1c10100301c01c02280384900b50060007811b40340d095035015580c2c41440c50b281d5030315568610300011041007110091211800036904010340c1d1800d2404c110465006401050150032034a030360003100b080000448804001d1410a10050b200010003481a144683c0d0014a4046010000000c203c0503c68050003002003609403a660142c0c00f4800381100c01c02c0319035100642c848034030b40e081c00b050b0800640d0020322000035903014400200815040e00c290f0a48204140c0c80080c070034092040034000c05030154803d2400080c1e0074513180b50640c0c50383c2219860381020800040500095a4110b030030001150710030002c1d912628100161401442801803140703e49060021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 909985836 1250 909984586 909984589
    0x1030c0506030f0721020307090503100509060f041704090207060b030c06190c0203060c0a0210020a0504090c0203070c032f060a0c0c030b090a0c080c0a03060f0b0a0806010f05 77
    0x940744102e0001e01c85024640d110581102c070740f52003411000003507165000e480c0d40e41c90b007800203510a08c142c4e299176800c186041c0034145000c0c50b412800100703610303100074005406d00205000744c20014200c00445140c03160300b407680303094401b0030214010182c000342c0000d000d01160003505c4010700500d0104082d250f10b0301419111141e001c07a0b981d00410811201402001d80360518842040d1840c28100314a15940400d1034500240ea22002152000c210107292036410800601d0924800c0703025410300312000030251250050340520680b00da10740384402450392003041590882ea420101c284001956820300c4a4030072070300041d0440072005030051800071503410550080042c0040c00d46454403503d4442101c421020b08401c940c2c1d095a080700101046001c41c2c118002c031080741c01350070310403100d207071400042c41258401e00544e00501205449903440c1d90b805401c40c2c1d00070402242204007040d0100090035035168803540b00861100c0031a002c0000107a05050700c4240d849018010b48440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 909987086 1250 909985836 909985849
    0x7061b0f080106050d0e0102030c0405040b060a1b03050c03130603060918021903020a09021809010305210d020a0e13090b150a0b0a0e03160b04170f010e0601030c05 72
    0x8056002207a4050300400c00c443c481d00082c403041440700c8001480c007008444003800c0e43d2059031000041d0401140510181c6411f201d00c2c020f030031003222000d103011580f07034024080b40d07005030864201c00150031884041c103004500b154081c0781d10b00140c964441d150308900c51503002d18020003000910b400300205526030f0314890080001c4003004803002e1480d06a08011030503e1103019203220f004038810010060700e55241e2040502012040980c0f2080004034a121100b402150540700344c0303442d4010004200c0101d5203020809031341c8402c1d880c4203810642c00ea01480317202d40e0100894800141400d400380d119a81c00c0c8503070012240c00c0c2d0295010b4041c08180d590a030b8000d05482030300f42c0070030440c801010950641802c00f424018002c2e50750075030400c17a0303001604000b022078505958000c50303240511400c60503d01c8066410038840c1002d065030000e0140307014525222583c4400c02d05000c00401c62200703920348081c002d000c0100d65503174040c0c61714028401280d01480c0781902164525150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 909988336 1250 909987086 909987107
    0x50c090f1b0c0705060c0102041707140405040809040902010e09280218120a02090112210519020a0209180d020c03030a2a0c1a0306210f0307061b 64
    0xe401029600d0500302041146d0f03101000d079a01c1d40d9030030080020b00012034000c1d800551550030140000c285072048a14402e881016a54411481c240400000800d05000d44141079403ea60005040c903092005841400c0c20340c004580c07082d080c10070005025a200c95164070300c811070303504a50078143c50001d00c041e401803d14040689090108460103070400301c101c0c0ca901c0001c0b800301c0d0245400f680200c1ca03000f40a0300b14209441204840710240412440034006d018502c01c0e4a926542100340000c00901030f2041c003025443ca41d035015404144208914403107160001c3c44020141412683d0b81595000f40c1d10a43c40d6004600301c4141031400421000d0602901401451500c80c51800456000c225550703464038600b9072008d007140031100804034030405031040e02003503429420a941100740180c003160744081e40c0410810814240c440c2809102c9042d40303005214510034885103070b1390424a0244080c00248804240c884c1440300f641c008a02416000206005c4000c100b5812144480369 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 909989586 1250 909988336 909988357
    0x10c110105061e01020304090f050109061d01060e03030702041a12060f04030c060e0f010b0102120f0f030c040e07050a03180321180308060a0509090604030804050c090f1b 75
    0x1640c1c450919080f2103003200a50f9052042d24900750322590164110303141c04400240c055914001403001c208207209540290480c0303404500c1040c001c8142e961000014001e01d0b08014454100c110642c500b081a234070640e9000300f0a00c03181d201c011b00480d43c100f2030311909114001e02c48062078441070110310345000d8410070a20302010342d920784003a202c00790307450030890341556120300d42103c8100c14010908022412000425503e21507000285442000e6011000d0554104407000364000319800b181d643d51136645c840340d220380d0388400d100704900035a840381c0b50064000c070801008680c010010901506a52010008008041c1c090041d03401d0840700107001c500e0268070b1440202040005a080710100c030400708005040303030422140c04040103003c5000ca1541400e216440c034101c600324018013020b4680f2410352400c0c41c0c42c6a913410b40608041c00380100341e008502444010b0010000f54803002d08460010700f04034000000c1680d080301d042050109104c0d4020b03001e6000022070f4100e288 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 909990836 1250 909989586 909989599
    0x15030f0c0406140705190311011a240d0c0503010905091504020103091b091a04050928022101200a0e060409050a0c080702030910080c0714010c11010506 67
    0x4850300f10055100c44020394040c81680044903003080f080081e813051610a60300c2243c642c200110031405c0d02c0500c19013002285d400107501c00d45403035000408500a00c40d68108584001d280d40351891481030150b03003050f036401e288250354110b820000031812071311009410019640c1d500c42c0d068999180404412441c0302c4440440c1c0590311903040808028054455103c000c03a00c0c0c0884190f00031964000c110441d2a41000c0300a8007101203410350501040d0f4050200d4500040440d031a0130b07c0703c80003001803201c0f1120500780300c6002006540c19501070450701e21071114400c2e0106584031841244503546c00d0035000d07076400340c02260500b000c15210507801d040101b1303404241c17995924101800e810403420b0100003000402d80c021075000c0e520031040082c030075451000003080080010017410665100700031624454a54203100b020082091a1140071038840c0d0886801500c91300b6806406000034440340d10201c4419484844508502e032245e65424010307800c5c050984a0441b5115030080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 909992086 1250 909990836 909990857
    0x20d110d03050c161128030f03140d140105040b010e0405070c050a06050103051e0d120603120909151d06010c1401050103050d1409010c1115030f0c0406 67
    0x74003a402664000014450003400d0101603120100c0c190104401526605500d81d50000e2030b00300040305840030f40c000302040d1050720490084e0102e4240901c401011a6040d60204007414810442044900c00118006559a00c5a00e04101a1101c2000c011154180c4000000d039840c0a00c038540d400340c1d0607103030019800c0d2140208001402c00928200600018440c407400059050004400ca40c0c40b07500001415415400d082e80351150390311550600c0d002c1c0000000e5441d400140c108690b81b80e9140c03441da6107480003044406020503500041181092f09460795420750401003140075200d0b441d40c204201034404840c44528491171150035011090b40a07031400c80c000000100c1d500c540c060500480c1c415450350340000d032100c072011030700d02030359100010b000b0400c003884001d4103035401c4e20b032150303051251044200c0c662043c50b07407a9060081600340041000b500d4842c84c0c0ca120700062034201c010b00683e43e10301803035000700d885496045101000480c4501c3d2202a107060700c0f60366503401c00b0074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 909993336 1250 909992086 909992113
    0x30b180d030c0915210b090a050417030c0315040b01050a0c06091b09050c030402060a110c060406032403110d030c0c0308041509081c050f030106020a0201020d11 71
    0x42c8111801c1a082000001c2c0c00b080c5000a01200310440880fa0340c0ca2004100030340003404560440400041407a007841d0801c0303041e0b0790300d004503034014040c0d0b6000191500d41b0b280c80d8030617070320300e05075041801c0c00841044403040c45840a5441003607401110051000384101300801c64201d91099404142c0038000c00b50200c0c46a08002c9059200714000a01c0f9070041e1a06407030101981e6903800c0c0c0700d0827a0420700120744240581030300290703802c0c2c0d03003030850421350b002a40340c0c02104034090400401515490b503802d0100400804d138040604403030740c7d803900d03014001d014010380c00b0390740484501d801c61003808418002810b0200c90b00320011031445110803081100142c2101030540811010110040c0410b03009611306005602c01d0030320b65030702c81c42c2c5864a1145040150140240715803a503082007400d502280e5898a01072915002042c107000700700c1a40d05010b0280007803407100003c4004035065400045100226000760201d07002d0040002c0c00b1210720007950f0040ca12a0011400d42101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 909994586 1250 909993336 909993341
    0x303043e1f02031b0708010f06170d1709011e0e0111070c140607060f020d05060f1e03100e0f0601150e19080a05070e09010221061c080301030b180d03 66
    0x11004213009552410380d03150401800d5600c82c2d070100d0b034000d40e00c110401545c401c0c01c919800ca200b802002e040720440c55480a01030301000c400703607000d43d0a1140004c3d8650002c4d404031446c001040040f0403c041200c803650002c28040a40d0078084d0300e0144461080d000030b009403003000c0d51050b12284660305002c00b100c8882c1c07800b4080ea400550602180000aa00d8014032540440e034840040c0c4584042d24440242e0f84050704d410f008003440705400b0b4490302c0340140c002d0b41c40069030501d41c610600d0310119140030175130303c43c1c0c0b420b092401c6107020000314081032802043d4043c1c03049801d02d980710401070303194409120600380400c1d0180b1030300e0140d042500d85e5480c1c0085c12402c036078805595880050505050f14821141034200810501c000d00003040d0158115003107400860501d075540040c000707001d00a69024115908581c0000da099a0b100094103151002d040380c02003449243c540b004940e0001c0c00111012103600700080d010360810400ba659900d902c400802c028003a50006400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 909995836 1250 909994586 909994627
    0xf0106240c050708060406150501020c0f060f070b04140303090a0f030905100f110d090e060409021f0f020303100501050703092103020c10020303043e1f0203 69
    0xa2281821481d80400e0042c40081c00829280028014a14041c64114201d81c1c95004001050201070414405640c0c001001300703200c201a101d8500c5c2100c0030f4001003050007a001040714400001407000704000c000300025004030b109540020020001d4049a42c60340411250b0450503481a5680408110160140100d2a01034102048040c0e00e980c0403c040d0701c1007110b04004a0320440000203d2036101c1041c580c2142c0042c0907007000313179454200501d50700413841075802326040d5101144840d60380e40d0101e00520390081c0001080311110b41e46c66004451000c40b000030866514110000134008411070b8801e1902044207502c00f41404010350b4160000c40095041010b00300c0046a405180100c1d6840290050b9000d0fa00206a140003440c22118805507405009103110070002c264000007a030b41c0050b40718455501c1a101402a4210940d0800c1101d94030402c0341886d52004c40b030781c4d6851103c01030580d00d042e91440007002c84c200c0c0c60110703003810005038010440380c07402a1301807000c1d99 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 909997086 1250 909995836 909995909
    0x3050906011a0717030c03070e0d0308011a0408010c02010e1006080309040504030c05060103030815120616050c030a0f0305010816060f030f1a0a0e0c0f2113050f0106 73
    0x204e680030320403c51502600b04496540809600009004103650002c1c1030000b0301408541c540c940d144240c0e4000c14294041c480d0120f981d9400e20100390009841c8251805014044001c00140403001c83c0240a00000b2110100c18000c00000c0c003c402103038003449080d40c0f05ca9004510700300c082001c5c03000510700204160101301d80202d1000014105101e1240258040d42d0360400505200700f100b039821004500e0540710707034103088914102c1c1c940805c42c2540720803000149010310415102c2a500c1e4400c11409800c079000000d83d0900954002d0340c25005620740b540c0401c0b081c1c3e221015035035601c030b80c800200f0380c00c0080300040128900c00c00c0380c0e807150603140c0f402051680581c680340342070300c0340c8005130449180000d81c50525800d28024440043c40034191150441c2800701e0209098031405103440000100001d90010200d20050024541c4600921981c0c45241c003c501032601041e4075170441e00fa0040c0b01d00c500300c1400c140a80d6042e82c3d00c544217070b540210400c03007001c2c0302c03c00c102214 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 909998336 1250 909997086 909997103
    0x309070b210406150602150a2331021f0e0a0e01030203060f040209040b253212040f0c030b0a050601090b0f0703090510020d03050906011a07 62
    0x1158041c1d569400710701440c0f003110085900c8000e044100109645900035604641c88105410310b412001c0c103090b034006400d41000208229901e000c02d00c130080c0e500c0e4014842c0c040b1800d02c1504060701c075090320402244040d41052504d0030818441c51603030903a000c1c1d841103540c6464440320711049184051a4820304002c403400c0307111030128548511a030301086c400c107510b000400c1581028421181d001c02881c4081407245440d60024400c88405080074101501c0300c00001c0c00c0d2120701307401c2c1800c0e90801601d44a1800003107001030681149403940505500704284a0030704555120660044901c10700c110340c20f205815050030158100200180d60b950540542840850203071945a400346006401c070011a182c101803503c15a18068010b504000c0741d1202002000d680c072050b10416010030103520f550f41d1507418211001503043d00600e50080c601d54080e007449800040751030441d0b0080e21b050103159285030055171961424401d02c00d800d410780c060a5000c203008170007802600d2042e000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 909999586 1250 909998336 909998377
    0x70e0a03060c090510020c1503090d0c030509060415021903050a050f04050603040506101d06040902010e10080718050603130206071b0512010b18091e01021801050309070b 75
    0x248900720300300205c405604401c4c240780780340c10448d80000c1e040e103542051a1035401d0210540e82d90369103a118940411000c103c54a0804d8455001c4940d140d17030080100340c480d5114640019203281021701503015106a10021119030b44640340000d80301c2e01510b686080440d40c140c141e449a120440d9004040c5003040049401e039240c40107903026500620081400d4680206500080d21044d08a0520001c01004111880350034080c4140d11840c255030100340780c002880181c3d1402c45503081c86501c5000c07402100441030b40102c280d4415400f03a55502004080f0707500303c110040080c0156138000c0c1c400c200060301c0c20206c20000c4c1e50144042c0685292081945609083c90b481403417840b51030040c10300402c1107160a0302004504040c0d00020404580500c0000344600005101c0c4031854034080001851100240425950069800000c0b040c404040d00918002c3d400289070341881c2c0d40301d00700307400c40e5403158007a240b251820710000c0a280342055120502ea07040340286180c81401e8084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 910000836 1250 909999586 909999589
    0x61003021c05010e0102040e060d120e04092f0123030718080f0709050f131112030d0f0e03071511041410020d0c02060d06030609080304050105070e0a03060c0905 71
    0x183c5204c560800000584450500c031004080803000b8000c0e40c421448100c1003004210301c20110800080342c1e04012020210b207102060241c6100c2801a142e04844076404620100410100c14108400c04078200300000100056600c481007400200c003202042041e030842c0c00741800250381200c0c1034281002000c104062044803c1a950406c4c026600810719a400c200000c000c544064800b50005118034a811810b0300c90542c001004401c00c102d40d40214002d02000143d0640500c401401480d400c2014408559803a0722000b16020240d03d401c00e40728450901d0310a410315417001c02d015625113045a241c0c5201210150042021180d0703808001c1c024101d031100038002070151007492146082080100000320502020398015504030202c2c00c0001c0780d02c000900c0803580e04a92030303a00d500484941d4030040000d500020032840c40c11501e04144640107020b14410b42c4250000d005961314144100c8001092250854110084400500024465030403a0000d1015440e166011654400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 910002086 1250 910000836 910000841
    0x2060a180e0c07140a21140f190924120c0206040201180f0e07020607111009050c04050f0f07021507260408030a0e1b010c0302030412051c02061003021c0501 69
    0x1034420070401650703070250030400c4c5c01c5070200310403106081f41c440c100103240c2001c603c0c502ca140802007520040030040b1916501600c40340024003030942500e5000c62030b8021410700845082039080105284186902403160140262410025594082d14845d01da66006540c10008002d41a030900b105000115842d808001d1100c000c241c40b842121507418410300290414402905070000c01407440007000c2c01e94000611b00c003e580303442c0f10000e07600102d800e0060800c12006c150550050500f01071080c41001e0380c4082c0d015040d8400820344a840c2c0390002d90381c440000003000d10b00700c04000002c5185014a070944c0490030701d00100001d034094100300503041081218101e903451008030901c84003042900c074114a0300000002024503082c480010144028140320284c1040f816172040e00806109005640040144600d0700d00301c00781a207040c546503800c81705018100c906e0058603840151000500c1401110355410b07008182e8110780a002c3e84842d03c001c2c140740312180f04c000070000386003403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 910003336 1250 910002086 910002113
    0x6120a20031605090612060f06040c080702070e18061f06111504140303040f030f050901080a1109060a0503090c0f010207060e040902060a180e0c07140a 67
    0x400c210169002000c0089000c0510003003914000e07849102185001410310a000b4207a41088800781d540b41e48000020303c100d1400010740201e4003c5000b8030003244511070742540161412101448011013861080300e40032001c58100380181c2c416807042109620080c0c640350416004246414170081c80f41d0340700d1406406461444c0c14200950b03840c518006c0003034500c13001d0aa03d01d011349100e0b5641d11403540d516205a0703111000741600c0c0109041010320040c0c080285c400c3c0341540d85910305030405a40801c0003840640c0445e0104955032103c0c3d20400481e54a860140c550715060348501707100c28002c0134106402000d0340b4003004002c00329a1180060044011141e03102a07680c90888e01c82c0b03052078028000c06015081c1c18099a565070780205103541592403034500a40d03600d007000001400b0f0110b0190103500702c040040c14007202c80c1e0000000038040720900c014920075a0b95003c0c0c1e220183d044032924074540c8103000090010f0b01c908064440e040c4c611003141c43e010707915110082e81070b801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 910004586 1250 910003336 910003343
    0xf090812100509090304060503090c120a030f030b13181502180a060c1b0e07030518160b07080d050108030c1515090618040c08010e070f06050306120a 66
    0x50042051464854081c04080e05090310610a541807421a0315130728091ba005074400d00c44003000243c17170700c02c04002440724200d00030001034070300322926202a1102080c1d001a000039018544c483d640c0c2d4020300a1003a001c402038910952a00c4441e03d81005110500c608290b203400186d80b1004502e580b81d046c1d050881c034190042c1d0780c02080030380d50310128610b00114001d0241c22400c0042d144c00a076000b0002e83c000c03040828090201c04600440704c0140c01502010001d0310500103019815804640706802031600c0e03145510840d11b11558a17829012060404402040244a80281e880141074000c0c172035000300341040c400f02080c0080d10004d8101c1c2c4110392021480b02c0d824203040105481580060914105c9403c03c48040400380e06100c0216015030452000300f269902d80205900d10307041c039408205d00c2801c147c900f142d80140710b40b04260a40d03017402d100340a02c0e4030104440c82203230002c0c804a0301a80c41c0070410f07249900003c1c0040d910155484c0310a604510921a00040501c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 910005836 1250 910004586 910004617
    0x1412100c020304260a03030b0613080a140c090406110405091918150203061f030b04150f150509060c0f370516090e061312030f0908 58
    0x1c043d8071180c950b940358100d04c060901c44501c0b00602d900403e110b00141c0d058540403966082480106401303101c0c1d01e00f0403403028544100000e20500108004594030b00c46c0080d400158010ba0100341c1c0c901c407284e4100ea0040b2501c0c04500040c01c0c43d4071855020301e40c20210342c03d0558504c009030106508845042c0b010440070602c1516102501c40c0e4000c40f07000303401803000309409443d5402e0051802e4130300340f643c0c1d5001000c46d41e259a680d081405401c00403466071030320180c0c0e0300c00a01400c20398004a001d142403120303589070003601d200340ca001d40e030300715a02401140c9481850700503c4070f101c01d040c0602c079082003280042e840388402800d55200392001060249600c0c5040c0d40b410145140f440c103c0d0302c444001c0200c40c001d0180f041c0b47c040120b006d42d40740c040700e41000c904258061031a1301401a680500069a42e17080d0400742e10180c0700f0069801581d01c3ca00d0000722008404001071146170f440c1c046048482c040e6100d0140f800c40b10000046280342541c40034015803154491004801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 910007086 1250 910005836 910005839
    0x60605040f0803030903180a0b071110210209150310030c05031204050d1b23091515041a0405040f0c0203180d05030a091a041412100c020304 62
    0x444100d074070005100000c011031451600400345501c034081c4c180f9501e0440d4500c0c907048890b580e082841d0b0080c21980010940d40c2c0301e145040d5141c1c4c00007003191405040030420b8403001c140940000c098501d520720740b040c44400d62034189002940141031495100c04070407542030150f414880030b98441e900c2c588900440c5421400c040e1b01c07411042c1d02592181e4400d0000804292420007900c003200c20681791241720980c1440d12030103514000b01300c010182d0000e0320005a0744507010100302c04020082c003001d2080c0f01c583c14808402000c03590051440703450100c0740d40b28102410903c4250000b480d03804d00b46031f02c64010b204c070350000c0f4984105140300418103100a182922407001400e1305103808210410141e90069102d00441c43c05400c40d2081d54140c0e107840e11007210a020750365000054940d2000884009403984031240502209181201060503c08400104442c15100c0782d00081c610259100101312100e20200010403850103101c04101400c0414015050124480e802071512107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 910008336 1250 910007086 910007099
    0x3070b0a05040206070201080702011b0203041811030414100903030501060818061503010603140106140d050c090618040b040b1612050a0e030f040306050c04030203190203010e0106060504 82
    0xa48016141415952402060000590395402200c042c03690a0805a8040d6120102030380101140c14240c201460b035408117102c002d5011000348161800c41d400e110085c0191404402200c03050b000710650244200040b40100d48040f0800c0071122851f42200d60700d40300d0355004c8054130b01d8008124086510303140113101641e0003e01442e448001d203044507160707207c51421a0fa40c0c07440070b000e01c10940c440c007600308420b0702c0a400c81d00296030400b560b090108110007405000300761a1007444c6804103103100e030109a00d00f402c0f540ca140d0350808010201e141440040141d0701b00c002d48200d40c051041ca172020503c1001c030b840c4910490250003020316030b14040c00c00a80c4880020400c511400c000d010959102e6040218100d030b004007000002415035a0124044c01001c080310b80d0041d91101040c60405600c15400800c29243306040c24056520344135504881c4e03005d9401b000350f15404c05150b10300c0340000701440da40b803a4001000030807840020700d00e95003124a00c1d0482c0000030b00014050010303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 910009586 1250 910008336 910008353
    0x2108040e040605070509010f030b27011e230303091f03050901020310030f110d140f15150d1e020f0303160210032912150c0f1b0307 58
    0x46142805c04a182c6800b1400090522581c62480414103998920300b254646405200040c1218020200039814446040000c0d00d4482440707a8000e4030110030407070408854400d940c000312005110740381c0000c00a005140d00782081020420742520040c0080c00d0235075039981407800c4101e1256090b4103440d50607a00181076a600030003c42c0c0c6a80104148150b0392741184220701244c3c2c002003500e41d401c2807482c203400b0015941080c05da2045403a44940207000e9468400951851190120b902e0501c110603a5a00d0780c034080550340c80e5603910000900b5584840002100040006040700c001000319900d001301c0348240942006c0c549003004095003103042918500400e544120000c50608510f5030b4150108660124000c0c01000c42c164011030203030082c1c020740c1c0c81e0b100e41385050740700001100c00c41d84129000d4994070f1081255075880c031350035030001c102e50b030821400312a8102a6599030300070801c258403100e82c5161554041181140401041d01208044c21016015654030030550604030513 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 910010836 1250 910009586 910009591
    0x60a110c0d2103060e040c06021e03040308030a0e010608030d11130b091903030f0e01030203092d031306030b0a0803030622090b0103061b0206012108040e040605 71
    0x1078000a14020108511004441072441036601c4000380c2210000214081d00440d401406400d01081c240820018a4412501620016801c5039103000203803032408007461321b440f0782c1c0e11903400070001030006c500305100840d403024401601168034040e1030542c1d030841d03502e0380c084c40c41d5800210360440540858043c162084040c0c424403407e1100080340d60350704c500136200750540d40b6000181c084080c0c5881402c098250f6120320b801d10703207540d2410080d099912810419000465103204626558000d10035640201a402d0040400912030b80300c2c1d0480901e1351444200c1c030700450301c1500080004200a08581d580a001005010700e000005016501401e0089115440300c00051081c81c000005699008100b10f84000c0c3c54516480403451412080b0201500c1134206000f02041c80504034400c0c0c1203a11405041260300c25084108200c00310440d01100140c11410042003404000041c201508032100c140000d0402942d03a0403100c2da003c0d60042e015001c5030300c200720604c11140711b04ca5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 910012086 1250 910010836 910010839
    0x120a0305060f120a031d030c0906041503050a061103040f030c020616060e060a0c140307051c0b0f01020f0c060d0f151a0405060a050d09060f0b280501050315060a110c 73
    0xc04440186c80040d071940c202d401030a000d0a00100003641f00d5545070000c6920f958081403100c0700e02c0d264100309403105140c00042c0d4045040402c6982c41c5080f00048030320840e00b04000b810902c400c3da07030454014a400b8400c1e41e01c0202881681c94408804c0b40c60500b06105000000e00100181842030a0080051080392180d16000c01c2108058000403210303d8400e4401c002c0b5a01e503208002980e980c0a8088090f60980550b09596a101c4d0258401d200c94082100c0c4000c8124005004a07511000442200c02540000061501c1e03420524068122a1308000011850f01e4108055000715118000142074030300089404003d400700f8111861805004002003618081c00c04c2c0105120703101d1003102ca420807800151541c802e00c415807003022016800b101c1840550601454400602110200742d8841d0b104640411005540520301c1d91441c820356450300030b198902001542d26801c01801d05140080c80c11091040341c0e1000018094520652603298140c0061564240341c200300d155071a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 910013336 1250 910012086 910012127
    0x12120108030c2e18110a051c050109050a03020a0b0c030c18041d0c12030306090106030506060c0d0206041208070e100302070203060c0d0c02120a0305060f120a03 71
    0x42c500792008103603a0480c0702c3e9a000b103452a40c00781c59200710030f81c112450500c520701c0c09280c501c060020010320f052950203200080c3c1d8011180041009070a0710780704166201075130300c441986c601404041042e626008000014051005803126401c0440c42801217005800108100381041200c452141d0000b01c400d41036800c52810244011007072080c60682d110260b60645003242c10f5640c2d030004122034200c40e10074003101880e0140d4683c0d80d244442401d100b40c00340f9030706058018000040e0b9106030402010f08800d0307443c0017401e400030304019142c0f40c0c02c0b520801c94440100380403c85442d040701140d000380000c3c60f06041a00002e404001200101320900b001d00080c158000900744428804580c241c007800c4d0109002d400030300c1040c1d40250140129010040012801c0000d801d920b40144024010031015502c04c82e114190810b00108010041c00b0a0380b0303480c820303800b4a40c840c100cc3c002c0e824008a0100082040ba200301c1246042d078860031100041540c0945201100c1403c0c9012 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 910014586 1250 910013336 910013347
    0x90106020f060a1a040c0801050301050a02070201080c07030504080a1a0703050412081f090207061103010b03041511030411010f300b060c1e0d20070302031212010803 73
    0x90750745035100039120440300b5848444130002103035503039245503402800074010000c4110040740035200507424030820f482540307000005807808a01e40200c600300e0340d05965240ca01d660b4021400c02c19040b6840030780800c00b040c400466001c1e02006030b09801401480c80e4021204c0580b50560032400c0189050201810308080c0000681171044042d040c155a04200d0100d641328040c0c136029488040d10002c4624040000281c12410355004100303031409000140310700c0102e191940c1080c4070a10410074024010800900455100c0d0038110b80c0000080d8041054a903003404412190010741e01550b418880c0150000d456801c075203d1183d5100604100041403080070031080b801e411000b80000b92440400c901c0010704150380325410216005000c40d850302c110200c0107aa5a040001130803d8490781100d01045403400600741d059a100c0380d81d201000c11071031984403807140051141505501c12684040010f07a014056a0246c015219a003500c50404440c48000944107901c030382980c5c0c00c03c000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 910015836 1250 910014586 910014613
    0xa0801030b071814030f0d1709160b0a020a0209010609170606010e0f01030204030219290708070f02031f0f0509151b030f0406050105040c020c011116080c09010602 72
    0x3082101c40c04030840560003a04c1c0c3c0400e060030150784546050780201a002185941c109010b100d540e140c26101d1166542d40040b40c41c0d440c42030101c04c04154440000c1003241000000080042e00e00b148140c6114400310390115414510030303005100030522118051088070b1300c2c148482c1411014030014009418500300203448410b072600e085000b0450b8440b11401a400f03901218021a4040e0529501c001000c03044101c00e031f070750300a61104901002044403001c180380d0b200700d204410304a041c0d1502e889951901410340c01860115920740099840c10096034060200401d06040b03510242440b20030700c0c2c603400c00c03a41e001a00104aa1504042c440c203258002040401464401218001c41d11111500040d03240d0b13420a00007440030020800022800c5991441e00481c0b1400c01448566281c0301080169440c2d0f59080300164440700d401d401b198804e41010031f2612015054806c0101040e10301c0505071801e820943c0030358000c00050b4002d0070181c8150740180303014806081500010354 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 910017086 1250 910015836 910015877
    0x11b030f050313020604080a02010e0307030b0c07060f051609050105040b0702040b03030702030a060923211905070203070501020312010320130f0e0607051b010f020a0801030b07 78
    0x21124041281c04000510030002849080708420b030000c2150340c5460355400201d6031381c10060b0041340001c0c81a00c0d41396880c20002000400e80b40d0040f803110b4140c1e52811500b4a03a0852203080e64500d4139149201052041841018002ca000d04424400c0c614980d5000d04600c2496020034104101040200b10400340481034402e101c0d8122004140c190f80070300041c4c5140980c501c080e50502801902d1010010b59501480340e4510403c1e9440002c8403482d0301841028520010824541012810451000142c0000c02407241076080c024100505810004d00580c001d102c0c820215200140c98000d41c0780810080000f4402440203501e0007000c680309401802040c400288450090002e40d2013001145990025070480030b001c22811030807030608000603009400451601a10b0590031105c103140100d8540d20401040c0c6503140380c0481d2180c1d001c1800d001d01c040712400d542e641c07484440503440780014281e00303410380d0390b4001c1541142404400440007500c2c2c45e050010f001c842480151404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 910018336 1250 910017086 910017107
    0x50105040f050105090d1e031e120504020111010614090f1006050d0e060a0b130c0f0c0303060b040e091006060e100509090a0203010609140321070609050c011b03 71
    0x4e01c1c080d070f03c03019a079000c11a1444920001000344d03200c0e100c000301d12420340408804150095441c0060283c0012101c41c0d00f0710108500c0d0002810960000c8024200da08580e40151061401080f400002c098442c01c44229030443d200e5440c4040c02c00313603a481d100b54650381004504000303d21031b003840206115188140c2c40758000340840802d40010303010082c1c0c4014040c204040642d44d052a000c1031850080c00c402611b00d1045840b140540e00310740342480340020025181e1201c064078108500240c0704034141d10130490825803280d4010a54002140c054001485400c0803403071182026560b050415011210942009203808010003000d548420401f140c3e48080e00d10540c401c4c14032108681b00c0c41112003803030b0440f59620030b00450681940c0294101c0348d40e80e070f4580400361915101c2030007145030588254517034011441e190122110420480440030703081c1c44946402200d07a940010b43e40fa0304000e0391150030004004a455821403c00c0c2800408582d02400d07610f100c1d50b0180c80300c04603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 910019586 1250 910018336 910018339
    0x313060806030304030b0109050103060e0105040201021239060711070510050921011b09031223031f1503150909210302030f040605090309060a18050105040f05 70
    0x2000c010494640b024400c40d8080d68014005482c0366855429000140000b0710089880a180c261007011000f0184a003901943c0c2c168040c0040f84600d1080c601160040c00645001e490548082c442ca80407520350700d02d488440c03089402c14050004410303410040f00402c01c1083c0190084a84020000400e0031f0055070411a85449205210081241c26004228000f90001d841582c140b01c00f02c0c01e00c41150550304d008000b40324482040d1803400300a02c08127407003004502402c1c1c0c00e05c00035980b090483c00109492130071003401040d080f10074969002001d60107411100000078080d404c0c6c1c08100c2e038400281a1210b000100e860500c25075a02c5030800c207070404140d80c86010344050465140c00c40020700406d0700c01c4c401101d21f4103121903000c82001c21450385240c001070446034107000b8001e031f0744a1004580640080c2c0e4481d15031b1070103070a00402d40d0605020401c100c410700d81d40c180140451285d15508c00c5007006090b50040215007087d0801410301c403050100b0002010390500300c0f01039410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 910020836 1250 910019586 910019597
    0xc0a051009061d0d0305220510140c0303010e1605040b0a0c0c080708030c0714031f020d0f0906050f0405030318030904050103051f0c0207060e0607051b0f0102031306 73
    0x1010407903810045405110f240e03c19200002903060540c018060203c001c0084010210400140406000c0b41c0d074906c981c03500091118089034a5a0080200074181c035844900c540c905840c8180807421a8000d801c165240907400091200d8241a40e03070140d28045142401854141402c2c0d01c44014058040144200421414450104444004d2803001030100c202110400c0ea00d4000a64076500444103440c0644a440c1e000950700c07251480006030b10b480030300036200d1005400c41c0c059125107103601e010200e54081090000005043c07240c9400c41781c1c07072503000a4031a807614028043c0c41c000b074025583c003003100040c071020600100c00c50780c10903a0b00b2602420500b0889003581507010701e60380c2c80d5100d81b5100000081c81800702e440c41140a000070350382c107450004000102101d00c2c81d19800010303400721038148440b6005a0b6480e1f40d01800520301801c016140d918149485001105002030030740302d0400c1c0d4098240707070300b0b48858940240060340c1081d0241c28101c2c0d2011680c49075004101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 910022086 1250 910020836 910020857
    0xb0c12090a300803150a0e0402012601080703030f0201290a08010519060e0c0d0c0504080319030f090812130f030e01020d080f0f270c0a05100906 64
    0x6040441d0001c07000303039101c4005100e8a850410b8a030a4104171540980035001d41c9190106151091540d0f0680d0800c41c00c0c3e14880c3c450360011a800204c6820441040d100304480741030f002c00e0901c00750700801029000304086402c5140050880300b100d00000305680c10701d002e03003101d084104003210b4903c0501052080c401d0843c00050090039940e1b2120407154a007000b80300300d49218411b9421001c0118105110aa94410111100e42030460381c1d0100c1c008140080c0800741c8150304542d000ca1070a180890500d61510307030302803e580c0051888000c0300343c8100344100e0150940030310b420070301e102c032400c2201003042e480d4410a0701c2030f13140340304060840500103050920491906600d007900008a8040c2000306c0c0f4014001b60590b00340e05025228500030b80040e144940c04480c071609080103a10280e80350a6084640c8200241401c2056031100c025550005081c0c9041d06121040e80c004190613a03950003031081400440d007100c2d01a10204201e40e8000c0c0d08201840103c40c11307407922442e0403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 910023336 1250 910022086 910022129
    0x20c03181504060305040b060306040b1f031718090108100203092103250e1c050105090c0103050a020f0304080d090203030a12050a0c0f0c020d06060b0c12090a 70
    0x1c0000740c1e030180c06600100703010854580c10391000303105502c544040000e9441d560109651508100c4000f48011046d6000600070f030410017028141100f520442c0018544a41d10b20441210720304000395480400319000103100c00501803100c20700c00550703c403947e0b541001405501d40c9410791202d0310b0b80b84c00101051010408101040d55034101b00f00018211a200401e00e0566009680007003170005801d44509800b01c403608000d82d0107009444000134107806809000121100d2a0b0b604d41e62015584268041502802194800c0c400c045c017504210103a40000b5040710300c0030b4074040041d4818451080c220161104032030b08180c111160b41d803603d40308901c1b00c000c2c002c10032000303415000c00b04070742c04074903000040804d0312244008140a00c0d41ca8605000441e007410f0500d4002030540c5002d440c80500480c00303c00c1d540d002030300300c8490325400e0300d516040d5103955121204040c000039640080c01410b0009004820030013031a2460000d1001c0000e402a84502480c20362034070f03c00504001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 910024586 1250 910023336 910023349
    0x7030b100f021c050c010218011706010905090901090f1209061407080f1c02040302010305071b060c17010f081516080a0b09040c1a07050304031e051c030f020c0318 72
    0x2e80045c0000b5544c800d0084074020b0038900c0510214007280d05010318030300302c60001480034407484041e0343d0364200d0352a150401000700303005026118503550798007901000c1090310034100c0407240102401011074040b00d200400e00c0450381c0c040000c02c4501c600c0140480040b208481d81d03142c0101890351102c00c0c05290040c030303105140e40003203440011845500086000c0c0c002d8400c80c1d000740c804100994031400295098401649282c25035401c0d01c1c0307034000043d120707441400c041041d4940340e52005111403c4050324042a040010707080c414000c01c20000804018641003000b140d0507010aa0906084400040e01e01c0218982400881e000290502c0c00c264400c0c54240b10040c0001e031142803608104031400d0703841c05201340041160440813206180403046500d083d46c40360007149420700e0f607101e11a8000d02802c2070704445020541030404204100454491000d5160309090f03890342d15540074007107400c5002200052801480348000408010041d101b82100300d00200d040c06180d9800543c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 910025836 1250 910024586 910024597
    0xf14070b040b190e09071d0105030c1608041206020304050601151d010212071202160b09040b0d060903020f190c03020d0c03060501140a080a0b04080c120307030b100f021c05 76
    0x10040b0ba5402000707451980025011247c3c4281c0034100314a02c1e043d0011560740c8021102031f11041ca0400001846034034041c1032001140c003500146080c10744071100071848070305d01c80b400d5500703a8002c000d00040c0302050041a006054500000c211000450780c09400841e40803424098001b035038010360596402800031640701003083d14119592240380c40c149010b560050503820044c803980f00e210544c4d92003a4808000d8810350401d060600c0c10500411020303100e10307404950006404840080040c3c6140500d0031910320035006461110106040e003854031036180c0c102c2c0040c418002d041c001041c440c0075050b00781c0b50161541e075820400c5007418983e81072540d10040c40c40740b0344000051120400c503c07528040794100c48420803240c0c3c4102040e507d5010480c040c0c5102440390100d00002d02040007441d41c00c0c40d4409440c0d04a900c403000b100076410840d01440800d48611603140503140c072081c07200000c2d0003820520b8402e860604020b44d0780c80116080700703145440c00706145c056801401941d2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 910027086 1250 910025836 910025839
    0x61909090303020703110f03041404090f0c051503040c0b0901020a0b071115041a06010210110a11190209060409020d23070b0d180f14070b040b190e 65
    0x40a61072400400943c0507403c203400091000e101c40a520700041020500001150021800c150804030f051005204a103000c541c41503540074240e0025040c00c1003212070078012074aa652952a100c02d000a4015032620fa8030090410010040021f400c90007000580c1c1e404a0f40603254495200141c0c5040c00c281005040de051010030001a564000d500b0b10184080c02d00760b1344001c0004904506421040d54028801344200320300a1070489035044107680030303d051044a107080c6e030780411f032801c64004c125270794400403001440028007a009002ca03403204e1003400040000e90314200e044546e403000c610000748241030b03420102d8990b40d107a4000d1610b1580042548001200740c0c501f03803a20115850204549014021000d000e400010820500310384e5002010391502c00e9400c25000107081c9960229001040b401d0090080f407070152011244078414840c01400ea440001520b1920880c0c1d40128030892003000309000c1c06406400360b40232000e00e1550400f291604000507201c82c4000d41f00c60b07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 910028336 1250 910027086 910027091
    0x32d120e150c0a030516170709240e030c031005040c03080309030405040c090b030f0a200702040b061614070e09060402130c0f0e0d120f180501080103030c050c03030307020f010e15061909 82
    0xb000307180780d0044ad0205410035100c1409240c0307140300740768030741c1e007441034981d0306400c06000c05481031200d41040c0d40c001c0c4501c001840090316135540304100c0c0c00a640c9503d052384049403e210a081500c81d514442005081c1508071502d8240144858803008141c44444a5114003050040f07195400003c1ba000d08554090181c2030b4550305846aa005017609910880c00e00401c5580d5062290131601740501503240c2c200c0302c0302a629252201d4400b0681a442d80c441c8945c001600c1c210404040d008441d07407001790040d0300b420300401004c00b00b80c03a0303e070961514215139404965000001240c00451508040b1042c1c100b0b400000e07291400c1f840058a03900c202d801c03142000b5404140d00912103110745404448100520043c07600c00c04c1406a217022411900043c00828001c1d04030310300c4144601d003190780c01404500400d0039a00248d8020025911105d60000c3d81042802058000740b43c54009120014001403006c1e1f1090001d020030340107804221020501440307a0300400d028140b4003009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 910029586 1250 910028336 910028369
    0x120f0a111b030111070c0b0a0c05010501030f0b100605041806091802120a0209010b030a020c1506030f0c060313020a0b030103032d120e150c0a030516170709 69
    0x1402540c0c1c01180d20314841d51070710303200e445030280e10019644681e40151311204490f042000a440c03a500a42c982814001100300c140c0002e9003d01580c1d0207127104540c070f400940c0d0145000c3d052048080c101d681242941c1d8401d01c0410391140944048440c50700c280361090403803142d05070042001c1c1d04241b04280c1401003419100e15106a00c42c1410710a8030034588200340740180c1900c0c1c0c0b130701c65070083d03004031408010415111030034051500002483c41c01458113058004581c545200314181031001c10042040142c0c518003030012514043d01c900140c249103e21800040c00b911004000c2ca01403096518207200b51340300c44035103001a041c030425450f0349584900780038104240241c3d4415844a003419507011083c0d0310f43c00c102801c1110740358072624060080712480600082200c41f50107101c0c2c4200140f00041c1041c02d540200c8144502e10fa940c20008401800d0310401084102c650381d2461a8500b019400380e120030100c82c10381b840041c0c50b20351420880784c806c00b59100c0003860454852 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 910030836 1250 910029586 910029613
    0xf0a03080f0c12070503030105151b07050411040e01030f0303020c030c070f090e06070c020f04090605060a06020f070303031e09120806090106120b03120a090e0603120f0a11 76
    0x900720750b00b1a000311070302c800d4109041203103072280e030000505580050004001d03034145012941401c0103130171055800e0001c990101c10401d60074400442d11540803507801c00c1182000d01c5181807144013007403058078050404c40354440b4514184001000c11480c01044402d240c032030f0b03042d82d821300f016400f07403035a40317941019540d43e800f40c0380078101416100000c0042c4001035417050a80b04110700d03006c0d148594a80c4400d4541140300e0006981050441380c0000540c0c2d03a9109405409204010001d401d0a002091240c140d81c05d030080c40c150b500010003c881954000b9104080741c4d0b0600c2c0c080340c0c0b14a02850400c000c86a019018410341c00c0c406000d0400c241da221105403a500d5644071441a40c1d000c0402c5000c0e4803c0c443c00000c150700342c041c90081b10854104d8603191001804860203990907961a54442c0d001c9203140c0001421130388e0a010300342c00f01c0d01450304804210b00416411040804442651003440401c05034014001884130196008000b20350002c80c0210965884048544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 910032086 1250 910030836 910030867
    0xc090f091e091608281a09030a120c081b040906030c0302030f011a041104120b010e0901020319020304060e1510061b1202120c03070314030f04020f0a0308 68
    0x1540500d180c150f000c007144c225800900b100103001c59011454143c5c0d0141401d000c1c040c0504000d0724040310707080744030702d40d44000400c040c0a200315400855a4000340c8000403c114221040881d6480c10420302140b19544000d0303894001c07111000050040402e02070403007280c8100d5029515041c248200003083c04500100308044034009c0e0280c48180d000016568206c4608030b0288040c0981d070800010b01c0d0030581c0c8107000382e00700d00c01980d18040d2980000d180b0484d40007000c503040c0314200b0041c42080c1200040300c1e000071a030802903046041451410160011031904840b1259000c0001810b111294100c900c510030158241c640d203010754141840410400c0741c0741000500803c3c00007a00d0b901c1095141c040303850644021003400100d950703011181c500c0440c92400c502c1000e6240812507045030003000212150002140d0310700c201d14000c0c00c0880007140c001c521003418030030071001d01e00040300c65034010380c122030202590b903154001400011150304003414410000c12a010b02e2009030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 910033336 1250 910032086 910032103
    0x240b030411040b0a060e220c0306380403060e0a02010e0f01080f04061d070819031706040e01111305090403210216030806090c090f091e09 61
    0x11054000c00041000512064441083c1200d0300001845000c100c5a4030072010108002030060000d0701c1d840140041c0d0060f51002c01e03080080980d62154088001c0c1c0502c9100014640515902200181012402540403018010b10718051000e00908804031a0004940265078880810480c028148907c40c0d926400c120b0128080751071444014103c1c03400e4510301110143c140d4442c00c442d0780c2c8001c41c8002590103001100d003e03444001c8040c00038250720320381004540820003051150306c0e042016191101401040c2d850149007604000030075070100c0506c2d60000c0c0100002455203e100c0802e00822010280c0310095182064040010300c11600030303d0a11002d1940c0000b0544a00410540c8442524002c004c54102069214010451106013120038000400181002940175004840740c0740b8400c220002182142007258502d0041480d0f40c107c0380002c8030301e007030a50300c4e40807881c520290155a4401c0685100044030b2030003030100c01d03d244004000140c941d08004000c1ca0390707014407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 910034586 1250 910033336 910033343
    0x602031201080601080c040b0a050d1424040f0c0315020403140303070507120c02030307030f02010f090c12051f0606020f06060604050108180d0207060f02150a240b0304 74
    0x200e20002030311520000e44503050715024806041501c1401b02000003c0c0703404640300760800c03c01240000c5507500c1e141500302050280b695030002940082c9002e060049540d80c20090b0009100000c407030681c00220b5503170207984000c441c4010b9055082c00060178000351304c0148a0b0728580c0c14146c1241d15070b0003410441e403049810543e003843c4140300688a000448401001800034072100020071107005020811180b942425181c21110340c01003420b550108406802184503420500081c03982407048003503070b00e244070007000502c00c9591418218800c40c880c140d0600c0405400034180442031089424400913a010101344200920025002e49031501c14400940140755074a80d0700c07075010600b54810709004100c145880d0030003005542403400038100020321151454041d260b02c3c0c0421400c0d040d0050fa400514005140c101d0081c0407006114122045400c45e90f000288155804202c2d40c102c880d401000c605880c50031110400c100d035801e0710524070180520300080100301080114010f500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 910035836 1250 910034586 910034617
    0x50d0222080c060403050a0b0c040b030a05060a14030a0209070e21010b0105070305030f07050f07030c0c1d0c250305040302030c04060e070305280b1009030b0a0b03030d0501060203 79
    0x5480b81007000a0203148000341c01500320344107040024001c41c42c5154424248000c9038109906c41c90724a00a40040b40c01c2c24002c0c0c0d0350310a00106251502d410340040509001c0141450000c1d00401d031210341016009004005e84e1006ca44014003940d945120004081c04100d00880c80119018180c0d29005d110410395180281c8210554495400c6031034960305a12410700d5038440e40d03000c43c501c105c014005820480180150040b080c1500300a001950207690360703480c009810706200b0840f008907881303a1444001490b0340401140c1500205a01c03400942840340c5072003220b0300b011001d41c251030b40b00d01200c560321044001c0680040140080d40e00a601b20b814500649043c0022142a4022201e400c2c0b24880084c0b407881c0b20750407540d03005a5040100e1062804050300c0a5510001c2c40c003540f4a917211701c4070201c0390030302d01090b00390b810701460003420072461912402101d00c0302410304c80e140d0b03480b007013022040d480030402c940029000700c6041269694450000b5182d03009209030b0206c496 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 910037086 1250 910035836 910035853
    0x18150f0b28140108011206090b070507140d0c0602030907030206040b1b120409091506090b120d0e1e10090e1f3f03080f07080403050d022208 62
    0x903000100442c0c4400182c40f040b890b03900700769421042c810b40010031144036440d0500c0b5000102070007002409100c580e200d05455184a10b400d40081e030780c000300d01c04c031984013103503014600e40d00104422034541c0007400160390b52166001541030288a800180d04004005000212010808024103401d400143c146007044040003009071500607040d0800340204d418442440600700c168001403c452003181b804000c5480c155486094402039804400e000759541491440d41c00c080c5400360031444e034180030700307009051220060260780d503d0312600d0007661a01203800315a8007020b048000b0f503c004042540c6144061002000b1454034002c201c000740d00e8601180c810b100d44241405035440c0411444200c80c1000555441007070b28840c1c1c80c00c07801424420040e8042030042e030f424015144a00d00d40d80003c6414060704408010b00004100580130080040d10341e41300700e40c1074010f541881e00036651031003011540c01030b01034001c000d901564000c40134150042840d40c0705044070240310550f481407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 910038336 1250 910037086 910037099
    0x1b03210601180302210c0310020a0f02010504020a0e0601020a050a0506040228090c0504051c02040501061107030f03111b090a022d0c1203060418150f0b28 68
    0x41d0518480250450500f070560030016524065a120605202c4111401e4004006c0003a2a29108064000346940d0000746041076a80c84070500ea082c0d100340c00207100c07906103603000c1100c201c1c6520501b1001c8401c1d0021500c203a20034009074040d540c0180c01c46420000ba81000741c0c0703d46c0140c404030300c14011031041c01e5828054545100449200d040b415101514085488010703008a444487c10000c0c01c01000c580d6907181c2160a030000c2c0404940709000b409481031004586c4107800c034105120295901d580403403c0003d841040c5c90307000c4403032078410f0307614a02508c1d51804148000014003c2a00044080c580d0a0014412241c21510036100351102d03c02c1104912840038500ca1640d02c9110700c9528190203413909101c4c0c420034000c2460039000302a254140017540004841c02c41c030000502265282500070494086229481d00307250700015034444c4050100d42030700c20042c980781c01910010175040c1e4800f9040d040060003205c03d0707850702840c2034030082e80c04c500c03425040c810450210307030b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 910039586 1250 910038336 910038377
    0x20f070b0f01140d02210307211e03021312080307090e13020118090e0313050616020d1401022b05060a050112020708040f03030f020109081b03210601 66
    0x801c101805a62445005400380180c40c1c05441a20342c06046c01e040000c00c1d44400c10041c2001d80c0070360070340c0c112428962210803003c0850305c02c4508001040c10000c04030304e036146021820f0b481609005030f0b00c8059104412107501c25501c920a02d03010846004240010790000f0340c4510b03482d6507130614403502c442040000f214160390003000150007440220041d40503200c1e1050404011440c80c580c02d60321580c18056855001c0507031055000441c04403074403c1140400b01c00f805003203500074100b20030080c080008005003000640310703122020001091000040004040c582c010000790342c0d0303c20320190880b0713000300f00307914031110813000c06400d42c48242ca102c0d06000f10002848405142d1500004440c500c0c411000d00c00e115900b08803400025482e00001d000410b80501d0007240189582006010a0130f103942c000256414401d02500103424001121200c2c031414594022004114044616501401000c00c1d609038465541c0340d420404d050351140f042c1380036a034402a08202e109120070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 910040836 1250 910039586 910039619
    0x1060806013008090f030c210f0c01021b0d050d0504050a0f0f05040c02120c010b090a05190203070216090603140f1009060b09040308040201021612110301020f070b0f01 74
    0x10b43c0c43c003480042442d01d041d941c5c8010800d0b0003822980e08541400c00224154541498116440c0141d90180c0d035441c003d20803141d030810303010041c100d24028880040d49459140c08500c2d1303001c01070701c40b016480c0c3d50313a02e1111201e50000201e480005a030240a4290f03030003405028494120540c000030401c10f011040426104100c2000701c400c1d1034034040c0f20140c42140004000d41c090045405650003143d00584403110b540c1e00040754000509051241414000d48100d290505107803c000c2c00c0201d240e04c1c0c0842c1c0004e5203005036244d440d45404c909094220303583c00701c01c00c030034800010014041c4c0c1089040d80c2c0a45070440314003a1800300d40b6501e05082004007095082850121086552030380594100c034010000403075030501042c002504800c0882d01203004c500004d0500056503810030600c0345201240840e000c0c07150030100003034440000e801000384404041c400e000390a403000c1d01555060740c0c0c03503070b9050785400c1103150807043e90100300d640320081070a10f0000180a108a2030351381 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 910042086 1250 910040836 910040843
    0x110d0210020c150a1a0409120e0f19080d021504030c0812040b040b0703050603070506030603070314031c0b091f0315090302060901051512010608060130 67
    0x300038442044100301a401855007081c45001e03403215110403a0010340d0b8103105103001c540000d646000100040108404032843c00e0041e440c020900b00094084040d4551368080c40c00c140001902100000c4c5040c1390390200e0f1340d081030007001c110150401d020750031020380d00468140e0350b010500400881c1d0b21401c4035540700c4145600404100464000e515501095000d50300c110320305030750b140806149100c15a42120303c400d00b031040209102e000c160b0150403001c189010300450505a001039920112400385510481000000c0303812980c0800c0a00021503000610100451000740460f490ba0071600d144a20414035120050442c22544a501440c50004010040340d4030340400e13034007101000141c1c00c02c0f81b00301000c0100100d10407040e103014040c55908007240c075400034a4028280040601807200a80c188414402c0011481300d05400a07102900e1401d1141c100c5803509000d0202584150030b03070300610002040e182450040302c0408550401030405800000500110b91410010042c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 910043336 1250 910042086 910042093
    0xa0b193b070210150608071106070f050705062503050f0f07021509160e1b070f060c180b12011a130b03090d0503190207060e030316110d02 61
    0x20300c002009061529000352841c030442e03040707444024007001100c200d0500a003200341c2c803560801110340c3c0529110350140040c64402e41c9080600140c6a0351000600070000303100204840c088123600c1380d002d0ba5880f0307800000320380140c14001d0302e05c190700c00d1482000445500a4a1002480b80203008050103456031100a50840d0f4442e2510244420003414004c21401404022121b660845103c00e00600500025205075a806003855841c2481030344411450f5010404014811024005414415018008860380c4070f41074506441f002d41c103e40c0041c121071504124160088c0d012500710302600310110f201e03809a884072041082c038000c16080110003103c0b10b005001345070034400c800280320b01c0100c11a0400d4158094003010001981002c80c0401002c004c100010300104204000282142441c0b031079801c00000010125440b61210f821282d0005004000c00c44198004412100380d40b069903140d041403840204460f0482110307800107100144400419140800e0f03450340080e058009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 910044586 1250 910043336 910043429
    0xe07020304032910090c030c021c0504050612010801141302101211180a12060b0d081216020105070903030810080703051c0c0809090a0b19 61
    0x3207800c80f0103800090055020b100c1522001500840c034214064494020a260030500f0644130200b102d82da841024209030404028891964000c900d003000c09960038101802040e8a800c195480d1107190b20250b08050001004482210401c0303005040c0d6000e9002803094001601d8680348866040c0d40c190452900d640d6842c005203401c100d00d0031001c0090521103820f0340b000c005801142c085508410040b8400a54114400848000c0c5c01c002c00c0c0880b9030980d120304001282c140f01010340c000600081d905c1a080900380e50f0f0110303d50045038050350051f961200c1d008134144901058071090103d6482d403032402e00b640d006025144c4501001c0c3c0d04c24086c04e2640d02c04456210000c0d2403500418000000402d0040091040d40081e5008000811140000086032050040c2c042d16074420030090790000300000392500300300c440c943c4040316000041e4441e41031000c002e02c064000198450703078036111800b601412040c5103045802e500c140325001300f94240070041000b0000e81185090401004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 910045836 1250 910044586 910044593
    0xb06010c03030e0313060801090e0606091003061e0515100509130e1606032901030209090426181c0b040503070b01060f0903030e0d020603160305010e0702030403 71
    0x8035009032a01a00e400300785400c085403200d0669200211103965440780034802c0c00304580140d5501d004008181c020030150403000c1c0310984426010b440c80c1d106519000c04147c14400d50300d404800b45410250400150003900441d00c98140340e0045204860304100000b4254604180b00c0c4d40c007818040d02c0e1094001c8101c004072000d46c0000b804e02c0e48409911072420f0980000d22441c0c14401b0000c00800c41c1e0340b03088141032480c010a40c41842011b0810b62030204084442204c2680401d20403580b00c084410b9200617400790055104072504194080304200074046401c0e031048501c00d4484540d03083c0c81075550b0300b400310b118030a01542d010705020351800382400c003856040200d441d6401105010350f140d40d154154444152015103142d4804140c4106000713a208105005000c02d090041d101c0a00c80d80151680f80340e403001034140100c1300002440c07500c8200103614910341c0180ba80383e0742c1c9040d8035000000c0b21b0140d185000249454008510402c00d50701d21405071103550001c500380703441c664 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 910047086 1250 910045836 910045847
    0x3030901020d2609010203151f180305030a0305240105120c040f031103070e151203040b070303020408010f05060d0f06110a030f0b060a05070602161205250b0601 71
    0x2007407541603000c03810303c00700216044000c1d40203042841c00960b880c10008000f5131070846184000f84101e01e01e2440f8450310b140c1409401c44401d65080c00003800c2d080803a8006420038a51004c0d02900001800c0241190f06030310640c89103020491025408103422807a2100030031514000d03003c9030041100d0b544422800d1407043c0d1040d0715241c0d192425450300591110803a240e44211413100301006800c1c100d190611405c80606071002d00304100d8545400120b11031183d101e4064022000c4000b0030f10b1300c0c80c082c4100c1d030282404a01603540c6040740e1034000c0095000303128005140d443d1000700800f11303400c1d0141c02e01660000301180740854494842107851300c040d201c104c80082e81e680000342425200f001500c400c0510303807400140c8034070b20f02d0351805a41e055680301c1d01c903410030840ca40d003035030f0003409440095412550050321481d9001c0b002825032081140078007105101c04440c40000e600600520502a0340f8a10010441a0441c08519245120b00007017404100030700040e8a1751060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 910048336 1250 910047086 910047107
    0x11514040b0a14092d04020717090d0507060e2b080a02030d0f0504060b120d050a0215010e1f050f0112020d0e0f19211808010c080603030901020d 64
    0x18400b03924190032840055180394005030311007041c241d021203ca41c80c0d83c5250b44c00e94005011b540641c07034051f40d5070700c0c01c20120700134040c0c8074031210218410200383c40e20013100221030f501030120352a0070b44030400070713190580c3d04260328407c62031146660880012000031521900c03240d5030b8000200a180d0ba01c044d107400800b11001140301c01d100d100d4098a5502840d0028000c0301c000103254101801c101e426950149083d6002e8a00d0b00341100301c0d8070002074011b078080e080c0c2c500326445d01c00040c0200e0a12078403200f20b4988602150001c280c82d900c8480d4035002d2290120030b0742c05884040c40900ca1850030b0320410380d01503000c80700400c0550040100d4407030311041100040ca0007a11014100849600780c0c8801c2e120751040c001100c40440400000e58418500408003038844580c2d982c0300c0031243c00715417015107008a45041d40406000359401c05502d041c40c416501501e03101e49030a4020710000d1200340004d4541130214440307090200454514a4040c2d01a281d2040b0480c02519259441e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 910049586 1250 910048336 910048367
    0x9010c020a2d060213030201030e0c0906040e070b03041a010f140118120f060506180a0c0207150c0318060518030c0409050a06060f05060304060c030212011514040b0a 73
    0x221800b010004045200400c80003441c0c2d4032030454075007140001400c5070310520b03291300107a200a809004a980e080035156201c5012100406c44d2450700c240c060901141e540026070713003030000c000c2c0b1040118001e81d4459031407a000e081d50081c2c4e0303510521340d0790f92407505c110003032011000c0c448240c40d40702d19011071040240c00511030001c1d548000440003114036420a4034a080b09698403000c00009004450b04880200e400340b22200617109181c101c0e40d0301908040d001c917502c42400324014000d011178002801a041103104100c440c0030044c6c410160054100e0010f20079a002c400c400440d2072050058602c3ca40d141801c0c24036510790030101c80c100702c110513898482d00c900881c580c0e503503005100036140f0510203071003021440d203402002d66485cbe404c44d498004c540300050086803030381c2c01a81e5000d600b00314045080072182d0000d6000384070b00d004145102031014000700c1c1058005801d64900c080c10744d00c181104051500e09110303809540100d4044881c01c200e52144280301d0030040b050b01c601c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 910050836 1250 910049586 910049663
    0x19060525020d0308090d030b0a14040f02070f050606010c150c030915023619030c0308090f040c08160513080601081204060e01120b03010609020309010c020a 69
    0x29940008210035060b1400714001691901006501c1ca401d1100c000109802e08050059140403000980741c2c40017030154504041080c10b01c9081daa80d90b400c0350280240f880011075503402142040191020500d10540e100d10030f14021400707552147d619800d99a8001d00780e8a40308600d0148040a0818507541104050311549401c2c08203000520080c61034040820050f80c809050080d0001d80c6204810801130680840413910408004481c0079400e40048501c049041c0101c0351160b0010782a42010f004620128404001c220721500140505001182c2c9807040c0c000903c1040103450114450f0350005510201281c0310120000c100f07024003006043c521f0910550140d13140401407642e00a01d0700742d000d040100170f040800d00013503050581d14a1030901d4a41000e034041d08183c0c1030402e050411000b03440150300d1001c0c0c0d03070016500c1d0500074002c5c044940e0383c100e880b010f50015240c0c00c03c0d652034051050011800015243c007500d0f03102c4030911030350000b10004103a12000b009406440d16 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 910052086 1250 910050836 910050907
    0x1207020d050106230103060e07081e0112060f05041112010608010906150506030c121b0c01061a07021f0e030d02060f010b03070806090705040801020705060402190605 73
    0x10750a014640141c00448041e14101d00340310407051000d48889a00c906040c41c281040c02400302000010b54880ca4a040c247c255440b0003030443e540c108101d2003080404010b2001043d20455400c000b00346601031002417141c0311410580004413a02a1401031500002448a20090408090750404603580200001d00d00b80d03211602400d46160100842d03c030f598841400d4248010000c1d034401422099030150b041d4600401c0010a51007125031106442c26024005a60f405586c440f41c0901c1c064140a20b445200040440e4080c00150240808900c1c0701d0700300001805641059524503a0018504408000081c44481e68840d0303400184040144400a01100f51801c03c0101c1c08022140e00a03e064135105914001040040e048150440d20404c140720149510240c02c61f004001219518155291341009442e00d2182d40e201c480c59500215219040c00350129095100301e0082d5a50744111060100300d541c87d25040c007480003c94420b1011000c1c85058282480c540d400703034107010b000711 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 910053336 1250 910052086 910052093
    0x12030609040f1707060b1f05030c070c050a0e16020d171f1509061704140f16051203070506041205071704061101052505071203050105030d020606031207020d 69
    0x203500c00501aa405a200c02c0240b04c0347c1400340b00c92404800c00c0c005088403040d034180050180c403003d041c0d600d05200100e00b500620808201c2c0900405009007091701d540d0b980c00030083c07101d8048500c0480181c91030700d49841c26001240041416a8595400200b80c03140130107818a4040684044582c0000d18000d1305540c004440718000b400b50300010207503040807a10300610325900c0d80c201c501046881620360320400440313401c0a07000340d072080c081880850780194581c54035800444600c02c41c071400102e00643d141040394641580c90581d28050384135120b0300c180d40d5030b00c6200d00045c0b150384204006000300d000028032111120b811b2805500e484025240c542100c5185036170b2040c1c81d03000260400505411140c040543c2221200034000b601e0102c10954001e406a000c541040f030400d0303020900d481c0714408076180150b0100e00580c8501d4007401c020024242400703560b000c0d1181c0100c0c50321240c0005426480b5120041c0280400071340644c020005820401c0100c0e0403c10f40c0e194803002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 910054586 1250 910053336 910053383
    0x140318130c0503072a110907020d050f16020301140912041206050c0f0d06062d0f02120c0106050f03120301050409081204030c0b0c0c15070e0d0c050312030609040f 72
    0xe46c094000359002820401c1000300d0050080c1401c41903511600c03074158281e8009003541d038800c50950500e51180d4007101a031090031580d180c0250305500c3c00a81301184100ca004190140b00800c0132a40d0000c26034a42d007007a48604d0040c04650b40d020b2919100042841d00110750240d01b80c4591230804003e03903031107105d5401004264080c9926100b0600045611120402035040e41c910100450b40a1164840c9030b040c804140b2820030855441c4901698020031180d101c0ba640e2000c4103988070351924015008050078019641b0a0010034a01c2d661454000786507050001b40c440100d255910b484100002400741c0f085c111200c0d902804461032a4910650041c891070090300c41d10460303003452511000150340144054007404007400040c1400100144401040007800c20000558031804e60584515070301c1d010340b6500103040d030300c100c00f00714140000d80f04480c0282c0403503886c0414102d003484a0300003116595008013486000070081442045400c05031402240c9e40d40b0036180c1c100402c2007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 910055836 1250 910054586 910054667
    0x81522060303030f061401080408090613031424060118030501140c18150405030105041412190c0303110f0414030601060c030c140318130c050307 64
    0x920580d034203000c00074160140070702d141d00c0c500000c0411020382000420a622190004014104040c010024040108040c05c4410039440100715545030007400b0b83c003c4440345140021100d001184100001c1280005031310706d802218a00300303e1a0341c0c020341c80f048039848000d1500d0b04002c1d0004280c8010002e40c104c10001d940070301700110309602c0500c0000302c0c0100103403003512821410010000d00c0e0306009081d034200801254407503420400400e85886e10b000740c0e0440d9900d54070703010900c820400d09000f02c02c0310044140c191103c06601c40080d40e403a00900c40303c0403180c103240a140000305e1198544d088054880e040c00104201e41212041c0950055041c0c400c0e0443c0028061000c0b12940c0d4440388130440860040515605144006010b803001e008000c042c0038800c40d031103080241c0750083e40c0100041d001169118420f509401040442d00c0d1840e030b018250381000d0f41e04400844c015150459a03d441c1c0a146440b54001264501100060580080010010401308803050101da82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 910057086 1250 910055836 910055899
    0xa05160b0f070801030c1401030603080d020a090e1b0d0e01060305010605031006150f021c02070504230402130221040c080313060507080409150e0709060815 69
    0x58091a00141c901003840000d404801803100c004010000910545a4601034072911000314441c1e100c0300300140d016100980005000c02d07004124942e68540b00ea0140c00d990600355502440c644d82e5008542c0d102c04281d88503a070142007620002c414510200c000c110741104000009170705128005410300b1209903800444599460f61408c0006140c200003501c4180c0c01b51400b000500d1401c070481c0c0c1075241958240d400e2124008a082905009120102170384a000c680d41d803ea1b05000b90082d101e141d9405290f200c3c52030643c5120301583c0c104600382000d00021590760082e120b40d02044608a0640d4135062015000c111044d000b071020f60011780342036080d40c5101047c2c203151a0510b4244201e07040b412103070380113126042000c40700c0e40303801c8121202ea00300039a860703041c3e041c001054426a0050090903080103481806c1c0307510700c1c034854210b5224041d442c285840b001801c80304015644175200004001002088080c0c031804c0300b200d450403008080340064421000984004585212104c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 910058336 1250 910057086 910057103
    0x210209070c080c071410090e0912070303240605120c090d030206010306110a02120d020d1a0127052e050a12050402060d0c09260705061e0a0516 63
    0x7040110341c85c050324401d1060803103a203405200761500003403595070b5610541d42e85043c04404100f1200051000350004508000364956401c1503081c00f601a0034200383d0320713000101c03203072038442d00c2d0341c21840c4881910820340d9414035041d8480007094003094040c28544288808200c0b45020b581c0c1c000402c440d4907c29006417060b07601d10f0428100b2204c00d020380900003241001400c1144c4d44c08a02c144a070140c4030401074450f02c0400f0a90024022035447c3d564103498100460136180c100d8142200c40102617940b1030380c0500040561501c8411721250b136140e04038804040c051403070065521100c0c40c00c4003d00101c038002c00032104110040188402011400008074400c2050f8000c080402c4000903841c04c2c0090b0a0a0380442c000e48038495001c140782c2d5495050500f03075403149225034010800d0102d8003100441491038454854112a0441414800c0880002e141d042203c1512000d0b0a118400300a91140c810f51070311035800700c1502c000300041006a01d0301a660340d003a03204458000c8114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 910059586 1250 910058336 910058339
    0x40608070f090504110112020d1a090717070e01020111031f0b0c030a1d0a141008060d0305130b0a08151e13200c07210209070c080c07 59
    0x22141d825003002085030704040c204404120b00185042d280305e0b0030710f0700d890320400141b100c03c003e0148481605412b4100b000c800c19610340d010416440c15001c99036107565864400c010780e055500c003101510751031004c9001030350031801036040c000034004c18000030800451079a0280225881120058118001c0e80740c2d2030701503014108400080c003102d0310701524007404c2c014007a98a000d080103080070880c0c2c600401060b0340c50440841d2114101800c20000039446100c07581450600c3d9804a001d050040103400b49544100803050180402034083c05e030a140350380f01140c85512100480c007211400c07550010b90b641c00c0c00300610107401c817981d4004850420003080e000c0c240b9000a01d41c840c01c2440d0740c40c500c810b1603481c04100404201c4400c0d280202c03440c80403000d8010a070310781c086064003203044240903c0b001c0041583c1043c2200741d42406231100540304500001e40103602540c0c0306480c240b0014100784269035003000c054140849200d810f66503040403079001d43c00c055000d4002074130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 910060836 1250 910059586 910059599
    0x509030f1b1c06110904050739020f0d0c0608041e031224060302090f0103060b0316020c1e01030f0618090f0206070515010f0e041101020c04060807 65
    0x1802804103004550304110729a2000442c440d94401c200040d084a585615030394148000404417943c0d030344d002c1e1080c4030618102c0e40140c2489807d0802e0070b0341140c0c8441241c80c5503146203031620905109180d40c040c640b082c0d001d00607100301041c00c071608843d0b10174041e40031410940042d40101840d0391018214034161038510f422000b03103414503503058030781800000040d400840c04004105100b40000341c0c207512041500c01e420521040b8415081a8000030601c9a8540c004003000c0ea01980c502d0200b4000b007004504940300c910a294500705c05102060800c0c02c04070116070000341c94812600340f1b10002000940f1250002c40c1d000c4030140510740300a140d609402045c640494510081200398945441050464104d030790050850380d40c1c5020408100400480c5020b064000d00040d450700401c0c5441342d42d0350441110078030880040c100000c0d51002200e00d0b070341900c8107070544040d40e40300c50380c5030f003204d014810707030241940245905c0505c113440e02d02c0748030010a0004002c1c00c88038034250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 910062086 1250 910060836 910060873
    0x609160c050c03010212011e03122607030207020f031203190e1b0103051612020a120626060c07080d1e0609061e05060306010c0b010b0306011215060f0509030f 70
    0x200e481c02c145280d0701000803c90346141b03803103844131605140442c6411502c036000f51101446c684400711582f58248410640c2c19405010301e0362007a42d101241d15424010980d0b43d0070606a40002c030380b42000010894241c20b4408903102d031600d2000700d149860881c4040c10700d50031006402c1c10601103008000c00f9a4980501074004050340d04200d602e20300303640010242240300c182c0b19101a000134114041c1846a50241c070308400c024801c200e0f043d1207900084950840d03603450340c3c03031810a400c07405882d80049a428042c0e801030400905d00030b02e5540d81c01580c1c100d403030554440ca0350f541c88018540107905980030418142c3c80e0004039941031103140c0c4100d50f2142c00035002d00090441d1400c900d00c0645005084c1d460885a464581c0e4a51004076149119581c00070120300024000207580c2402a0103140280800d8860342c903034981541272002142e400e0200714060513420b00c01004214052014400c01c0215450090301c0d000c8c440c00480d00d00345850412008a6200c1460001040300c01c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 910063336 1250 910062086 910062119
    0x6031b301506041b0801380301080106170a060f111c060602070509040230030d06050609010c0b090124050a080d021b0f13140609160c050c0301021201 66
    0x80444403d442000301d00246038200c140a000c001c0c2c12040788140029184071300e4034401c010700740303000b03499840f030001c7e1221150400e2090b204550308181d800320f1155503c90401d1080f0099400911801c01503441c3c01e8058234203414160085070ba50002c80b1401c0000000a0801180303034004514910f1088203c2812656158481d00464010100511075552a820075540150f01102c200000301c840005613200000400e580b14644080459803e500f40b801002911007007411120820a1075998403c2c003103280310314580c1034001030204141e480080c502c14105500602c4000002440c40c0c4ca000c80c840f84512040384881165034498070400952421f0b11b8814040c1c003a0b031000e80840020060065030f12406c1c0e040ba81c61503841d031915488103407501910074441150050000c021946150301c4280101400c0e481c00c601c0310456000584e00d0300700100e24900859006c0741e52042d510001508607030070914880111514018032103c5140d40d0340034009001c1100035000e0b2004039515003800c02a40c02d030b20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 910064586 1250 910063336 910063361
    0x9020a0807050112050903090409031215151209080d0213090e0a0b071e030212060a0501020c0f130911130c0503060d03230306031b30150604 62
    0x46814480c0e40d13409142c50285109404c03000ca080e03105c0c400401d08501540c40441d40003464410a141856031003455140081d035503440c100a40041c0040ca185200080d01a5a410050040b010380455205502050790045c0e00b080000f1441c0159a0300e90031607204110001c2c190380c0108116480d50200030001005102a42003040fa41242c4e000690300d940d940c040180a541d00c040004a4060240c200c18007108140070700001030100c40345010b4006d4200b004017244000c6054002801818800d80743e06c25070381c05800030122100801c00308221401203a0310150440c00d100c901e6000203590f4015405e4a40c41a07410300c0d00d6609030014030015115011b170b045c10003410f0881e81c07014990014108c907040340050b145584200c8050030151490603a1060485500030000381e00d07460840064003070b40c0103410460685500740003407028440300c0c68000c400c10b42d000301d2191081c120100f01c80e0404442104204503002040860082282010400d0444403612040d44040113502d2030244102e242c1d8428 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 910065836 1250 910064586 910064593
    0x120405030c06071b0303171e0103020907050d050924040b060904030e1c06050603030a02060c16141c0311070224041d0603011415150301060309020a08 66
    0x2414000a586000c1c407120940280310005840043c0400a0141316800480050076041c10740d41c3c0c40c000b0084801c02c400845200f42140101e03118003400004034a80c480000b10f40707040c1c0e0b401c540030400ca00402400900038410b08000407088100c9601410780703c3e50701038014000d200c1d151074078070018040c1d1801007419205c0710720401c000503000d00b154540107032040d40e00e00c48694980c50196413010320981e03066800448a009081181403c01045890a00c90242130065440d010300340340e5070b17016039000940541c004000003407243c940700300a88405408041904d02c45107060321a61042c401100c1b01c5402a0445010301d01e1200180000e0031054483c0e02d4100021118030319403400e00d000b450790080c8107400ea40d03910804541c6107400500c90704120a141a91181d0354088000421213101200000e410b10030000f031083c6c941031292140f41414030068030041c0c2d591806580442103003100da40c0d4010305641410919004540240d0302800c0b994800250044440c0100001c0c540b09601070a416032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 910067086 1250 910065836 910065839
    0x20303010816052b0b04111504180e0c100f0216120201080727092421050a030f0206090c0102071503180b0117030a0f0c021f111204 58
    0x1242c80c0342281c0d13005084951840504040e403c8111400050007020781071a100c08203100134841c0304500b4184586c03040b51140561802c0c1e40e090307584ea025500c5001c00001d0f50000709080c501050300714492516001058903032492001c00040c03000450b880c6400c0000b200e02c90440d118a4042191140004c0f1120503104540d1424003150070060180000a0400602402284056000b60421b01c2000142880072203198665982c8100c3c0040520034441d5640c00d040480006a81c0000041c0c0740e003900341c518015090030011004003000c0c1030045072107142c0700d07141c0d644081001400f87e5422284030b0741c0e0700c00356288003007802890710300d01a10a00c0e80c1d4000d5840003a1903a0001180c4084608042c2440703107503004407a082d40200380494400d5190612466498104884040a14140c8a601102040ca80290884a956030080d0081000429001c603403840c0c50600030b150219441e8401410595040200c5202014001d1201d10b0300340400d0210903810005002072120070040c045c286110b03410305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 910068336 1250 910067086 910067089
    0x60b0a0f020118022112090a0f0308041406040e090307060605180a0e0c040f050a060f0f1211060d0b09010522020315030f060103021c260c070602030301081605 70
    0x1081410024400c0381703801c000041854142943c1d80b400000d031826605003a540602c00b559031f41c46000380310f2040744002404250600030740d40030320640c1d4101c92528203003400c1c140440c003050515174809500840074440000e000340c0729030b500c91045103038134091a1201160302e040c5d015201140c000600c1411080a003d030040c400b44056940b0079008200800d040c280707164054280f20507074951300d80090415891070404500360300000e00800260108128041d41c0d540a054460502c1c001c9000b42c41c1101410895208214000c0521600681d40500d0b0702100c900010841e9202c140000d081d0350301c4640d2602940f0700315240da030060030b05561410b10202c0004401c4900701200f0600003071a5801700102d0503001416030380c1515a00b0103070803500b099404003c1140e6a030000d1204900c65041204013031071a4070803150000c285a4811850f10a010283d2686002c0e13507045098200c1b06402840303810785042c4100a0080104040d4018503985c0d4181300d8900d040c650144102440c0358032640c03040103036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 910069586 1250 910068336 910068371
    0x40c1d0702060a0c090f060302070507090e0d050d0f020301030f02014e06030506090c0f01090e07030b130207030809010203040f0314071b05120f060721060b0a0f0201 73
    0x80c041c54400190320300300100c181c5940c80507406ca07051061080e0004548203030994003c0546e2401142100d076a00e507111560010384003402d0b90504290880c15800142c10302403409046041510b010214981006181042c101c2c2c00991064407944043c0d0308000955810040e40d403d4403c1e141010710990000040b11200b0203102c1d00c5807151485101e60348c1070565030ba80e40905c2951f520030000e10071940d4a0506030344d070f40b0782581d101d05e04d40202c070501d048a1800d0710041d034001d503041e168a8607140c80c02e0714003041c5010041940c41896101c0c0c44245450b40e034041100d6041c3c0304110700680312260b905008201220052980145070710410620004c5000002d4590085525260422005083c200c2c509c031240030340c0320024032840894903000100b1780d0305001002510400d03200148200a09031001c4d58464a540c0c412040b6007044c808128414271400c00c2084040b213050703100440d4410383e50104d044522550002140c03460214143c00401d5000940c00e803d90710f5440280190f1080e030604124 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 910070836 1250 910069586 910069591
    0xa091403060601140a02010603060c0e0102150613020d1808031905060d02040c02030706020c1b031c030507030e030f0301090b06120c0310050306160207080706020613060204050603040c1d070206 85
    0x201c6440130171070ba80e10504c00d400400107107500c004140800d020080c8090103100d0501c0f103d0740540164144c000d42078070758170411881404010051903425244e404000c001394040181d14120546070b40800e0300d950f0200c1c103940aa10320400145540f482d00c0c00d08043c0100d406d50102a01034100020b100c2e555807802000120660102d60024003641101e03026855442014002407902e0b002207419104800042103d00e611b04030901e4200c203841190382059101c22804100c516000c0c5042c603044150792081d4022944102d00b41000030b03510724401c0031149103412020200c000d014000005005440c0240600360b20804d0603902d190038030304010207917112050b00401064002c0404000662012070425484006000203001c1c0d0b072140c2003040850801034040710710440903100e00040002c1603040010320000700c580700d6000d0040ea071202c0c9030880c0013000501c0140e604035024000401c3c10307682c560085016511071103041800c54a0b00d68468082890398001409148008040082e00c5401081c0c2d01d0303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 910071942 1106 910070836 910070867
    0x31b03050106090b09071112040f1e1a03190608010219110a151d0d030f140708040507150203070b010f050d0818060a091403060601 58
    0x1903900c1c0c000c130306410000c1500000c540510441200035805407101c1582c0c820f005040651019401a400c11420700e04520340c01c0114942d40c08640b03140d07556210b1440c031f290346401c6071f00a420704540b50b5440c40740030000c00140041e02040c04607405e250000c00c01c1060703580700c3d00114001d40081e2101400b40c0e200117008400240212202d92103100740c400140f4000309290b9806030300b81c0410420f80035150b01d48181000c0081291580380d14040c5200082c142414040d9000b000e56030311f9076141d80c180b80340c02020303a031120289451a503c424a03042ca80c8854a07a850181e00d001c2940c1c0c41481c040d856024450f407415030200080c030390380d80074004144107a40c0300c5284403c2c09000b4403580e0741c07004c80d005242c40090000405044c0d03040054011070740c00c140315804621640d10401503130b000180542d0b818401400b100d03500c0440f84100390024003040c940100007030040d0000d28041c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 909892086 910071942 := by
  have h0 := BRFrame.cov_init 909892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 909892086 ≤ n) (h2 : n < 910071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
