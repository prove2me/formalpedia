-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:55:39.758812+00:00
-- url     : https://prove2.me/submissions/0c439397-ca58-4318-8ffe-2cda98ad6099

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 926798561 ≤ n < 926978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 926799811 1250 926798561 926798567
    0x18111603020c0603070906170c0901050d0b0d060c03060801060806070f050438090a210501050c030f060102060c03060f0f0d060c0f03020a05180307180603020306070f0f0807 76
    0x10400703a20f50030031000300a028081c0d070041c01d0344042e9000d550703600003104042001c80c404120300341c032501398040c805c00c8182d145504c120001c2900b403d410101082801c540c1000c00c4182d6111481a03c981e540c6440a104003545801a000103264840081c0b1800e42800c400645034000581148280320105182000150141083d1401800c09095100101c80307903600764040c1b00c82039039100c84401040840c0282c0d84802c08107036251900050070910003e0300303000c080103c0c9030044520325100b03000c40e489a0006142400303441d104000c540c544640b28100f54a40c504140009004a41950880c4007000700302c29540041d02d41c041e808903003201c1a8100d10000c61407000c2d4915500e90000c101252010500125401c801400c0840741d41d015200c0c40c05003412001c074056501c2d090000b034004c10002810010309002d40000c400f001b4180c404260342e50b6000c441d2030703207599064000e894841e50100709600d81409041c0c0d001a880c03c1c55241c01c1184c1b0002480b0381d4441c0b01d10b4052200c05004a007200b44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 926801061 1250 926799811 926799823
    0x90406090b010905070f051614100c02030702030d0905101404030c23040606090b0304151e050702060f060d030e091e0c2107120f02041811160302 64
    0x900540c492141d075840e15020005081c0031100b40c404140120020700c02e41e0302c6070040318841e07041030111040256065881e42e0400c0a116040141441021a0764040d600076104200d0820b005400959480560744181030800c8811542c810134414003000c200110b03241c04030142c2c0b50704107a107054001100c0700d8030320840078000c90301b010340042c0c40081c0210309a803405d51003030021000d4411040032040740f1001c010a44040f40a840c00242d00010208a640300b0000a1500640318201469400510655031001c0750b24001c81c8110b55035170395070750b41e107091007900c94035070080042d201a000c146004410038071020000b80c001801030701c03510751f01c8090504c1a8001d0418010050042030513060103080c2c0e500b1800310100f00380c08004080007051181e19003004845144851110704003c0424440c00542c011000503c0781040c40500e519030130003842980f03d443c0340102112001601d843c00c1002d8100d00c1c142100c646031071189020f00b03540c0c1000d040d13020740f10300503000300e124901da500900e4101d0a06e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 926802311 1250 926801061 926801063
    0xe0702062e0914130c05040b04061a030718050319031e0e0a0e04050a0f021804050102040905060402070215030c07061b2304050d02010504080d0f0806030f030909040609 74
    0x20403507903020034071401c1908203546504100900303503076503110031020000d151002d00005150403c076a00401c10750030f00d44c00580440300010000034003541e46426442000440030803113140c0341400001c018001d41c020940d41a181c40700c0015070441c50408000c20354404600c0b100307034900c0c05511305207020103205109041c04003a0000742031085022904c409080d04540c04c42c1640305215130b002c0480c2079483e4146a9104580090003801ca04c141600d40a040c0c07803010009036008441218003460190380740380c2c0540154800c000059540c1d14012584049803009800c480c895401040901c0c0540c1d12150360b0780d45002d6070b046041c0d070703500d83c030404205922844000801c4c1c076003090301440300d00903c800300c1581c490407921421040d0889103802407038848240c2900d4482c1e0030510060015051403075403240003900c181070041c901502c1d00411860051498038500020780d41105c0b4008182e4014003880e00520180c004000c49403514965a0b2280a0108001d02654034480090140040e03904115406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 926803561 1250 926802311 926802391
    0x314090423040201030c05070302150a061a07021009060807120f06140906010513150306050603090d3b0d060908070b010e040f0311010905030309160e070206 69
    0x504603004050088070411503080c1c2c0402c0c9000b050078034490084080799502c1d64943e0142c0017520712010b18440e1000080e04000742c13241e031981e0205002c203400f80142d00c4d040e11080040d0b2a061288100400c2c0845c50050404020b1020b00400026412401c80781e000b01003401c1c20f60b800c0f051070000c0d00003002c0e529013800c450f6084c49030000c3c0c0c1d0401d441d04000060001e41d0103200079a07a640064516205e511400c0c05600c08040080101030b0040480d5014581140307008680540c7d10030005000d900180c80030140d6801c601304100b8084c0c2c000140781015646054612061300401c41c0f507003540c6034540c148564680c01d00181503103a640384c1c0e49174241254000d0301000380041c24205440075400c181c004131204080c00c0c00100340840e00003035061240d0350080c2c800341c521400c0d80d8125480d605601403a5419900e0704201000141700340082c5108441e02c0008000150808a001d0483d000341d41c845100c0c3c0900100b4007110700c2e030128030a51300c01950f01d20f400d0064021a102019260100700203580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 926804811 1250 926803561 926803601
    0xc08010b1c0c0e011205060f120102070602030414010b040c05091002070f06050301061d1e0609180603011103061f0212030a0209090a0b030703021e1201090314030403140904 76
    0x3090f000316204010540a0340c0b82c501d02e1110316240c1c41154000d4407010350122003030a0444461600400307091300f2a9140d8000740c00c018181c1c0d583c1050342c0082c1d6044610181c1e41c0322007204290709106051665204543c1440491161600589140701302d80c1101d010300040c144541e0f4441c002c01c41d0f90700400c5100802c003011030b92142c00401c290001e001d00d0000824848480c0e050b26a20a840d10003042c0050200c00d041c4200c103110800c842000300b032290845024008803883e0341c1c50f01304030010006840035821051800300201821189039061001468405000340a001d0310b070812081c3d15000241c082000003422780301c00340d00c0e01d00000718580b07620078000304205c40c880664001d0840c0c10016130f112001500c60b40244801d40d000968403d4155000a0302080540307015800600c9103c982e41211481180010201e4040710f2080310b42c00142c2c0d16407900d00200341d44080104c006e00010085541075003000c0c1d400a01071500b5401c488800b10002c2000c0c04117584948c80740c609003510b1200284 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 926806061 1250 926804811 926804831
    0xd09080f0d2d02071106030403090603050c1305060d0b091003020901050f13050601030b06070b0411060702090a050402040b0a0e0711060c0f0c0109020d03020a150c08010b1c 76
    0x11598070001d01d07000d9041c100003069026182c2c000c42050b50480381040785480b0150202c2140080d049848140d0754100b44103c80151038440b803000b90b008034003d84d5025a01410303c0000390079a0340240c000741203000d007002401c0080e01c0c1c000843d002c3d14021035002c1c0d0340322800c80c116000345c41c01c09002e41d0b200c82d207403091100d40500398401d80110307807003030742c0d004442ea03655420420035101e841c00071608104045801c08020101c0d40c02240d10030f03014100010f4807401e034008100942c00c0f9035021a000d200e40c0042c0001c0c49418220706041c10340451f001ca00d0100c1582c0421311f003100143c081ca00c00c03511a8086000c654845c0c10000c082c8030060300300c0c4c440a5843c45143c1c01c103c800c0c1c4d114000300e00306c400f5082c0780303c030041445031080214017103481c50101401800c003180d0344521002e00880d565030b00c418005945152141200328040c0c0d009000101c0d013420084084170503005619421460080e47d101155004154941107400c08080b407500d50b44007104100712400550a400151454491455 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 926807311 1250 926806061 926806087
    0x30203011419020f16020a180c021b06090108090c0414010e06040504033f02190e010906030b0402190f0e0303070515040503071b090e0a170d0908 64
    0x2912500c041094803004503520a4003900f02c0c480c4420b11401d1100802107a800788001203c104112031000c0c0003410000ea907184a11b196480c0c035400b113003003ea00c40307500d022403d0381000f0000d4040601003020220b6100c01e400600940702d0f03188058140b243c0c51002940c2040d051144040d0400c0141090103040f00c50503006000100900481c031841c6600b40100301c0d2401d0503c2070900c11b90703150b141e54610314036111524108604d00c82000300f80040c219500310f9515464103041010200d0302d80c000d6141e000e04425890034080410340c1c00708200201c485501140c0e4003a0703114045510300d050005540d1541e001140191180c903403200306000c50260006d02d8203a000380902000761459075a000025000810107499115200c40600365038048071107001d10041c2d882080750054032820480340307085915900c2c1940154850142c844084a5080c2004a401d840c0159020a04a03900ad03102e511520780d41c801c0d0303180380561f04038021030005c910b0011294051707000c0c00160750409100340c1c4a60032070482c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 926808561 1250 926807311 926807351
    0x50c070f050418030e09092508010e0d0c08030c162001091206020906190809100c2c1e0f0613031101030b0d050616140a1803020301 58
    0x5180903e10702a00510151418801481c900e54140d44001049140707200700484100090003e41203401000040002c029109038910f8075025030302c4010032014500b10045084601c1c131903018840b44c201e640c820541d6a40314581400712a0b120701c1c12030b1203448a00140f003450103000b0b4410010703402a1203103410300c400418590011200c0d07038094845d01218400440728040284140b14502c0c00d010803000015103a5005001c520001400e01400c05070001a0001d04003900007808010030011428094568030900611100d507540040500080f1001c40c0020450701061140e4542805c51308003200a1a48080126905803002001445880300c007507640311191100b00c15080c03055010300380640032810140207460781b1a0034281404022865900c80040d01c0c1001c6d141d85e410156140703d41c50113030340d9a40c00351403854041c03c000d10712842c00301c822800711641d510589051045010000410500910131584084840e04e8203402c0420300801c00302d00009c113600025415402c0c52216001040d00041c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 926809811 1250 926808561 926808569
    0x70912030c05071a0711152b050709030308180601080705010206130b01033309050105090c0a0611100e0102030402100e0109090902030a15020306032109010807050c070f 74
    0x40e80c160960300c50f41c1c00540340003d042c0b04209441800b2010200310250442002c51030013070460b180504602c4070041b2164422149140039882c000c02058001400540c20161038008840c01c00a8ac01e20f107038080c062100394031000342080310460020307a4440d0741d00d688144025084003140c0a17941c4603c4001c4d1507400740e001e028014810032001481c6041403903a1000e100360095030000e5035900303544900442d80582c149199001802c0e0060701400c1c0440404501c581ca8041030004a0007e80d10782036083d510701400d0313510541d1201c0c2a0300d1003580c914648408844090814501030103c20a01604020481c4203050000c0c1c9090040c1400b0601900103510940c4200c4860600100c0403500380c0380c1413030700302086001907107d030806d020b000b00f240d201b0103200d400281280d42d0341100f580c03220700010110060b01c0d00940c02100344403660404105005200750404090149403007000c100139107a0052002d0130741080000d9011800d036070302a8045540d038010381415600c0450721103407000040056482 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 926811061 1250 926809811 926809813
    0x61109010201110f0a0f090f030809090601110619111603090f030312050417070302150a23070c0c030f1b150309080d0c090906050405011d070912030c05 67
    0x101c0012101d543c2100d40c8102c54001d1a410441d0f02d25048a01e41c800307039a000103101600d20b0105090450407134140c02548a003510958410704c02c400e011210501524050620148079034414000501103040d030b60250381c2000048a1001f08401d4001400c9411700e1140f56240c000b400a4a400042d001c80e40c0c694042c0d21030504032a13440ca406600c541c1688405000070380c0d82016000b05540b607810054106001d201c2c038606c011a02c20000010b680510300860159000441403040c8034207030303420b0780c3e4003c80c5804100304000030f03c01c4040d50701c01c8205041d410101010700040c1ca007070183c0440301107107801c512000d40b00c0380c813031624412000c10f450080c1c0d246894800d0092265a056407048281c038420121000300c219038050a9000e800d01150840395034205209508040d0206d00c184c88000100d9034a1104540ca4059100111000f81d003205008905110052110320219103111800900c542409001c59603240307402c4031401200c1d04848460440c1d0a420b5061550100c9031408450080c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 926812311 1250 926811061 926811071
    0xd15090b010f080a030c1209180c0906050408070308090604081207030e030a020d030e0414090106141f051303050601030602030402013905031b032203022b061109010201 74
    0x164840380e40c1c0141d201300034009070b0158450700010b403213010703a904988000d080004026444080c1c4098220100201c262120354489074a030007140d0000c41040100300360f00340b81d8541418008255125260350001515648000958500756110002140c004024044c281c840310301d884001c2c2c0245912914003a40007400500108005140100d00d601405500030074100a0b50156a415144a41e500c0d404551003540d03012078204400560031018460096407000140300e42c1001d0382d0b10000200300e05802e000350046a4031502028094011403446c2500781030140c4c071400006005401003020b07070401085400f40d00c000100300034594000e0740c0140d200b62501b60482030182d43d80348c0e1240201c6c3c000c078114840c10b030b006894410700160a00b48140240103482c40c0180070241c00c0d1246410400441942d80000b81181e407a2a07151050304c041081a02480d00c081e1031074000540c598440141c4054800c8040c10085101c0740d502000d800e660b9002ea014441522800d41182d0203411090245015500345 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 926813561 1250 926812311 926812319
    0x11e0b0f130f1203030e0a021206011a120105011815021e03210901020909040f030f0f02030702040c0e03010f090c05060901050d020c210307140c0c0d15090b010f 71
    0x104182c00d0a68070181c00565042074291012005007031034003805d11040c05000c00e80d6026031924005648040003050081030346526040f00c494840c3c00c0381031105031640c0b00b1310005291541030340ba951704680c42440c00300d01401801c0020100320341260f01802ca0b1152410807501802e40116240074501a003003101c1040224100604e902e0b40b041c4d92400542462910705010050310403805242c0001c661000142080081c6d4041444d00106171820b50741800c2541113031003010303841081c103881a203035440c00b1258003d480c280656079024106009105549883d402c2190300d200d030752110140d80e0001c0003408025503072a0a01c00038050b407401034880d100440004140b40c01c042044400b18030041e940e592910740c20034a400000c0d000310280b00c0c82c0c2d00506c5100042c1001c1a101e440e039440b851440b281c0d03207041030900a03004104010803015020401c0c044440404d801049480b04800103645c0010100114070b403844400081c184541381d02841c01e1002d8080c0201245507178160b6800260706000d02c0d841b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 926814811 1250 926813561 926813579
    0x411131d06040606050a0804150204060917010603230a120e1002010203060f0d06180b1005030606100c03121d010b03120f0c01021e180a0b03011e0b0f13 67
    0x25900402003c21400c12181040c5846800e50548c0180900048481c00130000246010f0342e106904c5a8005076494600f4008440c0781003140d40f0400501d0001c1040c2865030f514000078501c0030701d0008642c01aa2103100480740148034202c90180d00155000c010203c200d000342440d00c00d082d400303014254080c2c029140500510889000e0310700244050030210300c043c2000303c00c14610000300d92003a1618441000000c0102044a8040c4101d20701041480c103000d80610307201e010360015100384d00103c24006562103000300340d2036603841898a0281c014480c00c050303c0e000c1c0c5c00403100302414504030100302c40250031500c10380c100307070034038001d0007818544000c241c2d4071200108100d021080030060f02c000319213040010301104050000140c00c0454244c00f40b1048510010383e0340010000062001a001c1c070b005410003044411254641e903503042c1661100d031400140260018000002010440c003202c02078864020007031030106507500c4d05600c0b0303401c1250304480030303400e00090300320b5020030704040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 926816061 1250 926814811 926814821
    0x60109030308011a090909031e030708070e010302540d02011101050a0f0e030a080a0b220f050115120513060504110109080c0105090411131d0604 64
    0x50550b951040302d03402d05803003100c3c0709041000f280c00554104481d00b003e4441500c0740b07101e100058059510f511484001305103004072880301c40d1004408004110f43c05800c6018590070201620303008800c010071000603002441002c1e0003480081901c3e01d0b01034080e0f8421080b51402d1500c1c0358203072540040c1c6c21481e54007407040d500400098031220f0006c10509000804030100e500500d416011982d4669207035007100ca040d559030000301e48412803150a03c155020703040000060300c004500d86a0303c02c9009002d42c50142c000f1a1560701c452981103241c0e0342902d03c0451458034619442d000c0e11000b0b02800401001144550f510300384000042c80000300501d42c07204d1505c640b21070190203000480c1800924001b020041e040c2d82c00000c0c20041652481840d105604c00c1030315455032000307600050010542580072403080d5110070749030030352a64410191100481c0584010404250040b4582c0c403900034807080124054241d8400a50118255000d168103600035082441c989c0300c0c00c0501080d11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 926817311 1250 926816061 926816063
    0xd05060f060901140d14010f0f0b03040b0402011436040501080a080304060f05150301051f120c0e07020d03060501020606061903150b0406021002160311011b0c03020606010903 77
    0x203400c02d1a041000c5040b00052001402c090070009480440402e4000450750a8108011241907408c1c2808840c84030030610002c0c2512440c00c0d819490540e40d43c03070254100070300090410403258203052820174000166003405111003103540401303d4400040c40c3e540000081300d01c0a807100000701c00035080c10700c580c50503502800c01816150507551103026055101400c21501a903440040c1030364101d0520038a405800700c6140c195000310011704060079908050200600701c0b011041d000201c2040e000300e9011175800003001000c480c003070300302100c1c480300a51000504003001c40420201941c0801c1802c2919070700c0d2001c000040c0c8520049aa45004031074068211100304000e210650502003510701e400880c1c600440c07640140310a60141c22411380c000e4040e81004a0207000c00340e010f02070303030001090118045040c006050440740c40c6441e1000050305010b80e0082d81c031010340003034101c00d41c00d0b12103404814020b0881c540003058041c4010003030f001070281101088181d0700c02d000c41c00880b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 926818561 1250 926817311 926817317
    0x803070308100602060402090c45060d0f1e060807080c030d08180f01020c390112060e0a1d0717190b100803040612050a0605060d05060f060901 63
    0x5070f8444d070034450480c0c000740040692036414450100ac0d412140d01000c0214255405010803016507119020b900c0c500c4943e203c2405054548211a0388400c0b058070038041d00c0510106407020410502c0d4010481d00c1c1d801802000e620990790003c4032141c002c102220078160444180607501d01c0403580383d4107480c02c8640c1c9030308a0070803000b035103100b041281c2d080040b10100d030015403046111146054458040c49945075004158508091001e1181380b580703d030310302031255414010404800354484070700c501440c140c04e0004400c11f00d03441482c246a0007400300008000c2d1a840702285030007082d080300e148584609144201c861200341d50a083c01b5040e180d4000c0005908003c0071480d441e9405e108556a0b00c01d040b074000054003800c20036098180076000682c0c1504000850100f03100086c1c00c650400c0c0e2080008201c4503902c0914003c00701000039001a0540b2202103050162060b540306560000d008540181141015840140202030417500c01c8118040001481701c2030050084080c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 926819811 1250 926818561 926818573
    0x31e0a02130b430b040302010e1504150b0a1206060b090d0f0204022101080c030a08033601020c010f0506060a0305060402121f0803071113090506010803070308100602 73
    0x19034a00e0b44280a507441d0400f1a0703004040344036042000c4a07a15202510f400c0c0000b001e000078150280700e4903001000c0c40c0d003c0c1c0205152850b4000951401038001804070710410305000e400211641b10700d0100c0801040e003600c841c2d0b503406010017009042800c0c0c034210310b481d40c0000c0e040071010271904003c001030102c0c0c8400f400390710f4000241c0628001a608642c007000491003682020b0004140807111410039072680d4180024245494001543e180c0a5405400c00501151802c429254001003403544040e21000f050741a80d5159001c0a5100440e00e5200101754060419005081a0f1241e60020000e4407100f003800425120309561403904500c040000100c0c2e10720035004154440e00c0038101520b48045098030a00990f01241d40c1000e5600d8006000e880d105001030090090a804004504001c082e49480090800d903c4890b0310855108102c00c0c0d42c408036401603601d071038001095480070340c1d64044894481d07201d50400c80c00102d02c140018a04007081030181d00ba21030644c01846 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 926821061 1250 926819811 926819857
    0x60906040c02070906090609110a140703031e0c080a290102011103041101020708010b0a0e18100c1202040807030809120307110f030a021005031e0a02130b 68
    0x70003603024560114011000041039403583c03409520004c01c0c0700c080024525282070402c10444004005001e1201c008101c442d0302203601060481a00340903400c1c3c0350740c0f000a4074041d4000c0820440d56101103018502c4014501940c0d4011414100c481d1a924000e0ba0303a0461340c8121740d4001c40f0000183c20402c00c03000c01c0d80e100c1803000c6007460103000014100b80c2044007804541c0003280c08541e5002c05005080b0a540e0600144009011100c000d002c1e031604807000070f003d243c15000b600f00c994580000103014003a0601014000f40380181620501a8911507940c068051401d0040215a805041c08403a0b10b2900c00c880803148501c015180090641d900d8000960003001d103c0d910448034803000301d13000000d10042410f6803080340071446000010003800070303150f030840b03606119030404c105100250b00e03030420391503d2009524101c0e81d01d6691940180144600411074600002c40c1410032100781100d43c014280340e07160300c40180c0e80c2c1d90707500810401880750f50301e03c0050b00e140c80b41d544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 926822311 1250 926821061 926821069
    0x9040b03150c0a032a020f0a08030f070309080a030e0610061d03210405030607030219120e01020a02060405060c030903120a020904020c102405131503030f17060906 72
    0x142c88000ca180c0800c940045c04032000c9410341800a14400d89400c1c401105400d0f01000203c08a05d003103800f4012a60b4241c448411902004001c0140000c0400c0003c454030701c207502941c0f01035030005525450300746001004006044100d0028a2803246074046a00410281000d40c2180c00303a64440102070080c403038410400800f035030401e80520400ca130f0038468451280201e8000c000703203944103460310700d44400c0600c0e00304082c01e0801071500c1040303c512105051100c11405001c54100b030082c01c2c480014000082a82c4078be14403036544013042039500305a011640318083d03070080080303d1064a0300862441c440c40261010b1400d540200f140c0b0749003108100410383d0250402c1401403d00203d500400c050b68486640504690082c82c40307241d50080601c50452000c24a40040850304100b030f11042d00391031036000c2c01e4800e45010502030095405078003c407002c2103138004682c18a030342d245800341c1907040941901000c100b0051030610031140e400740035489081c00409400179030321203a0a01c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 926823561 1250 926822311 926822317
    0x4020c030f0d06030c0e04050709020717130515040905011e05210a060e011b1b02040b0d0308090d031b0e121f0b06040b091c0b01080309040b03150c 65
    0x15441c2d4a4032480004081340041a1140003040e54001040e0180b500d8a059030500c2e5068011800d01407041c400c2c0c0000c14410031304c0c00d81d50f0a0031420f03907036600c0080000008900081c0d0040b640304071045034581c15540110054000c40e80004002c0c40b540c0d803500724143c400c106c404c028184941840300c04000d540340030706284004100005a00561981c0c2614581c10a0b12078101a41d115444040901c1342000034440d820480c0c050284000c402da01e1142d005280c0842c0c40000f880b180d4107059200b06640d920360100100c054000c03e42782c5102418a400742007007408030303407460a0740a54003010075140e000f402001022405d041c04284500f0f0035440035500c90035519201c64000d0540c1c0c000c00c0754000304000c68030746203c640c0c0c4090440780411040000741c039a41e80c2c800d40658000c0c0410051180811f05031151081d00f2205590b01c683c404240000100e01d070b41c005440d00c6011000081c03c0f4070084020858808282e41c184400b0742c2c0711044c540d480c0610124108142000c03400142d95141d00d00c09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 926824811 1250 926823561 926823577
    0x1002041d07120203090303010320031b28030303140c03010902070821010f0923060f090a0203270d080c04150e0301061401050409020f040f12060b04020c030f 69
    0x10b001051100e40000d070813600b08032254940c941c40080148144064400b908a02c1a11a11001700f003c0b600f2000c25100c0c0b408426014410042c0c9800c0c1405594009030005441c80282c441c042d030805075400e000452116100c02c0d00030924200d0003c2d03040d0f10024443c0d108950700d903000ca10356480e02c40c0d024001d40c0900720a444600083c020000840c04801503410003120000450500d541014500c80c4c0000c0240d02011607141380c154000002d1001084c3c00010b0310300f000403850507075215004114141010345045910001d40030401940d8070280d4059401030140215401d804124513400d04c110000c1e01c003104e80706038048510f40c9032403440340c03001c2a403100c14161080d040580e144850300000c883c920720040800c031401c2c02c111041c20244540d10090040b0803c0c2221f03880d024001034060321450140c03003400e5400141680c40004c00e281143c000700702111098990a03074901d0382900b1941d01c200121071007800d180008205203850700946d008441c1c424090f510b80400019204507030303402056 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 926826061 1250 926824811 926824817
    0x2713021c0f0212010b040605100c0b130605250c0c0b03100509180111042d150801081e0705190e0106050c1e0703150b030a050d021002041d07 62
    0x75401600ca4200b181074070001d0301c001081500300c2c0f8040005452031504881d00074401e00346003140895100b103460340304507049405030441d034444100303401ca11007511030050700a90501040c400008200c40220072021000c0000042c800d039003140c1201c10848800e009426103004074800d01a00181200540d04a007001c403141d5003455644011072060075045506001c000208000b000b042d4000b8090800350035208140c1925240c00c20801c0c079401400e56000540e2000b2400c0303803100855554042e403000e000c0103050b03101c210740442c1d0000c0082c0d809010f00b032194004e44410860b0008071000381000002c080c0080c0603554208002d011599240e40c9042e503c003008803c002078800301c3c40f03501502800c16951003580d9850494051441e00d0070250b66001c2074098080c5c04c1012080101c2c10308281c80d4404143d000080100b203620000d00345c15201d0039414000e407482c134001c004e0001901c001c01c821580a071450343d4011050b000032801907104d458100541d5024041038141e5440520741d100b00f1501f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 926827311 1250 926826061 926826083
    0x90305090a0812070638010318050d03090f050105010e100803070c06030b010306091b0e09090615060d0c090810020a0504030f05030c12040e1003031e0e2713021c 71
    0x2c1012501229011b14250b6180310101d003115641402031034100c0e01034243c580c0c017810480c0e864a41d00c08040b203500c4105559a03c1c000300300200d80c0600c26419030001d0003031000d542c40d1002250000016a0503844a071850080060561800300030b580601e90003650102c80030b80f13005000e8000d04807081c841410107a50f0b40000c00d07100c070070b0b11071141d000b40080c042c9190001208406400a440c05035014842c1c07000c2000c0244059000a085a00500c8803125507000b448003000304003a4007903c4800194681032070f45004640780c2c8081100c0031100c0c40b60403100e403200020007010480c4a410280f80000f0003c020900c007041d0003040000b031580c8240126403a242e5044000b07401d1443c00d081d0071440d050009810410501c1a14456030000b2040c82064402481c560700507120f841e05605001152100c5141001d2150280b0309900a507440601f041a00300445220004030741c1c24034010300d0084002d40c02003a000f114498890a503640c0c00341100c07070044136801d420b501101c080c8604440e8031100e6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 926828561 1250 926827311 926827361
    0x8040803272a0102070321180b031b03091b0a0b120709090209010503360d0305090c0d140309030a030f0318020609060f04030501090305090a08120706 66
    0x10481a103901c80e040c0d002c5031440020b406440700e07400369542400d0440d4440d480501c00b040c40c2030144421002c40c03041001e54058420005d451082c159411030f014021040800580d03019845c0003144100b609821201306059076600c125801e000076503101b0b0300d40e0300c0700729400c001035450044850f12000040c2428140c80e500c91509016038001000550403c029406204980350405640c0001c1d2680200c10350509015800080440c00001d00e0b11039005a00030185030306001080c4821003013144040d900c0d025504541d0207540c3c1d0102032000c2d034002440c3c40009051070401241080c07191800421481c100c1403591104103442e10b45481020903070000304031103822036038108244040c2c58420340300c031060807040c080301400701c51640e0504104031702c00315110401a6248011030780241012611541c9500c554040404140265000103100f5880c05151200341500080035040c0071a089880b4050180c45800090f20340c0b204075600600b0150501c003860010700b15410204010000080a440c50034003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 926829811 1250 926828561 926828563
    0x17040b060d030e0a12021201050f073218040e030406110304080f0706120c0804021c0204020d0e010510060f1209050d1e050c07050d03211a010804080327 67
    0x111781c40121001880811001141402e80034070701d10314002d0008001900e05008284c03070441c401401007007084003815219807039102890140754800d02448012855454181404840ea84000c0d0203000340c0310001800c0034507281c980140b0b03911000d00c0700954205850070a040c3d445007a404259402800144404118030100300715030002e920103440241045c03450084050b0050a42d5681524501e00b07000b100c1c101d540d080b20907140c1180c0e0541c1c1d0700e005001482c3d411040c541101d18001e40c03090001a090703110481c1a0841c41010102100800040d140c0408100f140c8501c2d01c10080482c03004070000c26024020707461200d0841d20303800040340494542c0e40301810829003085c00004a00903811800c2a440302c55055110030070641459443c2c40d800310503441c0c3e02d0304184610352017091007100c500c0801d481248640964400100c0c24401240e014130180c024014040c455154800e4440c100840c0358401d503912801070b90054643da10f5030711341000504548000d088920030360040d121007201d0b1184 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 926831061 1250 926829811 926829829
    0xe33040302010209010e010f08070c320d0f0f0302030c120705180103060b090d060e0a050a06051005090112050c0306070309030206101a0309070306060905060117040b060d030e 77
    0x312950005a03110000c1c400980902040b211480c100070101030902d140503080f40c0d40c07030f40084403070400041e541c5540c070b8091a0b6071100c24003400640300d101031a08502e64411204038013142c004081d59105240d410041f0340809903842500009a0085242c020241c040c1d8000d5400215851210f480c200d41e40c64880b0070023405661482c000340000a03501d600c039126030f21601d001d4800740703020b0007001e03d029188603440c0070b441e59140c032405503480040104030241d0f011614648201042d2650f04240341800ea803201c00050003540c41c141040005100c25002c1e6002d40f007910030041c0441c2180c1d00f841e50aa41805501100300d404e031041583c250000ea030100200b500c22441541c0211b00e05040c2e1400a040460162007411150307481c05051080a049070040c801e450580007003161a42c2c0c4841c550382c902103c5a00281c4401c0c41d010000ca90342131940c00c018490002a21101039280d40d81e800c2030b050380d00484010301005490008900030380303480d124840c5414082d1400601c2c03050808000340150f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 926832311 1250 926831061 926831063
    0xa0e060d0b030a11040515010207150c0203070e01060f020609070b0f2101080c0901080606010f091e0f05121216060203011502070b07050d0c03050714010608100e3304 73
    0x1454013107085540e442c00780a069802041c01e0461000007800d140040e503034084901a40840c100300c0e003507140c0303031900c00c20103c58080e40040844900715a9034140c40c0302c2c9a0280241c0c0c0010321000d01d004003040c000038007240288907407401059110305d0040410003907048500750035003d007410085848402b0400b112241c03420509400120194035001d08140742214284a86010341c9802c0d0040240e281e010680c56445131080c2070101050b102584111903903003040c6c01c4080010060700f44074555415051501065440c810b002c1c6040540704d030b08028441d4400d42d407054881e032240035070311420380c600702c05000f807040b200c210030b60380319425510030013641c02c26080038038840da0400c00f1041d2190304020000003064001c41c940c1c9040c503292905911014085499818090036030740c00820035110300101c0d0245904800500038003000d0000040c0604958400c3c5540c0c0d01c9800c401c2c8180490506c1417a000c1c40e400401442d010b000a9041e080d950810701391840a482d904481d10f50412049a1445c415 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 926833561 1250 926832311 926832323
    0x30d0e01050a050705160f09360203071d0f0f07030f1805010e060105010c03050d18081612020d051c090f050f07140904020103020c0a0606080f10020a0e060d0b030a 72
    0xe10b090040c2e03041d1f515007030740c810703401e85080251251820501c45e0030a901d4203903458a88035003840030f0640c403d01500c015402501849101c10002c2c3d0020300002100e4075080321045505161101040f1415211056400700101600040030405080c001d41c041040102c1ea00d10214000e4031a1480600c00c40003d101643d0310f035141c802c1074180303c1c000d006040c003410003405e00807480b0314142c42c02084c3d405451102044681d40d111651000740400580c89451035211951a580b011544801d5008460a04c012205002003801c1d102046002207104200211140d49072410f1084c6000036a2483e02a48900e4161556038840c20300440c1c482280c0600f0980100010842050f080da102464080154090001d07903c2020f000061542c4d40d41c400d0b5000350302480c01686440311138460609040000c00024191440d16100180200021550041031500c040558082801d05403124041c1d07c0b43c0008003000914031940d80f0494034000010740070300b42140308000307420301101001c07a180c01c0c5890415159 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 926834811 1250 926833561 926833603
    0x5040e07172103090a0813030203060403110606121c030b0a080a030912110103050c09091602070501020c0a0504111209010f0515031f1503060b040b030d0e01050a050705 74
    0x701d41002e2401c1801c0c20300e041c40540356180506410b511000380710001800030303100180310486015001d40709406980c000341a41e8813030510b882d024044401c2c80764111030a00498001445914254849901005140001e411040c1e0000e645d420340d171a05072110414996100c0340d001b059140c039000c40010341503034402002e02a0003810041c001845540c004c51186501051810014002100c04510a00282804112030311040d41a030b0213402984e0030340c2d400c8a4a04208414a814041c612103412095005c0c0d0789071b5510307a0012a291150841d86503003060881c02c2c00c0100d41403546c0401d181c080c00217012800c10b402c0c5100700344129000c1d11011826910b4410400800c5803505c40c4a0304030340e01c0c3c1020203541e81803001290719040c1030740ca00010480d0341e026002821002d50400c00c010f0440300e00b00001c460301c81c07401c0c0d00140400388001c1d00a503d48000300c0c41d1030400141c020382e5000140c0380d050840d6800b0004440c076500000d404401c010b018070125000401c1044040c5031600c0c00d1031040c403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 926836061 1250 926834811 926834833
    0x1e020306010f2003030408131a071b050603090a0c150c080708040b07110f01110607080c0c070605030406050a09080f07020117010306140601030c0e0d050c120d03061e05040e0717 78
    0xc0e51302c3d0f82d00603900070742703200034600900d003010740850b55074a922401164111205003000400404942e204a420207000003c11803580c2000c80c3d440d010910031188e41c80450b0721800e203100e140751144000c9003c5240740f04840c010a40080103400828810f0078400d260a440e403c000005030400c0204544401001c0415480c5181058503d100c036402807801c004224140c1c0e1103566a500c02901c0c24080c0705040c4042070050700100c0c01c981c492021071041320010713561204001c0031540704032030980341c0e1072500000c40c60300c3c501c6000305030500382c0280f000b90400034916200140c0d81d11044c402c0781881803155030300c501d141200201c580214000d0100007071044014041c2c0c000c0110050250b0304051802036040c05141e0044020980e55400b5221540610000d01d407107858401241c4503690f00c461001d41c141d071201400240040301000c603550a10000d035450f11486a04907403100e01d80c1ca440c6a0503424081030515074070400007082d0b180308130365605588074005144003410b107050541541080403900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 926837311 1250 926836061 926836087
    0x2040f08060f0606030f040201031104080d020c10050901050c16090b0127061b0f0c0501200a0b060d0f1118090601051002120a031e020306010f2003030408 68
    0x7560069440e50944a145010b00c00680f40e40300007070900d000e0b00702c5000401e0035a44a81d105505280c8001405555203403564078665854024010a03001840f90143e00301c00303400c11840c0c11801ca200307510f595050000280c019222038000440c80341c454030840b0810b20500c090070944400500c080c01c40011200d85110005100d4010040780400d065104528500f541844144900c00c031000ea01e04581a03c40001da21180100c01580282144582014100c00e1000080c0428205c2e2400d8072015040020080d2111120f01c40c8202907295070001e1210704007255282d88540d40c000001404001d0001055461305140821110144d0340546400305c204140d041c00b0100003a01083c2e0745000d0b0070361074027600d101d41e600c0050140c91f0181d80c0b05041004054001c000c035182107a051503200b525000b032110014014a00d0058491110300b208840d02c01c21000740c401c03039000300d0045e0340d0300007461051682650045149031040860010304084050310f10030500181d40691303c0b9402d42035407119204102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 926838561 1250 926837311 926837323
    0x2c033421140d05120903030613050a02070b0408030601030509070305030406050f090d151d030f07051e06041a0c09100909060603050a0b03060106090e06011812020a060219020411070602040f08 84
    0x8040907038801c10074801980d9414012a11a03809e6a00c0418941e0342c040c01a000b80c020700c45c000740078101c07504c1803004010319600510312407a4282c0e010846c654a0001c2070740d0300c0c2468070006e4101d0b0010002445110320401c014403e9003120341d04286448141004104040d40a400c00c0e6810031038032001401e100c62a0080311040d0390b180030b4150304880c80800c070036101d10031100d20030300e401d01c00511401045428041912902e010094048000643c6004961035007400c03103044414034401411800c0502d048d5600e1405000c05044150400480e07405000d00e21000c503101d0700510103800400211002c41d401048040d000f651740205040c2482104002940c1540301100c0c80794024800601c0060340c000c000d04100d40d404144100b15490b1600183ca01e004424603107030007203100c0e86012030000d4014543e15542d900c2541c0305580141e07a007904a8032031484138151180c0c0040800440301516068000c558143c443c046098940780305a9121000c0b40d00981c0180c0851130030360020000c000e400d01107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 926839811 1250 926838561 926838571
    0x40b06060306010f0e0a05120f0105010603021204030f1701080d030e070303020a150e060103080405100309120c0309090515030f07062c033421140d0512 67
    0x8107415030400c800040c040c2c0000070060800c01c444030100c841156201000500200401342081003060a0410b42d50389030860449118513035801c0c540006401c900c40c0c400c507811151002d000b14000d844036035045075885015440714041000164105001107989a2028020b045041c000c060100c1d01e01406010f90710b46084040003a08208010001b00b41c02080040f082680183c203207680b501140d240340010700041581e45c00901c205800441001486001001039800032503200c80103ea442c50b0403415520344020080030749000c03494500c40e482c00754641003400c6100341001c0c1181c40e12403580c1c2d0b040b207000701c5c0c980e503550300c80d508800c6060600f441a0b01c40c0c417218602a20381c560504501130803114401555a4a00000030a5070345a41c04a00c1a41d01c0300b04000c066941030804c460350f071004060a010007030780c42101088080c15074040b64104008a40000070f9495505094035400d00103045035201c20346140c0e5060003209400502482088100501911096210746d4140c1c1500c094080c0101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 926841061 1250 926839811 926839819
    0xd15090c0903050a0321021603091e0302040b12150403080c07050d05030c0403062f1201050d0203210a080a0c0c060b0a090f0603051c0512100b0403060203040b06 71
    0x1c0140007142011484480b10358142c1000103001c0316011a030151004800c43c0034488034404541d4401c3c801107080c4244c1c840e4000d50b070711a4107035150484560080f000038411140c080b2a40020001820160001107000078010180b181c48050000d00b541041d4207408035802c1d0140c040108800c1640259070700c1c0e002066845001e00346215940c0d46955800800360075414440040001403211044c00c04a0340a198800b0301807004031420000b4191241e40041442c00c418800c1e5400450355100d031050781e03240d80ba00b04400045da460982800150f44031540140d17098011003080414404c00c8a01e2507100d07030b013501409940c90f401044010720780c0f85c02605039000141041600f140255103d019141107503009040010b143c8481400500c03580b81035409102c81c0340c14810075460741c1e9442c0e4421400c90340240c041c1d5041394408030491048501e81343c2c441d004103070180681316031110381a08840d40480f0000072910180e4441031825842e80007039004480c6103400004000c100b1020341052500f140080d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 926842311 1250 926841061 926841077
    0xf0f090f15090f060e0705120303091b030309010806060403050d05040e0702241e0702030c0f060709060c060207020604030f060f0b10030c02010264050d15090c 70
    0x2a0754103000304103e4101a160340e40f00e0300404020b1000340071700001414010f1600c0c0c1c1071402851055226001120342c0035a03802902032207240b4003000e02404000700402005545000103d80041d07076030142c041c0906d604984103200c0880042c408109a503c035080b10345406461b28070b0b002c49510203a0009204030f085400031200306002e20030781e81c40d0000e0016001554581c40d9102e800041c001d03020300000f00700c0e0714400d03414032815a401100400c0780d01492015112100c072018807140e546c000644802c80050075000c41040024440d580046416120b6580035141c005180c0000e8420b4219400a032046c0c1d0300030118000f0042030340320301d03d4a00d02c0d0318001d1003002e50722030004030b00c0d1907400b42042c10705440d86000c1001d6071003941145d1524024010074400942002c1e81c84040fa00e1803007114450080001c4140300f510204440e5000340080883c8401070440c01e1400503000100b60304e901c009000040c0300400018540c0d00a81c2d00106a20044400b4645801d0a21055030010141007080c441c2c03035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 926843561 1250 926842311 926842313
    0x31903150605361c02031608101505060903030c0304092a0e01050a022d15100b0901120f09020f0406210f140f0615130f0f090f1509 58
    0x100100141d0700744104c13441c00d44c01c0919540c8114615800c038009502d03014000800300301000c1f4100350b0342a00e00010480d4180c0500d14071440456107a44c0300c0c071100d00c13801d413000c01c110719001004007511f81014007078070304080c1228941451500150402020503481d107400242c0d01c0452001e0951030405800c48030142a452000a4003461036689401d0402c00006003074120503008102d01095050201d050303004005d0b41d84242070640c401ca811001182c000d0f03803541c407c2c00c3d421014250043e00c3e0100c820001d181b4240003905642d1003c0d4110741441800c0b985000800e13094811010241820000440c20020901c1041050940c01388410b210b00e107042c03001d1110000d901c41100314520009007929201041c0d08007103c01e0013004030010454503005081022a05001c6218405007019604542032a241c1c09080d402c5520000e5030160071100c40d184407503009102d50402c00c5050125000080e00c403660024400543d03102c0c0000360b40b0203804060800802120411184024000740b02c1040301d2006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 926844811 1250 926843561 926843647
    0xf04031101021204050607020415080d0c0614040308070f2a020301060e100e09070306290904030c0f0311060c210403080f09150411031603020102031903150605 70
    0xc0e480003e405580c0c1c07551500b4040100ad40610081d1207004100d42c11000304010062481980d46c00803144c2c0c80c104040740824842e6640c006014550584a240c296034170440200c501c1010b98000400b0001c10894020416040550f50107481100344400c64112400c0d005141c20b4440b15440218407901d000200028000d1040b00c0320156018504c0c40b07481a01e5080e01c0360300d449030035000588050702d00940300b80c0c02030b1402805800c5c0da0b0b100c4464480f103a0640100021490100c40c080c0114582044030303400100040f18800c2c440c0d2080c02c1415044540c10764052402e1000c44050044040001c1c100c0000410311080103d4251070707100900c0145031580c1c00030b00d00e0300e02411100341d42c040c441c046240e0640502010150500d901c1d01a10b2520b06030502d1200305031403544d5035010307000e0f0300e45903901d00c0d01900d5500156501a0000e40c5400750341d071001308210824490100170075507103828011103085003000710401070006640d03464540b145c03150b0b0300301440d00c075840e220034002100c800e902403800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 926846061 1250 926844811 926844817
    0x71101081e06061c050c040518060f0105071b0b040815013017090906062b0b09090717160e0403030618060e06010e061e0f040311010212040506 63
    0x90944503543c41d003051004a0f0f000d458013a1110001d40e0616040103414001e400c007a20884e902220040f0104070200d840f58444a000c0c0e6250307170407180b0780044484550141c3c0091010038410000c120a1030341d0290400380d0108143c11403480c003200064100701050040184001d1140320070010b940a524044100050b038a100317070041c4459200c1c020446070141d440c00042c0315107070007948112000b43c80d46180c06656204880c0148035000340000b24031981081000d136081e8541420400b04035541d9003001600980c404101d0b1100b15403610103e40c40d540b6214099405007620354000e248681c14447c10310300d218200c0103005a580d018000300c80c0c10a481e854030a0845504022003105500c582c14120043c1c11507421100b0a0804586d11000010031a0b200078103c8910410764442500d42ca00111400e2003812025580700506001d80d404001900d41c854034086600c000881c50315107903200c0305195400640c03003038403500d01c0865420300550f01401401450b484c010030546c40c003810500001c407640 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 926847311 1250 926846061 926846071
    0x609070516150e071221020c1201020d060902031006030903050d020c1905030a0908010513020609130c02100506010c08180d171e071124071101081e 65
    0x40380092140300301c00302c5640000003d0000409903041c00d43c030340d0100450102107850032a5540b6003000968458248880401c01081d100d81c0a410006003000c10410504150b40707080c0d59656007000505881d035403038032494005100171280540c0700d2401040ca01110052a40154103243c2042001000a5400030440300340d40c41e250303001a00c6403544403080d03250041c201c1c0049807c12000185c030060240000203041382c0740080e1340e0041c00a464031034950136a030056914100580310000140010b19080c00a4115000050441014904000b18880c1600c03141e54010000d43c20001015008601034005e8a51001d42800c1014410416949000c2548074100c40c2c407007494115007001841d50385480c000d8070901e0b00b041b2001c0e04103881c842942d581c0e80c018010301500c50b00000ca98100340c12040c094410160b000072501855425039401c0c420501401c82c00840040d9141c464155040001405480354034016260380381206000c04c00500700e07200152541400421640c84c43d600c20411b005005d5000f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 926848561 1250 926847311 926847323
    0x1115040b030403030608011104030b07030b0303040911091005090315090d03020c0a0b010306021c05010302102a0501050a0b0402120106181205060702011805032709070201050609070516 81
    0x256203506046001744425045a507041d4245201601d240800201400580e03000c0c00c55042c0c140c0f40c140d02a021500f921456a800d50000d10040040c0c40c0582c0c0304002c5081041e0000c1c0c940040400020503850356690071101107040030503042c0c5c5da410704001c01300307a1420520b203254080c24406085070359030512010b0041096000101300d20419424003000104540c441c0910080356140d107070080180d0048400c42012000c1701813982c2040b9201d000c1d00303040f00e070090710b0140c0c03844a103035044410000c02c419403c504500440065080c2c440f404c03c0d0b1103035601072400010307142880785882c8269031000000070b1140780107000209140211200150440713115081c04600e8000d450002000070075160b000034045500c40b43c81100388880840e405104142ca64000c000b10102c820001c41524406440945035603c2813144402c000c3e1810005204180782c1c07100240b0915000c1c000912000c8115112030041c0d4564091013502d0800000b55070300055035003007850402911410142d42802040347c09810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 926849811 1250 926848561 926848567
    0x190c05031230070f080604090f0b0a0209090903090924121018110a030302030a0311040306020a1d091302370f0801020a080a0e281115040b 61
    0x44864810080b8004001502c40c09060346071001c800303001c0310b4961040801245101000801c289858416400c070160700800c01d4140070300345d03103039584149402094105c0303080d82003209444070303510404100c0c801c0000078000c55a91007241d062240506000c2c0a120103400607a400c508104500d0b10542095001614101c51600d24480d0007440c2c10740b00300b0b80c403400a140004e4100f004006030140d0302150302452020580b0500002448900021448098010382007030108032840d81c801c0d040207090101445015080980340d40b10b140c2240d001025040224641941005540c1000031409064610842c1d00b148545805203c840158506078002445a00e0521f00405107500d0829110140b81c89181c1100310301a505400500c510741d2030080c115585e4518000041c01d807414000c8610304c03031441c0d82c0d0f00055180c1d94840d102070301c8600c1d4150760f5405140911088640403e00c4003024a4007103480a018568905240e4206402c450007140641d03a1121515070f40d258090031074044500043c0e0284d9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 926851061 1250 926849811 926849857
    0xe06090103020c0c09070e0411040308070305130305070f031406010f1404021204050102072a1403030c0615240304030807091205010c0e06160b0612190c050312 70
    0x410640540e07005a801044401030001d032513400030b07c05980c1002610b04009214140101042a0082e40710040051100f0010800001d2240018200b28403000d901e43d80400e4881d030f00d45040801c1600030401078460311070b003003040c00b4008100c808105800c2010304002e504001d51385480085502403d606d07221158241d1400e912243d0440d40903503190401901641401d1031301d80c0c080d5201c600141c0c2e1080301c285448000703005040340c0000c440417200340b8041a5241070500ba91400c00309103181d605002c18005204014ac060001c184101d400025071100d2400d040104100e00700007009030001018400c111442e0f54401004580d085905801e11603016985c04008840055142c0c01001100c1d0a046005081010541200c02884e500d0f4949443d200d40d0300003441198043c601010204c840c48400390400315003007501043e084071005e00003020180ca15035049107480e0703c1020304500c140d084c1c42804d061000404a080107007408074041c3c865144100207a101600481e403c000c4c0c90001080d50f40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 926852311 1250 926851061 926851063
    0x112020f10090b0a02030c1f06081902151c05010302090702340b040f050103140603100e0f03070c210c090c090504110304060509030406120b1305010806090d0e06090103020c 76
    0x140811182d4000c03030345008100112412104481001207070a23508020300400e100c0004102d00c010851032241070440c5881c1c540030005030b10640c65401c008283d0402030000fa601201d012005070311030340030012449514500c144030000038014503200440d0802405d0803d25501905d03281054070700d4084070a15500700045801280001c0d40c0051078a02000400146c01c0e0300c0b14130401c04540090328100075052042c95103034504203084a29a0781604000301c82c0a2130045603108211801d8034000325014240803074a03940c910380c0a04810348042d1f40091007007240c2098040f0800071003500c10b42c0d52611010996524255400c180101039129469100d0240141d225100040003020010800e1020a900445e007541540c01901c060741d606050100084003d00d0010032641141c0d1300ea50707018404400240d99000030303d0541d2200f60b106c0c691020b904a4a031280c001c0754040c02603240680610700300705201516040d5500e000909000725504240000c0e59204190303004d07075400307080142c1cac1c40745004041c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 926853561 1250 926852311 926852317
    0x1305130227040b180a020109090e0a0204060f050f06160210050c1522150b04091b33080403020f0d05030106030609050105030601060c1a0112020f10090b0a0203 70
    0x42204060700e00802007407140301480c8a010f00560580d00d1802e0401c03000c016211181e06001a0126081400400000085034403d140c1d1070007903c1613403900482540060b0541c0c050303900401c440d55410106000d50700c0d00c0310440100300b0013150303920300d0700d00c0501500c400b10b06a020003901c51000c02d400c1c48841405031b41203d50b0001d42c02d05907014141d1103002d904d851402500c071006505441c409061480b00401d810120203a0441c1240c3d40c0951040c000c44068801c1c4181c203a00280c032814024000362a07030301c43c4116099000b00006442d0b08081400c824070420503d007032801217240c0580310035020f2000441c0b50030314051030441025682c5d81400e92800350b80c0e115082151155020000d5807036030080146043e52010340c0d0911910790364041403804d688081c016141d040e00316070010000c40e4040d00d01d40034018440c1401d21145110b051004a4100c0c00340e101510090f404c0500c170702146480781c00000201012178030041118928140204100114002c2d03459103c000548140218020429 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 926854811 1250 926853561 926853619
    0xb0109092a0e071b080d020d020706020406140418050a1404060b190f0510031103010f1811030417091e130b030d0e040b04050a0b13051302 61
    0x35000044210a88656100c1c03410300c18140129103200104003164494041082c44503082920314200c0801130700c4102c500d070f201d0102a81c400d41d0800104c201c04c1d1490000e0100c80c1d024940041c4ca952030701001420318503081c0c3c1c80d200301140400050085903002c06070000e42d4004000b0010b41d0799580e034442c900500d50300c410b00814090303800402041103500d0700200111001a0703926003610300c0150f0100400c0c605802400500040813100b4882400d1210006412891072700e004603c0d00c2400341304040c50f40c020380101c080003140780070a01140b9020003101d8205001e0401c00c00c00440c44075460b414030f0001400040c0702041802c0640081810314080d00d000000051150002c0030203c0a461407004a08201e0f90090310410301c03442004406208001c501c2c0c10240c081c2810701da000c0703021074001090017203240d840341d913420420000303898a210b4180324108108001880e000301c20200711201c08281603111409081200b081020003641d20903a110580c151340180d40491a0031819410580c007610b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 926856061 1250 926854811 926854853
    0x5101503020402160210031112150d030801080105090c06030c07110907030204090e010c091e08060106052203121b050303090109020a090c0905101b1101030f090b010909 74
    0x241d28240c4c002101d403002c07080f44211003900fa1002442070944c180c0300c50510805040006000000701e0a070381000c019445480c5500c01740c0074045007800140d90420b03080c01a00090700c80c10042c41441000d02c5040e8001c101c5078010580108a00b0014481d031000801440e4001070100340c10f010014400441102c903c4020500d000c9844d005000400a404c6403203240c88007400c054406e140d207001841050303d29201980c840313034928145055502522440039000c1c0305495005000240b140c014491a0b02801a0340d50b219507622501003281c800112800502c10101149107040001600c0083c0a6020300001e05188151602015440c0d9028080f40d1019099000001c20001c030500c041d403040030700c0c620031500c1d80c0001d6202e685100c2190704560764140411258030050000d4641860021000b2a0a2030b200b030a1503c0380155981c00e15150500726820307004520040815a0140140403468115004c10480f02e501c0e0745a48000c400c0601c03492250302e942d42038000c10301502c08a41d90f040d495140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 926857311 1250 926856061 926856067
    0x7031d03150a0c08010b040e070c0c060201091208100e090f0a08040512060915040f050f071a090319050a2301060609061e020705180109140405101503020402 69
    0x562480540412510201e0b10741ca48008009aa130080c42e00c21305a8078020080360a09007030800003444918041c0c0f0190034020003687c20000034200300e401d803010304125800410b01400790720340301d50700c0d00f002d01c1200203102c007010410101405150780d200132601009030b83d50154403405a00c0d8285544000a000f13607006040c420070601408400030800c440c01607a004590800705030a141e2100001d403402d440903000f4414540d2030005006019420500450004003d4041503a03000d2a28080510f5500300fa0000c4000b00f101951003141c00e4881080c04401c1c5182005c2007001070340310074004041c40070148804004509001040000300d40d100c0c0e1280f0a40544c44a01000401da0540000800e11940c200000864000d00c504401c401704c51541d2a55807150104d40358880200031702100080031840b412000240c165200030f45401c0e0090a81100410780d410812150252101007072203c001b601b540b400e010010310000b40101c218a810500060b40c5240700c04240c015039004c0d440603511a0002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 926858561 1250 926857311 926857333
    0xd17130914060a06050403060b1c060f050a0605030d050c011b08160c0b010324020406110c030a0b070f0e0a09140f0f130507030204020a111e0307031d03 67
    0x50303408030342103800070102090306075115001c20040090b94054000002c805102c20000155a5000f003942c00e84000e0211018170300180d4801024850b044050b50701948508001c0f00c403c0da14407905401800f40041803004038200b0010070398906d0440811403c02000280c1d50303021140c20b41c132000964001001c0729980442e01d581c01482032409035102c40400104080840c3c8160042c050100d100343d03c40404103103607203952142400034000040070014284050754420041000e407000b0005000c00c1e0702c40340d00902c00d40d0001441d1043c4400460f00980c081c891140102d109034480c980c0c4900d0030320b80110000043c481c00c1f00c481030f401110f0364201d20701c16408640b08146401c440c5400d0b240c0103500c01544c2d1040d01503241e0390720640c0c03c07001c0d09100402144901003554034100c6910b000e2411613140641d294045401c036070042500070005071643d217440309031000900140e2640001d120700303c4031603240030400300d40300d200c1d110004043c0540d03141524107075100f0742c0c4090b03100c01c0001c094502d02400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 926859811 1250 926858561 926858579
    0xd0302060609090105042103020c01240b12040b040305070c0312030f020315120307020603180601080a03350a0510060207030f0206090d02060304110315060d1713 71
    0x10079201944034054180004021881c144200b07846650042c06803008074028040e00403103100101d03803031420140c082040c248007903002d0144007911031b12880c1c0440c214501c4400ca403003189c40758010701e110b010104982c1061800450040d038025800012201140e01c035844c041e9841e200d9080020003481d480c80001080c007134088094a51a2000c2c1c80611841500500d00030403071000301c03451b110703000414240b1342c907138101221241c0311602010b0860345054019000a80c1540048600715900c3c15903217075a50140c0c405210487c0100400401010b8041c0300750350260203104142981b800324643c84403c2a00545403000d890440100982101c90070b050a400440c0606012500d805d0b10003080c810000e45140300051140880e038200b00458502c200c554208440c42e880044001d6000c42e1103c0c0d400003594400e00218080c80c820300c0040001c10001044c5402c212168091001c0781644104000017500d43e0708401c1181c0768010b001a408000e543c154810030b009680c581042141c4170000440c404c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 926861061 1250 926859811 926859823
    0x1207022d0a0927030206040b06030f0304090203060f0102030406080f0411060c06250f0305191503030206090615040c02011e0b1509010906120609140708181b0607020d0302 75
    0x49125103690f1070154080c119546000003410050060340a01c00040110303000f803809940000004041d85c00001071b241c82c1f40d16642140c0c02501885500100f0702c6280c1c40c0030b07110318074862028005182170a01c1c150014201c80d0004043d1111400c0900c001001c01c011180511050070004141c01c3e1103130107004082d9a292002c03285143d0720014809860b802003501259500764107055a41c2c103011215421048000e400d014066440e1380310070004100c0f81040c079001c0d00d41d445460001e4056540e05d107090082c03401c2c00c00350070046990444001c1c0820510000165041c035001138030049031054140004030700510108102c107111170f04401e010783c0004007641007541c4500c0e0440350200644e01c90500700515100e20062180413480d854003c200f074034003800c402c8000603039452001500695a05008003990509480c3c061116402c4c070400074115081018250016100ca450007141c1a9917000d042e5140308949104208510081e464a40c0795180021a48075650140049400f05402c1c0f50181d0340c0c013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 926862311 1250 926861061 926861081
    0x1103030304030e13060e271c02060705040f0b0f09090c0301052e180b030703090c170d05090d0602160b06030f030409050c0c0105040c081207022d0a09 66
    0x1030041000814440480c0900010340f00500b0a80d5116150038620501e0b030007c03005c008484812044892141000a00405c011109031458540d08150038000003420040018805801d200c0184801c0c403d00301c0b2002c2e14800e5a62035110340d43e481030360350380b183c0351402560740c07940e444100c140030041c480c10794001441c12604142c40103041500c200350480d4491200100c0703825802440000000060700c01c1c40d03038170443c0802c24925203d02d920794103650344030ba10803a60040842e446807034003002c00c0810301000b401003500300060326046101c20034807502c804201072450100403021503034410656801c56519002984070030111f55a500303000700c01d4058003141100b03a031075403010000289542008a803800b070b8031403004081c0d0319041c02c0c15081c800030940607084040d030040c00d110803003030707403500740725480c0524040c000c0b04c0031107803600d1565454200c400384002500e0405100560068444010b15410111030004000c14003c1a18903030340040300d1843d0450784040c1c2d11700006603045003603100d01109 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 926863561 1250 926862311 926862319
    0x150e061906080114060f0a0e25080610200304080708070503030f030c030406020909070e03010c180605091c080301060e06090a091a0405100509090601061b1103030304030e 75
    0x65036005507600301c5401103421211a12004c0c0024014a05420001520032000340380303001c425258a9070409610702203405190310480303c100c82e0104184a107445100c0c0e251881c00000e1407070200041007400d04851110010b0121154000428060240c40d0f010407650110441e512170b83d543d032401d96071300201e10a8070680e0040050126030340c00c0100444480301403002c1c8180c5551a4000780c10300300d609c001c00030f4604035800d00525005030f4405441600400780740c0e540b10301d105003100400d42101c819800c92010700c040600c2d42c1c880c594940900c08100c8082d4101030381c40d24450404500101807602c0c0580e405004150385400b00018200510306842c015541c201e14481c01c0ba040c00034034032441e18030660040c401c031410403040030f0035000203a500380140c02c41c99081000d10301003000d541040d1220a400c0c00c1600c0300b0310072818003011741075200030358200809407540b400c10050420030040d0041820300001d4003422050041c0400e64a10811015003226942d03d42418020b0514501c3c0e0b01c95485 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 926864811 1250 926863561 926863571
    0xf030a0605090c071704150c0302011b05030108060a0614010c0201032a14090109051020060603010b010518011103070c061e0201020c10020901090503030c0304051503090a150e0619 79
    0xd1100c1755046e94140e402e000d442044203ca944001c0d140349004410440456407118240130055001802c1c0210101c01c9485d1075031a9410f0040075420401b000f0580581a8600032040140840300c811030b80a0007000e0031310b044159420300040380981059000c46030003280002e9a600404810700401c80d1034003160750341426000012101107103a1049110082c0042c80d090800d000c1850203040103002d010311820000724403409003425140c030b07402e4032151201642040040001d9401d0030b0040514840342460483d140c541d20a084200b0386c1c60710400a0b0401940010303a0100b2003041003140d14907508501c0c5465481d6403001c0c020100600003c50140401113205460321403801402511010b80e600d1000d41140c442c1843c0b4440250424000f0034104042e0f14030004070754230188010b120300c1c0341d040d01a540d150b00300f0003400640e141d0504040c0d515001041080310003a80807803c07409103584481081811041c4000e05c1d4054030610303d8a82d080d0089000340312183c03914020800d14040b01d503205200e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 926866061 1250 926864811 926864843
    0x609010506120c040f0f0f06080606040b0915060f070c05010f08012d1706150a03050a11041506020f060711070b030a0f0e0604110d02060f030a0605090c07 68
    0x8100403842d01c03182aa580007444039051031419800c0780d0486000c0180004074065542c9926080e03c0429081409a6a48480c10b02c0641428401c032139115030280c07814010a5500f00106010000042041000860542120401d40e40300c03000c46202c1c10000860b140c49003401d091003054511240708842c0419009407103440f05138041c1a02904031064815440240b401d040012481150a10310800c4603000b007030380200390a40121402d00700f044040005281d071745001c0c110381e5804034290036298810100a602000040c00000b004220300c0d6211744d01855100408000c2400f400c40402440450010701602083c0550b00240010f00e0540700342c1110340980f2101c405461003a078400358011980c1005400380001407203840115081021800300040c201540503c05080710311100c003c0d40d240c3c020100f84010311807141c540c1c90042c00c044903d10201222980081e88611030081003205a60300840014900c0e51036a21940003050040c1050083d481e1440140c08154803858044031403680030701da0300c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 926867311 1250 926866061 926866069
    0x90509060103030503040201030c09270f0b210312040807050d031b0c020111100e0607020d0f08061c03090510080907030f0206071b03200f041a0d050609010506 70
    0x141225010307100d0311714648581e0011009091a0300010061104092000030300700c6201c1d15003000b410b4104440104c5910201d442400d640c1080c40d1036001e2070070304589040c0c2c0e40d2030344003c280c0c100600000c400116803a00b002c6003140100e080000d00602540c0412041c400440014887c442c407440170b07902e003e96418400d41c00c41c0d0b040c4c4c68095906000350315481c4603a00654001c4001801418894007440c40801503a00d48100c1c0341e5440340382900c42008400da590100580b03a000078040c00507040c0a03400b0040100311045100c0c00d00100300040000c9003081e1214803c0c15000c041104013001d84d011103040140c40189284160781c011a90061900b903103620503e1040d01506041001d8a8000d01d561a0014407601c070300800c8c1e912940130080e02002584090141d6804115090f00604007451414a00100325010000d0b020518106820170340940e80e080c510111341c2c108440008a40054441481218040d0110746420070100c08601c020f2290004506103c0c4e20168000d0080d565404144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 926868561 1250 926867311 926867323
    0x4050a120c09050a0f05240a0b121504090302070609120b042603160f05040b031314010204032f03120d0f0903051b1b010c080c03070804090509 63
    0x2502a000701503092140301030a4100580000c40c0d02c8020800703040d100790003000c481c01911240030800100ea6100400304c414041c21079807070340c2103400000c6030b03103400346445082c4589264076a01244500004001c6c1c0f1254540c8002d034200038104100721581450040c1d40d07000e046c014603000c9219110f0020311500c00d422251610b41d480a100c50007034442da0703100480b00381510b1050001110707420700d03131001e400d0020245100304420094150400c02a080103428a603200030501c003006820031050107005054021030f0303000816100b18420505103400d1100b180c1c640d5400e48c080f00d500015000007446100c00404030140035072400800000c55880000c2c40c8000c406002a816802006c880c0f141090700314080e041c02d0129041c04110107406c003842c2811250b0543c411400300d003001c55164000d204880c0c4007e1801d46890003810b201c2d020784c00400d0ba044052400904000c415408602080810419500c042100d4021652140d455250111894005010780740caa1440c001c001a03440c4800108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 926869811 1250 926868561 926868563
    0x14030708150f0d0303050c160c140d0b04020d030c05010509030c1b0f010f0c0507170606030109211808010e12070321091a06120c090c0a02070b0f04050a12 68
    0x800038001d42d260f5003e85c09010010021400c83d0010b0000301c80d111041001c05481501c42c10208800506042c103a48030b184441d00c0003070140c0600c0507000002400400c0305504142c0485445a8104175450112080189000010080d508007414032407080c0e0000b0181c20700d90f001009640004001031310290790740d40000036143d4080c1032035a00003025401000c00e00d91018032840c0108034550142c5605245c003042e9441102c00c06080000100a00d00070701a854100004400034480010183c032407200826500108640c80c2281e10404206107000340c101910000301d20014500341c03980c0303040c1b460007041c07402100d030300794007500341c001c039200708218129010142d154840f00c000804416802003000640104036200359628030302d800c0410341c072103408829043c006540d0079903450700f081840f01d514107404035134031554880c0b42c884105940d01880654880340b1507502036181c000311031049103058282c0d884040840000903034075205110f1903006000703554007a00d40b110300664400f84130182050f0008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 926871061 1250 926869811 926869819
    0x2030f06071419080c072004060509271608160e01030804120609020d230a0b0615090a060e0a0f0b1911150906010602060f0a020a14030708150f 63
    0xe490546030041191503004114201780b60308102d52681e41d0319003026000c0246500040f1100d0100d503034a0315010b640302030702041d2075080c1607003440c40e103408401d50241954508400905494159203c040041d25880003403102c183c0750242da40e441154950708001400e40440d2141840429100d00c08070645048031307844a442c41c501490810522660701c81440104c031031b41d880741038520240c0e0321001050301030341c040c8107071603180b00a00043e11620b00c103910201c51aa08000f0000703010030800d5510b949d1011040c0d47c00700c0c01c140c403007049951701c0c031414800303591010040c10003054180d80035422904004003500c10264003511210389041814203071080c400340440410542401901c80d0450721240c00c494104990349094114140b81000e80024009407419a06000c011482604000c0c960040490703001914440c10462038003602010020403285903a07400046c40842103114003c111500000c2401c0d1644034204903000400160082d06c3c004145118000f00301c1e441d00d0202c0e80407041d013200030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 926872311 1250 926871061 926871097
    0x160e131116170913150f031202070807150819020403080c15060922080406051309090c06050c0c0303030403050c2a2101050103050d090902090604090f020702030f060714 74
    0x1c11000c02170304903106110303480c403001540010103400c96448440a144180410040c003100c04000034504919540088090390201030104110b104852241c000a415031503e001c15646454420103240c40700420514281d10001d4000240b09a90004d403203107140f0300d070030342d1a04800c2965401060400707454241c0d0040040000c0b59804030411412a000c804c042001944001540c84203001500035a2100000c0340c0005000b01002d45040d0120018040c244010000b2410700e403200040c1d079406004a01c00d000000450603645481006010b041c10001000c907a03803441c16280040c030540110780305490510990135181e4115040c00170a608800d1040b1044103450502c0301002f80c5401940c012240c00c80303039404419420030080c043c13603020394014401459802034241000b081e1030b005a110700300980c030620401015940c2e400803141102c1181030046070611800c18290000c0c4a1001e00950502c1a0015403001240c040744003485075045454080c445a140ba51b40d0301d0910607000c0d00400c0701101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 926873561 1250 926872311 926872339
    0xa181e0608070c0506010f080c060316140c030d0617030a0210020d0f11070c0b180d0201030e01021c0f020a0e060c0a0b070201060e160e1311161709 65
    0x101c521640c042c16600e403003800107080d500c40d0381c10840280c00095045411560512142804003c61a5403541c2514028594030b4070042d152986a070345c030325260400200301c03010301c0300341081d1040d180b85000c2c1a003640d80d03603c991002e510050089102e41116548100c0d40c00d941c004010055880c0205150007905011032809035040007907220080f840480da43e02e19550304506a1031094a0400c001101103640d40d40044c240020520300527400312040b100304210485007110340b401c1055103080e09a030039030780f10003480c80103801030150b800102c0040e41c808a000e001040f1000d40510080303120709002c2000c0c050400c6c960059200d64904070021505103030191180c1d0514038024100003101d82d00765014a0144d44c2d404030610000e5480f800143c1d110001030015a0742da2202c0c0d83c1080103c2100c00005840381c0b00a03100c03c0a014015100e101580d02000d040002da0300b01d0350800807c0780c01307960354082060220701c070b180f4403c0c2c003a03810550804404c01c0300700025040b5182c0c40320041c03d04000d40a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 926874811 1250 926873561 926873567
    0x6120f040c0b0a051c020c0a031b15020a030f0b0604061d0402160308220f050c1c14160506030405030f0d0926180609060a181e06 57
    0x20150048801904807100028024421005811402840e54806a07030b10019000c10950440245980304031510400c03d200e071000d00010090201d03035042c11320721001d510b26050020000c529034005081d9030042c0a07031003ea011030f07a0042100d41d00340d4030100200190300c44504e0807103c1c1c64145580240040006001a5020f100440c10907488403020800e00f503007400115042c0d0f00040004603400c284424148100342d0010b12060340110322410b058254045a203042c06c008000307030300207417000010150f4039090110500001080c03982c09001010250b240b5444000b508413003050688480717207080030352444181e000c1031101d0913030921104248030b9030504e020080940d10150044a540c4070070001070305507001c150080c10f40c0c0d052540c800101800f02d4241002c401414110840e240303221140f89107441c40c40c1d48240c9080c100d40c500265802400a008079419200f051301d8150301c04000706404200e9a0f11248244202030029860700e03546544030341c400300004100d03204010074a1100010301000348 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 926876061 1250 926874811 926874841
    0x6070302071b0905040201141207110f06070509180108060711030d06060309020a09020a140904090f21081012020f040e0c010807020f03030f0c040e0916050612 70
    0x8002c85a041025012016110180040d40c0c0f26404168440d4100015903030460000d40b046942c100c405450812500c614400c1848020103030404c1c015406c102c2c3c2d00d181c0d8108a00100512194216501401e0901002d801500306880303045c4a00d0100030b503400d24800c1e000c90315040b51407100003030140752070300641610317103820100418407a0312080c8108100c045040c010400104915100001c90f06c009005001401015404c0408024010481c1f131100a51115140d0403072000e50207600d840c9d40b003070300c0028080d000801c0050b01c005c01000315071003408480381542031208007104100d11841c54021080d190381404803404200784010850420004484844a85400c3d200030030448441006000040847d41051480b00c401d03401000c28000740d503041518603410000900080c40042d10903451030b81c3d2803000515241c54194110003103000e11449209640142c400d41c8400100c40c41c119451039610f4082000034014413215074030016003802c0140071103846031440803100c01650382c1d000300058204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 926877311 1250 926876061 926876063
    0x507020d09030b0c1908070219050303060d0507090f0e0f060601020a141e0c030c010516060f09021f080c04030213020a1806020a050c040e06041202030d09032f0607030207 75
    0x624101702c4241c0c02d0480c0712020789020b0b110340724001d40d400c040034000e00c1c0c80e0748042e9940d280300c3c0d840c20034804500c00005481c2d01400c00c44620f80d40e46850315149003041c556501032210341c0c1c2403400c040715504103030b045550001d209200301c600301c003640d0384d416580d036600b90f5205002d82c00002c814400704a540d5250314a25030b0f04800c440d04000d40e10000d41c003d64160b40300100035044140321501c00e19091020321003141e424078100b400d001a03a0300c004031000e0360410003406103548001400003010660803a10025400030483e0146c0d1b50020740080300030a1941b804000240300a0014010200c0e03a425541900d401401d40140345040713550f5003009611020580c030a201041031400b034050074125880c07001d8042a4040e218400c1b141c603140d13151103c001c80703c0d80300301d05100c01342d04da08030300140b0164400d81141c180d8a80b040040300c240d086108131044e0503407044c02c0011280505d40c010203540d100301c501c130355156408080c82a0555007240356249150050308a0300200d80c44c180f2940240c1041c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 926878561 1250 926877311 926877331
    0x528090308060d0c1a190e0a09180b0f0f180c1c05070b040f0603020c03071205070803010905040c0e0f24061b060105150304020907090302130603060507020d09030b 72
    0xc0c0d4840c440008240300110f44885040f5000400d4402211a0000c1b040032070b10724103240007103810641c0011402c00c0c160050707458183e0b44014403000b03011590300444613a600242d05202a04145081c2039038080102d6440344018246c0c000b003203103621000d01044114044501801208211504001d002003218144285540c0700070310348000320740188114001001c88886141d511403424061505409240d4807030350501d84144200301060304084204e034a100d5000c40300e110100340552054440b800b1b860f1000c0d0800901200102c1d000180d5801280903d001d0200c180101d6580c8940681102c41100c102c00c3c07044d29480480c000a00e18081b4664200b04842c0c2010840040e03408220a5045050007400e07124015032500c800350320921a850140000340c43c081c00031014107540300b0b03042c480039000a0054400c4000074929074816555000515401404080064007100c0203901600043c0030030b0b5101781c50480401c04550000420044a5551b0b480d0002400d281d919411781040d4014860058 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 926879811 1250 926878561 926878583
    0x403030309020d141b0a060503310c03060501091e050712111902070506040e19020c0a110609130f0b040c36120203100528090308060d 59
    0x181c0220700d0b42c02002521300041440144001001c600c50000d50140e41c0074500d003800500c02640d1150880f54094041079014030303614009004103080717102485060901105500c011801c10054481a0040342c0c0228070901c056600d039410542281d04401d030f50a080c00d2016044c01d00ca03042a085541c7c440700c40c0c20f02400074100d4402c140292900c0032400406407500003019407003404119034404009003d44014440c0030b042602080c035500c43e501a900c091100600020103000140c0c00744584c64003100000e54441c3c0511008654410704107400325501d00740c44008040c10708014090341c0d14004c005061203540350400641c48000c00e501c542c4024a40c2d00c5200071001130311140034242802950355a0303c07000b0b0381c0940c280750183d0741d041c448440160114060084005040703000500341c0e280c0d003030003032420000351000a1610344a0f0720b480403410309200030003126500c0580b091940000c100b07540c0e401218007411410407130b0300b030100c0100840e000c5000f01d41503003414100d031903050b4401c0000c640 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 926881061 1250 926879811 926879813
    0x90a260718060b0301051804050f030403030f02010b010e0a0501030c0e210706030b0f3c21190201051b0606040b0904020a17031c0207030f020d050403030309020d 71
    0x4108000d5030400c2004200c000d0485054001c6403148000030943c15148a00710350400c00040d0141c40d658580143c440c9181c00440d046c058188011880030302441d0440b0790702c039641d2a010300304000180548000d94680301c4c1000c48c0c0e50041c075080109042c0100030600701400c4c100150001c00a9000c0701003004030141c45400710f602c5110840141900200a80c14400c4034100350b285401001d4200f4800c06082c088120041c1d16130710108998260b040b110090101d203000800b41d0034001c0c1030041c1d041c11482e01c01e10660f100c2010105401900141c1d0045120001c0c1511000d4400d1005c6408001742e1000400d43c04500501201010755032051520398548405d9082c00000d901d000310b0400510f40107241446003502e49846648465001910f003490715240503000500030600303901c561191318031101c90804154106004440d080e004e040200180c29200034001002500190301c118003060003003007036901d01400040c0c04440a04103a540510745170942e517040300900408501282c2200325442000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 926882311 1250 926881061 926881063
    0x16030b19090602090a08070303080a0c1b0f050c01020a05060115020c0a17010f050f06130b121e0f031e120717010506040617090c0d05060714090a26 65
    0x4600500800d00541c13101101410445801010f500901180d8811a0100000394109140340d5108030540b0313000801c00311501c2c041d01d44070301e8107030125079021000d01110100680c185181d50018028012501c440130f080b001a039840302e020301d018000780d01c400010800c5d01800078803450482e02078419103100e01c000310003203140c4061542124210201c2203598400a4000348103610001c44120b0050100342000316000081c00780c080c1509000c0d8a403403801e0140c250454025000350140502410141503000316026101e03840351565000e02e60080d030014800c04000606000e80111507400f640c6005c1814144525101c3c10412420442c1c4041c001d408a0710000c01449205014503190040140411408a0329404058002d5441b80f4818801801103c0c1e0010035641c80350380d204000b00d00c40d21202d042501d403220350030002e079100101d546003404000703010610710301501d100d80ba591911244d400c1c8038844c43c0183c0d03031903c0d0400300c1c01100304031140e070a9205142c540e0f822501500d03500c01c40900c003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 926883561 1250 926882311 926882321
    0x2009130206130b190807030504110103051f08010605011706032a15040501030c03060320010504030f030c1a04030c03051c110310060512060409050312041b0816030b19 73
    0x14600d480305200703d188445801611780ca5108000346001c2110340b42982d1441c0c00103414842c02030405503500c5c0003078a0f40d007000d40610309140c0030300307021103c07d9503034908035000e422203008250000d086041c4841e040848424014080e0703a004000d03080b040c00302c280c3d403c400c0c2c142e058210005030401c0400c0700c2a881d181d208420900f1031940c074507030300d60800c40054180c0310365910a02c101071400404001098031060304520001c582c127040580003030220b004032a28011a00080c0c4007001c0c038a520010184c0085281100d284640b442070026074a000c070200c0101404c9a0140124440c2c092070750009105500419060f0300c00c4801d8944900b1120028046175008000740068110000038010301c03542c0e00360200c008082078640545810080301c0e08908405001d01420b0196494492013000c0020501c2921400368612043c1100b900d890b08002c200c0384e80b1801071141c0350000450110384883c0c0032070f4148109810850700781401c1c1c55036465400f202c0c00100020000c032180c02c03400560340e1540c051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 926884811 1250 926883561 926883577
    0xe03180f0630160f02060f040b101e0311011403041104091b0501111f02030601020c03030a053402010c030e0d0b04120509010801030f0813032009130206130b 69
    0xd201c0a1800000581402c25200c40d130801d40d401030040080e22540754040e694010ba010b014000c6940f55036102402070800f540103034607004036005500c1c2402840603503460840b8050b0080c00e20281c00007005441c125429494441d101404100140103c1d02301d1003628039006002c0c0000451021319140c9044840c0d08148140810250381000c09c243e680c0056070310501407100029121000180c0c035041c0340c040311240d0000440b60080002002e5a0080c003058410020103000e07690380725a1420010540e5200040d9a04400301502118401c3d44045101d401c464101c6000701c00316440c3c0b0b40054813103420f01603044003088005051101203844000c0c0d035031249445000a8030450a0916000c0c100609004074081004424482001e0982c0d0003035901e81180d822181c000464821414000020702c907210400104480e50400001080000c0400284c0c2c44d101d81c0c154004111000e04000001c0310907500c01d00310950410050016203801402055004241d002e1100c107169101c00240540d040001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 926886061 1250 926884811 926884831
    0xc15090309040522020d050705090108030a08090114190b0a060c020102011103040507050607031107060815090403020c040221250201060e160e040e03180f0630 70
    0x1007103103403810640203164210310322588030810002d25414200220072034000203480381002c045074406000e01403001001902000c0c2c00f4044940c0c507000910f0707480e4080c44882000640c040c0005400c0703507040c416a904a0402d02000c8529211409000d0303455985131004e06003141d032400c1d031b0230a903640d0702c0c1540024030254481e4640e010640c000642140c111000c25902d1860400402c00001c80125061050760400c440440d2a00030904040310940d4103644524801c3c032901102040841d000040300784140c00c07420b8400f076010400c0091100c3d0990544005001d6440403039074203070742e1910307070043c1424100c1814850b52803c1b10403d426560300d0141c03440c064004580028074070758848402049440304442c00288200383c41c0c540448000e0b40c0c001d01d4043c2c10b42190320400b0a0764450314182c101800010310074003844c1d110368840754403a17011810300c0035403807038041d044042c40c10702da4003d20f642d58000307001b64148030560340b094184104904c2c100100c0c8034462800c0115503402e24140340140310b039071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 926887311 1250 926886061 926886067
    0x622050103061a040312111009020f0d052116300503010b090a030b07090501091a2d0313050d0804050a0f030e06040626010810020c150903 61
    0x100050100c6009411100f05007002110000d5a011401e00b200e0480f40e111825003003280c50b40c0001ca80c55404480034a140d4028208908071001540d001981d03854021203102e140c5200b10002c002c0500140240280349802500d0000702d0414580207070006940800201441c242007025524411180503900710354000801c01c0d607107002e401a0400c2070304d801009528000503810072300c026000f408140315030500f035480090180169201d80306100015984100001c009042034400a40030070030a002c0d00d800140b007134500092070801c8040c2e403150401003080080c03800c0c1c051042c0c56042d0070f082d1200603400401c5503081b442c005000c0011881b412040c56040b4440d86a45042d030b00340004440381100b0090000c0600005c5080400c11503981980000c1c4101800540e1a090302d611040d0100701e540210f0100740001d0042e045104140343c601c4200c142c1280c440e0079070550003103807420300800d209ca40c0f1a941d000c05501440d8000c12110503000b0488403504000070b400c0311014001c44155079540c03c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 926888561 1250 926887311 926887319
    0x2003090606240a05031b34060c0e33090a0812130e06011b05161d13030504030308091501060905041a1c02120a08070b010e0601020604030e0622 63
    0x109420000c0c0301a001071680c034148802d102116441f43e00c40418040c4401c0b051402c084251f00c6419101240e80124240f09200329108040c000c0c002c4504454020801c00c0c205100c041d1042010303a03001c8521714100e00c455500c00d1058922900840d020f6030b000f4240d91404a02d180003000000344641141200590300c1120f0516500d100c601a44030004240510041c8a0b0b0360b038006a4420f144101d6844800459040e0b060052404c5003130515004408118200800c49101c01c0c00a1010b10300d660b114880d8a0700c81c001c9006421221500140004405100a2000074031551520b50424200c600310b0b50400011254080c82c1031080e804000401c00c5508208030320304240c05250302d2800191080206400c907070011a002e010100c0101c000c554403048030501710369510721003e031022100000c49461207684d103844015039009031070917550024040000a4101c0114034010310501069002c3c000710b84032580c00766090401b40d403815a04c440180200d000d1941e48503c482043c200350030620a043c1d283c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 926889811 1250 926888561 926888581
    0x2a04060e01150801080d0302090d060501030528080a08060d05010c0203070212011e0b0109080312060f060712031d0604030c1b0506120a110301092003090606240a0503 73
    0x4031070385109003d00b42c0300401c071032513000c580c000200301c07507080240c1d69076008000940c2c41d0703114032001030001c0c0c0342000100901000103400241406403001e1a80d0f41c030760100a20848810b58000246805420000c40c041d40d880380000603000304004c1c0c400c4030194000e40da09402d450441129000503803000c980102585400d180702c0211002200080000c0c18401210001c00100e079039159803560b03159004030b000350b4403c810040040600400303503a228849000202940038094510501c10382100800440c28a00030b411103140a90291030100d001c208000701354043e007114000000400c204000300340c01100300f0b03c12248518401e698106204019207000a4061560b00700b845401e8401042404141c80d0001180d841504044058587c2d6440074554005000210a20304440701d01000000719583e664011010248007010b000182c0580040990100d0004882c0003000d07600110100f415420b206070034503070780600e1222901c030551181d0305101c2658404101c010001d04004100000900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 926891061 1250 926889811 926889839
    0x30a0906050705251b0e043008090106120303020a11060c0d05181603060c020c0901170a060c021e0d080118060807030803150901082a04060e01 63
    0x16030070414101300c120f01e40c00c40aa01d0490b0100000020031400710709000071560104d1440360701413102496503803104081001103030165402c0300d6005200c0414520811400b20142c045207041001c10203044803040704903200c2c0d00180200c4580c0d543c0b0400410035446045440101030b0190701d0141c0d0742d051407440202464205c40390303200703640c0218041c004100d801000321120300c030780c0c00004601a140c104a65007108850301c1d074998588503080e80c014074090b80a440801712030203001c041081c010341c81d0059072140058507000da80040c4400051100040c003040c0000b410400404882502074103503120b0040700c203c0890100580d00c01481a0300046500b21040f0b9039079203050203800744054800b005000b41006018105440604040203110f04025034840d00c001c200b504211100c040c1e40b0b05000e85582c0c003e441000c3d5500503450203e01c5401d103001c1c610304a40d920002448094504400c0c1c0c0c43c0020002a0000b4100402d28141000d41d294040c040251004003024030441d403400042403c03440d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 926892311 1250 926891061 926891071
    0x2040b04170a08270a0815010803090a031e020409111309050a0308040201230a08090c0a15270527010306180503030a060510110c0f15030a090605 64
    0xba0100c00d6880006640d001030b140003a83c4062903110301943c00b4100000100010415604149134000024000000082e140290740b44940c51204a980b83d560f07c3d500c2c1d106514400e41c110a42c1a82080044e010310528459001203038060a1401000c4d80000e09944114906450241c4102d581303809901d009403400c12034103138011041203814820743d40c0d143c41c0c0800c041d000c0d06025442e0001015a406806500a17010116900905103c03c04940207103907048480c80c2400070f0a4100024446c2000086080d0241c2c0018807103200c5910b0b010700e10a00c071030894400d10420803083e84145421039002c000c18400000c0400310300305581003200b406031408400d10900104d404501c03c082d0000351260485056903080301d0040342c02c01e958280101d04410102c001400c80c07000108102180c00c09600650586200701c0d482c060100d20301c0300855429002c80e0482506420600c902c0005240066441000480c00303403002012020801c140c1160390003c0b55410070141e20b07040868100b00030b6101d119401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 926893561 1250 926892311 926892313
    0x9030906090807030f021c0b0411091312031517010f0207021e010c0209180c0102061b18030a1202010b09010f050103020a02010e011a03061e13030c0602040b0417 71
    0x861404681d169154564400a005e031801408500c003076403501149000000c14250281704121018a48645100421038050b66400c82201c080c1100c2d1030141441e500074180010000d000001980350040400d00410740001031699411400c1c08040c503807040c880081031469034421004605d548000d0945e201c0f40a0780381c1c00c5204102c401c00581e03030442c80e8031040c2e00007081c00304890300f2000140c506004280e8040c2d0b2000c10b031b13020070084468110080314042c600c0410f43d60080c28003001645c1e00c20b0b00b650020503d000b580c00014580f0100c0c409003108801b9a5000d8501603048000300c3d051120b040d4080e1105540c0d1780c4404020780e024061100402000d4440550b9907150208896801c5010301900d41010740015002e00090300c01d4009038414a24107008002880000d102a4400003007907030224002d0082000240460381920040380d001024180c5031001c0745e4440003c091040e54000046060003107841c1402c0c0482c0716403024102510710048400d036254140924602055000743d40a101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 926894811 1250 926893561 926893577
    0x1615080f1012030219060203041a0123031c0c0b010b0712032d06060e1203030f090f0d0504140418031404030b0c070b070c030e27070309030906 63
    0xd1280e20728400210b4424901281804145103000ca0403d106118032802406440307010105115440c2d00039401036104034080710000e90b40074101500c805003441106171100314043c0703021814980c900b0002e26444010103a0f11458012242c1e043d50841c9518200d00142c4500020340810102c5030026000d0070f07030352000703070b041c40107a80e1103a6540d5464141030007019261040001450840b6100d40c07012072440c41e403400015030900e10355005001500c81d01c0c0009500d9031220246091101502e80b1078850100a58550754550b0034582c0380e600090308510049c0700b146000100601c0900404550400707039928582d441e4a020120b1480d4102200100c4c0705030300e00710449002055001c00011401d5260810015800001c0d061340010700a80e4400740480c0d03e1002004180c180c038000800e0072038440d10b40c2e800c05440300c00d421140d018130408010085440001c04950900e4a948461100e03006485100b007074a172488101c1d80e8a503400ea030b0000119850706047c908054000c94104054480c516084107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 926896061 1250 926894811 926894821
    0x60e07030c02061b1309052e0506160212030a030204030c050f0d11010201020903160509010b090319150c2f0d0809030906030123040b090106050c1615080f 68
    0x10741d0032105240d4807584030009144c02d0708101601d00000601c0760440c100724900c0c001d550002e2807942ea0054160032072070501c190408d40302c2c0c2c11104042d204003804141c24644c4143d40051910341c03d0005070b80c0710f401e460010324691420001440c20031501c1d0703000741c1c80c0d82c614a44506a1100d40c4c201340c3c0b00d44030503011040386403188034500311410340055151500b04100d20041c0c2c020700c42c001d800d41c0c15008030000982102944410202200c00070b8901c5417450f0303a104009000303805200c0106516400c05100009070b0411040c013030f9912800b40c04590b0404440c0e040d90001c8400341001c80020400c04c0c00d032142000540d242020410700c1c529000301020f050038145588400c180d4001c01b05110700c1078003080390418108150ba03a00308000e8422940ca584581c219200560542d5204a050a50b00d82d4a41c0504140c0103c04d0300b20009450580540d090810656164005032a6110203202d128022032801c92035030325440043c012a03a80c3d02d03911808800060441ca4010a04643c00740c940040c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 926897311 1250 926896061 926896081
    0x30c060302090f01050a14040f0e0906090c0d0302010b1801030b1609091d0d0e10030b0121090b0a05160305102601021201090e0a0510021309060e07030c0206 69
    0xa070342000900c1c10694a06c03501c28161015078010003e481e8043d80800c0104085403804c2645060b41c1081c000100700c0d0303036440c4000760350720811500c0526079000b9410001d0385080501c00800d9491180c000440c0c0c1e4019240403a00400b0200320502e1000c600710010414007003c0c00300307103400c8100140c01c00c40803811007601078130780d10081c407801079400d0307580100015010942d40c00300e0b49010f07540c054441d200d18044004204903600b00d0180d115400d02c807003050446000784580b1000400c10703124410884040110440c0b0340403040d903400000b9460301d60610015100c9070000b4810780407640000707040d003440140c41c15a9981680d152081c1440e00040c040c01185802c1c082040310300748180480d503417140101c1c002d07807001c80301d50701c4c81198000710740d88819000c0071b00e800341650501c520030418098240103003992840c903100058910741005280c0442c40350b040e001001c1c0026209810f06990380d440860300e044034050f62014a810741c00c2414400302035418094030240030481e1006007e642800c660403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 926898561 1250 926897311 926897329
    0x306010c02090907120f12020f0a120e060c010c030614030a080c031b010c1b0b0a0903021c05070b0105030a051e0a060903050c0105220f0503040e01060504030c06030209 74
    0xa8402c155282c0000c010040c10803000303025003071450318040d8071101c0d85466040000102c01c1154407158068911800c00e00c0001c508a00d1140c00c0c0040196255a4884510316030441c0e00030404c0101206590f0b0b0b140c1c40b14001422501018000004c10400101005049034005e0b080404205c5189030b429401c0c1e0740000d400d551a0707400c605d046584005480b1b02c58030b18402d0040c1070109049400343d03a2541001036001c0c00c0301c0b02d0652100c4a020320044503040640d55211401043c0c00ca00e140851051202035008404807403207401202e484454070040b081c1c0e071400395512000055000502c030010001040381e074600600b429001000c450042d031340c0d401d466102001941d5080e00400c19418032451040100c1303002c094000b04208071680e19400d00803d15032003000541345640c00e01c008035000c44d801c1d4070000c14265914507400082a410b90b94101007140c00d400540342480280008900c15101541e614020141a1180c42c0e841d881d6181820b01c3c8500ba91000003030510600200640c0e8848080f0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 926899811 1250 926898561 926898563
    0xc080406091703010611010c08060604210b0c040806010b09060a034b0903090b1e0a0c05060907030b18011d0f1e03040b0706020c010e0c240f0a0512150906060306010c 73
    0x1411040000901d402d060f801050f05000e024080e3b01d20a0107803100618004009541d54141522a96a20f0703c1000c2d07000e11030b043c039468000000308100aa0588264403403202c880c1c3d6a001e04a820403891450010030b00707410304414000d1000c0913840c40b400c0b0303590240211f107007802e40700303110541d032584002d4844043c03441440c11010300002c440d0700c1221140e40c0b40404061061000c2d0300c030300c13403084014079051691008a500e0b11484001c13449206000603c1030442c0d500c03a42a101e076035543c00c1401c40c0380150110300c401643d00c0e010751990030303035106011941c00b10900e4010001b00102c0410306140561101d84587c09880043c00f48080d58404011181511440610250f0307450b10752400000030310502084038265440c003007a103107414101040d1004170b400c048582a424054138290103600500070060701c2c0300003104002c01c001c86107140c0068079200d030709403d20300d052040110307000c4420b110440311840d1121841d04071a021749410329500341c025a00391401030844c5015400600728004400d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 926901061 1250 926899811 926899829
    0x20316050705190315270c030606060c05070302060c030c1911010f0806010c0c03020d030c02090c0a02060103140a0c08030409060b09030c1e030a030e0a08010c080406091703010611010c08060604 85
    0x10b0386e041000046aa400e40f902c580400e09900c04818248850300d0101070100315010303818140001001442850703e614201c1d000310240079414a95800c11074154841503c01d001804103000c7d00b04c0e4500248403041e040c0518519a0310305848a00e0098546980301254034184540c0ca45e00140c115401b1030030582c819020f007850020381e0128241a03860f031003d1342c0b0080d0f011501c82950800c15600c000c10301c03039461003560450030640301c1402e11482401100403040059014000402c00728100c00380307100001c100174041c0c0f2101c0f117403611242110a441c0c3c1154070076600004d001c1140c5249403080a00910114031540d0408102e03800281d100c042101100c1c0c842c40b0780c0100540004054210040309440007000c841d10034000f89400761070704880c0304003540304c1c40420000144286044c040e4002c4480c0c0c0e503854012a03952035072071000500d240701040d9248403c0880c101c101d080e403d070080d8060503003510741a103000883c0101a0030343d00018840310400c6420700034002380c0d49460040d501035542c0ca013 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 926902311 1250 926901061 926901071
    0x1202011104030f02010203190e01111c05070c0302090f0103200a03080d060b0a0f02010b1014160606170f211b10150b030103030915020316050705190315 67
    0x2000403855800348852349403040b8060018040055003207003010304070580a0b00c4150103612201c42e61ba40759000741024202446590755844145849000200505449603090900071030300c5e07402164000c04100c07140300e002c000ea20010300911180325001d5500104e126101440006d410010440c00880b40c8802001070740c0100d81c0b108015403507003100014001c40148a9180c840783d2000030140842e075400a0090352805400e0350181c03c03d030317005042e011a1074584e5004c14000d410060002e5200b0a07090389034140d1050032074001084d038090140203000031900c00320200400b007106400e24034807142c1c80c1400d50260301500340d4603d800c1495034140c4501800c0315194288460b903005242440010340d4803602491881000c15501540000c0440058194203080203858044101c8144030a0001401084c5500c07420440c01301c8900c200c1c18460010b205507400d22008010f07a140d2407840200c215a00e0f0040641480035060444004203080e203091b40f8000c01750300d1902c0d1044440e0031509000300700c603110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 926903561 1250 926902311 926902313
    0x803040b0a030e0d031b050315010c08070506070806011209020d111c0f061508061306140708040b060607030516020406051c0c060815010c020f13091202011104030f 72
    0x60383c81002c51101c01416900409911100240200f071800301c030f44001c0b0140705000c9402403280701524071407082810199038103203106d00103440941c015a0f0484a60f02d0070841480001d4043c0003c2e4000c104940ba24000c5062000000d03102e12181207056480034680752400c00543d03036440c0140181500420024480700d0701d18007061800ba403c9522412201c031241c450001c000c45a40501001d9001c0da40820620b19114034500b030403001c601c02c1c40c107190701400c08240340003220310b102c80e00c2e20f11415000402100940c0c0110310b0103005c40e46100400c0d8900200300511007031000042d4400b40c01c494071450f00c68140d80282942c01030007900d40300703c034168041c0403c544543d03002e00c1c0034040003030062001c01c002800c083c122038100c200445103503444600c0011001d005d41300304c074064001c021030840340b1902d01e03004403651110b04c41c1c00ea90088481d41c1e130444944500c080303021f042c120400041440e008074203203e40d600007102411030071a817510040003140403083c1c4c140ca00792903106004c800143d0301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 926904811 1250 926903561 926903567
    0xc011a1002100525120c030b0d08160b0f07030f02040b120a0e0304120317011202060c011b110c060703080408130306021801110f0607053009060c040803040b0a 70
    0x51011402202414042065507403600001404c1c8006041701c1c0c144001c90070b4a1045068419441c0d4032a00b000030b5600c0c1600140e80c04000d050050000810106170094035240d40c084034070155650310301102f28009003c0626070500070314800c0c00c45250158a46032403c0d0900c4598491440394460100c81000420b2200c0d509820005082c1004812261540d440c1c0d06044c01c50f405401088010a003a0071100c0e48400303001c080c2038102c6a0000c1656450710a64003404010342c0031900340780a6550313910346e0f000c288142103101c01d007014250383e808039070102d0622003d1428400503421441000d080c00b070500007a40c004074a550140d1f22620441c2c80d0314046002c100c030042d0390f400003403ca50000c59041d0032001c01401c0c20400040990724205a0b076450902030752264400703840340b080c80e046900010040c41c0178000402e000b00f00d00608460010701e8840200345840f581c40701d400101184001d000c180e8400300405c540003000c84120618091500344455900d1040d88100d4428520104611040c280 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 926906061 1250 926904811 926904841
    0x10209060d0606180b071403092809110a110a2901060c0f02100e0303030a02040f051009140f09040b010501080901021305040504080f0c011a10021005 66
    0x2611240c0c030740001da551800684558010000001c035000e00840902901030709440c01c4903c800e0846107000ba42d6121a054204e04510304122844208000340311170f200c4440681034811200d408240400112045003100051a4401d81c2d54074140300e41000045210f1040b54120001414000c3c0080f4850b03072081c0c100003200388060604202c0704402504000d501040080f42240c0920000045ea25594145d0707060b00200000340200e007520901d4801800d00c0385129965520b281444060900030320000b030314580c021101d85000c0c07900801d04006440580d404c0101a2000701c500d1f050304941d60400400b6041144107103803011000101c0030030f940d04c0b00e807030341012441c5c050020a054502414502c0a1000a02c03510b40011804030005261400600c203451400c4054400c103030069141c403040001400303000d40155595981005800f1101c1a030a0084c010b03140208008030b99099400e013180070750041608141e0084011407a6a400164046620303031147c44071440006164403402100d81c0c0700c031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 926907311 1250 926906061 926906077
    0x302270a170f0d030501030807170d110c071215050709090e030a0807050918040606090228051204060e0a080d060f050a050a03030c030c29062209050102 67
    0x51860303510200041c008102c500b6010b0062007240e1200002c00da040b42124000d101c05440c0301014481c6100141c28844814080000c2070201030814641810107801c4411361075005c56141000214540d5005042c000a001801c2008200508000c2d940301d000c0100c0b81d018503040350554550025081c90301400d0b944000d4420344604101640b00e42184030380d603501034241c0b04003040d0384000255074035203d0001c80d03c0d4104060042c0d0403c841400481c501500c010b84200c40b240c2c0c55100120b071644291000e06815250f101c01851040019001c00401001c01503c0d002040003c101a807144039010090703a8100d54022030004502e00c0080c01c60b030821a01c0b00340103002850010303c174000f000340c5402c200f0656003400c0544800581e50420040302d040e00e0710450750802c082007001c1000c28010503810002ea4080d0070400240401d030742d9900c158550500400d0034900810710202c03001c25806010560089003136a1008010b02c444d907950540300702ca000500342594691036100104482901501c1d001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 926908561 1250 926907311 926907329
    0x40b06090907121b0503010302031516050912191401060501021209030c12030a022806021606060e1501020105060a15020f010930050702061e070302010c020d0302270a 73
    0x44d102118000d00316882840f00740c0c4a0707c0352075001c0502c1100692200d00039852481d11024188040d04c007625150441e032002c5620000d10a0001b1410780e0900c07814194401400586048008503d0104c16009132202c2603074842c1c0c0b400c0b8003405030b6600001d00108901c0085141629461400c0000303140000c0f80b0f01003500000b04ea032420000450000181c2244505030f000d41c2d908001c00401da40e0403080241c1500740404a440c000b00101301540d0050500580703032180d0030010f88554a50b4402d80305503071300c040c80e1682e01034100900071132040d081c40301c00a800d200901560500b4000540d05c081c06001c1c0d140c000c00001600008140200030159911903c20028000382515040c1000000484060100700c0e04419040614540940c8000e40e51441207440e400d0400c2150780034803080750810700c41704414081d144a4009001c84035005001d00d24481e500100380c050603044000e04265211401304141401407100042d021615541c541c0e0751344a044075440c10b01c24100014000c030203141d0002d14a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 926909811 1250 926908561 926908601
    0x1060c0f02040c030903020105090123040302011b05130e0c03040b0c0c10060819020105073e03010f15050904170403050d0e010906080a052a0702040b0609090712 71
    0x15a1301034102d00314081c0603400070462030b0303980e41125080e280321580f41d0000065800301d2010301e008140040d900140a4800010301030039040900c1400910700c4080d001080d0081092041c05070076002c480d001d820348050004060074103003000340141c000640014030011085000440030100c040c1034500503117460b0101d0791400101e9045100901c414042e848103401030390500c86036402168040f004542d41a0b544503d0a642519180702203034a89641380c404000580d4a90407225020380c1040c50861803998a00c441942c0d94101421500003c4200d942030741001c807140c0c101c10076a1a4078080300c0c000d03034a009040d603483c0303018190031043d460b0855100c4d2002c00e000c011311100003080ca028044070b0300c410400d00710754001502d01460a10a020010305c191002038000e5000b81c001d660082903058070414825807000340b0341000140380c801003501c0240400c0c41e00079840c0a0017145c008407400e0307554a01d07000111002c42e8880400400030000e200c0101d189184640305980041c1418580b5484d002c0c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 926911061 1250 926909811 926909831
    0x60d060905010f150b0901081602070f09140906010302011436010908150106030908090307060e03010b01030b090609040206160b0f150918011401090204030c06050301030b01060c0f0204 81
    0x401003000d0b900300840c1d101380400c0803038983c1004084440c2400305071076075442607444103401d001880d52494010700318040c10344000340050324610450080c1c82480d002144a105a4550300c80b03035600102449171a51000c0300420240c2d0708100c41d40c1c0c6526400c1042695104800541126815101c140f140d848400240701850511180890440e900c0241c1c0c80101c010b44e10351105948040c001e8240500c20b91130170040080350b000703901c0440a10700c695011800c29404100007801c244007580100003045445c000309107039180a208042040009082c2081440e0f442d002080b02e5440040039503010b0070002d00444c0940da16042900c146851880001000c078bd058076003500310400649161000c0300038840440c2d004990407007400c056843c082c26034501c5985d0744030080781e01c005c407500b07040c10355683c0d03212440e07440c00d215544c9001e00003146002da651891071510010511303440e442a010890305200500c001a0440080c504503201890700011a4000e401e103220043c000010081d40b0524000280e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 926912311 1250 926911061 926911091
    0x4140f0114071b03050318191a0c121003080a0305010f0824250c060b12100b13060303030905060105030a03091e090f0519050c041214011e0609020909060d06090501 72
    0x25142d14820544062008000240d02745c0c961000d5500680402d0305102240ca20301640c8551a480b03044000104400f682c0c90312200302030362148086074002130b194401031051001000c2054014400400100881c0d00d0070300513424040d5100642c260050a64400310300b440c00e401411070403030805440309012111000e5005002002340d084201c1d120b42c00c0c40030350586890034814115216000b04060100b03d00c030106a84002c2c507910b0400f5134080c400420309614032050b4440d010107140301c0d4400044400326401c14603d1700d081644058400d41c014224800001d07404160401104e401e08214010420324a814002e40c9905402241c9068584480782d4035140494000a0150b2540d5480c0d143d101d21ba06010b00654504071961010103034100020480010101c03007035074616010700b050091247c5100055800d440100c40046044e06c81c0b0400018a4912032180c1d00c01842005021031070225040040b400d140001000988a40359190052090080d117800c005155644200200803804203900c1003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 926913561 1250 926912311 926912353
    0x70801080f01020a050a0806150d150801150312050409050a0c0f030b3316210c112e02010605030705060d0504140f0114071b03050318 59
    0x16a40d98414030003660301250040c800c954500c0c080340c3d94145480d0190a0603100c0b40f0025060540082c00b21640c0d03690014244040c0003a00c080b102c001c03540c4801030442101c8110b080c0c0000c0402e9140401d02c0c0c1f61052000c440354100c1e540071038802a041d00402003510140620340c01031707982e10306040400903038902c1c41c0d2080e2214142c0351a54032100458401c00c60131944d03442d4a16030031403c00d40304c10403c00e041a5002e150b852007003800e020300740c0c048080f45519410000480034100d01e101020f81c200051425584c408041481c414030380724cc86114000c00440d41500094550a8501c880d44042e460704410442c004070300c124103001044000141d0501210b8035292440154a09070f004a0319103008119602114802000c150401e85400062001000040c0003120036003c3d8480d510126403080c448041c58507100700000480c0d2200418920003403030002e2044080009070504c140c1002c00c5a0701c81103d1a0705460050380701d543d03034000f041010403421a8001103104850031003480001080c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 926914811 1250 926913561 926913569
    0x2d120712032c0a0b09130e01020306150c0307032a03020d091e1503020c0604080717040503030a0804080c19140f060a02090a0306020301090209040605010807020330070801 75
    0xc064010b00c0d40280104148800405840d4007040d401410840c1162003006080c040c1e50081082c2c18880caa00d50040c211007109803002600e135000b20406c82c2d280380031006461600b0001c0c1c0e07040d00d030501d00f1542039202c7c4200c040080501c01d500204186d02140300440e2900d103400300d2031203c00e268990070065624903a0f6a8070400042c610000803031501c1000000c5201400154502c0d82e04034101032002182149400041c01090b80c04e01400e44144000c00c000390145014452450307403070100d42044203a032031300442c080d100311108020410940d140041124810121403401c81d030302e82c844c0e00d00042d4500c11801e20368800e10800d00640381c000b00320000720300103034410b0340354058203688031620701c0e100d10072095125955081103000036001c0540d5001803c203200c0c001d207210a015220b0b5554401c9800a03000511060343c0411280c606040602c5400050082420042a1483c0c0100002d544e44900d240061021000000c1e00f40c004c00c0400c2261900d10031503550840c940380100e80100041d1007489 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 926916061 1250 926914811 926914847
    0x61a030907061110110d1b0311040513020304140106090606030f18030c150507030b010210050c18041118100c0201020d080c160503092d12071203 64
    0x1000600703a005889031120301c8500d2002c3d1030715507403110b4840c00170081482064410b40302044884401d0906104400740e0315541c05041c2185250050000d01322050041c00e0b408c40c1c1c808010600803070b03540500344108050900c802594903590f600d010211901c1107070003082c2a41c200000420604481c0e0811010340b40c080ea0100304a448450051040e9030a11a40d1680381603400c40500c003017031103034080d501035601906144032269501d1540008440c804c0300c28000082c0c1e00c1805280c07541e0b05100240742110a1203042c042800d000803818494850f40c034035201c40d281d804100b41c0c025200ca4102d040c40c0d013220f648981d110010310500f40301d000740c0a00014480d0b442c001515200c140150444101160107a005102c0c22030300e00c034182c07889000075006004846060007041200c2421260540301c03540704502960b217a10005040c4035084500841b1900a207040c0c00342c941406010303051581d00d00000b01c0d8900800d00e00c1403849401c0000c00d402040c0342ca40e0801680c0c1c24160008410008509544 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 926917311 1250 926916061 926916073
    0x51b0d05070e160e0a0b0c030c030c0a110402120105040b040b0913030311030103080a0c020604050409030909111c0c2c090f0402030d0f03061521020c0a1401061a0309 73
    0x560403500d0894a5013580d80c00003841000f80900c40303080c0f01400145170a08100c0c0e1034400c0c00c59000e407442c2c11001c1c40c80c010b40d1190421104104121526810786981900c0560416890601d4070122010501a20b0300407075441501090980e03e54010320f00350348000d40801c106080030603042c5180512340c1000d5021a052000d1000c04014020440341200d402520303181c1054229001107603044d010705002d0b0f912000600c400b06081d0784610894040ca8480c0d101c3c1d140081c034029200c01603c5c910410f04a07520720078425810100210942d01c1c0310040c0d298000580c4900030b40083c0c0c0c400840c500d19207000c290b51040e44600343d00701d08110209000843d903150099541080f040700710320b01294000d4050300300d0070010f5070150080c0d050003a03549060902180d003135224840380c480c8609001075000011510740d00c41184001130b0b041900c00c0c8440c400309510700300c8964109035907108030342001005048500081c0400d80003c0d4009009012000781c2525090102504c0307082c1504255807086450041c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 926918561 1250 926917311 926917351
    0x5030415090503060a0f02040306021c0b2d0d060203091011180904060b0310020a0e1512041505070905010e0103050601081f03023a051b0d05070e 64
    0x5070310280c112000280100516a1400d0b15100074003000b5402c0c02189409010100001d8024009028400031400c884040081110803007020781c2c007a41041c90040030020f0328607100d0b5010019a456501d40300c1010510002c1d03420201c0c18000484601030112440401400184040410701c034400d60403040b01404141c43c0701d60422410711400c80c2005481040305909811810000d68003a0321500030341d000200e101c0c0303407004281043c40106c501300b0b0040d03001403607403034150700a508002040d00c155101d1020030340d162118100352151101c20760360b403102e000020303080244288426030480840d0806100c80e00f4500030190050806000e0380d0b021901d030394a1964907500c0b80c4541c03031042780c050f59482502c0e1501c9035010712244404040b4202d544010801001613103804010380c203030348000000c03d00c0c201040b8200c20200d100784c908008111041c50114000300384002807000710340d81d1702260b02d400c4010480020b4456031200c00000c0c81800f40e090001014140005500e10911455903d0201000c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 926919811 1250 926918561 926918567
    0x120705150f0a0e12061e07051303080301061704020a090b0613080a0c0e1b0a0302040b04030b040b010b030c2212050f0f0a0201021203130c080c010e010c03080f190905030415 76
    0x8200e46c0801e030007030104444804040311001160300051681010391a041d0440845482004150000e8074100742c00801013061035804050312824081791101710040341059800280841c903a4443c22000b43e465140c181c00381d0742d075417084641480c101c1602d0322540740c2c0d4081c0107817560b501c540240d49000903107600082c1c0043c1d118a281c407441c3c0c00008485031000059032100a81c10403101c1c4030030564284000306101e01c0241c010006103003e41c601002e5480d107841e2400312142c0507080000800c40034010701250031310100a80306c003440d000c1c8007102c8400c0e40e40882c0c401460280c2c40310306180800720100041c42008540044079422950a4412440503001070f240c2e9001c050700000e0061740b0891003000c01e40381e0305000d903400a884ccc1c500c2c45c000350b115485a40e100303099a0400320483c1c2180e60501d0a5607000412140710000a08291540f0255a200503142c0e44001306152882c1c02007200003030202c902c40070907009003090b040e8104801c828501300650b40e44c0250003400da1444000b15146032041c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 926921061 1250 926919811 926919823
    0x20c0f0a05090f27031305030d05181824030d0c020d060e1e16140d0609080f070c0e0606220b04090515120705150f0a0e12 54
    0x4030160014445448581c07020090003c001c0c1450036040003014124a540c0390701d02000c00c004a1140159290f0301003030200e218003815030b40001e00c030b94040001140119049016a010320140b0540c6d0702d449180c50303000c200d00d0080c000700700104100b0003041085c0343d569509844810122a20300981d4025040300303141d036401c8404280808110306465200040ca4103000030440203101e54004181003800444e03852400c1c2c4094094041b14003816807080f414002003007104591550b4034005c01c10646405604e412488a08003118092080f5110315414041a80c02000e016a03104010540d1050308103094052900184002c40b82c0b42c5c203031603000580d41455400c2c1800f80c0700081400703140c00702c1440c80020440400c0e0019881c103440d9800040c1c4004004007800c0100086440030465203000e00c403000140365550f54007031042c507013200f00070003403400003a294040d039000ba504600c182c40140f41854850056080346a04030720005601e290265202040ea0b04081d003e6800c1e40707a000020800d151514 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 926922311 1250 926921061 926921069
    0x906090f050a0608100b010314010807030b09011b050c16060806100e0303030f07140d1d0615060306010207050a03080d0b0603090c090403050904020d0e160326120106020c0f0a 77
    0x68040c040030041800c895002010100c0305040c0059400140c40c000c8a490b1270980c4a411182c00c480c404005021510f003000f54090b8441000700003201201190a40d003c090751084410490040b031000c20000d8104a200fa545401100010b07189503507610003000807008803503540c0582c14000300c0140060080c00d200c525454024007841c15591810b00000f41040300030300d104104101c13800038003105245000140031310700301080c001c40d12420044000004030101c01c00e020580d48050204038004e044115414490300381222040d50302d888181c0102c1c607001494000305c1d441005080d001040003404401049840c3c40c0b214140180d10f500c004200f45030100f02c1d62808107402181700c50040d403519001c0c80790b00c81d200382802420007a1b204040b500701c0c2c00c541c0641c040c50fa0ba5070303075040c0d004408000013600800080e040041650441c0d513402d00c452000781c0601c1d000800c01c015607800c2600c03502034907030035094820340000030741c0d40b20b000039031380c01864480a025024801e0510114100b03900d6071400d032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 926923561 1250 926922311 926922313
    0x21010621020d14030910030e060612150a060513150803041a0a0c0f1115090a0b090a0909030c060f02070804030b070e03010f140f0405120309070906090f050a0608 71
    0x7580b45500ca07111030380f510701ca00c02c85a00003003050100c903644000d03d015a1000b40d55000804803003000406240500c0940030f188104002c103032100c021440015442c09071244441d07114903d8a0b107010781c1c000f5140036000954019032420140d40382950581c07151240f24084d00c60102802d03502c000050700c81c415070180d000001d00030761600454100c0c20004000c441c00a1800c010380003046c0d00c83e405514400d42048481c030090300300502d02c600d0b11520000056102400700d900e400e02801c0090303135102c1a031007001103004020410420591b54010104000c00000e1400e00041d0054070700103107200c440c0441141c1c100e203003400091030540307035200382c407807242e8401503a510749030a6071554040c2d03d80060010007004402c0342104440e4500b8060380d80c07108680200440c03580e4070080c00c80c000803802403802990142c2c100400000c00d1000606c0e08102590980303480e80c80c1c49507103210f03092803201e4010000141c00c0a034001455400e5511840c0340d2440000c0801c0070707440300001401a125240704080203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 926924811 1250 926923561 926923579
    0x1104050901060513030206041202040b10120902010e03030c1c0302160f05101b09050102030909010306090f17090405241c02130b030d11070605092101062102 69
    0x3031640103800030150100329404500c442030b902d83c0054a143d020ba00901c0c00c00c03649c042e68a0450805001d900700001080b5801000301140c2d14008124241c20b140e00280980c071565030800b564020207100c0c02240c40942600e56030801010340c160f0f0b52411503c40411400d01c02000700d1801d101c0e10079103402c00d48000e030541258041e80c032041e082008a100c01d68550040451200101c4024801d05103401000c1e42c003103100b840e4008020303111807000c0e80324605542003000b030449250b031444161410359606c103400050300881c7e414407040c0120800c0005180b0022060402600076541003e0206d4440466042c0603d541e2907008000c1500d60020700c800c0f2800b0504510b950b807900e5420480308401440d4084401c1c40f5a400280717400002c0742d88101c4080d580e03001a0010704051100417000c5800703081058180d5956482c2d946e444100b48504c80030024040358541850382c0c0c0282c4c180800002c0221559100e1480d03c034240200510310640c0100c0503107003000c000310b60901c9101f180e1a90000c00c0816 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 926926061 1250 926924811 926924819
    0x18030d0906081b0a1806090308120a020c030307020318100c03030b010e0a0306020306090c0301031e1506080f1c0518030c0330030103020915040603020a08030d1104050901 75
    0x21254805072a080e08640035030800c840c2c41440c00060315113151280d50f81d2010b60b2680f0428190140c007a00502e0400010510520101e00080f049540e8000400c0c031191147d030b2404c0e9a41c000340202c00d4010014003002040c09101d5230b00101909c00e401c07820034403148101603c02003103803150b89007c501010940820310000800d009902903649582c046c140382d0914200e071030000301c0744a1705400c11100c2a6010080c084181007443c143d0340d000503001e00540c0b4550441c0c07140340e030803400c1c07248a48940e92031180c4602040302c1061030550510740781c042406202d8031a01c1c000d480d4500700c0c103444032512400c0003d01c030440000040b041d802145072542850401514490070b240c3c6410f6100c10f80600c520040612503460802113200e400741140c2c96524020040028810050304020342d1411992080c801400980d56000c200b075007181c3d410100640040c00b85010802814050707001035400007145d800040c121102100400c4a01712456003040420040d880c0da522038091030060a1b00018072000600c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 926927311 1250 926926061 926926067
    0x30c031505060d15090510090c0b0306060906030408040e15040506010c0c1406120403020c3d0318050d020f010612080c070807080703292202030703060218030d0906 72
    0x6980b21003105002c1500380c446d8851a141c405503000000e54980e5801400781403000c0c40356981c025010241e030035072843c14178a00040c5940540c840301c2e4803130030001000c5800c101124003200c0c000c1000081150140c54201000ea10300d80804082d40e000328100b00014403558800c1e0765500146505c6206598030b02d0416104c98005030720f0b4180a60404001c0200c80202c3c144110300034491440b030790090a4891045042c0300003414200b609a10340410322280c0094108000031512880a02c3c58071451030307620b4001c04402500c088042451903400e481c0d130031400d028010841c0d50728185982c00b200c0010540711686400c032801881030040d8100b45811420008101304000c15040c0c0e22001107c11180d10b42028a01f080c03520b0b80100e04035844114100704104020700c5404619071000080e03100b00c403410b0702e0740715409002808880d060300c4507134800c500d071070501d555011a075401608540b0115100d14081000394081c042040ea80480284a4051854002600384108034269980d00e10249810026 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 926928561 1250 926927311 926927333
    0x60108010e191a01021908040e0a1d0d1b02130b01020307051606090603020406120e0f030d053403050601120c27080c0f19030c031505060d 61
    0x1407a0250200c2450724074400b100d02403441080c98082204164940c0b807000a4130304401080d001752503000005c1d03410007040e80f000554086940070280803c250b95005404030050080132b440d08680984002e501d99884400608010703200d10f01e03140c1c01c00c00c1346441c800d60101102018001d43c4070385c04000f14144220f86800240e55054180116403e007601035645608240c1009250849072548c440c08102c05584030070484010105030504516141c1001c0d4024451108150118040307030700c0d01c10040c1100c004002d12001c0001d0101502d480d072020300700080181030151400b0084008e203d40598042640802d0700407000492000502c503405131003020785c09000010030a41c103000745042a0002000c4900400341d001c901541d8994002e00700128180d02d40c1400200110462a074003000e102241002442d54400c81040f20840c0300d0940c060000342d428690f10300b00f600501c04403100081000111064401074034410304500c1c0300e110340c00003105c04907801120381990101200c2c81c4500072a40c0080c2c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 926929811 1250 926928561 926928571
    0x3010f0519030b090604060522060902032104140a080c100309051501031a07091701111204050d0302070b0601111c0206100e0c0a0810091a18060108010e 67
    0x21511166251121043d081048032603102681101080100700400d5201e0241c0c070010115140200d0141d014211101e200112002040d869482842d070381555405c201c100c2d9010f8080703070701148038811001c0f45450358001d407103454003001c1004d011041c0c602c2d0801c0d11005072080c16000b0900000e90100300588204031185c80d1062682d20301104020032002d00c2140881c1984800500381c9501d9440c3c0403425071084c000a0541d510148203001c521580011075104941846061555165070015218010196810149240d142c0000c2d400b0320000b451030030300e2080b4025001d44a20b4624010160180e20405000821640c10240001d0066000d00c039500d04042240080b920040030350b120101500b41d51b00c1c10710b80941d104c00c08000013001603140000c0503107002c080b00e558074203002c05024010300507043c4482c1404005030010b0a40c000001e540c40080c00700035000e11100420b0803440001440100c1c0e010300039410030302c3c000d130460626400d0500880041c0d4030a41182e103000301d180103200010302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 926931061 1250 926929811 926929849
    0x20070602010e21090d0c030503040e0a02190e0415090c0e030610050123030a090b0604090f020d080c0d09050315010e070c051603200420070f12080907080303010f05 72
    0x240200201b03964200d04006036106000943d0340c0c1d030500c6451000a01c0051154000314010400c4040b003040c054080443c9a589042400720560170b03400040151540d00313644c5030307400700f040b000060400542c0c100c1e43d83d4080f2070301d425440031400b1091546604c5d00300c402e6604025181e0b8204900d500c100e1203d00011000f24840f80038424151400d0301700d5105841c0801d50944600c0c0d05c8090041201403190007180c1203400b0008841143d442940003152180c02912541c0c900c030000c014042c542c412a44d000812400740c40c2c02e9a41c40a0141c0007904a005040c001d10606402e641d414041454050607250960810f9106540e000412596040c4e10502200c40f405245409d0482ca404001d00d0346c0550b05c41d10b400d00c8088081d0101c00c03141035616120300c0c0300e2030030718500103101c400b40c0c14220306c1d50b094031030b031507a0742c2640b0b0514080b84189824000d1411040d0903d100384c16521960440c042c6000701c2c25201c1440c0e0ba40e202c03c0c1d49000a01840c41d0103410300104100e6860a0070703800302030100d410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 926932311 1250 926931061 926931079
    0x10030308190c1d010e0307180b0301021b0d02061e1f0605040501020114060d0308150d0807020913020114130807080a150203040b040204090320070602010e2109 70
    0x280702800382e40040ba400c2001c54042948840c2c0008104140760402d2002e1030010040e10021000903a0340c1c005101e914004809422409120781c4160029041c140e009002555981ca6805081038150807201020000740920305503172400510200300349025240a60f0b42401905600d010064286805018103a040300300460b654100800700345600d00509258886c15103640c138050001e803c0d140b4491800385e10010800c00c200459403400c030a0565203405180c1003246940b003402e2410040d0388460140e91094201001008009030310004141c11407081d41c140c02c0e5a1128011000c0c0c0c49030300358000f4040b9126415928139801ca100c042c00d1103005200c4d4208803595203a55250400105400c02d01f0755030420f109030000e0200a0300050489003610800b14591300c1d05480360168001d02410080c407458a49941405140c814150310400030540e81800c0700d100c032148042581e07070740350744904409075003400741540e0540008201aa1080406d9101d9244000030707a058031103907489846a030350710407046 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 926933561 1250 926932311 926932351
    0x507030b120106141504060503090a051b0f09060a14041d070501030e03040b040b090d050105070c0b1e0c0706140408030405100b220f0915050f10030308 67
    0x3075460302036032116038000082c200c0c00d058000c00c40040703404002e80109186400340000c54070342012101200c02d00d242c15501e03900d580203000e052100c0c03110094254440d0300742d0601c0360ba11407031100b891000200d881403040c811000c24001f8850f011a503c9600018541d403c00180080e01c50198038014010700024054202419102035940c01d082003148980c810101445196054400c60101d0007102009604251034010402564030031809000317001040400c00d00c440d91600c00620580552000003400300741b0b000600101359019429041d642041c0d502c0c04200d804100c2042999010000092070045a440105600c610751140c10200c0d40b05544124520140ea0415102d6025511a00d10907680341010f0824515100c00704050008191a2540b132001d26540c0055428103840390711300440d10a003840c080352000340407140c0c0b0b18036a03504003480742c010030144105060003001480c80400c00ba1720385065105180c0c40032074900c1c10400c0d29a6046c0040f03130144041e281e01947d01c0c81c10303900408003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 926934811 1250 926933561 926933569
    0x50f0f041a2e03020306091305010930140412020f121e150703091b060507020910060e0d2405070e191505071b03030810180507030b 58
    0x914031031014690350b08010140e580c11540710195110359245419410f5080c11000281801e4002d041c45120460358074a1104204c0b00390801c0c542d00b0b40003500000001346035465045002c411004102081c0c4002d00380c5c5103140d00450000710020810501542454140880244c10090034641070b84e20010321002c1c41c020303685540510304e1220001c80540200511840c0141845e42c4a81144c0125009000010540030008039101da124003185808944000c49090030712075080c0f11075904c00003a0400c2c001007030142c8c0040060030701c54402d81742200590b5420004d800940160701801001440216a054840c034003224a448214004c5060a00c0d00903e4080d450801013000203819403184ca071410000c4090308005a0070104c0d03016560400341c04030301003030b22a840340c4a008041c040c10300000d480b2000b41c42a000d403000b1380d5000700e19241461003008000350317240c110300c4100c0c0003404c0ba030009200d01807011000c004450505a418812011300e620020190100400100270540d0340d0060980c0c960b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 926936061 1250 926934811 926934829
    0x40b0a0f0f11040e01170a020f040b090103080903120f032d04060506310e0732011103070303050411041b030606020316110105070b0a15050f0f041a 65
    0x229108201c0e0b038840c900340525440440503032020220020700280ca502000c40032424051813541201d41485142709040090000c0c120441c81e2600440d030000040304014035000107210a07101201128520b44401d4074032000c0f031213660313190300d070024041c000300d00b940c800c419413080c03054010340e042c1e00c1c65080c800316109005402c550580d02180c440003400290f0038007454428861104150b808030840a180003580e1400040c034140d000a5076400f40d0050a00c01400500040c1a4041119099002911495070004600c40142120703400c1c06140c3c03d115800f0f0085006503180000140d41090101c0d1425401840010000c1d00c3c80d50f80b1041100c03066440f44500051101502c4410050050003200101118400d0b0050020342d44100030396408020a83c00202c07503598000308041e503c9a1441c01202c1c0c40c000d00c08014404020403080c040018041e80101491600303100c00c140c907040c1c0d41c008109940042002450304001900003001d401d0809070441301c076000710125070012078000e410110302e42035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 926937311 1250 926936061 926936081
    0xc0f0315191401030f20040f0f0e0609070b2d07050f06060a0905060d060203180f2a0103060b0a03140a09023d1115040b0a0f0f 56
    0x1401c0081e6144550400e071141020050035441c50b6040d0703605542c3d400020b000b034060040c00d685d03043c1d104400c181200003401c4002207809001030040e80310602d4180301a01c4250100c0e0a540e040c000c00e041045400281c0324816640c04000306070071407030051840090790145d41403111006903003d854105200603610000c540130108038032651031060382815424a04958004c1a950708607009100c0700e0358600c000320064608004001610340c8441000a01d0f48210040080091f40040100281d0882c0610200c81e078008031001c1c3c480080201c0300c070740d80f10565614000d07180c807845401c094500c0c1000c00c00030b110070018180012802d844542c00c040940191003000c00207078596100040d800d0f44294a51b400c028510018801483c1036030004d066006010702c080302e6031440c1c1e03800d4014000d42640d980c6d81c01e41d44101c0041c00b0380b610480240b91300c840c0001c40c0802d11990061150084240031014070940e003100d08091603441e00307483c001c007504c50780c401c040c10603403100400200740c40940b02d100d481c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 926938561 1250 926937311 926937331
    0xb1902070501060b0316031104050f040b13020423060a030c030b0a08011d0606031005091501080a06060605090d1e230601150c060c0909092a080c0f0315 67
    0x3d25150755001d15021003106032204040c102003c0542d2103000809640503610211002c0490185000c04100140100c28413b540504811b1003024012503940c010029541040429014052442000080202040340aa410480400000c0c02986c429480003c4402e49460081000150b002c002407006000350000c89960f5942c1d08250123201469585051850615001c1d000515114000a845000940c0d09a000d103442c0c40000350210f0081c0101030803030b58841c081112658448505550f1120190821200e0b185400400701e5101d0152007941c2d5812401054020510303a00d0b65250b01260080f80008a960405003038003001600b1941300160a50300c0d2004500a020150089031504806911440c0241c2401221050107907014500000e9250070210100d80602c50070f40440d5884007660010070040d16102c0c14030704000145020b0f442c0480c00000c6585103040c00d103401d081207240b520950342c00b0761100411040c103007410020403814002c000c0a490040c500d20410900450044400c1d0041b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 926939811 1250 926938561 926938567
    0x10c11130b0301181a04050c0303030a140a0623040b031002090906090603120f0403020a03080915040b120405010906180b0a14071b02041b030501120b1902070501060b 73
    0x7103410244206000d8034210070048804810945540c054028002880364443c1d9258001a062000c20003400399414000780c00c0340d40d24900b2010000051210b0003501c60010004c40109401d081c2a0151800340c0d603481c544104c0650017010b20030b22080040e102250469190f01084030565000d01845480c0701c060b58000d82e03a00540c0c804c0040499004111a109480c44014400c2c1510005206803454144414542d40c403141607010310064041c43e40f00940c010504880030042045403009004204402d8549182035104910046154040c40c05000141401070194403141c64220607001d400a014000000d10304bd03045e181c2c0400e0b00c00200c034078150401586070310010002c002002075803050008008200400700c948003690b808030302804010400640a42d804e08003011104045180d0b5801841000256504040c3c10200031001c850240420700d40000040d50002d00302f01c402d0810307030090386000c0c56612510403c0260b100e5589180e2615428809600095401d01c1b41d040900418040192 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 926941061 1250 926939811 926939831
    0x1e03110d0f050618160201090209010b07110d1e081e0903071703090907021c03050912040f1a0d0c0507060e030a020618030d0f050114031506010c1113 66
    0x801c0c0c4a0140150f80944611384030381054407405559543c1010213020000d2201e020450300301d000d8026410040d50007071003c800080d050344008020184144541210070300b000c2c0b00010402280d0542e0809009014031644a481107021b12200c40e481038880c485041c1844030070160b5071802c512a11800d04903a500040c031500c245010805900200003291940200f15001020a0707183e0080c0441e41d40101d0120021844081c0240400e50319040300d050a0900c218404200901030031094039984d0590055030340e080b144001d40720481d0203481d00d0704d2100c803c25103014902a54007800c2d40500d1548002070081080454140c0a039402102d115583c060300c8020350304103442202e0301400c1c100041c1e8001c1040c0e0007103d030003042c110740c4920700ea5413a005000b100b81140e0300354480c1c122150038652514102e004102c07450352150303040c4e40c05540300c1401500d40780300b8940e03914040881c903007041011000140046d072003014900600c0e80f280792081100e03c0194080b039000048407182c0000389403645204c507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 926942311 1250 926941061 926941091
    0x20d080f0c0a0c090506030a030903061107060c021b0609030a17190c0308010b0418090215040f1d0c0f0a171314060c0a0e0d0210090315020a1e03110d 66
    0x86c0d00104210060302401c822036030040d1480ca00e40c03200629454450003d56004044103050b0388030103401040070b000b5603620b01d1009440750b4040d20751518800c04841d844115042500a4a01d048400b0f0b00400c03600c2078a0315207040500031958540c4601f4010014042c00034051007890100300b510b0b40300d4208030305070792801414141050304840800401840200500050103800405403024004001103040103400843c46005040c2c5c6080460480000c000407a60307000720204048860600700c0c41d18880c5210481d013207413842030341e00820b003580c24001c09a102d00308070010080111a418115500c111030300d0346040b8103e08440c0487c1550010450f101809040300403441c1c589a01c1014018038604000385194501030060b40c1e0080181042c03801030180c0f030b95030689188640042c010758003280803110081c17002d8103d000c2280c500050010403640c490a500940b0440540f90315a11705060351411040c24044401510004054581c400b1007465a0b08400425403503081600114250712203071000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 926943561 1250 926942311 926942321
    0x30c030c0601090c050a031a060c03070215090a060f090906150809070501080c130e131e0c0e060105070b0a0518120306150d020301061d0904020d080f0c0a0c09 70
    0x80c4811800d1151032100e46174040219404203110341030005040342c503800d01c0140c1c003800c08412908083c00081e50440303a0400005400200d108a401064001c910411040759000d40300040c1e401a20030b41c8180504ea0140c003514031494050f05c1c020203095a60754011003a50055440b00c3ca016100bc0c00102d00a603019030309076440f2224000a051103840c0c000000c050720f0004107400350012010400e00345600c0c6841e80c5000a100c04640c800241c00c01d0031020100d01103c0c801210703c8186103500c030340300c11001e40705a40802e0300507441c1040ca515003130300c0d494100401441e0301d0401a003080b5801c0000c144003042800b81c602082d00003060b10303100100a000004102813182c49a01590100c200c40a005003203175805401a6824500803010100301d6580d8029103400d10307800c0b4008000413a601d40c0c4240404682456080c0080c50201d1050a0040d0b80c141500d019400060189410f004900c3c030000401034049000003442c03806442c0c2807101c0c1001034043c0301b150084c0c801c140030070a40d0001d001e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 926944811 1250 926943561 926943569
    0x3030f05091305090309120304081509100c0c02060d060303091a030c09150703020c040f2309030d151805072115170721061805030c030c0601 62
    0x3109203024110340c00a2100c00070680c05000700d075112000110040828415a140300304080d001c011180040c011154807a0810700516485104030341044034013840340e910b03a0f8020520a0090b18481328001c480710050518403400302c0900005109840041c1c403003500a00c45c503a0b502000240782829440d00030310828940c0d01281d00c220040440403081c2030a1801c494202e50902d100c40c2c1d0751070a1f000884e001d44224106c40b40b03030420100c1c14a091640201d500400844201c0b41000682443c900031811151104448052041c141c400f1400300d007601400c03d83c10045031300c116030820101200171000d50780704141c1200d6032242c03910b041100c08080440c4140f0f60025001c28091480c2440d0300070040054080001c0340c21158403101c07001d01015912400c11100711015101d0b4403a02c07840d440b42d41410100c0561a03a100d00000000c000420480c0b060500e041149202c52110b1207480e018040d1222100c0007400c3c01c490000240016010002001001d00d9170024507100c02407240070364184001680 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 926946061 1250 926944811 926944817
    0x103051c0302030c090103180c081506030102070c05010c030e092e0621061e1e0b1c060b0a02150f01051014090a0609090c0c0809060f0c03030406020403030f 69
    0xc1030140c07880005003524210202031070000703061003081c1c2c00103030401888c203800792036080400070200340d022011070300c0d04616071343e003001c40099203402c810f0500300d114051010700f000c640c07001300740820341c85a00c040417003500914124101d21404d400040700c07030405030798a0100f01d42c0c8000c04038000700000742200c480124010009515407402d000585130741100004000074402c5066000b2900b601035000d00040c002c0b5a40600c2075060300800781001500b05e00072107440d40d00d100716030302e000c6203c3d0020b00207464181e00a00c0c24881c1054260154510b0f2400b400c8200341c42e80008101c0c680f8000c0500403156040d402001038840005106039040400b03401c8401c0195041e00520403519090114a9000b1092400490003025030002c440c803400382c0e80000354041d864a0340007400c03a50104c107040070341d844803400300141c903402c00090b201181e08080c0140f02040920030030b010386c42c1c1b5078003800d0541c18040c03c00c4e107407602500d40d10f8199401214100c8150358049014130074542c0c81400c0b0b030b10450a5003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 926947311 1250 926946061 926946067
    0x13050108100e03073903020a1e06050d0905190b0c07050304060c030c02090702060f01080c1507030219141603030e0d0c0b0a0306031101090f150212030103051c0302 72
    0x2c0c00003a141d20581d200942035130104078900c0e1a031600055403110058884100340141140c410b5074196004a510040c0e214920b40d01340410306030f20550030b4154500d40c0c1f0344600b003803c1c0b40490945031501310030f5405060994668084011a80c280800c0c10ba2040c05845101011040d162503076a00b400a00f1824800707100780074600000d000001105c0543d405400c0c403540d58117030751070221203280120000a420400d070100b404a0310f038000400390700034a5081038440700b80c1e88412825607191030b00340d40c507a4045289801841c8100040c3e0040150600a03c140c0711041003280c500310b040c051580d021941c08820400c1c0b0003405400b03000601741e2007604d40300400464a1520010318074542400646c1c4100a404030040820401d001184010071000e55156160040214090010f00300e40c4810745040004006410056120303008800c261100d030210901082e0034050003080c01c01e23041d1905000e40c86280400e0703049400a00155000b140701c1c6004000156141480a424a50307010f88642858014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 926948561 1250 926947311 926947331
    0x6020c043602040f020d0212061207030b0603030c070f090b19030803060d120e030c030105010e01170c06040f06180333050c04061706030303010b0c03091305010810 72
    0x40c142100c41d54200301e022251007001800080c00510340c902c2e50800003440083d060041040e01c1d005495061443c7d001c0000360b640302000c0c0104000c1000801c0318a800c55203052001504104159410610150417641040f5104d0441460b04180f608500008448003100b04490f07621402140b284000a4800b4204605411a460550303402c03170000400c005404000103240d5215101708048851700701808104414aa05018041d80810f5081034024090200044120b0505004107412150911080c010985c40c2200224804140e607040701c41a0192400d09003841d65107001600141c2608503400e6034451500754054003843d50284007000c0c280348003804201203182224880fa212504a107041c8504100901c400070541005010700c1506251a060080c03186402c80980f00b6541103032180c201d50845100d04190740e1408503071440e0b043d07000b080140b0605c80030101802c280c0c420b400072a820520312600140e144959581e500000c1a603035001040500c0c41000310b00900206080104481c40f07003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 926949811 1250 926948561 926948621
    0x10120b06060319060e0604151a1312150606031b050a02032203050607080103051b0a081f0b0105040506041202010513090204030b0c0a0816051306020c04 67
    0x10840c40c0724038004000150fa000f44402d4150802c48070100c00c11034140c58152030120200103680c580d00861070540c0140c085c501c6a5010000e492074000e424912040040e0443d00c6030740030034116000c40c00103010002c1c244220003e01010103128411044860100711406001c03501103500060805050881c1002056201560700c44841390038075210b41d507920385405c00d0f2b15600c03880a840d04584210000c0c00d0907041201d2006058900c96010368425444c2c246003114906001c0c0400b40a540042d004443d1040c030504040b1100c1601409100a19603a20f0f02207003401081c020320f0000403801e40c69500b000c4c0091113160556403090a02e2400e01d4185400705016000c0d600a5400c4800f02c422007805580c024800d580c0a80e0394490f0b4114032544035611034002c0e401c24070040b0380e1000c101000c502a02d0248040d199016035560f80d1125a0b6996107201c0c01802c44a200c21050040c01c0140f8500d0701922034600c406450560005c2290034101000e1100316a030700003031440d03412a040b0044c44443c070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 926951061 1250 926949811 926949833
    0x11404020121020f1305100f120e01060f060c03090905071403150a0803120601030b0607020616061d150103020607030819021215010c150c03091203051012 68
    0x140408a004250b46081c0e003810080c4075181062450301c00100f42051401c01145401c0b09555043d11601400300b44503c05a03240d40b81840100c0104640102a400482e00c580c0640908024000042f650b50380d2032680072090750054100c4000aa131035401407017450b400407241030007800044400c100a01e441701c00103000d00804440d14480640010210f40100c42100d08003c1c1168001d280004481e50b074003901d9525880114141040c2c440d940000312958041d10030508180b002828052034440b4642c00c005a541c003102d406450b040880c1140400326030305209001c0c840700e00c540c07508611211071040c81e2030484000c007051040d5030f1100c01800140c990030182c40b0740c0c0c6d91505080d03070a510b5080566100703074280250000c5051011070002014014144410301031038440389082d959580d40801103507018244580517064000e0b2400c1540180c007641d000f000c004006113000105548265200c20010052091060009848809110111030482003400007009100020b001c000c4056441b440000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 926952311 1250 926951061 926951087
    0x41109180702190f0519030206070807090b0a230d0e03070512070201300501060c030f082e0603050603031602040b150c06070f020d02150601090e070905030114040201 73
    0x3441d00d071440420012420130000c6517400b006660444d2400b0901c501e10041a0710240e006105903004a44000d000d1032a180c0901c109a0300c041110713042185801407580305441c800304010340c005000a80d00703120007016020040320030a45589154500c4480c0989a0041005945410801c181800104000f90003500c41140100c03054403001c80c0c1c00147c4041c5c1001e60f8094416566260030760740c40003006140519643c8400c0100502e03622842c048958a0340d501004001c980c00750300f41c200c9140507405082d03004207116800401980e50f1003103002841c513000000386034108011000e00285805000d2a03034080e00550046040016110501d070807071118032400390149680c0c0583d100325032502d04907000c0d0b200403003a415590b481d984c0c414a5071650100e03101e000081c03444a0040c2e240b440410109212540350780100f68000700b107802d140c1c0101c00a006d0300d040c845605400524101d1007240c240c811007007a190204124505024942074030900c07143e598000c1a0041004010b0b80c00034a414200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 926953561 1250 926952311 926952343
    0x20102070f0b120a09080a02060402100306060f143106050f0d0e01060e04051c02062a0c0f0a03030501050607020d0f0302010b060c0a02010e041505120705041109180702 74
    0x3d03403154885003000704040c104c05420301c2d00014288000c550009032a0340128400c2d51520005880b40c8011400c982d400c0c0a20400141560240545503100d079004031160b429004820307140000c25408a800070740622071211042d411582a071141368000034801c2d0042c111400e180389071500020078030703000d0b02c601c4041c40b12450750f036514160880c000758001009441451008603c904141c06c209680c0d00e501a42c2c41100b8040300843c419070b903c0400d8840c0207090b4011051903440c002041001401040307400c21425050030b0010700038102d01003018803a80310010014240458003820000d064480580066005503410802030f401030b22140c080d146c803d074000b442451400c0310303450704030701411028910303075803040c1c020421805028000c03465a40c0c0c103100b40c84540d03645254006002c00d44c2c0340d41c1580001c4a0494108114030306100c0780445010b0300800170345800316258000075089852039003001480c000c02058107002403c00c402032100110008140012030305d8044002582c64244108807101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 926954811 1250 926953561 926953597
    0x10f1509050a2711180a051506030a02071a010f061b0804050108060301180804051002150a0507050c0303040507260706030f090b04050f120301080601140a1809020102070f0b 76
    0xa011007451307041c3c11114020600005454100d184094041d410b4401203d55032410f008500f48020203c076070009003001600c44d83c10b5694410890009420a1400707a9079480035142c1c2c01820009c1a20301070191048100c01441d5905100c00141280c562540091044034a4070001c3c0c003050316242902c08a440910740041a0703629040828054a5482d44408100300040049420010000041c0003a5101a980742c1c00d500c405070812030340d851950b00d081c51281c2008011502d6502c840c0c00143c0d001c080c50078410302c0d1018010604d0320315401114140c171280c1001800307004041c501c2411034070050040e000391041c080e044030000d85a4609200e98002d01d5035070481d0f104104c07019001079940940156036800340b8603160a11540b120000319080006d0b00403550034644000d121010340f41a18441c6006040d02d03801c0000000b22a44030340700c2c0c20b0344010783c010f000400c0548008030204c0450000fa01191806c50361002900e07020180e0481160081255010f000d81004801910040d07000c1e65802c00d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 926956061 1250 926954811 926954813
    0x1110c1e0607030e030609071d0405010b03060a050f010e040b07110c030d110625030c1b0f021807140d0b030307080a080f01180905010f1509050a27 65
    0x800e400526110503007024010a544050540020030f409400308203034182e45007a42c1d03035422181c03191224001d1203041022440510b91040248038000ea1181c4110300008141c1e04000009180180484003100c0168031241003044ca40012081903005003448a022601410b01d0741c0c400f180c0a90081200080000e281002050328204000040004001505403900141c121780020140c0002d920b41e0030f4207224000200e40b20a545961032100000310355508029002c007004124058020700c41c51804100c00c8040c00b10102285880503c03100b40b1950304800c0d914003034418010303205480100341d10f0705214941001840703600400345c0300114002480c2659500a0840c41c00b00918032106511b800d840081548010002d1000040501c0d2005071920750f583d60707075400321860505090040c3d034902c0e44060050b42018a941d000800a584a10004501c1c4040402c0c10b0046440607840d00e9040c00c0000010000120244505a0404034110040c09641361049004e000c1910344c009050700c49402c0c4503098 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 926957311 1250 926956061 926956099
    0xb0f09150406120501050319080a050d0f0902030c0d020a05010f020f03031e010b0403030507031b0f06051503060f180a080d0903030b090402090708060a0801020f0a030b01110c 77
    0x205004016a16140d01c440e281d042c001c0007221032604903491a45072400106440c640000c041c2d540741141c2ea00b5000c40c00c0d85644024482c0c00000a0000740407007880040c2191a41d0b0044813018022160001075112807401018548070568500c14080d9a10170b2003803016803206403040c81515001c0c00c06848010b00040124034140b4558482d11042c04080103214403400c4046212000e841d10420580d40e903601d0301d8500416128a20004011950402c03007000000d0084106000034030704483c0c0001801c1b5191030700c1500c0450920201c2c0c0b00c1e82d0b00d104001c040403441440c1452307a5003e4004050b2840c2c0038103208041700e0007034803038180080c0582c0d0340c07040c6600410000c030700c0a620424403503c568402d00b100c400b4086000044020908048025030241040c024051003660001d001d0a591f4840c004207851904010f010300790881703507050b400300d0000d100740000c00051005a07141540c4584c0c0c107074010101c44c0304c40300460402040441403004e01c0e40028405d09001800c840500c52800503c1902c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 926958561 1250 926957311 926957329
    0x9050f031002160c0b0f03041719020f1204080601140303070213090b0a112d07030215010503010e0a03080601202b0c0809030102040e011e0f0b0f09 65
    0x1400407a4000a81442c101c400050019501c51040000d5503005450381e500d1022800740320080250620180000303408200303400e0856541e03403856060740b1b00e0020002041c3e0886200c140d040d0001d80d01c541b6002d4402c035000c000c010903078580c00c150142010300340100551608c01c103101d405c01c90030b100c610940044e9420700894201039801000c2841040408000402900044030280c07180c842c940005902c00c5081d00812000500d443c11403481c01d903004060642c01e0f00f500118004602846802e03655290b00d400003420400c0c0207030014484035018800207080c0c400b050300094001e9040c002c8020100300001500d400d165418103204041d65614401200e0003007441e02c64000016030311540000e0801e000c245403c0c4080c011001032700503642c80c0080380d00400d4000384107002599410b4500301045012002e00700d13000000700050314150360382c00b182c4076a4000f82c01c1280b80b854800100c0704014140303180c0600800c1031004e5488030741d01d00146034800d030007030f0503800c070150707000040c1d10440f95900b9010b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 926959811 1250 926958561 926958583
    0xf060904090f140a0b0f090705090118150f1a0f04030609060c030b030c06131d0105031b010504030b060609030a05030a020d021b0d1b0b0a09051009050f03 68
    0x100511862400c190782c0e2401585000d542c40c0b0f200da482004038800c0811072078009074208003006181c1d29100344104c10400300806c40d41290142c4030000c1641d03139401c11041d00a240c031000b151000018541c42c6e0b000c942e41c0e010140c04041d4040000c01004105518403000c440c81080c4014100d01400316011451144914074500312000003404810400c56a000741d811307034000d040030418030083c403600350f00701c81700f98000036459400b1041d80340e240d2074000014441c5485452480351290398414042c20000040c01c0741224180782040144002d08081007994908100303011080c1d11040c0301c4001038100e21413400302410040540d00014078507192107080391900c40c005012540c10a03440d05007507442c0d8202c017500303800501444110740342c20317440000c0643d0100d08804d5504403a490f50700421246800107242205c042c13107a207004052440c1c0300b158180051115002d020396500881a006003a103e01d5046503103d0040c0c0c80e040e41d000d640c4111507000b81c410a6a0310300c0c1040014001a2500109a030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 926961061 1250 926959811 926959819
    0x12150c0207080a0b010e0a0e0c10030902040203180d0203070b06040504020d020303070c05040b180a05090106170a06150608041502040f0b040e09030405010c06021e12070f030c0e0f0609 81
    0x1d40b0700e0070440c1c0052068100c4a0700601044140c59440c0c81c102a1000c8000707048044d03101320b40027805464022603026085109041c00a4103103002d60101d400d030b8204407945c186420030700300c101d40d2840044c019540e150031a8070156160411a540c2ca240d6404090309013401107540340e0004085480e2105c100300c159400504a0340c0f112aa4a003020807000c940c020a4011824403000c0074190612003040102c0040b960309003d0281d8071017072a200100401002244150740705c41d400665284002100800180300c640600310b800d944d42004e0090ba80400d00d20002c40c0d02d5541c040003401d612015158209a1015071220500e24580014001c2c1c0910380083ca4401d94050001070070451800c000c000b181c4500c58100b949a80c1c000341c00740c40b80524030401e808070b100b031078900d40010340603070080280d240b040c20075803014181c220120f001038004c1c5041800f22844a0248600b141d040a403841c50410a407034140041807008000801c4004143d03c05070080110b0b9039440141d07518a01980c92800c4060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 926962311 1250 926961061 926961073
    0xd0603060c030608071503051306020a0f0f0207060c020108130506010f32010503101a0702040b0d050d0513180212130c0b0904090512090a12150c020708 67
    0x10400d14010100c00505201080c03400800040240c4003180345812510b001100d0032410046581c01c0d4042d141c0100b4017030815085000e4400080d28500c00703030001c061580d589043c16624004040e0503200c025000209560140c00200318042c1d20188000300541e082c64001f405458000501a45510300ca800901c1740c0545000820f80481740840141101e0322008081c41c00c0c10a0303009200e074001806a640c0c120340361048501400d5010714002c40d0000d807001c904000099a408148500c44014000c1212802000588000b54502802078144200084500c408106a90769034555600d211604040504c5408581c00c082e41d490544840020585804441d110003542050b120080d80242410380d88079001c20086203510030010905910158020001050181040c440744082c0d00000c10803544507803141d014600081c1e05000010b007070004c00048580310030850b807c001124806421000d80c000f1100b0042d40801c1c64078000e11610202001b00003000d0b443c13007104034200030054101513850301c10703d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 926963561 1250 926962311 926962313
    0xb0403081b07150212030906010611030418020921060103060c03240302150309060c0d0b03150405120a17040201030b0d0b091902130b0307051e0a08151305030d0603 72
    0x240d0f0818025400c180d080c0d811051150035507041c07502040d203100030294132040042c01075a00800b5401303c0401c0c280c04903401d043c0d49201c4818100500000c20000d983c011410000c141446d0407281241100007128101c81c50003210255a6000148009040b65403142126a4060f029600c001d86c2d080d14941d150360303411010804158171020f00e00c81240607003050100440c241034210141c07400740f00190081d1050740ca0748203810400d81c02c522044d058969403446c0c6000c803650b0420140400c0a82c0c105201c2062a00f400c145d0700b858110440b01692a2081209214440e480081300550191110b01c0031125129400100c000304020804139800500301404541844840b080c0b00d0301c5109900300b00c4c0c00d02814030071030840400c90f2a10083d001500210000101151500600c03003100002c0c04071000341c0e64410000d4044449000d80e0700d502c40401c800c0300441c1c10302d94254005019884010a8901c03100726010400d1a402004032883d65403090107001044000d100b20745410349044014081240c03a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 926964811 1250 926963561 926963579
    0x30309090703060b0c0f060c0306030a030e03101d1002040501170901140c07060507030b011707230d0f0629090d0c0e15100e040e031206090c040b0403081b07 69
    0x45081407001442180d0000711100c014004690ac10340f00507018090b20b002e10354040d80e81d113540c804030645c14040c1d480015920302080c40341c01c10001209180c480c0d0128850070240c00c041d80300980d4000e00b0700401041c000c590f04104006a8210300c0035810300c4560310600b01e1401420504031070001c1d19411800e0252450f8080050403007030303014140c10400c46d2141401601141c80c21000c3c2c50101e91a42031a0340b04c2c0807800e01c066403000f41070030100d006100754412088004401460718032180c40102e1440c18481243c82202502201050104480342c01e0040c0f0311115240c400811007941c0142603071401c6d1214080c155682e03120007610780c1030b41d94002d28141d4070904540c0240300c2548110b10005024000c405607200c10920f000c1c00c803d42c105009901122400500071a81e6002510f6851513602c84100b003005000301d41010741c0b8102c0d1410810f0410844401c041d05440103060240b1080c0b0801e20380804880480303911841540ea0b4801c07070102600042003100814495018084c400a10400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 926966061 1250 926964811 926964823
    0x3030f0212180712230d021f0203060a0302061308330f0f07020a0b010b18030307080a052109010501080f0d0c020f060708030106030e0d0e030309090703060b0c 70
    0x51000010b8602101142a555840d809481015001d001c03166502c8081400170000703082150807084400c01c035a12402e4001c1c42d10381951412001603021041c0c24103481c120f01a0803002100c02a020740c5581805400a11011145d02029208590024050320b110811668900080088005a03080401220950300701c42c00c40c00d003080280203c8100e01510340030044200c038841c0d0b500c01d0005146403107900035810070480c001e02c1042503209200e40c10f0003103840642d280d40200910b20f041d0380c0c0c468086451a440c00c00f210744850080d4030510106000a1900c800c1d0b400e1100c4514105407208003c9403110980380315691801c1c6e0004d95003041c030192020641069040c0c42e10b200c1140e108041e00c03064070b66a50109220fa41c00074040401c000c0051403d1070421144480085c58030341006099200c01341c00340d0003a03010101090b41e031006009114010b121841d0481007506100c4200d5a508001c26180d1245850640c8200f94131800501000d000754044009401c141007020707210311546582c5503440b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 926967311 1250 926966061 926966071
    0x301060e0108040201080a0902060912100606141c062403050105030730021002030703140406050d0b01020a050f070503100e0307030507080c0a030906080a05010303021903030f0212 79
    0x14161840c8200a5000341c10b03403030007143e0603503480c002691081520402054885001ca038031402c104002d02e1103075500321484c00300d0042000901000c940407452001210b9240e07204500b4401c144104684603101d0030117641440200b0040449100c0a502070301004000d0b40d004000703020b8107140c1d078505500d90071040301c002d100c40e92010000744c2d03220f4003095683c0d9454071904818803003407401e601d22000440b0994800a110891800c1201c0190340000e00f4031100c580301500507130003c190803050690000d40c80001c042d01000b150b1074241041030050840c07081090b0820042e880741c48030700059100300000c01200703030400203590320202503490b6527444050910520b44a44207140c4111800c81c020b114081c2c00300400e0000310b240240c9940c0603101604400000d80e00f0182c00c0c840d000780900107000203c2410300c030f6078a0003843d504001c406010160044d00801d8040d24040061000940015100c2001c0e01d00c5007426551509920b17048010b08200c1d10211000750000c50350003000c0400c205a14010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 926968561 1250 926967311 926967317
    0xf08070f060f110a080c0f0c1f11010c2303070509041d0a0b1603020f070f0f0c08010c0305010902030f0a0b131109010201180803280c110f0109053f030106 68
    0x9091f858003041d60711a08901c4540d0300c08080304c0d1142d601004d4605146000d005801c00500c00d20382114514215200921120b0201c0d10b0b004025a488603d03a40c421491180c55450a056080c8518001d2460180082e0180201c0e80c9003c102588900002c40320003242c80e08040720102d42141c42e00072010358043c1d41d540c414050481c8a440741b03e0182c000d4840c00031803080f078182003d0070758554544802c4441801e5036103080b007011f0100440d0040e143c00380a003448400220320a41144801012240141c0c0118202803060040c805c401810300300303564102e40c0702400404ca240807000025060803948000d4030f030135403520b4400d80d62401004060310621009800800121001d00003d0418403d002801008507000f007002400710120b20000c480d9a011252919010490459402341210f4a03001640085603201100e8105114100603000070486400000d000320352040c1e6039565110100b042c180301d00280c080c2e650055405280f86109504020312038040110703201c114686556000313015031000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 926969811 1250 926968561 926968573
    0x17041208180d0e040b01091415090909160e0403080a0b030c130603060e0307030f110c04110d150f1419030f0b0a1b03020c0709150f08070f060f110a080c 67
    0x10542c0121003100072100e0110723914000050b01300420468040c0724421a0f807407002400800380301c1e00d07003078102072140c2e003c80c0003413440d105a00c028004501c415408401900c04600c100000258000ca440760803240c00e050119003e07030305c1d000007401d0240705420301e038016005042c03041d595500b50700034030120ba0180408102d442d41c08010940c8a200f80302c800340200303c114408003102407168502202266207034007034910310701ca210005401d03a071501181c2083d41c1c0300860b400c80c81c12a98410340c18940c8100420492282ca001c09881e43c1c1801c81c42006031808121f10000a1a190161070b0390280480491041c3c06586901d400c1c40c0d94143c401041e11410070b08800145c3e1181244210000c0d0480e00c0c000c0c0011801c0d140302100a54801d80c000a03007030044400c0051020030354007a80040d00c0c00301c00c24142c0303e82017442586401180c0d60103d443d650100b0b50410000002110002c1a80c15924200c103440e081c609050340c6050b0000051203030707842180004428044800041c0004001c40c01c203542c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 926971061 1250 926969811 926969831
    0x30c11011109130603050a080304050111070c0e070c1203020a09031703070906171303110d020105071101060f0605090a1e03120509011707140d0c17041208180d0e04 72
    0x3c1107030360a000040c800c2c0e000c80540000f0881e581c020356030003881240080780c0716401c11809030f1542c0041c00f04485414802001380403640141038425800019460103800741112521685590710a01402d10285079001603142070562040e070402c405150000030700000800f2448031a0072a5000301d80e22800107a0b005c0002c80d40c2441401d4581c1403140d12815291581c40704d80c056149241480320880070701501030f92800c20900e0a011010b42c0303803030a400014a40c9820034002e081e07401034107200000c5900d000414800c10780c003440d0300800d4510b40c0c036102d515403104030003003174100c660783d08284103840a200050401100042805041d02c1c451110607600242d000d0055038540141104c060104a40800d60400000e400081c1c2e940141d40703182c034482000c1020310504159121140c1d1543d230548a466401e132031074100c46852108280e10070300c1c03020703860643c03194480c0f5882510301700308114244000c1001c258603030078001c1c16042c0314401c1e1207210300c5042c40039111410490034103015900380341c0c1d401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 926972311 1250 926971061 926971099
    0x12020601050a0e0f0a020d1a0108010f0515130b0714011406030a0b040222140705031e061516020a27020d140f1b03070f030c11011109 59
    0x408640f000101004180c80d41e0344505007070360f00200346400c5903a0074407103408180c0d80c5000d040091000031004294250340d00e80010704120058014006580300404100441e0702e41c034040d80d055082c50384d121600c0c2c0410810714000d00341c040e031000c49a075201287c4401406441007a542081200c4c40081100101000e40b546008604807805d80d80358110f141560041a134404003141d00500c01000b07400d072007002c46110381800b82c104c09112410b60340e9080345094030032215801500100a82801c60441c03805804110107098041e4040f0b4840c504080420f051303840d1035000034000c1401c504800d803609a107509140d01e04c91804803da2051441250004035404210600d9114800c0c200c0d051000d49c0301019000065407150a0500035950750340b4444030385584105825025030710811b0804100d0400701039001000c0c200c400c070101c82003403c1060005031030700200110305401c0c0d28240402da1030312081d429540c1d024991403203149542084c0f402c650048180c2e0040800110468408504021500d221 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 926973561 1250 926972311 926972329
    0x15050c121c060e06061204020102070306020f0a0905090c0417070905072a030905010f0e0618090f060a1710151a0711220e0c0f030f0c040f0b0603041202060105 70
    0x4c00c1e0081c20400c507079134001181580069002d401070040f21404e51342d90303032007000302e0b444050210201c02001c80c1c049820b0750310541d4800180002c13200d1440d1030510351415007041c80765201c0c041414119508004025100b40428402820010810441da19182d840603000b184c4440c51048034002d58607515414041a8030f021404c00d400d9665a11005c2c00d003801580ca101000b40c4140a10000541140469032004010850b104002814152502e07154081c04400304028200309500591034040208c1c035201c024603203007140c242e94400602400500086401e007219404e03440d030b1407400c0144441c40c0a0030756000400311555a803031285480c1400307800c0c003250300480d90000e0083e509c4019414040c0741c0384805845182d044090b003618001d1145402040f5100c07004001415008407690110601e0040940441d100c0d0940103131020042e201e40c1e080c0c5421510079800e00c52651001c0c81091811907911407000c7c5040540115902e00b06402d00301085862642810014850036001040780d007051955 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 926974811 1250 926973561 926973571
    0x180111031b0c07060f0504052e080c0d020702040b06030a20070b1503010204080616120b09060409030e15043015021611040e03030115050c121c060e 65
    0x1808025007060402c4a151015600020801000380400324640e552780240d0104580381100d08050078940c05540b40d1061a45a00c3c0307018401840d04000c040c0018804464000e400e103400140e5440c0c071031000030014140145400c1c1c00480101c200705940c1d03030340d50110420042d400c980c003580c0403c15450058910680c3e000620a00e550350201d008201825030f18810104000d00244c1026155203640e440c2400460344001c200d4401e003080fa800c2034000a03003c811400542090003895000000300f1402c490160400340903da4610515050611130f035084103165800403c0e5010705001c4810b1007241d5003140c000c810046401c4144200100c68100c4c1200480085070031120074200b10f0749601203528950541304076074540800c50b06050091085107801a1807003042200400301220052000b02c0c0c148180f050b12300c3d4001c00061100c000300e960031003480b841c1890540d0751441d1003030030103080603442d6031644016040815003c00d8025a900388012640310701c03804100c502da84e019101041401619 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 926976061 1250 926974811 926974813
    0x50604060e06190513080a020714040b31150e1503060c07030203040806013203060105270a1b02060615181f0f090f0509180111031b0c 59
    0xb0b4405081949900156804842c070100380d074140c1c1706030b100c45003182d100d8460760f8016003102005004070455900602d807180001d8400300440440b0101040034200211602140c0d440b42204449080c0b1031080d40c0082d0705800d10040c4560a80c40c800194140110b00601072000b01d000005401440c680d44048d4034010028010300094503444111042603115400036000c41c0010000803d89580410006008154401040036290742c203d03410004005500c09400107c4050040304a040d0740002e4000c1c15194200d41c02c1c0c005080381d010070025158039650032640300c04000c00300721880038142d210409552613156815048188000201e8031010f084030b150350f01400020203155052030000151803200c880910820791092800001601d5412102c00560141e4041e258004682c0c1d01081025411940e03050040e817071800d000342c115000c0301c580078880c013030800440010081c0b80341a100c0400c00c070246008010308048800440d60681c41204c40c1840c080c0030024444003000414103c1d51603848e058 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 926977311 1250 926976061 926976091
    0x61709060103081620150c1e0a05100c0e09130b1909120f020c011b0519110411030c070605040302010b060a020105091005040c09020a0203120103050604060e06 70
    0x41d6400f15141c210803260007102403040c80c204002511241c14205a2205200c1561030400503001c0000018015000315610303801800b00d80d090080005482d03040390b030404050100005a039214500e40a50140054401d2065030340142260030180e11000c112440c6580e030744210004c0206224101d98107640400d0418035690001002c00d05800101d03800c1007104a10400030f00259140e04151038400708107488008880d07100040c0b403600076200c1c03a0070300c21500240c01c080d924074001800101c81041c0b11448030a458107081e003000018000c41c400e08585c20b034011150500d80c106035020307101c0741c00b5480c041c030318111181ca54442900152131090140643e01460001a9959500030f0712000c4c004405644d200c10078010903544200151403406402e074000281da1911400f03251600d4100407541d00300c1c41c6444c0c02c1c0710201c2c01d440c2e18401590305c031544c00750781d41c40c0c0391004a14510902c80d4844085d090b90001104020b00418400d003c1c038062030060004054003c58291908416030b002d01400c2194 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 926978417 1106 926977311 926977313
    0x1101020f010e0d08040812090d020c031207030e040906020d1a0909030a050a140301121a0f011e0306020f0c06010e0103020312030c071b061709060103 66
    0x1480244880040c610500d51541410f0030726000b04040030002a003031040d081c0407241001c40d16102c000365890002c10342602d07103843d089000018005c1024142c000c0c50009500c0c00c8a03003e81e0300341490f00300c981c1d5040d00d4819184000f281c01c1501c5e0301413000440c1c441c1c07020304108403007410041294130105040c0e203850300e03041c08d00c1441108031800340003072a400001035a0750380842e410302e0f80d0b40703c80b8440159450403840c0071980035a000040003145079103014000c0c5102c1842968540301105d032036800515400d000b25400d8144000540c0100250200c02e1856041c1003602c000000c141510794440d8010b0343c2c8000c401310402000050f51102e000002c00c02d05004105079034002005504690001791104245da150300305075000800461010303076080080301d06503548950b040282a140201107a0f04050501c1580d000c503001d002c1c1d190f150b00b900040244110107501c0906456821 = true := by decide +kernel

theorem cover : BRFrame.Cov 926798561 926978417 := by
  have h0 := BRFrame.cov_init 926798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 926798561 ≤ n) (h2 : n < 926978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
