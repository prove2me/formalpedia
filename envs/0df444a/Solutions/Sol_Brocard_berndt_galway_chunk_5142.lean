-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:53:16.330129+00:00
-- url     : https://prove2.me/submissions/9ff7e1bb-b5cb-47d9-9f3c-c0870c1a4a86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 924640287 ≤ n < 924820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 924641537 1250 924640287 924640289
    0x605041119020609060c0f0d0513050c0f010c020d081306051201050d030509040507110d0e090f071713060203191508031c090c06022512031d04020a0f0801 68
    0x1501c02083c962500048041e12400040d0103914a000f0200d40194801e014038150b919000346a1800c20291500c0c0078450320449014005494130f000700300c0840d01340d042202d4151217201041e100e40c1c508400645c03e018201391044015201d1520a10070200c2000390035029500030001130740d500780c545469402e211658201a800380303100f40b45011448000907001010b035a403048080300e000078207a860140c251822100c2100c44516802100c2000840b9904480e02c4000c2c08000c0d1000006c0e035079038610f800c0f0400710a40341c09000c200b50300c0068007030b851104501e960000c0516180c08066509556460036a0801e40f0902105900e00e10f114480384800c0c07180c00810307200107484010b0b20345044603040e142d2003050180410001c0004003600327981d0303081c0c100c5c091940d80b00b60702c08103055540ea0b000351a00c032903108843c41007004075500d1105144648031041604e490881903203913a55682d4003503900f550504541304200800c0f080d030b0021656988003400030080c558492a00caa801c001d00207201c07001c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 924642787 1250 924641537 924641587
    0x16030b030a0209070c210207081e06011206091509150c120b03010b150c070608070f08060315090c0f010c33020d0209010e270a06050411 60
    0x31081c07551015070349036061242c11080e182400c40c0d545906040c17455403440128509001510228100d00703003280d0001e802005c0f0342884080d80c07c4982c500c825541040709a441200c0d1607848080140005c5120481d8055080d10501c07001070345241d140c1c0d801039402429410384c1c50155440180d1002d00500c03240c51000018601b400704003034036100700080c0241d905170f010400f80a60b551003401c1c280c0c0302580700c190b18801c010502da815032403004ea02002a0700c108000b0f00030380981a03000885900900f005e0340150a00c2d29101032040390110101c03a0508020100c41e07142c490280d07613020940f25070210a000364041c1028201240000c020301c800d1103059540d035810041020710f09004141c00143c1400d030504409401004404d880846120708078002c2d0000134031701c0c070024500c107801ca10f0364028161004280c0718013004030041800c001c0c03203000115550441440003000ca2040c40c455180345940520001b0000a116440d4804101110815140303440b03001000914464420b2145e6100b0100340380c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 924644037 1250 924642787 924642793
    0x51303030e10030209030a17271f0906111e0102030610090f030b100b0d0606090501020c18040f02030d08010e0f060907140d02040e0103020f06040b16030e1018060f21020d0516030b03 80
    0x42c011100030200d03a20341c032908040012203150580b164009000218985100c51b0115035403b141e841004d000394400d03581d20b4491007140d61411070180c041d1000504a644000c404200189180c550700001c003c018400301280d01d80400c007040c4400300901070143c1011b402000a8568108500070382040c40342d421a034103561100782e02c0f000c95a1802c0c01e509001702000402210784d140c41c0f070911295034560364001d525005201c04140d40e6544280c9040c100e4021058000007502c0b1509101e00000b07007500c0642d000300c5030341d0005002c50b010709a200c1d5044240700d802481c00140c450b8900803070b0402d0b000300c413000320400010000d51822400b07a116000d0100d0f04280b8103898002e00d000c2e2481182d05001c400303480003005400749400b8444149a618029101c1c4620513405400109166036917501c2440104200c0c0e00420200e200e029117098001e0b1581f6a0301540c4d02c001d03000381d422a000c461200140d030302044101c100172200e010f41d038002e80c0451100410300c183d5031405000d0302c0840e030049000c2d80c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 924645287 1250 924644037 924644089
    0x20f0c100c05010605040204031505340e0a0f0303021b0307050d0503040f0b190c050705010e120d030c0206160f0f051303030e10030209030a1727 64
    0x6580d58140650110a6003061030301141c40749051805020f0541c011584144041030000c14491071802d40800e04946140c204070560340e00c891000c80b00c0706031102c9020074588062544500076120482c4000b40214202181c0c02142c501c0000c02e4900680c0003002c415219800c204101501005007004500c5030141d4050310702c503050b01282d46d9504a201d024421200d0403074800500034103104882c05404805194401e10342ca6910003141903200240c103549440b16441c0c00c0d0000c070f1060600a240d5a804006002294a04801140d0056441c1d000700d80c4090000c02c3d03a04040d0007000108080480b689000c02c103a42d07800f60184c00d19000030b043d07850b40820700042030b10203030740824000b80135001c5040540c001c03107034000200e91500070b2842d0329180d2a070950b008024950482244000c40d1002ca0f021030701c055001004405030700034034000d103801d5800407c00400090520103926800040380c0d0309241000041c1c540036415000010085105051500c040303081410412900201c804041254201c15 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 924646537 1250 924645287 924645289
    0xb0a09020a091413091e0507030c270b03010b1c0219080d0807030204030813030501050c0c030d27030806030709050405150c3f0601090b0313020a0e040201020f0c 71
    0x1080f10b506490b8a20b41d4590f520717410002c4210513203503091040440d0348201d07106460680d943d07a10314041607846461440000540c01591000d105481072485481116942410113501c042e06900a4290381552150721b5050380d62580b111024804150701c2d0950303c40c03400782c014402c0485600c01c90308820b1600303c2d414416a030300014120300010a9280c502039035075907058220000d02803030b00010071121000480c2c451907510075045405480c02200204842c3c0c95401007901c861049280b58202d41d041403080c006c4031411a4407086c800d955020000c0d01d2540d172032240252603404c1c09012004200403a040c40080c2c1020030141d4050710001e03c0400082c145a101d4030380c0c41d00a240606041120000010a001e0019065418000304410080618a09840151800358190309128101c00440c0c800c11130b2038150304001401640183c6034554990305041440030254000dc184103502020f005100f8010386a201c0744000510020006c3c0c212418540300084c01d04150020206059110100d21300b40c17 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 924647787 1250 924646537 924646549
    0x1213030c0803090c13022214010503101d0406050106080f0f1302040c05090111120306010c030306030c0e060906030703050c010f020f010203010806160813080c010b0a09020a0914 78
    0xc00350440206512640c1e0305626914110000d480160020b04403200c01c80c441c29a0740103048500c1c01d8000b2101681d9250501c099094104d108001d10408984403801681d40540001d5801244400d41134034520348501c9100003018030240001c8007902000304000511001348a054050501d030715100e0802c0c1000c054000e9203400150a1010003196640400d10422200440200fa00d40c0540700b880943e0241c0c10150a40c0c00004486020030002480082e40c60000301c1c220322901980d85059040d0b07100d81004440d034001c0c809040341410340d05d041c0440400e8600c203120300204a040285170f41031400c2014403a8191340035061a010354400c6409000003100480e448141c2102883c0c901c02500e034484c4100d28003110564500010b5100000110300c10740045a0140b1030740941005c81c400d908000400c4030078410440301c0c003500000d0181c054001940d42d030000d00780c2c04910030001c1a0302d40c00000040e6a000650b0005c1c2c000e80c3e0000301c0c4044075030400c3c04100285410f904000d90070f602c034400b2034a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 924649037 1250 924647787 924647807
    0x70b07020a03120e090708010f0b030402100e24070606091a0f0303120f090d05030114040b04020706020c0a0213020a080f090a0b10030213060b070201140d020708121303 74
    0x110f14101d201c2691914860b103514034440b0700091014205051005002c0d001c10380a02079040c0c0300800c6440465404420b00c21680195400383c4184100d44c13480300110b031140c8821f00700d541d01c500d156000d682c07454070742c00751103031118001d518a0369140d8051400c0700440d0b245500c810891414010030046032028443d0380c2c0045407099948002003460500003030b05600c07580820b02e0010005205001030841780c5160544640d010f80200c80191240c0341051b605800300b40704030750030010801c0e201d03025401c1c10f410254030200007910160804905c0c1e96503a046e42c010031040303040c07035000e52400320540c80c20000c0100e01110800d000c51509500d090028282e041c002c2c0f42143c003170b5004c030114031450f0040145024440e08052000540e00b012035690040010310300c81688107110180a080c40003925209480488004007449403420000b50b0055803110f8940f203242648078803e02803141008681d0004103401c621030141141e03501c41e0a01e0081001101610540c500f007000c3c0c1c4108000794014503119 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 924650287 1250 924649037 924649043
    0xd0b0f0d12091a0301080d0311160203070909030203030708061c08030c0d02191e1d0315161d06270303072301050919170408030408070b07020a03 64
    0x3040040c1c1e1840c040d118840c50b80d011028004100c0f110034038502404000d141601e08810a554200c42c2010044056030b5202c87e1180c580d0b8400c100890101c0c04c0c1c0e007030502c00d01c0e1000d0140c0c0c501503551020340c011a800c0800c164050703000041007004450744482e100c0d0f0300c428200c5601009508400702c241504900705d100030300c0304600202062407106141c0079507e0848911200303644d607031200000180d00744c03090400123011400602e10b0030380c0b030350444102d402c00642680e580000c0ca01016103102254203e4240d0700e405000e050329035003035200110241407241c64000041c410b88895220010b00130841c1d03c0d05402d0341d0072b540c5648400e656a6078101c030043e50300c01c1c41d4500c00104803c944807540c0191851581c0c148000a6950704020042120702900344003011540b410104124030182620b00071100d80302107400003000c0040100130b0002d02103969000e01800201542d20062490340350780603422000d115800071a0801007850100700a10140c01ea1001304c0342008600c2e404214032004500000b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 924651537 1250 924650287 924650303
    0x70318200d050304230303210a090515150a081608070311012d080604060b031905070c200316060801060f0c1a04050606060408030d02090d02060f0d0b0f0d 68
    0x4880c80d2190241c020035540001b01a039503100d0000000c00781707109002201091400d0464001190705003180700c0c0350304264002000c2c245824103801d402d00d4540b4001c0003c0d002d814401c408040ca07071211043d241c045d0207140024161902c00075040d4050340040e500c81520f95100120500014104c04520b0380b4481080c00c1a00c1911040e1403000d4400c05030781e14541c039124600456000c840c0e400786045015400a1710204102a2680716415035440304403004000203031107141c4604149021386c071841e4080d1940c41c20080c40a40c503034030755001442100d1114125003040d24104004e00d014040041c8004d02440200222460044064245481407207000c050049003610a95810f010f00c00c01104036612500281085040704241d000502e0243c03070540f2039204580004400c0d003803038000c0314181d60b400e0b4001d60405400c0345420010351710001c0704c00d030403541b900414401071721340d20080d150314080ca490064803010700751261011104201c141c035109a2800d0408d4200f61284594915029000a00c2d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 924652787 1250 924651537 924651569
    0x509090f15090c130c03110901020c1516051005100303080c030406020715150e010612111b0307050610030803010e091f020d0b060a1403070318200d050304 68
    0x31480c1010350040c031a603001184c012100001401c01d03445150801020788081060500c034100078140750140c40c40e003501503488582e8a021920740005000102042502000d1030b03e44070000020010041c0c103c1240c203548104015041304209001d6540d0043c8103010301200c4518540340203004010251040710314040020100c2c00b40300e002e07012100c040c1c0d001448000c1e050f0350003800e00700034090005109840b000410000c9180c154a101850485420790b40741c0c400c0c0031201510400a002a14008105440401000c1000702c0914100050740c0a140007841d240c4039142003141c20800002c2c0403c644201c011001c0c0b0001d0289020360341560030000e00d2560940d158615980b418600c68626042d040510914081a2540d60014000c3c000d91400034400700a0080c00d00c003041c0110b139483d40100f40704a1007201c48a40e2100034692060710303441c0103c1c2d8840f0b9500341da06800c3d01e1403000e079150f03036101d4103440c1c850fa1140301d880204a0107884010f1940d203203440e01e54032801240120344260300000301c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 924654037 1250 924652787 924652801
    0x515060d26031e07020601030b0a0b061b3406112e0c0e0307090c05160309030c0503030c0d120e030c100507050a05040e041e0605010509090f15 63
    0x80141d18000c1e00300c0c41c0325502d0501d00420100c101c40700c60501042c804003400200c510340b0200b400b41c1246e070b10a510524a440d540300302400780c81f81c01100340c3c11607002c0c044a0050851422044a47c44a00010b0900307030f003449c90b0b0b41414801c41c40320001411001088001000b83c40d40f614412075070035103000300f00c4000d0580d140307061039200c0500300720140701c02d0354014458120a5210070b02c544080e03410040015003010540325100703050001c980c50f070000741c410405281660401c112041d014608545001c45030308490390080002c0c0300a070000360194505100304100c0d540a00041c290440040d82005420f4a10560300c4590165030000c000e03287c2200c0030508855041090340306983c01c00e07603441e00b5114180b60350b10b1100c5204545e44500b4000410075050041013281d20007620303035880038074060604211035003030080608115802035029401111251445d0303107007007c2da8803511002c52694904070800018102c0982946803a0300f22800034a203a0a0020b007284005c1c4002c8607070740b40d036940c4003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 924655287 1250 924654037 924654083
    0x20d090803190311030a060e06041a0607020102070b03070509030d1e0e03010b03030408060a05070906020a030f09210507060806010c110a1505190f080c1303050f07030515060d 77
    0xe407000c500139401105025011300281c1110b010b40e00d505034083c1d1641e5804041005442c502c04021021172141d240a4489041020060203598018011103d5155039491104150340c000c80790040000c0700410f01030303101d203018000b083c0041454600501010480d03c60b600d1007040d651362500500c2040483e010041e00c00b90810070100200806480d1110741d6401d469880313401c115a40d03880c0c2407510b80003d14940c01035240506580850b4000e0102030b1a5503029101da01d07810020a0a00c19205c100103580080040d08a034800b40c1c504c03443c0e80e07091044c50450b1070b11a15802c60414808020b08000e41668061100d170320603900000030ba2080448070003c19840d00d041d4101409600c0185c2c03080f4040d91b0003400520140c4090442a944950707102c03000c4031026050300d8840d00007001c2401246072500308001805180c00d004101c0c00b92540d40b940d5035031a0007a050000b48803500480810030510030305210031401521a00c1401985291a00002c1d8682a2041c40104501000a994240b40000c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 924656537 1250 924655287 924655301
    0x105010503040c150e0f090403090b0703031401060f17060102060a020d09150b090907060e2806030f2009060708040e01030b190e0607030b130203010b0a020d0908031903 74
    0x1382041131120082080d00400113074004550314041c12030000481c4450615800f00391140750140d48907641385040c07240c85030071980b00c0d03103081d410952144d518114404480035918020700e80c40c0c4030781e44004600e80e000744c020131610032208250301c022070802c022a600882c070190701c00312406e00103940380c0013000d05000400540c20050444074034441145160803240d801400c0780c05c0112010300c0c2650b00c050724503959400e02e00591000442004802449003000e616014010741904031446112000f00c88407132040010f0350041c80003036150031200a40c1d070203c5c801c148036856240304100144600d89010034040c841d030600f4034000c060014414041c0400760081d00c02810203034000c4080c07543c0d80c4c02c14982008058940006451080603034025440c0c6900c83d405c500c00101c001381078155117038203050b030040440498850b000b4074032500400ba0b4004510095010f4401c00a80f2a280d0400c258020702c0c10402c2c40022003404505a010f1049881c00419203509c8c1941506802c850010058110068007413 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 924657787 1250 924656537 924656549
    0x14030705041d0702070f1d0a14040609020108070e0307030807242003150d0503250b07020a0506010b0901030f02040b0706050a0b150d1113060e03150105010503040c 72
    0x901c9800300d152601040009005030f10302c2c0d084900040d2512090500c107060352180040fa40c14059416074180101c803440c3e507116082a4001900388510403ca034841c1d030b800c58003290215500c460300421507030080491030b0800101d00e00801030918140101e035546a2501001d1300003e004101041004001440000311480c40c00003615818000c54800029060750362200d580b40010016641002e002d20050764411000390400300c1c00e850140040c007060350b45400065403540000c0182d1054040c49c0540700c2e484000074050701c648940d440c1000000c10b180608600210f40089514001040b0000380060645c2c03800d602c510b685654940040e0020001407070310030071032030020400040d00d400e11005480a01d000b0300d0144260780e0f60003902011151620754165100e00001d0b42d02c41410107000141c5040312001a0000311400c000741a0391683d0018130f2074140480107240140b0401d03500900341d01056a06030000c080b070400310302030385020000502507107042003008400202032041980801005000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 924659037 1250 924657787 924657809
    0x403031410300c08030c0607031b031d011a130b090708070c050703200d03020712030512090607140c0705010c111201020c07120b0f04020a0906060917010902011403070504 75
    0x2030b650131120703181e03080301d0b080807207c0c01010000381040780a40501c1c3d4210100f1f091021121480c1d102c140e009003400b02c100722a543d480840c101c0b01150034030400c0380b501038400429000000d0041080f11a00c0012004e500140c208a031300c103556158059401c2c1c10910078245525207a0b11130781c0c212031220754400040c11600c1503120010900002642120700d118418801740080c5400d241445040d41c00b100008006030b1103180308120565000a103144464070a107465460300003442540b81031103034141e60707800035a0000c80c00d0010300c40d044103201111000c0d98082c0c1341071082907035840ba10740015216150600c2038890f03c60040104513500380642003002442c280c6488065014a4000c1d00540350200740752141a01c0425299000019120308a902100b1034142d41c0e99030006941840d03000d00200d0700800013110101d020440350240001809180c0c4e00c01c03800724a001360044490382c1d581801c91342a4507182600300540d0b0703c040b00640344c0500300b005903641c3e103d2440403a444d02c1a0b5010711140c0f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 924660287 1250 924659037 924659039
    0xe0d0623010e060109091401170f03190e031f05060112020d0507090b09030624100305040209010b0f03040b040510020a08101512050601170403031410300c 68
    0x9404000b1440c0643c100b80d0703c00491940b81c0902408032101400c03a2141d0343c0c010001001103c1000200740104c4002800b40c50703405441e802484d01d1a0071081803407403000c80004403c00c6190f44000b001c1e1180c2000c070014010003600f050300e10070381c4008003e28940755454400003105a40200d81190781044105021541d800c1000100340051505031020740c001511214000b40c0300c00310b50309a403600d80e00103000d8186526107000317170070341130540e14980e0462103c800c056003010ba88400511074160100d8502051034134040c8100b040c048070582001e507100100344181c4564042c0074003600e911075848070a8210036103c50800328503080d60030840e00005c074000904240c0540e80100304074062313840c07500c07120501511002c8041907022401510304c001042940045aa06095042907401c0300041c14041c424a1076135003159000076045074103038042900c0d186480102001140f080b0f9000711200000301e101402d001e00019591410321000e011842005041001d50892401d52000503510900c0c42480b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 924661537 1250 924660287 924660299
    0x151e0412050f01020a020d2703030903031e1b061103090a0201090803031312120507050a020d0c0c05041a0d060603140f0c2106190c0e0d062301 63
    0x1a4069241101e8a00a005405003420014001c0e281e120801d17030003600702c440700e0303c20859000781501c1120708440311200340c50050354980c80318030000d98082d58804140741c3c00d50601070139440402c0711070500d80c101043e00e1001150b00100c0f4041c00790342140d81607200714182c1000000303410307502c226032508100001800042600042c3c2030b90302c54400c3e00d5078034605941e111020340701e000449648500301902c05501002500180d0000452900390400303a402d96001c00f400011030380c00715000004500b00042d400e840580405c0302ca4100d940340c3c98282000e490365a03400e9440c0c3e0440c49414001d0b83c5600034581c0c10a040c2107904ca4100000d805d10000000d81c2c01d011010380400e10040d40d0407078410b188002580340200e900e0f04030b200c1d640000c0240104203010300641000542c489aa8103c6107440c0d080218001d000f0b5a006a44400401020700d1a040768082203034402032101051008504070303070113940c95030410b0191701c98114500289248a208410f0360503587e412052109101a100105032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 924662787 1250 924661537 924661559
    0x315030105092107021302131d10080c03100f02280e1c0b0712020a090510050c10021e12100e071d010e101e0806151e04 53
    0xa05061942d4070070f04844469410007452080d11006500090114680f02074094a0340080c414540241c24005503945c1d59280c020180c0c0044c201050340002900500ca424003165110101426040b0007500c200210000081d40d14543c0d04201c56002da141c090141c01c01c001c503070650310800140401c03690a0001114100701200014210201240e90312104140c6400e01228080d9001060007035103100780145e407100903480100810030400c00401c4c2900c420f440c0218005001e2440c016150040c5080c201400c1001982100804d4400c2000901084500c083c0002d41017488420019005a6940103500c461981ca944c0f0780b8140300c180300c001601c00c1002040c0040c41c0c452803248005010780da4a8207840301d5a03902c1a41c0d03403000101610461100d02e140c2d40301c1851042014142021560244030104455448100d11b00740800d043e052010402420b086c0b500c0194841842c11071028605040010b69101e04111800c05160700460080d045a610340f0000c005088200c1c80a40c645030b41c0e02110302 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 924664037 1250 924662787 924662803
    0x605061308120309031204050118150b030c0120070305030a21020708071101200a031b02241e040302040b0405071b0f0213090b0106020a0f0206031503010509 69
    0x1c0c10301c161100d1100d02d040500680f0f00886180300a0351921040d1900e00402c5000a0420b540b603550710070034030101c901041151006640300d50300001c58800003045207130845021081a0380250800000c0d000d5503a032100108200a00207880c244154007131481080c03a000c07050304020818440000e0341c10303105801c120405c1d40e0310034041a03080c0c00080903c0b540140d00444c403000303010842c1406204001070440f0174100c1c01c0b0301d0614001c00210000710180d0309050b03205a42d4a03140d004522072005050340520450b510301c0d071498032820401420381c0411011204042652403904c494034880410200d0745c000c031101402148060081c009910300b921410345d0151000301c0c881c0e86401c0840000b41000e0282d503200b840561210409500c0352050b0f10007172000500700720b0f40081c0d1103c4442c0140d035002c0323081a44107041e00d0006140d006038030380006a0003040c0c01ca8810f641c40450010009151050303541c4a4590541d45c0390b44075254801039403602e50304682070507032650a101c2040640e1400084c004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 924665287 1250 924664037 924664049
    0x3060a050f16091a1309061a070b070f05191e08040506070302031503010e150606040807060f0e10021f06050a140a1203090e0a0b030312090106050613 66
    0x5505072078058240700e250301d0b425064400b0440700d4004000d40300c1d00540d01ca901a1600d60418a4910010045600716100d500203020041c0da504040c0400c6102101c03558006015203000f620b40289030312585003415006103d0020001d240a9a06800b41301e80d0648010068600640d1004601c0312806003951411208803010503000382414103002e0310415000740203581090140c07600d922103110840107907100401402640c01c808144505540382481a943c3c0460054082e200c40307801e14440e41048800034101c1e03807040c0d4042c0000d2203100c1d030220b280e900701da0150400500100c1c9400085c2c0362000c92552055000e1030f2040b0300000c00340c010891100c0180ca0a07000c00d008041188500101c950601456411000e04801030000244005501071290001800034a1195480c1000d10110b40c084008400140c21031404002e61080f0303c031080d4212400d110140803046803800420f58071301600060409501e401800718442001c294406000b901e005084c1d07075500c296020300900c850132180304030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 924666537 1250 924665287 924665311
    0x30504090e0703150501060e1c0f0212070609090e0c030d0806180901051f1427010f0f080106450e06010909050d050703030f06090608150408040b0c07030203060a05 72
    0x3010708c0e85445542d01c005a044a10b42c02e94162040d1102d901d102100f00040360081411510003920346c1041142900401050742d41c00346150820304402d09441401161a2850344200c00c2001c0c0c0b44e80c0419184203004991900007042d030ba0f1030000a07048070080311220300f0040e4500601800e02d10642107544248800100c680110070204451a21410544905150303441240d0440e010340ca0720f500d4002c511444030605130807249080b01101240b480a038840c244841c4041c80806c0400d0781d0344002340003411004020450280303000e07010213480e00200d40b0503000f40c80c8000380c0d10314018102440f00d00408994221450f507901140100018880504081c41c10311840d0000180c001c1240610742c0c6007540701c0e0282c110170310844802e1300e81c3e4000b560111300b89904d030355a61018200b10710580c03004090b00d800110391140381c10803070343c01e0141000340c8242040001d810007011442d5842101c049a100e294807071f650b41d801445850805c0c45e5504000d615000d080240010b504007500080d002c0c4400b0180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 924667787 1250 924666537 924666557
    0x305180109030c0b0f0702130c08011a030f060117070906110616050a05071e03080106111b1212090a0509090a0b060117041a060d030504090e070315050106 68
    0x15141d4004910008000c04014101846030801d420041c20240080f0110706051598640c0011942d03501c40c00d03a06816590340c021180100c0d402400c040c01030480d9180110840a0b4074100d00c41c0c3c0c480105000b204048000c003248180e480765002c00369148046d400c00c40581403241c002084035010703100704000294a8030542c3e01d03646002c52018004c80400300241070400502c101510582c00c5003202800b8003000707006840102d20420309450002410401d04100003140d40342c003900700903042e00003000300001c0d984005a422000580c0510345c004500b100204860141f000034003101e00306040c80c15600031320001109403541c030f0340500350310034080b2a0f40950544038002c4c0000c550003120604515404145102c0121300b0011a0b40c0d04288103140c420040003500501c0303c02d031002641c046581c04003550188010f44815134002c2d0300301800f00c0704442020b0580e00d0040860185001c0d50540c59540c6180308420002044508001c0d07602110b20300d59001c00a51140043c0008d1140402250302151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 924669037 1250 924667787 924667789
    0xc022b0b06090702030c0703020f040e0a03030e150f040f081e0c0705060903070b0c1006030807030e0102010612021207080115140f0616060b150c0106080f0a0b0c16030518 75
    0x7003514101d1b0001001000c0107072554003001600e12480c4005a002580c0d0704504001043c02d125241005010f03844c08208030020045040ca0b03da1500c140304100c00b2114148641c0d0700d588140b160b0003035000801d60303135201254106042c8610030009003a244c0305401a0054030b40c030124000d410182e4039001a0341000755a54140301c0203105140c0b050342c3c107400040b400e1110b0300c1c032140074203a51080001104c00c54903083d1b113980e0898026401c01d865004010494004155000343c0003059404d0a02c024060300f880e212130311124000f0610000d10580a00c0010041d44004020b4031000b020440b00034012100a170810f2107110195008410004501e1031400c0050b0510717400d006034601d0060300c518a403031012403a004103500b210200300c80c91610f401c100b0605a80e0681c0044503020101141a515524107000c6402c4a01300c1d803086840e0380010b0708200080d1004241c4c4590a0b03041400c100c2c0ca5594201005446c0c030521002081860148160b00300381503119004e4106500b40d14038010071480d41d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 924670287 1250 924669037 924669043
    0x12030207091103010e0405010b0d1a0a140a181209150806090406380a08150c090312030109020748051e0f100c022b0b06090702 56
    0x4902d4240c0038000c00c01009103040c2c5800076079015000d140002550300a420000b02400e02c01d40f026110345c0c2c6c1c2d2141d8990160450418145c1003001d9181c1044049030380c42d0035981c1160b0060080e480c09a450245481210494042c2d0020315070001c140d42c0c1034608944041c0262031180105822006d0200b40103e189004404860051600619028441d0b0b9543d56280c094150800e0002003140d02c41010502030075410100c4145003441c0c14204c088043e42c070140454086145e0104216a1000c1500070b0320b550381088a540000764422096503c1c51990042842c000c202100e42c1c0040c40000000a4140c4560b809400482d104550041d42d500b400001a41c011000e0720350211800309141a1042c80c139000400301000c1a1900213080c0307010b0740c40c800613200c0804800321145808060002007610310b4a0303205100e24490448030000503086889008000030000c81009000c0c002c10640320800500c462088031482171080c811000182242c03030300c24129142a640d1038010121400480c20450000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 924671537 1250 924670287 924670301
    0x10b01021501031b0e10030201030c1b140a020d03030209040501090c0816030605030304080a06060812181f0c1103030c120d06080a0b0915100302040c030b03071203020709 75
    0x480c01d142040d90030b5803240244000c0c10002548034400c4008005000017111402c20321540c0804290303d00c0d00d00d580009019240f40307102000400c05808269600c00d0180e0740010541d9410007600340501121030f01e054a0a010220007940c400d03046080c8404140c0e05400a01085009640502c1142d90b101c0c03901e400da036510b48240000c1000d0800155445010070449106400c9a02c5c0c04164560b0f14000300c0e003590b0240d00120040d8014a10300350610000740244001441280300a202030001c110388108240601811500380200500c00b140d4295542c112007a140100720414160b40c40c04180068102c02c8140380c01c1b01c02c58030091140c00c0c00d19011040d1000e01400102405048800e6081c454180d48810240110690340300c0300866182e02c200b103040180b0b8441c081585c5d0b1401c0009049142482e10062508071103d01c1040011100000c6103032000c480d07044d130f0042001c45600f40150060017011404682510902d0000948002c500c0ca40240f00c40c02034095494154a580000b4195201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 924672787 1250 924671537 924671563
    0x19062003011401021011130b0408032704230618060d020120010509071e060c0501090f0c15020604110d031101020c0309090c16020103020d06030c1502010b0102 70
    0x10900040010558a00ba001e040110500c190f0f2000d20951000008490020f501c070440c0490225160003c028a83d40c2c03140035092005074241881d00d4014103a0b81c0384607a0007104003007640700300d4240c094901d42218455155004205008080f80c6006003c00c40768011030724030015200001042c501c2c24200e0880e405000c4142c0c09441d04c0d6200410f101107540030010480c10002c200265000c030100a81e03401c95083c080b44008100ca0030550b09070b03031504c41a070b004030104002c1408030040081404a00703100b281c0150070009003025440c00c09500400d20240082c19a0f02e03030b02c4070203003040f400002c0e4100351080080e0082c00c020b42130004983e1081300312402055483d0344502c1c078045240c41d1032100c0441d072107032130f08407082c6600c8034800b400da130817080500080d6840820701e001c0d540380054140e940150344111140c18580510202078036803030000c4001c0d051513400200c035028104140c00c804060341c0c011000707101d003a5540140c3e0500322244034415005528105000105600c0440c0800c40702070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 924674037 1250 924672787 924672851
    0x3021216021804121b0503040b070c151205040c08010207140610180b06041a1218101e091506170d140d050103050a420b031906 56
    0x203131310b0001d541c03200303c400000484690405500c4002142040100003401c00b038201c89480d003600345880740404416400124860040140f000c9074a43c1c0f0480b162a2108140310101c1d139030b1a24102a0b0401c1d0703041d08148455400020034105103c1340c41c0b05240101025800c8950395510701c050805120b410f07002e80c80ba080254200c1d110005032a4110b2480d55000074500b0386025600c0c0541340011350b14030144100e00c0404692078860108640940b54850588030705a020000d00d1440ca5803158601503403890324541e188000c940305a07040c041c403000d2401214042107030346600e092403020303040507203126607146041c400003058200307503d8405221035095500900300219100e0b000e5915441c00c500082c0b080c001840100c070301c0882c901410303000790301038000b506070004142030040b00c40e8981842d80700e0f18035100c0c03c0c6104501c0c3d0304100382580d15554601c6d8800c1c200035141100901941d08585c0d84c140700310040110320614811b489d80c00c080c441c1d101000f07688020302408030b003100c00d188419150a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 924675287 1250 924674037 924674063
    0x60f0105071505010e1b070f14010b0910080f010b0d170906030a090303050a0b09010920030405151806062110020405010f0e0307060c03021216021804 66
    0x250040d80909109840389050240b00c0850b444210700700ca20136071000307100320800c07005e001e079010003401441c4910a403194014546055911941e00542e40c0840080c5615500c07d100f90b0181401c0d8071007082010001c020240311300380704030a0501c8205a0013100101d01a4107081655004144201c00c00780d24068204030300d010b150b071220184003120741d000504010301000000e85c1592144025486203010000004080410b0304004048501c014803103080a850001224010394801c1d03511411a2500a00851507942400311946045079030140c0c206456408070612040190100720452030b400d00980c0d001659543c1e2014001d0311048118908803a00a00d002c214241440307403040c4691202e0340e10b8107100c1034a01486910300545001d250070b100360b01150600156078480e411303104000035450700106500b0b6400019445844504c25031003446001902c0a04040c020f0056001e150000c04003a51501a03c40420307002c8030307208201702c4c4581400008a82c802d000115801e0080d03411500c84000a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 924676537 1250 924675287 924675289
    0xb060f030c030c041104090e1501050402070309090b01030605030a05070e0702070e0c091f02010c091e0e1806010906051003020c060718120302150a05091f0b12061905060f 75
    0x9051605c0c64103c1541c0800010941e1401c078060101614170440082900300f201a208000d4024103070000743c0300350700410034440403a90240450041d02c00b030f07400024007654030b1001640100380c40c1c2c1c070454041c040c60006006100021449608880704803c0c201c80580c0d40030340407616206c1034008c0b049111701a10206a611851101800000e507010b04406082901c900e035011760342d0a080441c6006030f45550040c9030440d44046104000c1060b2400c2d11010134a04240c3c1907416101c3c05411210080500000d030001074078841072082c0303520101600c0b2a540c440200c00040c0110f03026660180c038459600010307807132103072089591045140c40a01029111018100c1c2c016540c1c0b00b48480c000c450b007401003000d03c0c02d101c0b590310325231184d0000c00b658440c400140d00225001007122400314607010030810505408034959200d41c0d610010500c0629240b81d100004010944000d90030074424120022009800900c181c01f0354048030f040071702c00c03840d207401c101903d00c00c0311004e0b0001e81351180d102e05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 924677787 1250 924676537 924676541
    0x3060f0e0402100912380702010606090f050609180f0106110a03120c0c0804080120040e060d03050d183c081c1b03060e040209090f06040b060f030c030c04 68
    0x10380d140c0086c8240c40c100c1400d445982d84e1603844a601050102c00091040807074092180b82e0040c134103410614009843c100603031002c005984103050141c4000a01c00d000c0b6610784a00d070144112000c0100c00500700445902e820314804d00648001c64010f07451041032203400140400115450754480102000603e2080c002d45403180000080c0072143e0350001c00540703814080c001524415000003007100003094000041070a100480d171510004210511003109a003c0050b071000045e20014407003080d900d02155103214011904140505d810404505034134090300d603414040c051079a4858980c04004d554100090007a0480018542e0500c03161210304251003407480607010381c0c0301d1401d0000d088080380b40c00b000300460b251103583d10801d20000d10601c010b1040340701706519003000000d04180480706030407805080640305504240010b031165400300b0415043c802032205070fa819050618103c85a80001c2d503440380315030306c1c00fa103036440c07810005400e00301d00e80c0043c010300c6a00a288207101c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 924679037 1250 924677787 924677813
    0x922020f1201050405011a0a0f1a131206050a020c0c0f0609061209120408070e060607150b1f081305011404050c010206010b0f091003060f0e0402100912 67
    0x340010994280e900744035028410207204a028070008a600181c7c2e803840300031000f4079090140f02d400c000409004000e006000c0c0c03801c0c1c030071400c2c203c0c803220b00e09440c89429010305031040c1d1031544120408a00d80d2510450741d43c0da01c0c070941c0b0900c441e0f2186060f05099000e101605001c43d481404121010320300074203e4000300c07601a100b9458101018003051940e4420020326114002c2034050154206041004802a5010038a054200b41c10074501d9030700c0d13143d075102c4d80b5620129074001c640c803607803000126a5216800150303070112120401e03c0802030b1100c0e00d650b5105d003000c08000c01010001c0c0b5045c0c841d092050740c0d404501eaa44005076650b2801001d4180c4a965841c2c40c07285a124440504601481c004e2000309480f60b40b04c0002894903005070000064070342c0c180300180400c2d51890079650020402c80f00e1005c13241d40c0100860040c28175074011545407600c8440000d6000440c403500e401a030003501c0f0440031081d000c40641d040020b0b8410811184d80c002d00b2400400c4481050358 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 924680287 1250 924679037 924679039
    0x40b130f020d150f05030d090e09030f04082d19080702060705100f02130e040303090804060c0606120f02061e030106120c0306180f110c07050922020f 66
    0x608000d20190070404a81a040b401030f55030044640c18000c03151050401030042001310014010020f0f044001042c803e001d100c2d90100800d00c0c404104600c03400d00589481c0404201d015840da5a6450708a42e41d0f4000782c0000d8099240b1810f080f59203a842034a20011800c40d0010300c02c0c51040c00b201500c0c1d0789009002d5074203a0082c001500103a03115401050341d140076000034030044007401b003e982250000d59018070b5540c810030030314402c6042c041c002c0d41159001009105030790f07a1418190f01a20413586c0c01003401c2400200031400c20703040b00d0080c107000d00552040046a454184107030102c030300324a0103401c01c80c2d15440c6030300503c0e156000b0542012801d140440d582041c114900b1190000e811500c08103079800114280d1040c01c0c850001454401d28080c070246152440102c0d161016000004001e620390004c1100303079519030000f0180a28200c2110b5842e0341341000c0030b8980201c0e008031441948110041114800702c010a0707100000012800101308034107600b0801c1c5000c40c00592 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 924681537 1250 924680287 924680291
    0x3120509060a031b1e05160606140a0b04030f1101120903031a120613050f01090c050f0301020313080f0c16080d050325111902040b01051206090a060e01060c03020c040b130f 76
    0x41c070000b48c1c284c0108402000c101c4010a9610700c00d00c00c220074140790360000c0418840500082006c1401c0006002034a6040004004403101100040311109040710b1240145030818501c4410154140d1142550001c90003409070080400000c02140301e500c500f402e44075a1040020980417100005804c00c540c1c400c030120349644082140031400d5985080c030540d4681c0004d5010081810021484c58042504a0003186186002d1a40030540e118981e000b80091002003901c0d03440f1045c1c070b02120900107491089609005040e80f0851060009004240e214000e0b000c0c0c8200c0607000e002501e0044810b80744060290390300305164a00d0001d5000e60700c042000e109640251003805010030701601e0109840030851038a070340184010307078018184a0f13040002c10004015103000282c80d0755000032080390500c01d551111480d440241040e5042454004098000002ca054000081c000c009200350261405410b020041100301c84c04090241d40040300c40b601c0b108a1042648103a0401c20351400c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 924682787 1250 924681537 924681577
    0x5041505091906080601050702100c030e040f050103230d0e060f220b0a0c0f02040e0102030c030901060f120b0702280606080c0a03120509060a031b1e05 67
    0xc050955038481c2c0a800c0e2198101400810307888209250310000078240a454180c03154080fa20302d003104000b41040060321912481054407400314100c01d00801003003449141e02d4002d80000800c0203200441c0d0b203040320303182580801c828040380c5002010b90000b8201c0a00410f07410380f040003040f4101540401c00b04a0103030503107040c40140c001d5070400e50700c0c801900c20002042c2000302242d0031084010200b0300801142c1c591104d4a0000a94850074080911080713201240c054a14820f0301a0254004010001483c9071720707025502c9411540000c2c0081c5544a1410400628a001341d00350701e841a07000c14046008042c1345c0da089401d520460700d403c0304059480c044500030030004c0c010003001e0081e00e42840803901584000e88803100280c24410404400603440c4150b51000030035448814a6482c007a030b00680980d0410800035020301d96884106000500400c3c0051f0001043c0b05100d114510440c400c06149154401d80d000001150b04803010546090704003480214201980c894 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 924684037 1250 924682787 924682789
    0x902061b010f05040614060102072301021c0201020307090f03051203150d0803011d010e13020d0b010b09100c1205030a20030406110703020705100e0913020a05100504150509 76
    0x10850740306034081c1c0f00000352246c103c2141543c2803000b03060541198840b22092022642c000c080400c641c560003280381c600c1050800503814001044440c01c5490b0b010342490766015019001184100e0490352145509511401d862000c28a1070102500d00c1c0e01c040300d03c4d4402a0043c005640010795407060740c6403220312000240b1800e0070404101c882020200041042103d45548446607207015007460400d9030400d142c0c080d00c6040146060680a007080c14101952210501404466044640310200d5138449210a10036848030b60010301038411002c06450144c031981c0000d0b030341640300601d9900e20120003812500b54201a012a181d11341c0c40c0da2100b000c940c06400820224400f000054403031420b820010110759401a102c090404200200b000295001c903980003913070320889103030401000d0302004a69042d00800e0480d00101c0709000d01001000d02c502500020384200d990018561321403082c0001070520200c0720011404c2404140249003003201c0c0c41303c01c45001d1625030b003441e80c124 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 924685287 1250 924684037 924684041
    0xc0305030c0c03060604020a0206040828030c020d0f020a2303211005100c1106030103060207020405100f052b120e0a120b151201020901120902061b010f 67
    0x7880e00340d038607405001494040e090134004c0d103034003010441d0114100312030b13614003075201c50000300010020314001911345009a160403244c0240701101c0d80714449114a0743c4050300034904145075001600c580e500d0b10018501c206070018088031240e000d0a0b15440310750761000240b84080000c0d01801100041640911007000074081030705103001d0009c41488241d07002000518060964004034080f49014419038441454203100c0000c149415404840e150501100303045501e00d500e584444000000418084260040c0c96410f001300c40402891b1143c0c03207411131034242441149034010001204001a20b0005007034003403040b86001c0a140000d100075002e254641e5400c04035400c01d243d900040c40981d004107030300750391103040e01c11081c1c0c50700305001e2a065581c00c0c80002c003800491400140e02c0080c040407141c1884014006100031807200d94114046c1d0400d002042c00180c20b121760b550442814014404402c3c1c001d410286095111200080c2d000d12110010244d5920743c0280400310b1054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 924686537 1250 924685287 924685297
    0x90902010306091e0e0607021f1b0c0201020d030605100c0f08161502030408070602210117010e01050103080409150315020316020a020906190f15030c0908060a02070c030503 76
    0x210409203000885010360100d4605044450040d1b10603400c0102044d0000340f183c109060001d1020111072000c1071540203484c0306445421a0009484101466a0051542c0c0b413050702c01d03000d4a45501641e4400ca0403110b040c803866030300c81c28480d402e40c4a28002ca0b04802c04a015001849814080792074201c140c0d88020340b007484410003a14200240106c401000158001002c000d510707509107510351035a9802200e001405581c0d00080e130a0b4501403030802c28a000f641c2c0505900e407503035120050500d109428000c01403550800764151035008040c800c00d4140d95020591505041c01c20072032034024a400c2034032441000c14400044041350300c044901e01441d603101c0d0056500d00d005012088030200c032210410079503106581080c0107a5808034115481a0180d40382d4000425441ca03c9030080881c0d80300007407036904400007003000360640314003041062090b1810b20005030350450858000008d80315403c0700b0307041400032900000b1280c00074aa00d81c0680000e603901ca440f40ca5103809c40d07000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 924687787 1250 924686537 924686561
    0x2030d0e0714010c08040501030f0b090f06190806190e0708010222060813020a050415030b0105060406020601060e031606050c070605210604090503070506150a0f09090201030609 78
    0xc1d0402c010502d0b1115850120503020b2808001d003003110b0303468140314000ca0040c507052544032003038403920100c20b600c442e0400c0001005000c00d420216001e43c401d003416030b101030140b0360321038031010140700c00300602044400101c0142400d540f00d5441d44040c00000540401e0740752240e4130065241010013010b4041d000d1031000603500c910b00d5440040c0010b007404201c0d90318601343d104000e203a401c0794407194000003110102d1068081880000d2048003650441c980c0b05141c101168490305141103030740140d0b0310075040c01b5000d0f600d400801c6440e00841c0b0410300164040c1d401441214481d01da43c5596401c050304072002609004c402141e000d2403608a0400070b41c0108038001b1140b0200041d10050034242852803500c400f0700300150b20441d03030b035845c0045110390078085040c684440d402a019180c1220550b03841d4400c903d8980d8a40b43c0c15203008008508440707441c0760728074060b4031a00c1191010701040280c2071074942c2e00c101801419605a051503a10000040c00070018040c0781f0401d40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 924689037 1250 924687787 924687793
    0xf0d090503120901052e0e0a06030627120c05070306020703020c0f061b03090d060e06090c0109090b0102151f090917091c05010603120503040c1502030d0e 68
    0x18000d4031190452800814a00d8680c0c10700040c011000032041c1116200003008246c0b04101c000303502284081c0b1141d0f84000f207229038440c02c1180e41412030b0b00100030b41e442400c003400122040f0304501c11a0034100784c4010038480001c080e1001424411100f0803036491801d100c1d00c0310b4620344075241080c140e5881900d1803034001440700c0403d5414817091640c918220703007150034603104101240e00d60291310f4041903100150900c0540c182c604109544c1c50001c01804605050001d20385036002e4880c505083c071140c07043c640030034a60310380070803c0c1d2401c88040e914811050700d810b440c6800340000c1c41301d403815070003800d04007560409401b12007032240e200090204075100000303400040074a400d03884940c41600d0202e181c0001211040c290b8414902c81440b5515801c8880c000781d007200503010306148900e00d80404a0402c14190004011030b230140d0000b007849504a082500c140c0700880f0001c10244070701d6028402c0090074034401d800084a441140d04011060700d08804440c5180c0e00c107500c1da8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 924690287 1250 924689037 924689047
    0x130906080a03030e0613061a0d060608010b06030c030f040c080f25060c110301180528020306040303110f160506060409030801090e10020d1a0301020301120204020f0d090503 76
    0x1070f018002c11504814401c024056480c154043d0840c2002408005000b01e4640c0241000d80c4030b81d0520b0b407a0600014040b801d108118600100200b101384542c8040b9401c111440000b07240ca001641d10410210721130314616511201c4984914100600032503545201b901c0c081200c00d0104080600c00300703640018040701220700050940300707221041a060901104030b003440b000c3c0e48401c23030486244d03100516a051140e864002030142c00080e1003c81c1069041c5055414448000385a4a0385204450708031268921041d1883d030200c0c1345640a90103a11441c00304000910a50001052102d0300b40041d0800b51902c290214551200d80034018a0a1075a142c8060110620000e904020b0440342006103005568016010701c10511441c801150fa802104944000501540d0031206c5c201c40700310340c1e52104816000c0107010000505002100d54050314082c0c2c10b0510850b03050720080c00c90729a0f540c1080c1c2c00c00010f5407040100c1880140c05002c0005c020385507019441507284164040c3d503c0d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 924691537 1250 924690287 924690293
    0x40f03050f0d091718040209180c0322030e0d06090212010c021e0606010809070e1e0a09020f04020a0c020603101509060c1205071208100b040f0605130906080a 70
    0x70b02c8910721301040200300003500c000c00c40c60f4001200700d401a900544c07170710800400222131050010996241e110110204858030342107030015071280c28003019142a04038070500408944e082860b0007404580c10000603013032841d1030141003d49031b100e0803000c80d44400742e40c003080303045110713200030308050791140d05584120380c040c05250550206080c100841007a5620b40541c0c40d400030700414180028107000c1203d00b6002d000302d01c040c003c03402c10f40940b03081c00303810b5610000d0418442c001a50751600490f030b1706c0701c0c10301880000540003000c10b980320b020f04007040f0080d404070021400344130784004cac00c50040c1c8404014500c50018802d030300015500d060424410740c481118001c4c1003144c1400c041c0400da82010b05848030b1a048414002035402c018000c0d2401c1c03140d068041d00d50540156104401c9a001011038490801280d070303003286644c0c8001c90241c500403800740129000354480b00f031201521486c090850400e00700f101d05180d503502c40f01c640842c0c000e40c0084441d038104418050038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 924692787 1250 924691537 924691553
    0xd15200405040c080f0610050412050c0405090c10030218030a05010b0406050d17031305100b130c1d0402190c1a0f06010f1e020a020a09050c03040f03050f0d09 70
    0x7420b1070f5052504c11407034084241c50a00400601c1c4030b01c109544002a400f03240b14205642c09000c0c400000c0c01c60350014280303141c1d51240b002c00c441c800c078248000240019408074807850460009054a8800c0004401c2038000c0d400c01c001842d80d442d403100c14448603035410040003a400303000f4000042d070b40310300c181480300380c03034003034200707e0084c542c0720305920014a400002c41c0c00c00110b0308623241c682d25958054245e5414850000c0c1c00b034450980001c1909440341d220301c0740d00c44116401900c0e07e04e02c40b072540584a40c000608045502c20017082c01c00c0c452080f45201c00b0340014801450401c2080306c0c1007001c08803100e0301c000a072012800008014081c00d40c10b0442a4200344801c2e946400d81108100b20b0f00245000c3c1044850b4082d010001c0c0140c04a41611400c03080e09145c8dc0010000259039003a41503080c0c1c482c10601b0300001c0c4400c0c0c24800c01d4002d840c0d40e003640c0d180d0354498980c2403044d804154202c04003e820404020b81e01e03c0c1d9805440c0003d540f803400319058126003031030f0103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 924694037 1250 924692787 924692801
    0xb060a1106070c050a150f020c0c09480408060106030b010c021318051c120b2b0c0b0406030e0c210304080106120507060c020d1520040504 61
    0x106000d4042c2000001c22030000d0100003591b40004802220b40031500080003410004030b0b0143c1d00c0e40041054408950080781d4402940c00c1610b0461103980c412907070501d41c00451503164810382141d00b101400d5040803100d0001d8042e031000c0c21494a200a80d004006d41c095032100050b40c106030700510120b503050040380400b030b0007483d2410a10340b40f50006500c0010075030420a0680d41e98a002c1540b00c0f82c803400000302a009003d840d01e8401d003140c00c41466480c81007000000d00011100d4003540b42506c900191801d02070301a01580b1504e841d46d0214a84801d4021420340319280340100181d0215103400c06825081c010315141c6242040c017400703551440901c030b0401d400c002c8401800d43c541c0408551507090603c14900c000d0389030001e03642548600c0d00070a840e5401c018004c6080c800e10010004035038443c0045402c03007950b541089664401d0150000c1d03003c0e001ca00d1550115039200160f5115001403100001c00c134085050300d0b11200c40c2c4542c21070040201250401261419101c0c0003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 924695287 1250 924694037 924694051
    0x204050319022209120f030c05180d030219030e0906061806130509010312180f03150609091202070602070806010b0f040b0f0d0b0f0d0201080603010b060a1106 70
    0x301d02840c180d0300040c0c1201c030089480e0890f84151082801115154000c1400150020b1054518104103030b0020300c1d80d40c00241d00e8000c2828200081d00451041c0222029004100c80e20180c810808003040300c1205100320540840c45107082203501ca0201ca4080710501d846512440000f061590070302003440c00003403c1c86c2c4643c800340110048038106c44d9155000100c1107400c5940c1c1c2050041440305d6a80f180c10282e0041a0302001000304420b0030a070841402e840c0d1a104041445031442a00e0403150380900000c41500e0041040020011041e92141101d03214002c04c00680310035141c0210742442c07405031009800c41004c01001c640502c41d10014000300c1c4080c0c4060360510440f19aa08c20611a06210b1400010845000742c0031406660250580c00320841d941c042d500700c500c1040c2c00503c0040b58841ca440c401062628191400f0529810080c0c180c65103440c00340c0040d201740c00014103668042d504e8106666090366490002e080d01003140d1100100718541d0000c062070610001c01c11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 924696537 1250 924695287 924695323
    0x70b13051b0618060d1409120712030903030f0c050a0e090603150907080304080a03020d081e150307120317010b3103060603120804150902030c10020102040503 70
    0x45034072611800300710307008559100e05003410100e0400c0801e031075200d15441c0d0030541d480d0407001c01d044e04213001d8407400345925204a502d03042100d031180c1a24881c0c51401030a2036106510310920703a010350448401ca40c000d050000d402200f40015400380c070b503200d8030200002d600040b08144907400c075903c04484001510b82542620b084804240e494034124058500401a540050302e9640104a507201a00c0850700f5030780c072143d50b52501030790352820980840140c081d50610f07000340d5101e02003c0d4031a00d5800403030303820b0503c00a50707a500b40c0170241c00c41e850482d460070010400d440030080c4000406002814080e960002e0034001c14180c1c0c8000003004c4680300b01c00401c01c0036041815210f043c011544070b680c10240c0f001440d04031184c82c0403e14416140c66400009209190f40568216405a91100c20030040220119aa41d1013103400070141c3e8403c0e4148110412140d1101743c8061015044918080c00c00c0c002030300c170b81e00c400c00a6005030340014082c0498213042c86128030288480c010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 924697787 1250 924696537 924696583
    0x18010e1f0902070b22050304050d06090c080d080906091905010b0a0e0a27060506060d0905100e030c100e030409060b0301050f01020604030e06210405071e14040b010203070b1305 78
    0x346d5489100d21302c2218861040c03403400c032003030045039400303003110541c0624000020f541d5841d040b42c94038241c610107000724202c1c03400100700d8040450b15034841d01c0800040e101000041000f0170b04002043e00980381907590707a91881d915103400c4140c1e0090a5984a00c444902d4004e4907202a1749075200301c000d00c0d091401d400309c24504601d0702d800315258001008103c1d95a150301150381d900402c071001c400c0c0c078103254000050050100f02d00d0008c10000c0003d00c070011409040c01c0d581c2c8280340300420b00b903004881c0440c0710140d603400000c94101407016245080d43e02c450a000303460305a00b2400010100000401c194900007800c0000e00c86c0a0000e000345107040c1e01c003e0103440c3c1704200d59004910020703000e1140a48560b528101d003243d200d10a806d42890b0408981d03400e0310340a40030b8007030030669201490182c2410060110b4211010100c0e041c1c501d201440094114220f5050551000f030181100088940d2020b61042d1041e00300c082242c0540e0401da0316007203400414200003c1109a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 924699037 1250 924697787 924697793
    0x4141006021b060a051207080103110f100f110115051002060709090203061809060a0b01080c07020d1a01241b060b030f0f0c18010e1f0902070b22 64
    0xe0300508446044500c01e4403900800300031754003407190200348024a502c007001c0101d0f058112150324180c9000b9820700141e5100007040c040091302001146a1020406c000b281e1018801c1c503200300c14a40a1600110a1210001a50135a0016848000001c88080e010b000303504000d122103000908510041800d414415005009044a4007454581075000400984142c035103034012102c400d030f545001c80e03140c500070384a1921354030151200c003600e9003080000342c030030f42c42585598064000362007510f151402d03a9007009040d2442d001c0841e4041c81f000d0280c0b6142da495a017042c001c0983c458640884505010207000d0170000388403103001e106c45c2550400492840162003010701d079110600040325125080000c1c5002107000040340148202d035903601d084000424050102101560032514501c5800307802e0181c080c0134060f600100c110400001c5c000d8414007099042c00190f0725506006a85461218082e41c0c003408081e00e00800d41001c4c00b00c110701600c580e50003a00d83c4403c842c415845030b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 924700287 1250 924699037 924699073
    0x1a0f041104060507030c02060a0305070e030f0d0e0f0d051c030e060106110c091015050c1203070c080a021e0a050d080a0b061603110d2c0414100602 65
    0x1000b607008200700070a2640c201801840810700307031500240341c651620b002c45001405010100d65403000115100b1020703415040c0020078026842e0408080c00070040d50400845038012508080c9600007a400d0004640d03455020210101c207002d07078068855460510740702d050b00b18621102100f0185005011455070102241c000d040d26000e2418406035135410004520300381500c1c0d072485d80025054107028582c2002d034100e0003254580c0036130f42d03014503c0410070389050245120803402600174190703c443c5120303102c00841d8401c1e0141810b40c5101c0300350f10b81100c1c51b0008080b5101507408654900e00745080e481d401c200000c0004c1c01001034100c955610f07501c6504a1300300d00c003400104404110b005505801611905001502c003c0d22000d10b00f5100403030030784800c0240c1c04540015111088008046000c4600c2c0b000303500c079050f4420304c007128109030030300040003000e00d195a02441d4040741e0320b0380546115144104000c070702c2818600a69031007103071160310440c2558005041250310640817 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 924701537 1250 924700287 924700289
    0x9091006090b13080313291e12090c01080f0606190e030d180603050c070f0213020c060603120a1211090604150e01030908030f06131a0f041104 63
    0xb514119200c84107801c00466a140c2c0750800c1040d80400b20360707449041d00d414480011600006640d40180644036140d928080582040e40d140002c00c109140700311561000403200310030010344541c80c0c41d00c003d034886800d0800343ca0b91985030b00100055000ca41c1d00103051a005004403e6400881c04c5c280001210391003086800c480b840d86645004100d24011401081840b401406868004e180c0c2c000081c0380c58041300c100a458807c1120105031a44640300741c0c2d1080007540c014501c1c1c0340c8544ca615441c4180401c1c102e0740241881c1e015103091000c0d00151480300c00d40402800349060031020117040840d4218042c41600303045c00301e5001298010301402c1d03012401000015a800907890ba0300181c03198020041e005100001c00142c0c43e05004164071200c059940e0f031810424098004406031000100090302841c2d0600100700500b09406540350000001014000745105032100b54056070340c044d07a80702d011400c5055103c1541003c140d400560842200d0400000c0301d80310000c03480d8011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 924702787 1250 924701537 924701549
    0xb0a0302010f030e010c020c190e04020d060e0132160c02040b03030703020601152c03100e010b010e0d0c062609070609060509010c1502070609080909100609 69
    0x10b940842c54400c2c02940400000348035038000740b15040b4140c40c081d41c7c075680e00300807500a01c0044095420b401c0c1c2d2503000703010341d038600030420610b4559808000c2d111a040000752a150350b40c1c004160040c1003445007a60310401da00240080b80c00c8403900b1040070706102440b403013500c0f06900704117600c0040d00f5812004038150402842480c03050020900030b00140d0281780e010710001070700c0000c0c950000b850904841190004441210f04c28004455030b413044200001855003aa00790300d0030300c9003402100b25480c006811100d0059030042c2e001d0507038201a9090489965400d0610650f50b48840030326004007043d1070903c0e4140d2180ea174610524118030468007080650f20001c80c120043c041560100343c9400d0b118281410300404180d01e44465202c1c85c030100c0c45403000080c885004609848081405031140d01c55900740d6216401c0311040c8681c848400b81e4204030102c002645407045281c0c40b80106489078642c164003081c010340510107040340d4058074001130700f0410160312204c600e0548070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 924704037 1250 924702787 924702797
    0x61509090102070b0a0b1f0804021030050603070509160903050a03020303070206010e010506030f090f031b0106062d0c020907030c020d142a120711040b0a030201 71
    0x2951080ca140240103a440042c982044803060203005100d0350000c1c0d00f0081c080f2003a501000080c14040c0d8809640d4085e88040343c505030016002d0f103090310100740880c0d000c2c20a910049100304404c161900d0100b41c1c00341006140b03050054004591140f01d0744000203400a10030b580c1031030001840000b0003003681030010300d4005084e0440340300d1180d803c0290760040403203100e00000d140213500c0307404c02c0300d20308018030a00b400054a03c0240b10054100c0f04040c003854516100c18442d04113004009000500c00d1181c4d448019840c0c40c200300808904841b90610300701d0502985415082d075180e5401403040080310030f250f00607403a80c00e156042e030b46c1f401104002c04950380c0c1d00aa071402c1400710003950182d100010031040c1c80e050780101c00340300c41940c242d528410404070b06440c4414015200301680f24144100d25200031408201d980301c1c0b80c5003140300c401c0c645481100c7d280220b041d611491001d07010660400300071450701c1d9002d5050044905000e503c05000200364102a2032202a0400c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 924705287 1250 924704037 924704041
    0x503190c1b0b0717040801020a050c16030305090f0a1a070b010902032806050a171e1917040312120b010e0f04091505070e040b0a06360611061509 64
    0x4d5410307000c4034010104000255101c00802401806540044020004c00e004615056a0340900c0a604006490307168413050b00f020560024000040b085010254020184940101d080d8284403400b6904040849080d540c84080d45000740e040541a84114462401801400011a0000c07500481601c204406544101c905511130018114a900950300481038a0340840d64181c02d518060380a20784d8000c4864503108512184c4029092078610506600b115012403090408030b411904041c1c02a410050800c0a00382c045826500581c802c45107511100721080025412200e004800d000d0032900304541800500040d00100f00101c806128210409800515035126405514480d400420082d00c00c034010490780300415080d58610040f0b281072000c0143c5140c140035035065110041c0c2400e84107880d200050b10b9542220038840b03460b4548080d907001e8104060005042540130552004c181813800d030303004d0081c0c1c0c110000926240c000008002c003005d120080c9405c40e840a40c0c12018035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 924706537 1250 924705287 924705323
    0x10b041404150806090c0f0904032109080a090b09010c06110405090f040203010c0912030e01030912090305060109110f030a0e0f0703110406061704020a090c0e13020406090e040503190c1b0b07 84
    0x160000c0d04031031024a4104038cd0103220703001d4050442032800d502c0d00e400217038580b4900c070424001c06000b9400510890a900f0008040340c02c500340c0146006411418541c5550000b0380c1450122852128000700a042100f585002d0003048803815079820a070020600341021488041d08816016060000d500100352182e44660301010340c00b508012420b05070340d28140700908400e41884107480700d02ca000008a803414161050307001180d0440100c1d89000b01c1c0c61012007240c0c000400d40020351345e65814146941b6400d00c6001c980c0c104e040b024060681c294500860006090314000f40114038024040c410182c02c181c105468201000d0000f15036a038502c0001c002450039002000342e541091030340d00704d1a4001c071211080d8041269080a40000e01e05498220f029078414000050940d000403c155001c2681d150b030031500030002d807407410303a07210803040038240c0003001d0400040c030981224090040d204904401c01e440940504e854620f4030341c0702034403070044c40c10140114501705008120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 924707787 1250 924706537 924706577
    0x70305040f0b01061806020318011107030b0c030106030c031103180f0102190e030a120c060b04141f080726010608160e010b041404150806090c0f090403 67
    0x90203038044000d10a660b16100b000300a01038980b2110b0505c0302003200070035800d0010003600c445840c50180090501000b0004544e59010202c02003101d001e509804000b1444001c0024890000d40320484d65035490000b000b4101e6008000304c0c82058036051103484100704a008036a000715200c02d2a86003009d50600072403c1c0b09200b1040802d82d071002912114124180f0b0b28040045a680c441000010024041c903131104609800144100300300d25111080d203010303844042950340206800940d101c070715404201180e990160110302d040345031041000903142d040c06085c0c03c4a030f484003040124034000d6403945d20455405a070741d110050740c0b0640f01011140361a440403024540c000e001c01643c8800c42c50b2261042103060510b01c01e5418003080400561407210704075518081007518051801d01041000e1002d03081a9034002d840d0305500c04111401c0240001030b20030003001d065182807011116103000c1c20022001d00030040e1500000303c9035290f144c903982c481c1d01800e00c007180050110f03000300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 924709037 1250 924707787 924707813
    0x40e0a1119020105061c08030f101a0301051e0d06110903060109050f01150909020d020417010b0423060904110d0308063a020f0d060f1503020907030504 67
    0x140d1409107068000c0400ea05411440c007850064840b03140c00303411a064240c079a4a0300741c000d071244000b00086500340340601c90041d48a008004c03415046030300c9500303109800403442c00c9141c0003800400103020603d02030b10301c032055680b5200081e03281241c0707101240e480305002201425507541e884105015500c1001111b606500c01000d50711b9540e1a244280000c1000381ca4110211000c0300001c1150321001c1c4840c0900c3d10141c43d00b00c003842c6003400410103507001008040c00e9035000d00c400143c00d00c2100700c921104206000200d48100460240411280d03041484030700c00c005600008511002101c100f6001501584d6064199407141407a581440f814001e031504404894031a00905034050912030180c00c0c03ca541c802c41c0d0b400080000440c400402450200416400d0580c011108660241450f580301429461a5060180000e4481038130811705130707440780c0c031011018109240340c131920025002c0c0840c0860340d00c0c1141c02190482a005100c1c5050580e600c001c24184200c0d404289 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 924710287 1250 924709037 924709057
    0xb0f1815060c010501090b030f030414010207030b0411100f091a0c0d05040e0601080105150717040b0d0b0a060c080c0a060f14060301090506071413080a1403040e0a11 73
    0x10303a44005010089000308400d1203048081840d07c41030720030600d0045055200c0c07150480086040c00e040408205070308041070202c40c1540306880d4000000359100e80400d1087d0f0090070301c1d946285500c0280418042d00d66000c40804c400a040e04902d60713040001d41d010b60b04c002d02d0030840807000007031107990340c8640b003407001c070380d200b0300300541c02c06a4000014829508888110200d42e01c8000064816203400c1c052260710000078032642a804ac40740014001d0780d40900700d5900f040c282e44042c00004d50054008403141d09000500300d03007040315401402c2d04403000341c556141d850f00d001402440158000c4006040d03560010714a000002c003001901101078000d1800c0241e60980062035008101962020342e60000701c1c0b0006d0107610b018880c40d120340340c00c1405851107580b8038004641003032028440c550384000920280668910001e03c00020344051002001c4d040e05d1400d01c4140c03090380d60031821301e55004000900812540710f54140d0400450350010904902c5030017008040d00402540c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 924711537 1250 924710287 924710299
    0xc0c09020a0908030712090e010b0a080702150f1e01030b06040203060a03080c030318210d150e0a0509030424030204030b250306080303060904060b0a09020406030b0f1815 75
    0x406d001010b0111449240030b03403aa50101035880b41d00c412001c00034420000c1620041c0100c244140c02201141e901c03100314415501080c010b04441c044400c03080e649140c031190900f0401a150100d0020038020300311030788400e022503143da41ca00c03a9801c001440c09021303940100214800e919928202406542d200585544900b42c3c02d00c0c050741ca0f0421500308148100104000da440c08020920989035484060071640a8240a544980541c4015018032130307941e44074100e8502134081c04000780600168500c1c000300e17007002d0990350f054a002414401c2207401c208020080c0080751000136850b035080d01070b1240f01c2c885500054000340aa948050070038500b00e4100203102d0070803014620180611000881e001000707107412800c840c228001c00045500801c04951703a490889a5907520034424100401c0e40300b00f0101140f203035020742c1d010714015900807405001c020b4041c0540c221044d002d540780c850000001c400514880044c041c802d03440e1894201098400d80c0320340210942e10070190070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 924712787 1250 924711537 924711547
    0x607020d081e040303020c0d1707232a06040905070c050f0705010f12090210021b09060a03080304141e0105160c0b0703090b040f030f0c0c09020a090803 67
    0x8106030707030000012000e0884207041e030b142e600701c8076020340e02540d0305607006260080500084c8070191810010645420001000da0780807003103404010503000d4428190b90754a40f601c0700403262103100000684c0f600350481c0050249103075201d41c5044d04002c0d00d140c46d609000d07101012400034855034003da1501c608050404c000d1030b40103400d41c05c40381d07c00c4003200c48070107041c0301041e207030700090140a0001300b0410f1000034180c829440020f58454500001401c1d168907400203a118000340240720244c1c000d8a501414035024810403040c0c00010380b860b541c9440c10328001007181181d0302005280365404404241070100c0500080204030303441c022207031941d400407402c0e0001c140d480b0b40480c8941c00c02c00080c0c2c5003440c00203906000c1d98980c50b41980100d02e691200e940303803002841c02e0201541d42c0e079403002085101804c64003440c0550354801d00070b08541001020100c3c22400c0e86d05002e90440514001590261004100c0e030303007030388016110300002404840c0814550b0100c1c40520000c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 924714037 1250 924712787 924712793
    0x280b04030903030e01080c031617101d090709090302030c070b030a0e0f1e12210105010c0b180a050717010e06010f0303030908040909050f01050c16060b0607020d 71
    0x81401c1600d01030303221850790360818001126415000c490646080c41c0038004212485080c8000015071562424072042100700070f00310115840e0112034081c00e1008186003000580002d000c4040501007200c4499154504408210b590324030034030812640b80d507a1103410302450703c01e00640b40e400c035403c41981e801503034800e0b00312001d030030070707120f12200600d080c80c130505004001400652400c0c140b0080c01c4480720b0607142c0901003050b0300b96400c9038041c0c0106500700c1d5404000a00742241d08200341c148202409201c00104001604402c1c10300c941c2c3c084640100b640c1e00ba069500c2184c03d82c41528944603004c0050410400c0c100003045885121001725030480c102074590841c0c0c890344003c0108008a010081e600c103c00e01c92076501001c400028000300b0310030780000c402079004540940c5032541d18004c0404542070050305440d990000c10020000010a025141d0001191070030341d41050a0154000c11800c46510014003d43d5102c40f100d007030340c407850180c0e051a50003c28400b46405141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 924715287 1250 924714037 924714047
    0xe1318030e0a050d0b1e010602160e01030503090904060b030d020322031a070504050d0f06150501090b0d0f05130c05100f0f0909020f070c0b0309280b0403 68
    0x5601103010074035900d400030203070508610380310485100500c000c1d540e007055142c900412201400680d0000b031032440c100d101c202a2031202e8000e040c1c0340c6c010048010007000100ca00e50f901c1e007060100c00901c500400100e0b600005650600c081100d8005417620350780362a900511170503240e01d4040c040c1034880c0341d030a034010000d4032407280030200540d029200c5a000341e0106036580401004900d880070700d0568984111006903101c405410000c2c6003070703100d1001a004016952049841c0e0032a41d0009080050314050040000c01d242510603c150034500003a003a00250f00500800102c00f00b201036141000740c00584100c02c2580c1d0401c11800d0170040050b800d044a041a90008000000003c0c0c03824a540d64070f00c6c08005c2c0d80c0c1d50703412004034241103e0a001c1e62090b0400c105501c000428494080d1004060b9000307003030000c5545414078680442e044965622505400000384204007811001180e036140b0580003021003031125880b6411024421141c0902610611030142040304058000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 924716537 1250 924715287 924715331
    0x70c14010b01091a0406050c0a0506010b0c0d03060b0406031a06040b2d071e140106140904020f042403080d060e07020c1509060c060a0c0516030e13 65
    0x2079980840160b00e6401307001101e0841003d1142c2c8003020401003025a1240e4041e2000c60b14420a44040b400c6075103da070300d000420f8100e840703a003000042c1c0703140c400b80400980d60a82a6410140030040c546603414803207000d00e101d18020325864840e0003005820f8282e10118000f4000c0c8166115a00d80340d41c0c0341e00741c121085510505108101d04207001d00d05034407181074100c0300c42401c1c2c41e1180070307581c40ba0125207440d025101381d1203030324100000544c8118014551031b00c0ba00009407951400681c00084d540d00d554903030180c00f40c00240000b680701d46a50940c0450256800301c1c020070024501440e580c02c410050001007801c0340007200b0098610300500c080d03052801d050100540303c2c400c05110403010356509015070b2242015400078240301850050b00c0864003809814401050085411503000203211071160704804100807402c1d800788521302001d4503600d04181469401d20f0490760844802202505010110410305625551500701c0c05150100035810700145200942d03c0d0303001010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 924717787 1250 924716537 924716539
    0x240f02120f091c02101d070501020712170f180405060a0e01030b040309050d03091406030609040b090f0a06050901060b0306100302131a090405060f0312160204060303020f0616080708070c14010b 85
    0x44407c0003c466100040490a466102580340609a201d6807400d802806d841940c00d1a51024401d403581c1c00010f41c041d20f9504081c030131200700803514100b00700440d00010140f030b00c115040e00c1d043c04661109841d150540e90b010310150642d4886081c10b655601d0a030744003580c08668419844201a440300c2a42d0440703c0030f011444022000354108102400200c4506401240400000700890182c0b00455000550710060361003003c48400590304106103110195401602c45061190000c0f0910581c00180f01c00c4154508504100e8001010580f1030b07580c1c0b50030190049001015002c4440030340004045501500b0071409220710840e05d1904024501403003989840c00207101d50510420040e16884020041c20a1650300d02c1400b809810004c184040c0c4004001000c0c01600d4911a00000e5400398005010400700300c40d00741c1c81d14200502c4020703c040411101c54066405c0f9401c1500310701c2c40e0605198643c2d6a04007200d22100805002d410303a007044000741c1d226541940014103000c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 924719037 1250 924717787 924717793
    0x15050c0616050f18090c09150414100e030604060c0e0118051212031008061e1501052106010f02010b0d240f02120f091c02101d 56
    0x81c80800d580203000005041c20041030041040d003041140c10301c01816032401c040c080500501c80c04020a0351007804442403001400d0020304144a4a4003402031143e03044102c0d1501c0c50281042010200304107805c55060180030b81c408104030307aa000e0880050750070006001c5450519290600030090801c0340d0107031380030610345030310901c803540718103000d40046500d2442c1480c250302e03060501640207002082651640140859011402c900800460040b143c0743c00720784107903090107241070600c100038020300801a00106031040b070b010f01001c407a500c080c07030104254a0680721001a2580c2c420082e4484c554500404050681c140c81000d00c2d0090000380d80e00000c40106010980c200c1d1183d4036050f40c0807a0007070b0a800000c0c4895400180101c8002001c0090220141403d003519010b41110b40700c00c1e000b04543d10f04800040f402c641c003101c5510304000604101e2005912500708181041d180081c80c000c4d01d20942c020043e1200d05029184c040010881c00c8290010300d0212111111441c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 924720287 1250 924719037 924719041
    0x202209020406080a1101051c06121103030726040e040c15050703082a2106010e090a1d1603050708060f0109020a0e1e04141302090a0615050c06 63
    0x4000680c42500c0360344214001c81c805a00001940c0e5a040924141002030307071680748c602c2c02186405807100600c44040035660b01006458071000d07146402d08914002d40c002e01c00c0c10f0218030f5a800240c0c080703003828440440d4200d940758100e12032080d50003c400540c01d4a060204000b04000002d04984080c1007200d0240025001120148215180500040c0c1d040c2d004ca034000d921800000ca1074030a4881d0000004615501840c1d1a00301e0303018541e0540c1c014000d0401c0541e5101a10391211f002d10304004001c41080004451000240103102400d644906240c6025003400c040940100e071082140d85180c000c0050005042c0b080c00121100d000301d0f0700005621100081d814003402c0c08000209040e03083c0007105009400140301c036000c01040752628000343d100c2c0c03114044d10601ea410f00c2c240e10403a03202071100751628200d911649521460030881090113040100111550440d000507064852140c140090400c50300225038800d85075260302140c64101c0c0c01030802c0110102070300d000b5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 924721537 1250 924720287 924720299
    0x80a080a0f06142707090314030f1206130501140a050418030f09180b09090c0f13060302040213030219080a02060901030f14060f0a03202209020406 65
    0x1403010751091000d400900c04100b141440c1c002070525407042c4c00181d205404140c0342c4149502001603c0c06408507031041428401c3c00002003840400070f058600861400301000f5134480548120340c86140710500c00f9010410700c0e03a42c0500d030590303069041424440c07540c403450042c5072003420414140c41032001e2040010182840e001c0e01d64221300030b03403071026503168944094611416100611003042070307008020890a6550040d41c501900328000081c901d4242824040c10f070b03c01800105d040d80c083c017104011941c1d43c822038880500c040d529005400741d5124000f000d0f0074141c1009511078004940c40c402e4090f0241140708403402254a0101c0030b900e2003603680181e0070f43c000d0304815085a5090005402c2400041c00c0400e01850700040705170000302e40d40100c800b05403021208001640500c0918a480c0c07604e40c05100382280d140f440c0c585995949aa00713421031041400310307101c3c800010700c1e43d51403408180e800c00c030390310a201b0340c90260b11000c0300925100c241240300b03c0c0742100c08942 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 924722787 1250 924721537 924721541
    0x1050703061e051f020304150f20060c0d09060e0d03052d0c070203010e0604053d1d030304150203040b07140c070b03010f0e0606071e080a080a0f 64
    0x48036030103840784004d688007038218043c00d044d100360281948810480061140c840c0300359641d40d072030740b0b0390380400c01801680020201c062540b0a003030100103540c1c211255640111380b182c2c02c202c5e0321958640d65000c44000401078166188045c1190b8580181801400004660401118040e80c3e0410560ba02e105d00c401400703440c400c03820341e0308c00c40c01c0424409035406405950414080c101c66401c241003540020700351703580031005803070a4003c0c000313000401c5020015044c0481c40030300b1a003106810107902c8000b810711a500689070b2401145046062401c5600c0340250b55651040d4000070510302c40c0480d41c0e40d10035102210b084203c0600034403001010f1080c0c0e400782340e00c410583c0c1d558550200480e0312140342e0f00203643c3c42a081145a00c0c1c07070010401d040c000d111441c500d43d22589001020481e20741984c0c00842c140350310504020840c0d80f014115041a44e005034086000ca8044054440b15a43c03040d000302001e0000925468294000c0d4801380300341d10044013440056220ba0000d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 924724037 1250 924722787 924722789
    0x4030501142a030a02070602041d0a020f0d0929100504150306020310150309020102100603052e0f0b040b0f09340c02030607020a0816050f01050703061e 67
    0x92844004a40d1585040c20b001150052540390700035040000640724802241e000c2c1d84203070280c540510b03010700b101c107200b180f9591220064000b1030412010081c1a01c40340f2400c01003140c41aa68440e5200b00a4000b00060b0500008544c00c0e01d00c0fa00d26000300344488003514080031980c00154000b81500d00b600501c1d41c0e0b203401100c100d140c00c0c5140e45400107500301414404440400032004924449821080302071014a81c0d0b01250318095070001a00704401407443c140e425084c0070060020800004504110102902400304103031014444585d0031300000060f481c034641041660712000d00d02c0d800c0033803607120032182003003800f42c0c038810003098004a039802c981203d112400500080110f04520b060806d0071b2545007060350120071383c00c0300c103408202590082050619124150300301004050380c4800940010410403409882c1d04070680108180300100003005650203080140038420a11803401e00d90007801141031503800600502404c0c040d1140c3c5a190018040c442e500c0701660030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 924725287 1250 924724037 924724081
    0x8120408042310030b0f1f14030408040317120f011502010e0606041a1302040603200301030b070e031c0f030b0109050d03030b0919060509010b2d0403050114 69
    0x82c1d43c1041208099000d0002204241d44c0715130521a05032040d1102807074200340d0b0125145030103500e84210301c083c14401d0760407284002d14905008200c0011a09021a01070f2900458200360b0394011202070f100703a11400d06034803000031010382400040b40e070b07002800f4181c407040c4034841c00803044040224203c80001c0c4089543c2e50164020a80b070782010380c018890918910001c402d42c1134000c0124000306008443c20321b03001d41c00101001035590510030001040b02c08903e00c00300d01101d001d100d90b1400107000140c40f4000790004510500e000d04400702043c080030341a030f8001c0701d2024000c00c031a0286a010340200705103c0000740503038030034400c002d0600c0c01610790480007414001031000443d0202c0302102410341d42d5800030380c40d54507603507460b07c03441f02c0140e450102c01000c1064800c1d11074903401140030321035100050004146103026108030700c4001000c80c0c1d0022401c0200c9854440c26108e4900c00c00300001c001c0f05129040d0021b61351841ca461400780c80c0d031540c0c0c10102c101c0000490303207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 924726537 1250 924725287 924725299
    0x14031014070e03030c07030302030d1107050303010e0a0f05011503140115051605062406070b040204020306040f0e0d0e0a0e0105060706110a09140a1809081204080423 73
    0x80400740100001ca003102c1d00a400c80b03045c9104640b00d94501000ca40059000d6400400d00303440c0c01d400ba00504002140f400a81410035007640d44041d0b51380018011054800c140c100000e80c809920f40c40501c40c8010014140310070b503940c0c000c911440c030400488074006424003001d024181642007905040750380e2000005503032804041d08640315002003070b4140e03550001840b00f101040c0d04002140c00f582c422444c002118010f6244011025150740d003641c01418203121500204048902c07407a48660143c0307002d6629a10b4100003001811184980304020f440c15a008290100c00902c00184200c1601c5810300385080c2020080007407110300c40c0c41150080e210051145017009000340003918491b81c80402c002000708940421a0468009000007030409001040300b08020101c3c031030000c400f502c0c506811801c0120080c1fa68035180c003541c08248d01d03110400c080084200c122403180c90b5030721002c004c5d401c0510b0811415030207445582250030950b050624030491003030340a909050000c0c0340c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 924727787 1250 924726537 924726541
    0x3050105060a030b01050c010e0d1106151309020d0b06011805090610050706060e06010801090507020c010e01090306050a061706221112060108070b0406090902130f14031014 76
    0x100314098513407030124a0410200380300315410000240141c1d001c4c9000d0a002c0d22240556020040003412050004600b6500250034460542034210f40e035001842c007903401c811041c05003c0c00102802035018025005140910300c901842112a0082d0085000340d1380e482c04050400d102890740e90207030080136401412500132a401d407515180b510101d80407070030064140101e03a1202c904450180d400000b8040640c0704000c034a40c5e00c120818050100340c68104682d06107214003d41e0b032040c40b800d0318103010350600c2d1855103030300682d0010003c640c064070074440740c07070002004005401180320b8102d55200c00c2040003140318001c03900502c00e080c41403021107018102107129009100d2010282c40e0074014025001154440303c01503c841c805440043c0702e59403600c1c260350300e800c140358420400c00d03005200c21f00006600c0003202c41124030446016840300c07507020200f400010749a0102e5001ca0a0410000703a07110820066444450101c054407000480c0701041401c0c1c0d00c01c40c0c06d8410304005200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 924729037 1250 924727787 924727807
    0x912091c0201090f0b03010608060d050d140c07121b15030f060e090a02010917030d050c28030606020d080c0705150907050906030a03200f0a11040c0305010506 70
    0x46804260300515250b40f2203640c6010030443c0143c40e811542c4c40c1e48001005002075500103000c1a00503d060340c071850b84c113003d615200d4403420001825010000f50050303d0311908044001d651481e11490141d4500649d45c0081d0082d8078000001121000c010256100030081420030030403c5400c01c030054085210b904d88100c009140304201c4c07600c03142e9522000f080f0031419504445c400d00c080740042c5109601ca000240001d00349502c403980c9012240c502d07a503212400300685008c1c00300000d001c02c00b40c841d0300311140d031405100d2039481031480d50070400c9100d2105000401c003034215034404200303039502c0300000ca8503806c60f41d0550300801c0310a801b1030344d082403850040240c0c40c0140c00703035640d035001c1012040030b002c4241d039844940d034001001840f040c60102d41150b0410ac04500070504040582c1d8040c100d030425080d05140a81046168103c602c02406101d0310a00000d080d602d0100b140e10700f0120355a40e1800701c0b40581d1404451307981c554082e10400b030507241f0090455040a611034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 924730287 1250 924729037 924729079
    0xc0a0308121306092a0b09040e0f0a1b0f05360f06041104030b060603060111240a0209010e091b1303052b140c03070b091209 55
    0x1400c80341408401c0003210303011031402c1c0b08805140b403150f070440c020b0031509500c2d40000300f6552000d890940303c0c0c00703007005002c5110b0221a81c7ca403050314042072607038101d2886404c2100030a041c00840c010030383e0718030400c030a1203000850061020b11503240203071141380c441000300a5024150b040880c0c07040e10201034060103202c950401100e5050b5840091035030038023100b04810b58080c0c0f4004407042c14003101d032402703000b4030104e025110442c0d4140382c82d40e00d6001c00014041c28840c0105000404106242d1260350103901c8070030051704580100010160b2a0107108030800d03101e03034041d18100440c0c0401d800e402101c8041c00160358601d50000a40204050400c0240610405120041174518072501780000f801e0301818001240d140b0390b185003072090602c000c00c00800c000700707940c10050b19607030100d211452011526103400e1034104044282e00c40c0910840041c800184170101d002002c200d4249800b40c800e0184074103481e2140c0d1102ca00c407409000700c20440394030102d00b4030060b11031000d0f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 924731537 1250 924730287 924730291
    0x9030201080c1c050121080913020c07120b16020a12052b050903121906030f1401140c070b060a0302041401061b1106030a09060606110c0a030812 64
    0xd11800b503c0c01050442002040d0642c9102002007901c0340010441864020701c010350f034000c11144030004545a07942d0a0080c41800f0900740700f41d41c1103180c03120790400350b415103403200d5102089505007030303c030712058501d406c900c0c104440207a1041f0000d90413224241c91801e0b5543c1c0364000300a000038559401c0e0354840e10017050b108003c0140309050b43e40e044a141c181301c0c5138512175880e00084c13002c1c401c0800c0c0d40009006c0744290340b04001c40301a1442d01c08142e94014500c1d01041c0c809600c401b50794000d0300d40340e840600000c02c8d54072030000b40070300103454120301183d02e40200801d0380070000d60b1442c024201e8150a04407414070144001c503915a854583c4400c005160350540c988990015049440d18081e42e4905410703440140840c81e0444042e0462905100c54588050700310b0703503100d00d4035607401c111385c0c06030354080086a10f01c0000e410210070140c2c400014022a81c8850000b400351000d103504060304d214000e07842090f0704040b0001c2c1e007540c0d009000d03280b5103c1d03103c104503030704040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 924732787 1250 924731537 924731551
    0xb161e080d06243e0709060501020c0111070306060f170f190f0203250602030301030807030c1a09010e191a0408300c12070f0e0a080a140d0903020108 66
    0x210203803401c0e1224950400c2c6850400c0c002d0403003503162146542d60300c3c0c8045d0350400aa40d62400c03030280041da0b000030f941d00800000346802640c032122141750344c1c24124103500060441d0f00302103000c2182c250344c4001c042552803c2d4082f1001c0114100745951f00c0c00c41611184c2c0030b801c0031401d8150250800020811140150304200c01c01c900359022901e013448032007000c40021443c000a0800e411043d201c4070042655100642c00c6504540343d5007030910440c1e500070140404824a82e00300401400c00c1408080b464010304c3c10b91422102c21030181c0642c0c1a0000349005402e8100c0060100410480240e0b8001c00c6000e01c510003285502001030002e041070301c000c042840100d011806149117440044d2104000c0c1c00250500e5209070050000640f09a00070035081c05054884520030100c40c2d402001880c1c0203003c1161003406481c2c0d40c465104082e08006801c0d00410070030800079160490500c115114003030f003c050302d680b945803150140b8050015808501c200050b62080d018541c0080e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 924734037 1250 924732787 924732827
    0x41401060506030c07060506100905092e0608090a0f140f030703021c1707031e02120906100e040b070212030f040b0c040b161e080d0624 60
    0x52104001482c642040300d01058505000540304100034442c0035a54001c0303010354070200700711101b0070003624403903080c0140c501802c00c03007000840501c10080041c9140741d202003a04407155180041420b180200c0c05200c01044401c130205102d45070010340e07820301681002e402c5030380c4000d541c4c440342150800c04070300201c3d01c2500801c0b13010810500042512912079001000001410190200050100800003060004103412140c44510703143d034140d1b01250600c2d0001e480c001032190000154a01c4000e103802520100312010011386591590707024000010403180c2c10f1752010510041000c082c001c403011105d1020210f0001014603980b550001014015505159004080aa52a003080310040c912074003e80500040c00915442e01da041441c41081c14601402c02c606902184190301c041c1034120048100032040c4258104009808680710b072100002181c50300700b42c529900020742c1d1b0000b141c9440000a8003c0c00c0c5c80d0885004481c132181d61014405140d0309030f03804032603032102c00c4600c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 924735287 1250 924734037 924734039
    0x18080d0509120607202a0102160b04060801081204030b07140315040b010804350430020108060108180d02100b010503040b060d0318080d0f051204140106 67
    0x15020300445114000c1307669600d0211611244811005412085103c03040d04001540c1c101e00d18044008031041d815004a44500821a00100c0c40d182504500300010350b1019000314000c0c80d03000040048903204d1399441100d907211000a505e41c0509010070403a07010400040000858014000b584206203040c01d03181507003a20b400c03010980c42110744d500307a8104086080e50a10b17003441000141c0030b081c03800c003000e45000d40e1038170b4220203501c10040407001642d81c2d41e110340c2411581444148501c07032081c2d403140d42d03500c1805903102400c602208455001515020560840c0715880c942c203405030340380d05032520b8a00c015a141c4401a00e413104138082c940840c000f02d8000c00680b103194007151f004210115030000d400c0c0c12101c07001c0f07807181005000c105100100755080c4040d600074000701d40411940c180d41c0f40aa402c0b0410000c4c45804000080c40082c81660200710040b1810060300ca0040c05c0840c07001c22a2240700303410b0010b03061295603000c940403032601c0c0d8030500742c2424580009085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 924736537 1250 924735287 924735319
    0x1a0f030907090608010b0901051c020409110306010501020d0503160c1a04020a090b0a140d021003091104050405030a140c010f09021c080d0e010204230118080d0509 72
    0x5920480340a412503000c1070080100308058030541004100c508020413810400600140a07410180320b403500c03070091200030f140418a003844506c8401e0b80100200301c20901854208000400c0c80020780c801c0c0100c80001585500214003031840d41019070317a1074916594130020f0f10000c001e960b0000100601c207031105000604004074141d0100d002105003150346031078810000050300d04c0c1c02016045082207640ca0940c3c03501607094003940c2004402d035003004001c0780400d070b54004040c1d020350300840301d095244d41315405900100306c0601808a821036501560284402d849003528020100d40c0f080060b2000c0510960450141c1e182c0390700c03140d241ca610000368034203403040d200f9244196560b40c0c03c04021440d0034003c00d20001a0051151021100d54032014503034041c08400200c007c3d16040200c003612802c0d81168081d084c410b10300701038141c3e00c4100e03031204105c0b00d0011f40402d16500000e09108449980b200440d40d0303000c0141001c6403040c170201c0b840d41107401260381100303640096483d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 924737787 1250 924736537 924736567
    0x8030d230408070b0a1a041806110d0612020109330336030503040312020a1706120705010f110f0303100e04030233150a0e0f011a 57
    0x41c900500d615511240c090820085142000d045441d0302c524100018115003003150703e019000b50210707400580603c00810410480a50010040485161542a46502c1d8600018000003035500600300b105c4c0c0c1d01c410807a0944089590041e01103250400200010101b002d0714561856400220381e20f14183c0c01c8800c141248102d1120740400c0d03d032840040f040410010300c5003060011203900079407100e075020940c5640ca140d50003804000000000030f007890f000c1c5068944021510904541d54015180020190745083c00702d006803140c40d8003c10703020702d0121800035428030314038050a842031400c4015903400040703068080c20b01040324268100904180821074810100b01c02866407440e02d0310b50489105080e41086074036100c130388140400b080d40061581c40c4d40b03850301d1440110031b81614040040045c420542420504a1320801c460442940180c2c0080c3c1401e5400810042d1143d0040426400c1241c110490300710490040014a4184401ea24038080080300146001740c904800c0070303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 924739037 1250 924737787 924737791
    0x30b0c0c210405040c022a03030f0a030506130516050912030d050f091f02090f03010509070f080c0f040506010e0d080715020414040c031b09030b0c030108030d23 71
    0x601c92000c1020091401d050143c402c3d8052544041c1c22003400c06880740702e0401ca518400044d64000d007001c144240c0b420001c0319021500040c425403503d4040000801a0204540c0d50b40600301004245552803500c0c09244d0081c00e56000ca010400c2c0e01040465564100340c42c450f520030081a0348a50b018001e0004001148821201164038500b0300440e0503004005071145c00e0795404425540820108820306459040701c0b080007507170b0342c01c42400144042c09482c4c9c1148e4554070303090500c01c2003103001541e5030449220030524102c0a5443c03031455100c91000400e43e401242404a40f452890654806907001c03a05040601d20102d80c0c070007040c0c013042d41c46421101500b0010f803000502128001001c01c0c0302145000b503241504081c524400c0f04e0f40b0b035803584d00880d222051101242c6c000d400800c5005030f11207402241910480f00140070019502c030a541070071011012481d2900700601302da05a8200c54000d51500315010580c0c8024103071020814407024102c6c0b0410400c21840301c0c518 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 924740287 1250 924739037 924739093
    0xc0e01120b0d11031c09030b070e040218150f0a0c150c1d09070c03080624040f050901031214040f0605030906070c051c0905120a03020f07030b0c0c 65
    0x18002003c0005261030543c003a030356000364080d48661070b81c1450b44000024241d907484a0301140380e4030342100907601c0341801c14800703a10a0020078a2440840000c10801036500203ca031181510a45031a5a4462007a0350080c030824404102c200d010602440c1d080c400184a508004c1d040d41d00e0b25100c2045400c003095420001e030745140c224010044155006811110840709000a401d203200060030300291140028107001003040064580e981d98010200401700010482d0000751640500c4496070b8440d001d4199451420b40000c945030800c6a103d40c146c0703a200610705802840c82c6010380e032804455510040d112400c01020540500402800f03004168640380c2c9074990030004c1a6504000c40104080104442540381d48040b42001664400d05549024052684030800008503591760580d0807444d0004c0c00e41c4081d42c01180c000441500d4035008c1d500307a50f43c0ca902e011401d91038182500c0301a0140d07010030040b99940301440001e01080308a0300480e4120040130440c102a540101520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 924741537 1250 924740287 924740303
    0x20c070b0f032d131505041101181805061504060c0c0503010c120b010306080708061806073906060305070f0e0a0509150f07120c0e01120b0d 62
    0x1002c00944000145110301180100003084100c0c000e0443c0749003800102800c004031040070015051101140c018501c881414406001610302410041071290010a0031400118040762842000c20482403100540381c0f440b040c500c1f91920721a5090181c00301421856224a004120082248501d03000300009d001c2901c840303032540400d090142c000b0f801940610f0180e4140302c00c013a18650b000c05030000701410ba81d000510f00c0582401200100036136000000c041c8141034012a0300840002d600d40f01b413050031050140103003031070900f0341c5402060303880300e002c50b00070320b061412810081c1400701411050b016007442c5880c00001210748a1400c0015900d031965414240305025083c00104007900780e15540d040003528102000002d6030b00240241012942d920124590200600c9a10ba103c110300000c841d5a040041200d003907030805030765903800305500300c0448089085502601142400c90344948603003807070200041d2a4020b003468603151a69950340083e86c5603031440310313000c82e030340c0136000c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 924742787 1250 924741537 924741541
    0x70506040209040201260f130f03080c1902100509010e061605071e03030608030f040e0c040b03040b0a0614011e0207090c0c0507050a0509040f1a070e0f09040b0a020c070b0f03 77
    0x120000450015110102240813234541c0310128003045003481410341c0c1860808007947c1d030316001d805240642030841d1245007102200347c0410381d0004410021440c1c00100700900c1d202c01310034900321403a014103d10140c03c07040c009a0046c03001e00c020074103100b0505000b1b00c2c0042d02d0b900e10080c6418010664000501145040f0602d81d15200b104058a41d841c015440c00304c6420118880b80254814240d09240d0180041c500c016408140d42c010b11560710010f84905152030110481c82044403903406c02403a00c1c00006500c140303002500f01c4048107840e8140c1500c00440441003000c151040d41040d44104000010414040e1144044a00c00c5641d10b1011070300741d01d0401c0c1404883da0140e880340c0c0e2550000e000903540d840366160040d41c4003d80c820600403902d0400044208598000d4018160f002049401d607000811900c1030101240c02e0407030200ca0100f048164135007030718083c080ca810000018490101381e0700070103006032004100c404050b510b0b00f00700072a038400c0350b1b01d07a000340000c0b003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 924744037 1250 924742787 924742801
    0xb01060f110105150d11060d0903080a091e0303021303051c0e0303030c130806010f050a0806090a080d320f04030c150902090f070f0507050604020904020126 69
    0x7440c0c1d807115200300003404203080503129045070f00c400b03941d014455484412440d041101c0c0615156a9030780160040e074440c420284954028030310b203072065001c00e69040004040c10803030b2080580c05980400c0c107840300314450340303403850004006000f107040c5a800c0001c1e40c0c51440d1a2083c41c000c522800040c1590400c14034208005100b890f102001d002e05840b40c45c40595000c000c0c1d0341c0c005100340c129a110888402041c00e01d400560102e40d06004400011481240c1c084081094540540d020a042da0340c903c0c099a0302c000448400b55190000c10084000826020041011320380042c00421101d488840c0000c0d00001c000700e41c8240c0400b14105448247c1d402e42c0541e011100d140205124981030320701600f0020540300091074030803108030b0142d0300c1c80745507c04445a90003402c040710b13501d410030a940704003209075113110109540741403401640f4400c108660354154403001030107803a00c480d03003030100000e000350040b4140710403540c5154040c03140050b05902c92561f000d00d242141030802d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 924745287 1250 924744037 924744047
    0x90b060f04061a2208010504020414041e021f0203090306060f01051c0f110d050115050706020306040e01022101060c0209011e0504230a060e041502070b01060f 70
    0x10186030107682414030402c10705070076040140369040218075480c0d5820801ca1410402e440c20355a88082c0d1404034070200fa5a241580407038842d078401c1d10308200003202d101380b912071240b00b1203009014100503141c1c5498113690161041c1180c2c4090210203610340c42c0305040704800c8003100c0400c0141d00204c0c10400c20b103801c0205139000740c400e03501c031642c13003102d040000c1452081200760b81002a400c80020301ca210268418000b502118004001d480e5422a03410384980c0300841c411612803c11001080c21041240040c0c030140d0f40c0e8440d0b03483d124035079880001135007005150b958860350761265611440d00a000a102407605411112078091301300c0624100324034184c0020301003215103e040300058888075005d60541c0c00040c1c456030358840c030b515000782d010580d8000300c0c3c000f4148080c1804443c01030072440c840700d45100d03d85a40d03a6a18001400303e4956205a134008400d0b840413a020418201240000d17081a1340003504d40100c58a070301500384020b90060000441c9908003002d480e0703102c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 924746537 1250 924745287 924745309
    0x501180b0402030603030403200d0c0e241002070e010f050a0f0e0c0c2407090b031302060c2a0a0b07051e070909060c0801050d200f0301090b06 63
    0x101c80071400d504090b0042982d0380120b02004003000031080c400c400d201d1721088000e41400e001460540841c20740c1c6031005400d503044c0704021481951501140c141c4072030070040c001404c80d01059132003001040c010422600f61b0214684190b029400c004540300c222007040710301030301e240c500c1070444c240703440103000840c40280c0c001c9442c019140020b10000d4462141143c11101c00e450756911030141d46003031802e240e481071000000a45185400f042501403001c1c1d10f1084845807030310395000d036990400c24650b1000b00c2e10b90701d0105038030586000620301100508484c281c0300d41250310f46810b41480c0c190a80d01d1581d0000f11030000024114140313062a0010050000040742900344202990b60316510a414410340318204c2c0000c020038900281000250700902041400303001c4c0d14141e00300007000b4641e00201c200020f188000204290410060724420f07194446200c004600114040d206030701070a41e0815030000d54a107041485550900864403d40c0c05030000c400c0c181011002c1140c15002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 924747787 1250 924746537 924746539
    0x3180e2a0a09090b120a0b06040c0f05121b0301030302010e12040b12060f150d1d1011040b1912060b09060d090b0906041202030301032f040501180b 65
    0x4104002500180d002c0001000c942d1000720200d130300350341c001c00607402c0e28041482110900c0765048000a1207010b0890718014842a5010021403a807079408032120f000a00701400440d5041054000a10088070743d190301c08406924001403042c03142c1c441000341e1003070b0301c280d005030344503d620760500d441441182007441c03280c419189810f190042a003014010751a00d800560030000014055441c1e1b100c91070b001202c001d00b0380b0550454468600750a0700a20a0f203200103140c50344c0c0112090281028540f14082078000b0200d1004080b0039001410740071500c401143d20038040044e114070494064440d296210b07110b52000905072074002d050202010030302c801c1606182c070400186841004680098500b1b4400566a0403200f000b200a030a4640c4c00800c91070b031000401201c0000418040d00030f9205081c048030f0100306000482c0e032800280400b4041d0914051442c03030059150311402a00d059941503281d441c486903001408656090340058580701034405030035a201c4040c450b10a809030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 924749037 1250 924747787 924747871
    0x20a03140406140903100513050105150f0904061503060501080609070f05010c0c0e1006140a050409050402030c04050c0a12020708040b0f07050709020405010f0f080403180e 76
    0xc5448401001950421a0100318560004e4040c0d4180c07828030440c0380414000e01c05000c2030a100c480c9058800703a420b010b540341d5203803001182034280c42031401e04100400814024811070759030700304400420050004c468882c3d51700074181690800e40c088800450140c0e00008007907250025450030014000d1007010141c000303c906000750b0182c00004c2d410344a082c81c060700e02d40b16078a0160211300250b00710504000c20502003099603180740011605540c0266504541000404400380709401140007040214030113002c113000813a43c035880640c0c0240003c04448042d10440081022200300b0396120392460400201d0b440c80c80d13000b40000200106028045241c050b2035107504825000e14003401280c444001519400210983c09403441147c115090701d0708590355030324000095003e40301c0c29010400642c0404061405142e4070070040480ea12040503070390b16a50102c031074003545a6100036482c411403021442100110410b4465806045880350b0503d40798a40703030382c04081509410f5440c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 924750287 1250 924749037 924749039
    0x3151e090f060103260d091106040b04270504060b03010606050f0f0a022a030c010302042102041803081b19030506010302090d0812160c03140910020a031404 69
    0x1103000110300f070440380c1000419841d040019005134810194084401c3c0c00c03c00450341c2802c05260754004079803070744034146000c00d4071204414800b85005602c1000100ba03010300080248004e04010b62040d0032280061203c010b100549240031900180d42c152081c41e920156642503040074494080079061500340fa9043c00784a603041d500c9441102d0740b05d441e00130041a100da52134003c0158601c04501200c41c000482c202d00400d200d1444e1400000d846441501c840101d03c1d4001d20888054034072280802c0c0660001000051000381c4451080f41c1080c1e42d070741c494040040e0707c2c41c4512914420f030b940b42e00703500f0701d81ca62184140b00102051b034120401c104841c843e03034025201000e001198200403500350741e42d8005800034090030b24116041408003110008000b1140d004008440c0c0742c00d0f40103165194086c40c1c0c4c1d984504401c152021030130000a400219002d654046e0054900c01041440c005501c004140c00028407207200c009a0300c01d5000ca003c141d000300307101062414258010707080ca = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 924751537 1250 924750287 924750313
    0x90a06020c030a060914030c0a1104060f062304080106050414090312090c130b03061006230403050706020105041a04030e0913060c0801090c0203070b0406050603151e09 74
    0x14200100004c0c8042e03560004641000303040000101034043d0300050720740355020720041da40c0795003030710504076a14403890b460030006140602c205000d4812624100d612103007091015141985200003044068040076810500051500b00800c0688244000405d0103813030401400140c80005903203910f40040c440400100600000654094450b0559000d0940d202c010255092441c40040240c001c159a2000c0030303040c1c03541e00094400c550580881c2c030725540361001041051802c0c09540006803003000e160028000c22100f00305c803034032041c400c03030b1070607a8a90742c140ca0110268401c80c051b0f5154810081070000d00001201714000740c10701c1002c18030349507034010031900707490407014451420200403600cd00e42e100c2882d0b400f541d00c400104003000300c110740900200000d11500c6401c030b09001030925010320101c152070b041e0f03030710060100d140c0d00e865a40801510006100c3c07500752246002600c1c000288003241c81c058821445541248000712041c0c0520036030061220000e580400004008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 924752787 1250 924751537 924751543
    0x40c0504090e061e2a0a110313030303110903160905010506130e0411100e15040b03060409050307120309030822020f040f090c08012007030f12050a02090a06020c03 72
    0x140c120007180311081c5599041c2000e040c00c50780a08451081700250810715480340d0700c002092114080d454a0215502040711181c0d03c1c40354001244884010f29820030019002c1c1c0c0000803045c112981c90303810201088003003454125040c0f610769000c520b2000070004903a076449994050003055070703403038545400c035480506500114880c290307003440c020000501f44110051900744400300240107011521071690010300840c000c0450354402c00fa00074460280044502c00c8408940c103c441241c00c41d50390380300b008003d040081054810b0f0104201c2000001e07141d101c071300d00340c2403d03071800100e03415181001414800003c0c604854031720f40010601807481800c0001144503411902000c0d042d0400000c10302404c1449070300c100396418440c41c1010411000048001e171175421008100d00c45000c040840d40c0440410380c01e00380c04040012002192040500080d80d400d141050100c0d008107001000464804440103091641e02081c5180380d868101401c100900b10351005001007014440002c0d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 924754037 1250 924752787 924752821
    0x5030a030f020c040207061b2c0d0501020c030c012009040c033b010204050a05010c0303060f09020405121f1505060426060702031e09040c0504090e06 66
    0x70320054021900603103108000c0f201440501410a54070b5211034079110002e86000c4911149408000700c21000280c41181000c0e070307180501c94141c8020071142301c0e034007818002c5503070f03160071989240d078910224000340010480028464001c44d541d0061950075421185180d064820150b000150950f00d111640162456218200ea000658001c150341c1070b0010704490880c051482c079a090306040184c0b0b4440a21808529880c402d1080328445045608030310440c021241d200c403903000d0601841d4410107020748283e219060010390280c46203e01c0c080542158004003d03940c002401340401d081003c180030801c60200010100c4001801120303c0c1c4041c900a10800580c1e5040520f800740d45008001001f8000a044c42e0f0f40c85484076003020f4050025412a4507000a401d803201d040d83c00001d01c240b03e2a200d81c051414007035808100d090380f5069084600d1011f801f48200c00d4250360350301c103805500e1010b03160039594600c0c040c0c071a420741d14141c08110982d040101048507807000c84600c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 924755287 1250 924754037 924754043
    0x80a18050a14010c060f0c0f090803030f0405160e22170c0106050406030602030f010b13060f120e060a1d030d0b0a030b01060c0c050609280b0a180f05030a 68
    0x4810316070380100480f0041401c404c09400030b404e1400c0c0031303c418550390100c030f442c607980d543d00c00d00c10450b24005d40f01004188101981940104005503143c1c03c0c0088440d005803058054400710304041030413000350700d0300d0703044211010001814401050102c04094410040640618080d022140c4a0070144c02c00c0d190000c8400c0c10000d85900c1d843d40c01e52001010b480000c00402c041500c0b410114001e41003151003011204401002041800141080c0d601c1d00c024115211030b040d00f0b2180480b0180480c1c0d07000414401803108400d0035052900621862800400040003d864610703041c6043e944800c0d20040e03101c00001102d80c0b0600003000f140d80c61101e004020464948003408101d5400040d440901248145000450503d610203400c25480303014905ca072488940b50010843c6c036208650b2000d07801400540c40400840c80c003c1c0030717a03e40318650034028080d036031000881c0c4140c2c00140c0d140002015070105000f007151010441c40545a41c4201c11078450410020942c0c40f00090030103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 924756537 1250 924755287 924755309
    0x21507021b120709140711030a0311130909020306061c021c0506070f0e03010212040f1103071202030f01090503030105150904090c050f240705010b0607080a18050a 72
    0x506155101d1400028580510b44122101c03666203004101c010142c030340520030f1095260001c81c4655110f140d4071502480c28501035407030704c61004c1d021740c02400300d2842c007160b1070b10038044104001d100f1062500103056441010488960341d104050070040d00400182c0318401c40741d8001c4e03018180c050704420b055415034600e2040c030841c148400d2646070030240201584200810001980c0e8003d2141e4101d07070440e2211a4280d50031010107081c0d0149018491013100244001004118281401407003240942842c0d020750404201080c1041d032940c2216003812698a102811400d080003d040d07a10090b0f4001c009503105941c490392613200600c1594401e10501c001c8a18002c3c000d0f0484403d038400400c00c00940c0c40900d0441c0304241d82e44075141c03140794143c2070000c607400c2c0781c0c2c80c100308070b4181070304481c0c2c1800504586400d508240d40c16100c0e5940e8822021036034848400504c3c8690142c0300301600c9480c01071004000c503041c2e9a10440e8000905020000350301c07140da00d0310594600c1d4840d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 924757787 1250 924756537 924756583
    0x14091002030c0105042d030e0418020d051b030a0b07051b19061b0206041202030904090f0c12050307020607242c07090203100b04030501050702150702 66
    0x8100d1460103206092030495281800340000c0100382203142d4038a0300c400e24020038058400003004035411010101030049a5140d1103404149001e0380b0410048a00302850084480030f0f802140420a070315030100c9a81e8400180c12a20f20401a41110a50380840c000c001d1000903603242d0103d004040d182800b40040030408445030310859443c1074203d50064104c0350b40e40ba0158032119050403019055403030740e1a1803111910190140e145074454840c0750014100c6031504d40e10b4100300070700c80d0f2100085020a0240041c0c941d0389000303040b1070500442c86010700e00c1e010300f090a0b00c80c10070391101c4102158410900001100482600e24981e01110344546403400c1d030400aa2003010504420031010707000c590752003985003603449052000b80758130a01d05101000560340c11406d4003050f208610341e1000004010622107a0000d40d400459101c0d0410840d98801070780e001c035003003a00100d48a9444104000683d5410031160b902d60700317481035030b5800c5d0070455806500c076400352a042c420441d081c06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 924759037 1250 924757787 924757819
    0x1202040216121205160f0e0406150519030c0906050903010609092910031b080105010b040e0f040c0b030603010908030702030c011505060f03130f03050a030c1409 71
    0x14401000e560014489025034200b400018200c1c0c1030352080b00e01092520004c44c41c40e80c1166901d058480f4683c40d602950799680380b0590304424039410581d4010f84a65000c01c140000d001d0036204107520ba11010348503203011031103c000d030107a040c0000800d0b14080b00000c8840c0e00c0700b0f2107001c0700d0282c02c140382c1c0d428840d0080fa02604ca5500f0446615086c02c9007001005003003e4041380101100320085002030042d80d558205003000d40b40400c83c0c0e130301c200c1d0070b00100c0c03051740c04c12003030858048034440515a221005401d48909a010441c02040400e0421110740401da40e5035004a4003030840e121807a2564822040201c00c1c0990421490040001240350302c1c2507012000c550b03003000030903403a46001c0c0c100075520391010710080c0c525401c0480f030307480c041c04450f54081a560000c1811b0700744001100205550f4200400d07100180c5200b03465100800c13900c82d98038065a000381d98460340ea031201c403809000e8031501d41e9850304008020b5200e9030000107000c10f40b081504200c03802100648146 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 924760287 1250 924759037 924759067
    0xa080d14160c030b0402091b0a030c020309090705071506210228140a120f020d140303180a0c0302010513270b0909070312201b0a12020402 61
    0x2041d4001c40b10000c02802010209280f0031803081790007200e503075101c5100301d00c81608000584d09a6100340070340440035020303805c07682c501c1400d441147d00300080800080d080d51010307180d21011800c0010020248203a1080d10800a43c02040c10321215251034504070f00081c1700c00c1203070198130040c0b19460440d9511854520702680000050004800324940c503100d8500368030586c6031522000c0c01010050402c5108041242c445442d520001d20003501c0d24239428525440803a070200610b1254400111a020520340000204c801107840e0720f00380c00602104a010222403580d54014500340d80014004c030b10400075a0f50a280054403000740400444142d4940d401c80425a00c100d5032400100c41401e0201e8868031801505200304000321051190038003040e1035552140c3c201c08400e10204003ca01c0b858a8110301f442c2041d80c1c0380600405101d42030307030850309400540200d040d0400c0090711502021010400325400d00007a031802c0c00d103880300360744030710b00030f01032500801d40b42c2c0129180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 924761537 1250 924760287 924760327
    0x30d1407140d020705030705010c050619020702031c09090605031c090801020c1b090f0c18060c0f0607180303032f03071b0803010303120b041a0a080d14 67
    0x810202c800501402e803001c0e403901200e01803213000b8806e48000048940c800c1d0100003200e50450080c060948034403111100c0800c46581044544d60200700c04401600c0402c00525694006c414990303d0b40c0a0040044c685100c0da07000c0010301c3d00303203003040c046641c020a40141a50405072204c00c0c0048049094620801541c0b0a07046035201003514180c0c8031000c103450300001028101c0300c07615403001d810000000000d030754101c01c03014a0800074039032200cd0b8004250403841c841c0d02540f006944000100158131814001c03074030383c1101d03201a4008d407080200315003141c554100a0030345008403080c408242020f22001d0100341e00d466056550305168803440284a0a140316600f154000001c961025401078480f500011041d0480c549080300b02c40010000e1680300b0105403440c0d18588085411048242c60302e40c5181d0303200d2080100e644e861013491340001c907003100444595207000c10414100300c2d83c0c5c0804a6034100d951042c40007680140c5202d80c01155020700354484185550303900c016181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 924762787 1250 924761537 924761573
    0x818070302150d05181f020f0a0e03010e0a0b060105130f0b25020303070b0c09130e0705010e0306060d0f05060403021c1106040308060d0c150e030d1407 67
    0x41d420b00000b05099034030007044080d10050042c0500e458004041c0440d003031804450203103400c0019100c000042d060b811058910b00e6032409800e0940049903050340c1c0c0e01c64580c0300b01180c09014086201e040c00c2c021200115a00c5016209944540e1244028020028010742c100080020742c14140c455155040002d0624045041c0000b83c403031103181d500b45c5c8891420411212002801000d00050490305008a5406009503003010190365401c90030103409420503d018100b0b00100d000d0752940c81e0842c02c848150f00b030106160087d0b080d441c0c18049550405410440044104442901c0001c1d2098004009440104280c1100d040c0402040c1c403003c4000e02034060319061009159000410481e07440310301c0004c0d8490301d8a000107039035920f0280710070880e6410000024011a0049a849500c10409854203a02403243da49580205804c1d4000a00c124076000d09000350340ea0102d000e0480a405900400b80c1401c0b83c0006401422001d5980090740d10001e9404200481c8800071455814 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 924764037 1250 924762787 924762799
    0xa0f0201270311010215070f2a06140a02162d0b06010e09060112050c0408070807090510030f0b25030c02060a1e020702031c08070e0405070818070302 66
    0x42c90340740403144050302c00e803514014801ca012a641140040040c24021000d07074484107100c01c5504801d84000a02a2105002000382a038a22180006e101750310107503031180301c1c0002c142d49075812a44005002400810030207105000901e9401c601c480705c48141904460050f40c6010154540d8094510100b94682200603810b60340081044c0f42c150f15014802c242c03030f4020300d091460203004040b0011249280062900340c0f00b00ca55002c02d42c0701c282c110390f0100555182c503480d03143c481d2500c100c070f512038002544480000c0160a21510600c0d4010400c102c00103951440c5894049503412110b101421101c640000320b5032a2404010780e070241c54170b09507400d1004950440160003840e039581400050300860b00020b6101e00c0b68442c000005920394195900c00213845c90450082d084500c0803601481511800d030b900075040907040300d2551865075462442d02e41101c00070010b034002c4010b01d0140f0300701024401c11030b8229081c1c90388407800c4070b900201c1000c0d100c556880d00314641d1020350021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 924765287 1250 924764037 924764039
    0xc0616020a030803100e04020117040f023d02030438070203011826070f0b22030804060c050909090601080111180108040302030d05090115080a0f020127 67
    0x40f82da0059441858205d08541c03226558541c03100002000303e800074001561942120a9901b280039882d070000d00031290029240c00769408100c2d036540d400280c40c0c0c221419117458042e1038410b0201902c1d070705074a440d07038140c05402201941d640a54061a01a80350403140c18110200f00754460042161a440003186100e1740c030900c40316581700803002e0b4025400e204010200522010409a1301c56010170f40032a08106450902e1a00c02c00c1d1540c2103a4000400007800411080901c10300b03024018140d010035400c04880c02c0310300386600b00159081141c0900300070f01003904060b000d03a000340c02280c0420030304003100007102c0d01d2203030714030290f4070401d100103018034080001003040c1a6040c50303000b08a4042220300611403409107400d2141201e00c40b51010260794401c541045c1c20920900443e400c1c504407145120a0b9102214501003aa6640d045001044d00819460b40145042e00282c001c19855480b41d400f0b031455040040d040c00501036540c00180b000030a402a407295100f41440c600b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 924766537 1250 924765287 924765293
    0x190603060902011202270307030b04210c0302070603152d050613090b01020f1c0e0406260f070305071a0f04030f020f040c050c06180c0616020a03 64
    0x5001e80c5400307a0003d400302006a01144aa2080b20030020a500c6040a03481c0c1c01c481104030301d081c81a100303406003d002e0000001036907209840d800f07140300b2010303140b40040c54814584003542d5454407108002940003408042034012845200707550341450003044e46001e200c5074038904026584000c007540c5080019824070108030b1a03803013a00132044186105195074004008850003401500c48082210000070071502f105540103804494060040c0d42019000306a401c0c140410000070204040d41d03101d496010b10741c46518004614000c43e0200001400d00101c81e0750f440c00c02045810741c1c61404000421900104035a0706041d1402084840a580343d161207900c0d2415849aa01c1e8915540030300a0403411480c02e07142d480345032000142c2854699100d0040ea440640310990b0400c59181e120041e9031160b00403420f00d402951a010358900d10740c441a46440303001402404950a946000281008081002005c8035000c44406031103401f1a52584000558910000c3d40200300315000020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 924767787 1250 924766537 924766541
    0x302010e010b0301020f0417151e0901180303051e070e040608010216080703090807090e0d03090201021e0331060206011d041b0b0c010b0a0b0f0319060306 68
    0x4503100c14000d011456891052500307070b00440028125000060000388010314480e08045890307421402141c8880030030001c003c0200009841c039000d21b0000034411902203000c16610741c0c101c1c00141c000c201781a540240f0080405800e0030090801d0380391400709215106a00002c0d080540080c0c0c081c1080c200b081c0040d250201d0031b00d089015070700b040c3c0002901281031013524110310f1214100541c8200559030644039a0040c1411014001c50b4040491072038000c00210f03000d40300004000a4015101d122286480d14892910b0301b05070410703140c940142d038081040d454440c0c0c1c045034510181e000458a50560044c00256400709003424100b0501c0182c8101416000e14102e800c240b0740d9882d00c170103d07120b0740b0900505220401e00c0703c0d0494051000b0801a070300030300641109240c40d4070500d0000c030108030b40c3c0c800c0004400c0880e644921080030702c203051030380c3c000301c82c400c00702d91078000c81c41c03914000c8032400e000030795021002071844071003040d842c400c800025800b00b00301c07a101e03d06100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 924769037 1250 924767787 924767801
    0x608070b342406080f121c02041206062102061b010212040212030a050f071712100803040e0a0905150132010531060903140d210612030201 61
    0x850824800003003640000c244c1900440040002e00345245070200e041c0c08603400424200441f45104480c40107031203091020740007074142c0d549450140011814240c00351012034000e488119a100421070111600e0559452180d42c19901903450346626201d1640d00d00e9a6148a0f842d5400081d200384022044d001492169200b00c800200506d02006903c2c3d5900600490f0340200b201004950700012801000d0014640320b82110750980c50381950b540019009840541e046003005000c2c000c43d103088641d018090015640154207062411002003c140005070144101c196298250001d20006104065007440ca6442d82c60b12960750b141181c1d040f06c40300001143c02c48080c003140726104880d03114201210780594405040060340c4c40340011407000707a2080e400201d180c0307451a00340040c00f020712006082984440c0d1354640740d401c0142100c20130140080b62604600c1c040101181c028400b102406542c4004000307031081a68032000421031500202c00540080f43c44908160341500800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 924770287 1250 924769037 924769103
    0x210021e0a0b0c030708010311031009030513270213051906030c08060d020127080714030c0a030b1b0f03190504020f01030c0504090504060608070b34 66
    0x301960340c1e000c00f00400c2d00054654000181415004101203000c1030903038003030b0201c01001d43e03e41810f442c070f24400319641c4c5003080340412800304d40140032128108400c4010007115010407999102c4000e105282c0a000111180c040d41c08580c42091001c900488d002504002d005040008006d0080c882800c22920460001905000c02c00c84a244604011800b680001d401214950400c2c0c2c019100b0084000c4d00c80d4a00b224031052842030300e204007a102c0100740c0c1c03902420101c1d007042c82c140c1c103502001e0890380c0680c0c00300240145546625090400704c075084484903605407a039500f9120022810301028a0407840828504500c1150b0070045010328203004c2074040240c581c442c0001a64002ca8010754045803140c040e00840d40a508600d0200c407481c030703080349401d8848903a43d00306c44040e6000e60791070395030301014001490300b008908040c155442019045c0642d0043d400402a070740082400001d14480301800859154024148690b03807107401034456807101e4141031040c5505030150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 924771537 1250 924770287 924770303
    0x162102040e07030c060c0b0105010c0303090b1501120603050c010522090b0a0e0912090a051801060801080f0705010c020136051c080a0215070f020d050301120210021e0a 74
    0x1205d0f802408100c40150340b00c01c00300e020703a180400640b0705008556090b001e050b1501c04281c0021482c10000380300b01c491b4428049140d201c0070006250800c0d4400303520b805c52a2020501c00302d400007580010b204406d2a000356030300084a407900300040b1408000c15008800100031407081195000180c14003001c1c0c60329070b140395544189034080c29094480c0109504885a44c8404500c644000c040c1071901a1840500c25a11800724000380303885040c4840940c184401032100340d51002d074039401002d5940040030759101c0656407580790010b510510f410b000150b041101164010030440444411000e0000380324000020a2103007108401050340c400108020301103420328001184440c003486119102122508980d0788580a80c010044c0c03509600c105c05c00740940050450006100d2504c030360b104503c2d1042c40390081d1410030414104014000207100500c26034110600180142e030301117841c031045090001090f810210f02c3c420002d0520500000080904070010300c1342c80940c452014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 924772787 1250 924771537 924771539
    0x17010209030c040902090403121d1018050712050111180307060f120b1903080d0b04200717160b0a0c08041b05031f050603162102040e07030c 62
    0x80108030754010f013000354480c504c0703804100400c3c41409404d80c040907000b0001440d1000791211448001c189041c007980368001205502d500c5503500400c640140e54400d14560031050f81c0d0b03001d48a02c13031400341a010a08100c00c590511900f5044201200581700b065640c584800e00303a1b44400314050300e414001c0c8135001e00020458815900041c1c400d80c96901c0302820340c46414070402074010509295803104900d220351841900c041c05500c01035103d14078003580c5010014a0300d09031070383e9044243c812403400b081001e0000c40190f290811103401450240c0d0384825103013100c80003080080d00099802c01007502078084a6500d0f852602600964510a0550310b080074601a2040401c101c00020540d001090002d140741507144002d104001c0d81a0102e6241c00c0864034011099840f0401010b640701c2c0041e0102c81da02c9003680101065000d480100500d001304180407841c0d1241c241c05050f5050041c0254040c2c4681501e81607008100b88402800c11b0340c4107946030802d02060ba140403071820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 924774037 1250 924772787 924772789
    0x702010b131b0206070f0509150a030203010302090c03060a0608070c0507030302070501121118010504080a03030f0e0105040b0c030a09020d061a0a06230f0c010c0206011d01150917010209030c 84
    0x3c4e16445054a90345002d00e691816030115480d0300031007040d03500025101806910f10746284054848015559001601d940c590300400031051005416a900c03000100140601074035600d020390240c03a01d509100425807140c9004980e11404a40302410381e0049400101c209940030442d01c0469209030394601088142a8160046640040c4480000101006400e20080514107400d02030f400c1418001d00f0143c4c1e82d01100d0814a40360800c40001e40d592081d500c000e0091300c2030214280c0004001c10a61034103584e611124070000c1c082c00c00301346000c400261010342c070344c120b508800e5020740320150200e250318107040600300f0106448140c001ca014143d950781041c18010085484655441e41c0c144010815001c5e00c1802003604c1c040c650080010350011880007001f040d03980f200300c00001e28440048030082c140312040c2c1042c1000c5040011000c01c10b0100760505065070100d44900340c03111010a802d9075a11050b502c582050b041e0f41840c042c03034080650103040c520301c2c141c050745c08082c5050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 924775287 1250 924774037 924774043
    0xc011a010e0a03021302072a090b0310151203020609010e0604080301030b150904030c0218010b12090a301407030f030e01240e09030901080702010b131b02 68
    0x5804682c00c104040c0c410805890709000c0304500409865006180c210907031a0580c1440248c044403400c80d0000e281179000d140c10480c3c40740207140a54040040e1390305d103030001c0e80700ca405071109074115440300c40012005801e00400d400900380044d211070240359600c1c0107501c400e0111180f01c0e0381e519004010003210300114440c1d104903404811180780d6070841e9600c084012015100d19000d071103105480001d500c8905250340101d000383ca5090b000e40e418070411102c0107004000007025069140100102903285040d10a1000b100880d2101c0f03549040c21a85444455038014110541601844031014184003001c160258801c8800c0d100d030206a80c103807110504130b03419001004c4100301d400702003441001c2d900c6480c056854042030800e030b0030300a1400d403034944500308080c0c0d00c868405042c10781c0e21400300c8000d001d980149003081c80c1c070403050743d1607000b00b446c1e89044c44004c1c00020f080d0391003075200da110694010107292550546c080084002c207206d10f514241c0c0302e0000141400c481c000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 924776537 1250 924775287 924775307
    0xe010e01060f0f020304030c0e0103060c0f0801150203070f1a0f0606030403080601030e060403030e0c271003140a12020319032403052d060f0c0c030c011a01 69
    0x207849800d116102c00340c08030b5040c0f0074540440118002403102100080000704803400030a20300d02c05503440e5045041a508440c140b6441005204054520300d60350354011240318115055011f05549002c801c0002740e040d403160b2180248050400c0c5d404404100381d120040b818808462170654040d507030f502e000d03000310000b0b446291f03100a051000500013440f400005501840616000c500b0040610405140450907a0110f0209440384c0d42c0c0e2211800402c0810564901214440d82c0212100c00d82c0004071020170701c544884400340b00042162101c4003151000f541d100310117901407103183e0340703241d01d0300780215040703521944826107400418800402e495030a00c8141d0009000c0c8172000055000303040d0034011581e003655401540e560344622500709802180200098080c0300312003c18920100d100d0a402d0b4201d102220141ca42c02c100014002d5002d54800c500c0c0324552910344145480f80601c000700a81c6100c0001c00307180724030041d0031006a484909401f1a420381c00040151488590 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 924777787 1250 924776537 924776549
    0x20d0b0d08070f02040609090b0405010b0a060c080a030219050901120c081302030c061809090a0302120f07060f1e0b1e1f02330c0a09090c02070e010e01 67
    0x4180000c5011071062403c3c141541d10007480010741c260396114801c140d45041d01c0944400200d80104804e1201c28040c141d150b07001150b130510043c1c02c01030090f081c00381c2104094005080070401540c454002e60440e2607040310030740c45080b240b812070b000803c958807211443d400555851030341c0900c034070103019091200c6c0b12034840c51510340d0b0b034101841181c42c2048ac1a03030b145c410582d242103241c581c00006c02103125460004903144014409210341042e0103000c4001980c04901d82402199000c100101c000114242103a80c450b00d0703c485004500600c4000707810302d483d061401e00d03442020b1740600c44e092503401889100f908200c0d402c0301200d0f408407485810042e08000c0c00681803415111140010000b4602c07000e00c9040d01251010540e010300100160344000054224031f44211781301c2d8048031000c409540c40c88040954060740710805403950b1a0361101003104884d00e400b0790841c1e0060401c080c820040300d03585c1800256036140d84c0c07059135041c80010001045011401001605940c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 924779037 1250 924777787 924777803
    0x218071706090a0f0b1306030615060503070507030e03120c060601021f0b031014010e130c030215190906030e070b03150d0c03030e0111060f010b0310030510020d0b0d 73
    0x2076a00c80d02800f0b06211507130004640e940742140c000740c1e96501c1b0042d036040480280004d00ca408c51070b104045072040544400c802c0c1041404102c1e046d404000c40c0e0f40000140f03001a260207251800351218504102c07450341c140119034000a50080001c05800424458401c40340306858a00c0103a0710707191201c1c0c0c1070783c11a086840310000e64000d0380081001e46806004c44036400341d01c8054404840000841c0b00b080c182000041000b40c000c089080d4201880381c11481002e403096480c100561000d101c000d015052444020307000840321810754800490645119151201700c880c01400402e950144401107454082c106404900c0042e000058070300c0108141c0c40c40d10744c0002c8e02000c030603100340c01358440003005403803000600504048000b50700c02c1e01c3d98210341598600140034104a0301d05490241d101310308000c200003581010504680c15528030a0350f0b030312440300701c07072050400d900050068800c0b141c200d404cd41440d4014030000c43e95500410583c0505800c00c07031026026840582014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 924780287 1250 924779037 924779041
    0x207020303120a0c2d030e070e010b09011701140d030c05060a0e120a021b030c0303070614071b150b030a113102031012030206070905120d0507050109021807170609 72
    0x179001b5440815a514406c2c201c46e2480e55031601d880308842d09030400d01d8820008182c40105503003003082c204c40100311200e020030540c1003022100b0700d452070145051040c03010b144c480c0141405658121145030300002610038a10b0a560030300054420b40c198100c491240384c0a96504148070015580b0f58807040d03002d4248034656660494695900400e019494007426801d03c2e91650104028a0024400c440c081b0303244c070000e200d40442d000c0050104043c401503940c03403003e0b003000d0010a0b66030b07a40950003416420180522000030039006031010b07018841c80508205115500d9803c41090b4000c5681c0304201d4410340000c10489102c00541c020b0000350a00300e2224041074015580c1f246140c160202c03141c0e5501c440300a21900103a00354050381080040c03000c80e07070340500c00c5e0000d003030180c038558400750100b04599603920317415088100b04100403880004101c4203401050416400518142080a940e1614504000207070340082c089202c030090490801501c0381c0044c03207500c008182032030035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 924781537 1250 924780287 924780377
    0x3090b031e2a0717040f0801060f12030518042c0c0d030f0c050109080d15050a061d060d0209030616021c120c03020918040203070303030207020303120a0c 68
    0x56040f403c4201e50145252054001d40320749000075100030300c408103c3c80c1e07071075281c4100542158460341105548180c001d200384074003030848190803080c42c3c0c14a271881d5541014030000c0e01010a280314130740e03c541402206001aa08500f000000c0106000c1e25200f003d24610042ea80e0064180100d030401c0c800070b1a88007081c0900c0c1d261810304411705001e040e140040c1c1d10942110b041074401c0751070754030101e00c0d1455006a40710307042c2840b140c040f01d0303400c1d20300300000581d040e4034a22900d4100050745440040c07450b1074900b500d503100b1000d00041e444200d4240000040e400c40880c04d4040c4c400ca10003d101a4002c402c0e6410b401556005480070303068a9036204141c10605405100380061010a0020b400f420710480102ca01640c0c0c1c010b0300d41c59040100540c0c6500751340c080d00312203895402d0001503900894010100c0703a04d4100183d44581d54408070303081d801585250348010002c50300304110850513400c180158421a501c1c0040307044003401d01341004130f2100741043da40c004450b8403180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 924782787 1250 924781537 924781621
    0x1002061b070c0b1c05070507020d110a0314060a0b1509310903020f0706020312070e030a08030103170414040f0b04150302030d09060c060903090b031e 66
    0x2a50041820108843e1569401c0341103501c0801d200340c2201d4602d611a02c1044507110300d9822403040d2401501e0440d0301c0c0c00143c2e8500c403800740548a151140c1103aa0780350780e076041d03900096a01030071000d1404c520404036601da00040322050030103424684691403c0c40c00201055480580740c500a040c840d4040078084101d064112182800001b288036128405901c940c402c0f03029035090300819180c5140c40d000342455290301044006900c040c006010050300401902c45c0b402840444041d0703603407074100481300c141c08640c245030103002d44009142841000c40041d0705880c05100300c004d41080744200d0010307600c02e51003980401c4d170703840080d04403c0c90590030044040c8041000403808460f4a8005002c07925005a40d90614030104401c0086050900c4502101d100c80d00300761300c4d4180740c030070003034060301036410000c01840e81cad43d0700401014080c4140e81c018100300d07910652285005888031203030b48001960414440c40b140d001549001c840078100e5552201e07442080c040200821034803003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 924784037 1250 924782787 924782797
    0xa0f1b0513020315040218030c04021303022404080d0912021e0f03060108010b090c07020102061b04030803100512011a0d0501200304020a06032a031401141002061b 72
    0x1a803584d07140750049240d0b42c2d800a405000c25204000401030418030425242c1525922524019070050290343d80541e51030002100302e9030180e501c0981c427032a034915003902c00450102081075900c007040c082070348040003400348901e15240c1c846002981d2100012581c010300302c0c030000d512002145e961480d801d100e80d506d21120801170700c3d482c5191640000a0300341003090700106910382d5030b240750300c000d494410b40d070a8010000c0caa8242c50840281c00007034903460010820381e44c40505002c046d80c00c0280c04202d800071030300180d440d070b01ca04002615134803044203071185910569080480710038090313042c071514400340304840000c100c560b1018140520101f07090b506aa41b03550f034480364070740c0c0c00000708511284807043ca80207540c0c2c64140f04021284210fa0422410146801c900941440304032500d6803248503003802d401400d11178403074110017070314249858800d1590304100001c0c0c410011170303103903021010483d140c2c0d8100c40c0205040366a10400c4030803454403d55040060b0b5005c0000006103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 924785287 1250 924784037 924784051
    0x111204080607350a140f0103330b150c0c0f03162907050709050c09030f0c04061d01140105070f0c0e1602031909080a0f1b05130203 58
    0xc07890100702000503c003480c0c00155103412040480c200180700b0211321036000004401400c0b8141410411000480c440d814000108400010200048444140b0340b0b0303048440c2c0c0d0240030141c510f0144211030090700703c4510b840c1c011607401086901c844048410344440b000d68a008180074030030303c42000307042c6c4107024103c0e4240c050344120701e40310482c49405202078260340000303000e40c0e45610986031640d0103c030003c8041c94010702002c4005480441c83d10212040501c000c03c05e600c0300d2800c00514455158895854400c3c0308079810203030f00118042e01340410841d400c0101d50364035007000180c00001d4082c180010b0b5424014864841c5080c0d074103450368010b240044c200401681c401c00c052082410588100040d20300c00c00070400b0b51601103a0010b022000104002801c0c4d070060366a00441e04103151b48440814007090313152080d51040700400861081b40e180d03148506001d1800285d5900c15151701e80c0e03424841442804280b22071084803000b800740d0100c8298880000025040901a0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 924786537 1250 924785287 924785327
    0xd0f0f090f0222020703030b1002070501050d0213090c08070e010503071b0f06050108030d2304081c24090608060402010f1b210309020a1403030d020a111204080607 72
    0x90750804041c4060b05417140f19031800101400c010040050540001145100715800100300b4401c0343da00500341c0d5040e4800400250300ca8070402411034411219030032010071140f500d8060404140e10546150040c890303074451200c1d101380c0708011a803900c803c44c0e422000c204003900c030050004041c90100f079080d001d024860301c0305000360754000580d0000c0c0d002143c42c0d0b0000c03c121000c151588689508400b503181a480304011101d81902c6450000b0310280200d100400c200d41050010b80042c030403504491001c001840d54440c0780180c000c4076009208581c1031103103011803134101c0c61007000c0c2070303412241c0104165a034a900448503510840130708030070064010019081e101003030203140807680c441d00c01c08281d200c041c01900d1818505110107810036040c120010f003d6100c1a000c4c0e415200400503402c0761841d4a00402e2440c170403005198056031000500c280042e0b0301c1040c0302528031101c41940c0c5402039401e07407840e490103039018104c1c09030001c50100d52281e00400c400c100044104c455 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 924787787 1250 924786537 924786589
    0x50d05030c0106030c0303110703110411190810051203030a15030f050606090906060d1b0810060e071418041814060a092a0b0d0f0f090f02 61
    0x20782400d40d07030941c0c4200c601c090303444130034010190440e0720344107003c6910000708641840d50322607900114202903c140682e40c0c500c100c3c1000e1151100700c40440c82c04c1000c0103c10150300c0401400d60108440c042d40901c110b1402183c0c5141943c130714120b0520355001941503407a145a05801804100300030260320855046c0000010280e00030019000d029030003812041c070f480d4051180e001c00041040d00e994002104003c6207131b4990341030031980f41c2c0051069001104102400f6001a100d400001c0c4510a020340504107400300c0e00030606940c07207d00300109945800c1800c3e20561101555135807114030a011041c43c4004110042448540090000c1184218009010380d840ba03a03d2040c0c48440000c040600b00c580708205543d0000b403180c42c04c1012600b00c5c1c44680130783e039196100620024208810500c41c01c0d0001c0582c01900c054451035548040d250030321801840480300441c483d134200405040310720558800c40160541040802680d1112503080140135078400e8046d036446458619 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 924789037 1250 924787787 924787807
    0x10120c1103190e030a050120030106021e03040b040f0f1a03010902030a020f070b0f07020606180a020408010e0304035d0302070c05030705180910090303020715090804050d0503 77
    0x5e14682c0d0080000103680081c1c801d040c1d0300410034070310841100e0701c100b00400401c3c0d80060700c00e40038070801d14180e6403040c800d00703098214032070350f030024012000100d4041040400071801401700c03407042031890450340d038405492403c07120610800e0614081032004118040e010380066500c1044020010f107801804400066507030003c00040c1d82c0c00106008010112440000503a0008100e00042c83c0324030308440040d10383c030740c000d101c0a04500124003050441c0c3c0c02350141e0780601004002480003450021030341da983e421034030040d18100c4140c4101e0000c0d0b100c000c4800d10b0350b07000c01010782c0003040706801a403640e10030110711000b03025401004d071986001e200c004460412642c2d00940c3c0c0b0101d5042c580d200f0101a0401842508640c208100b19a01e0100181075180c2105885096503034180542e41020764011800c000301d820801d050040650503801004802d10901880241c02a194a41c0080703482d9450001c01200c0108802c5c0721901e4128841144507100c1d8003100c1c5000070140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 924790287 1250 924789037 924789043
    0x91b0307030f1401140d03110105090606030d0f051b0f060c19090803160f05031201060306061b060b0a050a0f06271505070210120c1103190e03 63
    0xa51400020b030b520034512080b10b0680c001c856140ca0114180241e95041c00d56050100121031001849541a040300d8020540590943e189040c0c6d000020071252038540c0b00b641d1914000c4403103a00c2030040304040f150075030080381030851120030781da285801c01000c072200f0102c0960540b1010564403e099080f900e003c0b00300005403040c4596a4825142c0d03100b0b905154115000b40c0c015170900c4040942480766100000641300c1030440c605040481150900f44013075400c0c0d14040241c0381e404000385118004541c0a051412030700c103982d08200ca40d81c9c991049440c00e446102c100340141c1e6000e480ea02184541d003003100f04034001000c0e080c0300c82d0b1700c0d03000494004840d0300c1070740c1000140c01c0810102c4d400c81182d07030a8003644206212041440c0c0601100365649018100b07109030f066144001c5103114401b65201c07154007609414150388040390180c180418103c541c090281070070312441c0f003a0300c1001d4481e0390005c2e1800450400200005400074601c0c146070312030800c540d81407036900c165410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 924791537 1250 924790287 924790291
    0xe0a0e030c070f0506070302031608090901080a020f0409051005040503040b0d06030c050d030c061e050702060906090d0f050d091a01090605040207121b0b070f230306091b03 76
    0x50740100039039460074480c1c15000781c80c0c0c0e203c07500c146414810480403980100441d03031400b10105902c1488141c51400881501900340c169801502c0040040b170000000550381e084503008961750070403010110304000603140031a000500c2c0ea0040304040c0d10140c4280c0010f5049880350302a40d04094305d4407440c04240c6c00c81820501241c0c5c50b50070420a000c610035001002e010140c1f002c40200d07641c0d40740902442c90051005007411f503107107126001428006070241d640b04010b0414000340c1001d400003544ca00c01600c6c01007440c003400d8003064000c217000070402c2646040781c480c551032481c80740f821b6805801100d0004601a00c0308058000605041082c00c01005001140302c12075060140c1201219119005103010368410480307080820280104200f07004254900023000740c0c1c040800601d95055008000c2c0036100c441c05002c2c03c1c60b088844400b2464140e030f10300c505103005820903100110003842c40345565000708082019402c104100c00e5121030000350450032010300134855000ba42c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 924792787 1250 924791537 924791557
    0x50c120a02090109050912070f0f0c180506011d0a1d010305060a0b011b020f0a030b09010b031207120908060705040f140306011413020f04030203250e0a0e03 69
    0x3003160038210301c0c101c10390740d000d084040001c2045190420f071081c0d4601620540ca80916800f042c1907080103407018101600c5503200d00609014051460003031008a0300e0f010310800d01c512881c3e207038032181d21841102e00c202016920016004035003005604001081d54680e030300401c1400b804170b001100310310003400c5480d0045103905250301d5402e08600744040500031488107400d048031703612542e92005c0c00c00c01c5403c80d020480200301c03440c400038141c0031124036180e0308001484000800c0c072500c0400240318a03030210091024410860826880e4000c515240404c2501130260101094440c42030800c04161424246105d903154804a45400401c0303a0b0040010000076041c8240c8208685083c01071108240c6060744e01c101d10300007501c501050007081c842560740703101400f05654100d90700440f043c64802c21561082001a24226a880b50005901038401c45400d1000c030075845940214400e200c00c6009c6100c1d040c10441c1200b850081c00c40300714283c440301e0030045c0c010140010944004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 924794037 1250 924792787 924792793
    0x10b0306090d0f08130201120f050a140a06050105030c09041d0a0201030605060f12071b0308010e010b091e010e0a091d071809051e0601090f0203010b16050c12 70
    0x140c0c07a000206145a0346803d0010004a0014800052502060300c000d141d8242488469545004018001481082030038180303075080034244004c04010ba40042c0d540aa82526030bd404c2c0c0c2d41d4017009040c0d41303407440b5560000e2000c000052039006100007518109100401c046504444111802c0c032000d941c0505034050b80080c800b000841da05880b445004010650b0000d0a1074648000c8540394007461600000e500e0310030300000d604900c504000144525a0400e0000c1000582801008000c0c240242004c1140702000800d508801105580400d170005008a1b030441d101c3c1c4e5540341c40080301c2d1606060000002d0001150b6036000784000107000c45e2600025140130001010030410820fa60041c01904800c0c0b00703025005000304c0100ca5401d0712200030500400f14608240b40071140101c01340014130030200c1014243c0f01165007412550120300c14000c5103154072088080788800e120380440100104507404200b040d607014a02c00c01d00a07404d46a01b2200000415605003501c100ca2a541d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 924795287 1250 924794037 924794053
    0x1a07050f030f040e130b06040f0603080408030d050f0115140904051923060f03030906130e0903130e1e16110a11010507020a092405120a0b09010b030609 67
    0x440f00303607101a88a042c5d849010340e00401ea48908102210281000d0f020b81d42704c0b10545408909078202034000d542c031090040d52540d0b00c8000548030b400c810140c00d0741c02d04000220700601c0c95082d07014103882500603556000661070710242e440150044140035070010510036580243d42d1031040c0c1e0300c600724840200c500241c0801f100000c481c43c0501e100000f02c50a803810440e00c619400c655404201990312481ca9000d1500103441d5004460b41c440d07000c100040d001a0078400003101e001143e281b0f40314a00c2d1611880d88031622401130070b5003505060318441007000140e0080b201150004850078001c9482000d2846243d00018110348811181031082c69486110380d0161781300600d040c4000c060301ca550035a64400090b9102c42004504010340844c140d8150354880d4000c038010248400c08000d484520b80c2296140500741c80c00d95281100d034200082c00b410002848884c600c1024007810803581c00750b07140040800c0290102149660392440b02d2900e440030031203d030003011a040104218 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 924796537 1250 924795287 924795299
    0x61639030801120b01050f01090905180d020f1b0402091e01120b06041811030f06010905121e01061e090e03070302031209150c030f010f1a07050f030f04 67
    0x29200c1039100e4850700c43c0038070310440455413007045641503c004540341d804102d2030b940100c0da44001904070020851500050020002a107421001e80c0325041043d100841242102a601c40c00c044021845a4000d8100300d480c824201e4200d6004040080006003402c1100001c2061014000e200c05000e00c0084694642503030000444110f400c401041844a0125100413803c030b4040c912070301c0c1c4843d540014514001005800c01c0860440b109181a203134076144071481040c0d0b0b400c0c0c8089012860010002c216800c1890381c0e18011200000100201d0b407880ca840b00c0b80c083c04a040c0e034100c0d561084081011540403481c5070110041c1c42c10301c0100b80c20b00028000b21440045000c05c2a8003c00440c4000ba80120a86854030000000c43c00690f03103840e20340b42094100e040039120144880200120b00364a030001d10b0050301c0c00e01d0f20401c0c681c1c03680c094202e00ca809000703080c0510070001c8a41c12240000d001030031828800c500383c400012882c2000d500c1c41d000b801080c01da84c50041414004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 924797787 1250 924796537 924796547
    0xd2309030703151e1503170403060504150501060309200307031202010c0e0604080a020607060906050c07150c0801151404080d1812060b030c0a03121106163903 70
    0x201d001044000c01072041c503884030030300181c07486c07000400308000301e501c001c180c80b040c8043e10000c43d0400c2051000b480d083c6024460100a40d15495069181200100b034403446072103404030705035001e03213108854100e200b40c4850284d02d0f2482e045e40340c4100705d000310005802c83d010704020341d2280c00114a4640140002d07005c5401010003602a41c42400100800600000d800d0b00aa406580882d9500c2e03080c2020030191880d800094400750400c4188000604035000034403225004284400d05a011f000c0d5200c2600d20300c03810040042d944c0300c014004c8800ca240140030780300103400d11600744000c2203180384554202ea0312400080e000850f035040c0c07407504903404a4050303020606400f8140c1c245440002585513140d00603200383c1e901d941c5241b050710200540c1c1c4054100802e42c84080360b492034007103200d03000400702600050907203500b070000801c00204140244403895040100303454810084541c0b840e80e580008062022104040102449044540c04141c0301c1d4001c45101c1039504000d09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 924799037 1250 924797787 924797831
    0x424020310120f030e0312120105090f0f071b050106120c0f060f1d0d11120304080c041a09011206110a020a0311010608030d05090d230903070315 64
    0x6200100c2c03412010008444070702c520f00e000da1504048a10014480110f49010300504460400e807800241039640b94400348013545c101c40c1c04481013a40c560718400140c02031001604c042e000301e207034100843c00303a50141c0030050b0415030100401a5403909070701c54500390764113580500e102a040c0005c41050185400c03400019100d188004583c1c0d038a81400100101c1007084044100103070980754aa0304401e2410000014000030909080c0c00a6801c0404459005c140990b20800b0000c08004071003001000b901d00b02e49106002c0c11510111500b404060840320b03800000080143d143d500382584c8464545010300a15140700e01c00c149a45855421500c1c418100c1040d44010701000074425400254000c50951525210141041c0e4010b51405032a064002c0041030202142c4011300040e15030000b2b100d000d1103c21105000160541034450b4090030441580483c0854030790059990108003d1004000c082c00b01d030b440759078030740740d07040304e07089a03121600441e40701c0b107409108510010600e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 924800287 1250 924799037 924799049
    0x100e3c0103022a16060206070f0f0518120102030907030b070905090630010e0c040b06070f0f0203031602041b0503070c1704030807030f0801050609090424020310 71
    0x40c500b111100442648901501408402c00c2900c2c0b403038141c42c4003e01600c80c06130703000c040e655052a01c90701c0c042c1d05c1d20b5007110a0b40005a146842c1980140309501ea101c201c80e050703d52506d0001030600742d072102087e01442035040326940d0900b86914030244000c510a01a20001d0700c419400c5240070105400041c10001c100400000107008540d14590450b40006040307900e5121204801d07401c90800c0d032140a160500c040346400e000e034034201908501141c8040034140c0741c8400c0008100400c031031700074600d00e81002081c411100000c2c402d600407003015008549a03c04c400306540024915070041000c8020f03100545d41100841c209405400304140003461402210000d003c0000c1550200034005001c000e20703402028140404420310b04283c000a01440765925200c2c2000742095020320422000038014544103500103207d000402e05035000140601d1400c050303e801c0004510b000b0f0010b07582e90021801ea0400c005100003900d0f11031100311005a220304d000785800104011990044e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 924801537 1250 924800287 924800291
    0x3040b07121b0203060c0d0b040f060f120c0b070305070b16090b072a080604050a0b102d080109060504170c06190902030f16090902100e3c0103 63
    0x2c1005035800b04030545d01c4500b0001c0c5940b1421051007103409410003100c0c01e03170041d151030300000200030300b900410103a070340205c42c021480f035582c0e10144080a0381d00019020700e0318414180001e01c500380052042d203002e03182c4181040d100703442da43c00741c600c280c03041103040c24000c001d001d1083e000448503004041030054581002e03c240c4034100040040d804c03400250800e2050329041f02070100414014140d10f034102d075044c1c9040e1030503982d60308018106551610703000300010707481320441d1420380c262821500c15890702c05d26100e4101342c081c0381c0340006250040404001c62820024420107203998000c003008a10390902d4200f0f1004035004801c64400d142c010403c4640d40540018201e13045501d41020584031000dc034814001016062070080d454000d00074031805050000441e05420214010344840c020396480640301140c100b0040250000b0b40178036105c2945000b1220b1389480c18001d4120446101200c005102c64071010b100c0340303140c24010a868041035170a0052039007a070020300701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 924802787 1250 924801537 924801587
    0x2040303020c100516081b0703031416140a0212060c040302090c0904090503030f090a0f0210021c030f0e242d0114240c03040b0712 58
    0x2921100d20012507070150b09200e03000403140344554200c2d210350707000d003807038004100c0581340086e80740d030110100c00111540c81207240040200420040c045036419112420303445c0962040381c071a030704020502c03c4403403800382581d00468030000703001440c10001c40141c5030101d050b10400c0441c4032040d90b030040a5015008211291914000b02c0b002d80c0d8040720040c440303666054000f00c0501c40c4083c819046803c1200100800600001550280f81c5404481c0da2960f100004c8590315060004040c00300e40042d41e507203001d03041102e0141c03805070091041d103c100d03940040102c0e2100e001c2500d1400a40d48012040083c80148210507961a0901c0a480d115038516080703006104000d40b0503201076408801315290b40080c1a000c006400080421105001000300c14082d80f402403050300344082c4020b920465601c1d12104180a803407007180d000c040a84100e45113072558110a44e2040c2c188400c11000c03034031400c0300010f032815600c540c160400c840d0902c0d80042c012401786884800c20030b50144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 924804037 1250 924802787 924802793
    0x5070e011715012a0501050103021c0503030c09060c01061707080c06030103032607211803030e0a050a06020706110421020105091e040515011d15030109020c0d03020403 74
    0x2d080c02d401c2c40901c0c1001d024040030301c0035124100c15403144400031880780d441c5000c0080c1900003604980c0226505d40c0751020404140c02000f075000c400030519001000050100d0511102810543c5006841d290501c3d0450903201c1c2110300c0ca82116441450100100300c900c1c90800050340509800c6020340303170036203a9101140050006000003014441071014124020746868210707200302c00032402d480d4141c1002400034084018030560000070403140c9a0724520400540210071440e004035240d014580c03010b0b1000c50080c64070050400c0e0a01035140c402e404584200070042e400c07406100016034665003403510000300d070340d5014850702c4404d090008101c0100d800d0500801180c3c80c04c110341d80540c0c1840100c0d102d100e141c200d1079112100064030714004410103c41c410540007079030204415200d4100c0300c42d08448031200c1034002851148000004044181ca2920950010780396280056034403c901945400903081560700580c081800c07480c1c540c003008060160b1040c0e09085103480e055403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 924805287 1250 924804037 924804061
    0x30807060f092f1503070c0503041707060c030c030e0a05130b0306010e1006110309090103030e011211070f060b0d140d080106051207230903070f0510080405010209030105070e0117 79
    0x41c00d0140c44c80700c0840010392a6001e459006402c55005050703d035103d0729060030f50010103110400400c184200003011076681d01071085800c4141c0c141e161481c0c8500d43d40e41c01c40e01c2500314100d9a81140c0080c2001515403140002400580c071000000301d0340f10b4485041c5413034400141e21007420f000c0c0d01014401443c1d40e080b00740e01912101d18009e841c5511407107500b45944035200c0ca0319080b01c6400000402d0551000c2d1800d000c01c401d907105c2d03200300460074554060740da880526072400700302001140d0005020b00c070f5440c90b42d48201c1d00820f011050170000350703517400c0144059680d0407424591600205083c07110310349541c05818601400d5051000040c00b074001c1c0c122005645002c3d0011032940380c080c01c1030440d0380800751444070713150703020002035040394001c02c4001d406031141c50004903030700200502e400c066550250200d13080104055045a501a0107402502e140d507003000511b01b5a1020700959100d0b00c1a912291103600145000400d80c020861400f06051091403e105409000c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 924806537 1250 924805287 924805309
    0x1b0e04050c0702061b0a02031501030b102115020f03010e1e062106090102130905060d020d292502060412110703050c0108060a0305030301030807060f092f 68
    0x85950340c803410b9a0400c641e4a8400c0c01d242c0070f2352511030000d48d141011800800710303050303038800c0c000d0702d809803540c241c00d828410050086482ca10f00780c1031401c248446035440041c855000700f00790300b404010b0300351400480e40500041481a4400001401290302688142d43c000e0080c0b202621904440c41040342c0f0081d024203054851940d0750442032101d8841c83d2000d0507118220103542c0c1e2400e00d00c4980d4003c0d031109050440c4843c0d00301b80040e4200442c46035a21500703000c2c00280c080d416070f500300103070007900540407130718a603425007211248510301c0b004230040c29015a01c1c04c62410041681d90203072044900a21500003512128121180e001c00e40075089544082c070f15110254561054520702c6443c203404005100d40c180c0003060050000c2e1105041500781c0720b6142c2900c030003007407201d4045076000152050740100010000030305100001e00c10140207410010b240c1034052501010b49103400000d03a040c0341005115200249190003100a418454541400380d0b1100030100d42165a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 924807787 1250 924806537 924806557
    0xa14040308090402030411120c0406060c02211203100303030f0207112e1e020601050915010507120804050c0f030c0103090519050a030f0503010b040e0702011b0e04050c070206 77
    0x400406c04100407459922aa060014085480103034410b101580d1243c82c0d0a68610a904040c800075075113005050040144c3d4004d072100e203c16002c280d2101e41445003c003e0708940c03060749030718441401e0700c01c0a54000c04508004070a243d2071414010141d941d880c1a100c2401c0c41003096900180c228140b8043c408429182d0704071040e80c080010410401d095451080d240c845034250300c025a2240c910590780c03100c80500d2a10000c22401240c3c2c8000900985400c03401031004105c0c907100c003c20100b007001c0f05241491606c4c50981d81d05c00e0400114548501096454044c0700c00c2110074010384800340419a980d10300c111200b030000340e8032050304c1c0310b19041c10350b104000f8090103014031296203040340c5002041000640d510345690389030101c1000758002403007120260341c9103200702c00b242e04032144410308130708040c01d0107c3c504004801034482e4040d91760b100600c52840703480d401079501024081e2179444825140c2d000b0700003582c900a1028510840412003400140c0d56803069a00c0040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 924809037 1250 924807787 924807791
    0x60409090f20041104032a0b040e07300209041107080301080d030216030f02030d050f01090c020c1c1a0109021803060f0c1303080d020a140403080904 66
    0x100c5800d0404407005080ca02406440445034190504040daa0305260807180030785003004804495095000180201e0000a01140009054100000ca104804501c09000b03581154140703607903c010360350039400396108000d505850403c1080103034101d0500303100c200c00e07050030a040c91009070112000d00510005920400d03030100b40800b454440380d011140c42810241081d544005900f0801c00a420034032891040e4402d0b5084c03d00410712900035070344107850b2010000b5030300d60740e81d405403405044912540118481840706261207170381e5024003400340d40c10131103410540d410010301400361900c03940399109540c40194401e11940304e0384112902e0713240c01420009503000c54a04518010000200c100350200040c0012640d074031039500a1031507038680c1541240721080c0c84281610b40c1c400301d80c0700340744450600000704204030500c018890325204103124181d050310380d03130742e080c041e0800304072610510303404111800707455001084003180e103100d0242d541c1000d01e1651241124842e4246480c0202d0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 924810287 1250 924809037 924809051
    0x60b0909100e011103041a06031b0d03050705011a030f0d0c12021905070510082419030f02130917160204090501020306190609051909061203081005060409 68
    0x90003e40c0f01d0403d400000c0941340c2e881c00c09081903042e00300c1d808405050402e02c1c601155461034009540202825142082202c0000403020400341c0411b414094052107801c10461000071000e114400302c01d91541400003200207014241454201d84141c0104540c3c000c0c0701c1c445426402c20a40d5002a50040161840700c15007102241854040e40540d040140c1c2103000104002003c0780c40025282e081d1070b0610403000016003261010000c1e10105009403120200195180d80d1001c2a05041000740c40d100b45040c94607d401d0103845158015070304400200d8220f811407404898524203e029500207110124036900c1e10240807035400013a201c00341c000500c98081400c040441070503660010420412251141001800b0b03500c101d81061040280142121326140740c410711b1000e5078a40e5031165011820071050240048000d080141620350340580003038140e190f8045d1070b0160203900d030744d4041c0315054170327001d00080d2000d0308610014030039543c20700094654000b92000c45190240c041942e07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 924811537 1250 924810287 924810311
    0x2091c2105030a0c0c1509061419060506030c0a08040507050402030a1e0e06150112020a031b1b0b06040e160f080c060403030302210a09060b090910 65
    0x1800410684041400384144602421034210020303501c41c00fa03549082c003203241d02c80c07001c0300c0c0100004401800c40a041c406001940001d50140040520401c4002111003484c400e494100004913485d451a4102d601010042c01d06030103000000c29080d41c4040c15410900e80c0340310180503160f162020002d440340010103000c010400e800040002070000c56032803c08141c800050300800390740d00150404007036600504030982c4256056400d00c1c002038400b07a19045032508929242180d41410031a10382071080c0f02d0015480204803c03843c584000484c98604500c0c00020b0441d02001da042c09a1000350680c0c5d5083d0100d405411640314407407503d142d0f40c2c400041c0040ca06801e00c0d645c0da02c1003003a80001044040c1a01080d2145680c4007a11156203180103550798151002d07040e0071040a1000f00002400b03500a0a02009900401e01c0242d0200d5092440b11000312060b252154540c581401403100ca88183c14004200303848607603da191042d503e03a03446411a103e40c0046684010709298 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 924812787 1250 924811537 924811553
    0xd140118170a050d0515010e090610181a0903071d0f0606163009050f040204030b040f0218010617040305090a0608010e0f061507050109020406061107060302091c 71
    0x1e103100c2c0d00420861030411851032442c1c1c02040d15190b002c2482108908c5503440d000d2600ca200d041c00900c0801401642c050440e240d40341c081209600401da1900468200518481c0c605050019400c054450b4140703420186411816403255000030744492030040128000c0c0e58855102d000c42c4d14600054031900c010800910070340192030b0030b00c0005024401004031100f604000f58051004a58002c603862640f400d541c40c0c100810b070040707144440200701d1800c003c03c0440c520140104014102692511083c546040882e4100c400c1141e001c120011458600c0d00d10103004640b0601c0102507050131400740c102030780c0b10907446c1c121026800042c10984540b0440307003c204040e0082c15020340d03c100c084c2112400b80941c092010303407500000c90703466900c5078052152200801c0841c1d0080030841d407054a510604080c1c903d55240c1000c500540c440f40608d00c0140300079a2000240300001c84407034148607207070304041c00705801000340c030041c1d5a4148078071004424882c04214038440038641194 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 924814037 1250 924812787 924812797
    0x1009110906160c05040b030a0303051803071401050c12060d020a031209030204050a020702150a261501110d032313020306100e0703020a020c0d140118170a05 69
    0x240c00000003401c00c242c40901a400e0449520610b040f110300b640315020081550070412000b50154010103036a40841e11a40110750088000740c0f50990042c402152a0b00710740c440c0c1800e4030b801e001e002e0b80c0903460341c1c01d00c207042c0d0046111a046041c5540000c0420036030354054141c502c24400e900c1c0c040155a50308004a00840c0c0c032440400022481070b2004c1c041c424188002d9100d90302d02800251400301074000c8608a5a0040007540c1440e4045103803070341038101e00c0c6040100202c1084124841071071105441c0c0891902e880303c0a00e01e0a80b460404190781c42e1242410841c0e01414615032080000e020542c040240c2000700d18250304c80400340c0f8100403031107240c041c1e621503418407140c6d24180c11a01003490094080ea00780c0ea80d8041c02c1e510008482c4035840881c50440009035502d03210368007401d012285e901c16078480c480b250000841003018401c0aa132840c030805503a00c54001e0911601c4083e04800342c4101e06001f0944543c100c080780325220f0520010006070417041c80384200101e83d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 924815287 1250 924814037 924814039
    0x7050406052208010c0e0103061409040812010603060f05180f070e06040f0906050307030f0b07090e0405061f1a1b030a03091205090d030c0507170307050d0810091109 73
    0xb45442e0b403810760300d02801404840c480428040000c11a080d4030902a00742640d200845030404840e000040c0100b10344000c00c01d480c3d0354024000c2110300c0700b0302c4150900a000e140c0c0c000c07907502d06107141006a0b100d2a48801e11600d10701c1c100b130f11041000c07511590301688100401a140d99900360640701c551090305070691000c000140400d02c0e004055500040e60440c01d400c10080e07850300e06142e61628540800307803094010100500021703158520165000500cde1610014281e502c2d42c08004505064808a460343c200e01d08001e206001d0407201ca150040400380720012510b080c3d0102e0384540c8821050300e49100000310f400300341e18030034081c09900075010120303a698803d030351004001b02110f0404913a5600c2d80d100100d2050b115809a5100410003801084d486100d075500b51040c41c01290100c4850103500000912040500004c072003c400f082d01540da59581460040d09228001c1c90740414070250b2000c0c82070125024000e80192200c2c07200003d041d0348040e41c80700c11400781003001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 924816537 1250 924815287 924815347
    0x228171008070e0901060f081504020a0512010c030b01020318060c0a170d0c020102040302010806122a032808071104050a0204180b0916050705150106170705040605 72
    0xd03410b1003d0100034400e0381c022000b0410540c40e55034240c09481326109040c11540414000494580611011500544003c010700ca800b991070010400a500781d00c00c1c02c3e4240d55442032402d03000c2c2c0602801403c1c0d4000d2020790318210b0340000710a00448041c0c0c055000d00f4011426034908481046910702c0c00f0303003040d043c42882200ea688001c40d9132140d86120703031044c00e01d5004c9120718014000d890a036a8140c44c6e0309542d80e07d00c82406a0366140740f018200911070100f8002540c4800c1c01d102140110442076442501290300038540791010904442c80c40c091261b40021218010400f0f540201d640015020b6883c0c88608201e020003034090f82103a0f02500c2d00742400100c004035402001298810122400308481001800003260b13541c0401c184c0002261000518246a140310914020150f041c0356040c88515221070303190107940240502c44184c4100103100031608131040283d10b45c042c0031484100d2400b401c000b007590080c1d210b440b00303001005c03c01401c850144920380d0002d0202c0c0c501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 924817787 1250 924816537 924816539
    0x9031b1009060b011206080c0111011404050304230306040f08070515062107030303023103020906090c0703050307140d09140307020f062209022817100807 68
    0x900105103003c0c00301d020172003802064001c1c41c440d000b901c04540c00000034000070390140b001034502617942070790310304595641c42c64552600d03034500b07841c0e000c2d60040d0019929241001c1e1300316100710000180883c80d07800c41c0c59000d20b9660000b4250f0380140d03c440d988010710902e2900280301c2c000c1410040c081d000306900c01c040803c01c101068410001107a03002d00f081340070208241c1c00c4501010b00700e8103420611085c000300707000350000d003904d4001030012941d0400c0ba20380c100300c004040b10b201c2540c0d007000030100f041d4034140d1400d0f508900c08231174000c0c840c00e00754a103020324450b801d8000c050107408800205c4050081c50100d4221100b100301076078881800414000a002c0000f0840303403481c50450402e098100082540c034015400380c00f01d61405915810442c01d44c0201d220003400200d06200c0c01e1203041340782c0600004040c00203025840380090780681c0e40389000700d4100c40c0b402c0321a20101640d0761f40f0044201e0000c0442a90580342e03110314211201c0086036400c602e440c0d20030610 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 924819037 1250 924817787 924817793
    0x21504050a0b031e040b060f150c01020904060b0a17150402030103030c020a0e010503252115140609071716140306030d11010b03150702100509031b1009 67
    0x802036100b00c08030a10042c0c81121904d020441080650380a8011560000000d0030341c2008040189a140020800240b512003d008480e0f0795002070344644041c1d402040e04a0f41d410709001d0701002d0311454040300e0801c0b2028500401c0f440c2214a4070004240041c040303100c0d070510003a8010003110141c0103541e81e42e182e0074060511058040124003c10040000050040c0c8002a5a06880c8000e015000d10164a07248807a03c07484000a1505406071000001c0c0510031004400030142001075038034038800b0030382840d82c103c110920200c1e402c5410300d10085280e824502c0034a910020458281030f45407505601140c40304070840b5400c0700030301c125060010b0000c00c140601c072142243e640341c00e0342c5030080c003042c6054041551200d070980e008404c11400d41c1c4c001d00a4689426100c000041d41e2a40360740028513000c65054000000080c0d2014042025410703c41c5e0340c41c2240c080c105000b281481d103030a640c2d0f48900b0000541901c1007030140c0304042002d11001030a010005018802e94a241c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 924820143 1106 924819037 924819059
    0x111819050f0f03240702011505011d032d03040305030d180804090207210903121403010806060f100e04090804030b0405070806070e030a021504050a 65
    0x42101ca255141001249019000b8100301e12a01c240d01c48141d08844d000741080045904000c00025448512044001110b10a00e0708003004c034006800000c604520070302c0190301d40140302c40201803080c0d04400e02100501000c403e40c07107801041e0921365a10440c40010129003040c009500c5c0d95065600c100c0a00401850003c10b0300300940e1036030410745c0035420480303c89a0104940c0180104c02010503a0307211860007503070100d0710352000600030321458130006021050756454244002d118143c4802503800c5078100c242c495841703c0d2035584131802110120b010702490354080400d86080b45c0750300588011915a002c10501e8a0148805410090400c1d03038610301c2000004009045000901c1c41580580c015019650500030303030504015018244104126078068032010550700800c02102465040307900841c80281031005100c240602c0c0d00280d0300864000001814040300c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 924640287 924820143 := by
  have h0 := BRFrame.cov_init 924640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 924640287 ≤ n) (h2 : n < 924820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
