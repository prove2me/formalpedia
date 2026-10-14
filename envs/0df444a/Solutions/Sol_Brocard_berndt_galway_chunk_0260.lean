-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0260
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:48:31.540185+00:00
-- url     : https://prove2.me/submissions/86b1d331-5293-4a10-8c3a-fe126e6fd2c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 46582738 ≤ n < 46762594 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 46583988 1250 46582738 46582747
    0xf030b010207030606180b040c1b0c0305012903070305030d0b04020403060203070905100903020a050904030512100602010b060c0304061103040e0108010f0615020a080a171014060708040506 83
    0x102e28146859202030b01050034001c00081c680f0000000d40402c0f110303440c0a002c2c009900d0f0600c41a200403145036000140c00c4950884091680781400c0031a51083c4507148a0958a481e800d081d504000e0031114038544445c108100c0111501d41401060350590142816918549406031030380180d0707651450194884080300c0d40b50f030f2aa8101c0d001f031584000115143c6c1001c0900038034940341c600896018a051710242128039004d5110780040b00d5000300900380c001d003044103200b4042e40282040f130510500744649a500020801018403c0c110603c900c81280d241c80d100900351145180058060300d410064a601608007200721020384c1c0d05410442c13080031100d49401c1c0345208903400107200a520100220b50100190000c0c400760f102c0080500c40c9540f40d040311032500c0010084000907922030b002c1840000c201d10701a09400c55a030514a030880440c41083c41d05040880d402c0341c141001c20000c2c42000000340516201082c03c5c0da0a504003800d0b980e0301c1900d88030b10700a43e40300741004035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 46585238 1250 46583988 46584011
    0x9010e07021908120601080c0304031209020d030215060d1509050703050d0302040f140d11010318081b010c05031b070c090b03070602010203091504050c03030f120105090105010f03 79
    0xc00141c104050012980380c50b001c1c0d0400c02c400d900014010b400408039030011894640c07043d92494028050440320350300c0c5488030759082d03854488001d032502072207403240c01ca0f5026075a800380c02d552260080d0081c20700d219a19904655a28005006c244038040c03826400300442c01d5035580c03000744070640100041c0b86401d400c02c28074203d0182c0c402811403007100701c0c2e5038000d681030300508129041d0140000c071160b10b600b107400d904006e4543d001c0d007040460703440401040052110b0054001c041c14000b03462811502040305503083d42200b61010b01000030803035940e1f02079031035031544140481c00800603c0c452000c010b0280c40080c0240307028030442c45107505042a82401c9500e0740d94406041d40b90103a81e41d0904000d03000c1d0400f021320038092a0360000741c040c018000c6a00c101c3c03800010704080c11048102217186407000e40700340c42c03a100392805441144c804000810160010340030154035103c100100700e84403207050b004940901d101340010011a43c10000d080e14580240c07c010a52a901c0d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 46586488 1250 46585238 46585243
    0xa03030605030d1b02030f0115090b01032007030905130e0f0f06010e0c0c0601090b190302010806120102040801060303030504050706110d03111e09010215040209060402091302030406020a030c0e09010e0702 90
    0x5140036030325407274404020f02041e40343d62032a00300c4803224818000f00700b801d4010b400b15240c4c424828a540d40303101e000c17652403403007200030403642e0710a04010b00295204c80100343c01007110f01d0f0180318140d0714403000364507010800c000e00c000a0184000c10724070702c072010190b48800e818850700c00703285040c2001c40c00e0303103001800707503400c064040c01229220341e540c0d4510b03006030111991545c09600e03c81c1e101400008860001f0069079010784552405468113410f2010041b16049201f9041d58240404240c8a030280211070085020741d501040d682040e0074045e0400038954071600c1409480c441c40e141d0f02202080c07041d03ca100500300000c01b01a0030060a1862064030380850030622084180e000c484000c0000d0440301000703038222403401d01501c2c044400d1002c00d8030302a6101d0810b0300024014601600208002c40c006800305090241c02c211070000d1342c00c2036804450450b004110b1041d0240e052003640704e80c01851070b00c1d4603a02204404a11505418003402844408a40005002c04d008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 46587738 1250 46586488 46586503
    0x320319021602100309030e0906060f0304050109030318170d02191707020d051c020702060324060418050402220e0c01030b031009030306030c080a03030605030d1b0203 73
    0x1408000d5568542100000420990350801280f042a44541200310b440c440e2103003200e0a640358841100d821100c4c800c0000701709000f040d03140d01440030044199003c4495000c0c5000340d100c1d00004c10460075614000e815248800a90319815003020081e0700840c580c1c0507030205401d8448901540d890341c48661030302a1040402000050a41c3c4910350703070041d4424080e88008868070008101034071006800c907210a07084200b80002002030208150351440e45104a0105035402801468940b080d808114213400494403042ca0940c00d5040a0184404490211942c001207500c40d15060821046960840e00140f4102120b507451000800f10348403100701300b04405aa812000d0341d0703102d140403200900321071112501940280c0205031030740e501038003569490030340050152019001c4204124010806d4250517010580c640d800040411860710501001d004941e001e090002c80905028040c5d8000e41d0209009034030001403007800c1c0360b12012f0744100c3c0042c20242060b4610780d0000a1904c500f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 46588988 1250 46587738 46587781
    0x3121210090c0206040b090102092b050d09080c0108010609060809010b0405010801090606050a050108070507030e0904141908031303020a02030d0c03020d020a08030a181b063203 78
    0x1918420b900700d1500020354a2007030348101440801991030000c52400d070b0042140f2960001c4d64000417a00308008480c00a10100034101c07400c6120340d46031601881c00f0107015007071020036044003003400700082c103000301c240784002820000c0155146c01c50060465003188a6081003046080106014035001c0d00b11000c60b031002402884a941c64490fa14000c2c03040c54802c803a86c5140500c00101410004a080308a8505131030764a8166543c100a9403641e0101c94220100310203d6211026503a4500d24140260b0050300314001e019034a11005107000700b210f10212100c40360045000c002103002d42143c2d445115100d0f0617081c0ca02e1441c00703034076024442c100203506000b100c4607510401e42c4400075214030380c040c2d403c450554800ca038069840790a001d1024008143c00c20000d86015545e0b0000c1ca030400e0140a032441e03030001c41d00c40d410000780d000c0040b01c2c2e00d101d00d002000b80e07070303401403255003280640e10515103255000701403902d460003554911850002c001c030008150f0403204140310000803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 46590238 1250 46588988 46588991
    0x60f0c0f1b090b0904020a0603020705100603031701080102091003150f030803040507150206040807020d0b1611010b130b01020304030f0b06011b26090d140c0312121009 74
    0x48003964540100c0d45001c0c0c0c224092038450710007044e1814040f2580180c0d00500003c83c0c80b814400110060b6101c00415580b51081101c440064411741c031840004501030399a090912006010b0420490410b9010140d80d0703005108244003a940c824003583d10a03928200003a03589081d44080b074000005620010042c51032002c000b040c840c011004510445c45041032b03544190729030b0403034885031010300034010069104000080c0003d6400c0001c141c110f000910f440400346050307448103001c107401c40d4040c1c85483c00302075004200ea0010b4054030007400690090040e01c4078500030407031001404007030743d032a9900c942ca00211a4002d1086402454002d042c184c2040164100012680d0003568032a00207080003400a84041c100001c0404959120b00520005003c4005007441d000da1415805203621007000300c1d084503a584108030000314454900c0d150181c4d0764132585070500315540758a501940000c3c130304d00700c1448500c1c00c64561603a04c458003082d544603445420754001154201d80c0c003a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 46591488 1250 46590238 46590263
    0xa060b0c0a02040f060602100e28050f0f0c24070c03140105070c02040f0b1c03080c07020105032809030c060f150510020115150207060207060f0c0f 65
    0x30030100e10600d101c0d0082d101407020644000074081224080c1c0326810041e044041482c80703000e010b8001c200705400000c115008184046402c8101031314008100c518a4900d400328400c10034240501c1c068000d144001e08030403001d083c3e03100e8a55104003030b144c0c8100359112424038011440030001147e801d80b8903129445411a00d0400254945400155941c03c02c1110046040505010f21340c4501403940e11a5002140781c1d00b17100c090094103901c28046910f400c4400e5268807180c82c11201e2503280000703009031322158240078120f450f0241c444002c20f90b0030004140507036005421a40c0044d850308100c4c0e40401a00004c400000701034140440407400d01e45a48189684081801c1c48a40180402c01070300314203407400800c40d40074501010380c00000b44020040b510348008010f110301c1107070001046984000c0440d2001c0d02554000b1700c0d00a8120440300100c0340d040080d24003070305540c0014140360703051140c0540b030858100b5032002001200f00c100001c002c860500100a640d2201495584 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 46592738 1250 46591488 46591507
    0xa05071707080f0706120204080c010e060706050c131205030f1e030703060f090902030d030b06091c1a0403020604020f060702040e010e0d05040f030b0426030402030d0518090a060b 79
    0x9607004d40c0701e500c1c0043c144640d680c12400183c403c840803640542d0040106086107801550080c005100e0160b1040081c40b514000c5030203400b9040c4134685c1c45503460b80d1145c03003640c505210041c075000008280f5006803800c00107000001200c55045004005945803100c0e404d0781f18082400c0b40c0c9045040720084103200a90742c05402000666440803e0742004030b44a01c0c54a00300c54080c0c8000e9810b0f4032001442e8407880c0a54000700c400c03070014242501d0b090106000c01c0100154100d511009500c001d40c07102405001e00300c00024040340c0ca0307a80242d0500b61030003941d0384c0004e0301c040c0c4103129044403802c4030780c1c0e04412a50120382c0500140160070464807010700800c1004500200b41c001c2441c1c0404951040f4221401d48100c0c002120840d4290b440d030042483c0e0081c01200c41200d1a956213030318020179180400158000442207075289400c0c41030608240240d2101d40c1400707814400324110803030081032070004900a480700c081c0b50f581e561a500140009a0124440802c00240201c0c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 46593988 1250 46592738 46592743
    0x507030501020903100e0316060b030307030e0405070206070c082104061d12040e0a02160507140a140402071a0a0c02070806010f0515040305011109010806030a05071707080f 76
    0x910303d0440030b991100101e20807881c182c8036400c1c0001e0031a042001100804902c014240404c607014400000d00c1c0b0350242c0100e40703190301c4000c0035008a0f1001c1100d560500e85070040b16488829840581140c0c1030103071029126503070320400249456400b01d0f545400b02032043d904010940740012071802da003030508061000f4003410b06811104c50090040c02546100050000b03051140528160315007490110000c43e4101c001c1d207000c480c540c0801ca0741d031001424450190b1924080c602400045141550803011001c50b000603e0042c000c841c01040016031303180e130300b64900c04141d1b00941c0c1d401261600c0e4140c0014040190a90005071301031200540b2a41d0104480d038005808584000d500c0314000e655404091180100c41010b50344148001c0c1810648082491201e00005041a8403541e8050954000c0941c8c003000f4040031500d00015030f448048950021410340145c0150486610343c01d0725080c0a01404000c1c5404e282070015500302006035600900390082514900043c0140c80c54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 46595238 1250 46593988 46593997
    0x105180105090c0105030c090103090b0405010203011d090c011b0b0412030f020708070f0507080102031e0109020702031b010507020301060e070305090d0801050d03170f06030115081002070f050703050102 89
    0x184290300e070900089111400091000112005031100c43c00e6680c1c10200c0c2d0a01d91110064178100340c2c581c601c880c001162000040d01407442a00007503165070400d11401400c1c900640c800040b4000c4005102c0c2100c00403581074807140d0300786400c5075803842c805650303420104415001003c084a0004010034002c2d0428800210710700b560307007400044003c1c80420309074050380310050a0070404002d15800a04e03010034868907684500c080c0c501042d03559a000d800c80e0012501d42580e1000e50340c07680070280d1616410b0f4050042500b04600303052803a008a961527241e094100e41403410f101c42110168041d0003030322031080d8000e00034000c590b2111045204440c040d03607007001080c10100490f0761118081401e00c8024001e9445a00603807800e0100682c0701c01c440415000e12940c0d1000c070030420420b002c0903109400f9407950070b4a07800e1020525003107075001d9040c02544480d4404c103000007040030403030031001c03d0b00990150321944107091040171240304e036100070b1103482280c10000401c08190041c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 46596488 1250 46595238 46595281
    0x30c030b060c070e06040c080105040207110310140c04181505100306050a090915020319020703020c0a080d1403060301020408010204031a0619060305071707091719030507050a02030105 81
    0x20100c940f17844003440192004200581c01103562030005014a003001d030301601003140550039859000c64404046810003d410784d020700c42a07102c041c05180c400b040245140c21500c1098030b1450306d80b410210103448442070900c03048154640c44540c213a070450b0440c110240500801ca0f072840ba0006001400a045902c00c0600800c070245c000500d0300d580e4030600c500c00303030000e1040c0c00d840c0000c0751060095100405500d1190f00900005941a807144007070028640702e03400030401d4250034020011b40303a2184d4060300320355210800c00d010f2a544403050a01c410b104012080c0c41e903c800340001e0181c00b1341e8001015542c800306000041c48580702c880805164050384100c2252204400e00400511803082e40e003110b5580a8200422442a802030354014100d20785200943e5480025081c004016180b103800a15001d00500003078007d40d0700d1034061003040d0010101d8081c001c20a6844205508002d018083c010881d82c061003c180801000242c0c020002c018502e405100300181c0045ca200c40e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 46597738 1250 46596488 46596509
    0x1f17070807091b050d0f09060902090a0b010914210705100309170702040207060606050d0b0d0c060503040302070b0c0a0c06020309010903081602040204091a03070e07030c030b060c07 80
    0x20302d003002840307a40d4104080194160715401e28841c15251680f140301c4100416076516900485001c061003201002885050007140c0107007103004029104e04081c0c4180c0728245407680f00241a07070804450000c643ca000c1c400700c51103c10000088c22140480b040d40140c8080525000300c0c03c05c0880e0300426600120b0340e003a1716800d422030031000c031502c5100c0240b00340841040850401d020902a150843c0f00500152401806030703140e605440c12942324001140000c500341070b4221031805107448491064846c6010070481e0384481c0380c1001c03103106150034880700101040c1411f1082c01418054000a07030003640c2c1e0381e03a01c5103041c0e40300e007940c1040e10b80320022a004222070f84048100c1e128803d0580d200c00d809401e64446000075403007214400d40c40e10128510034016102d40c005800201600680024116005001e0f5000c4016080c2d15912030b0300700a509101006010602c41d821440e2842c00090080180e041580280680c117100c42d40a000410015400c00300041c8040584003099507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 46598988 1250 46597738 46597753
    0x9160306060f022a061602011b0507031205070f050f0c0d08030f070519020304090b06040503060705160606030b0a0e1903140702040513140c091f170708 67
    0x112480c1881c2c000210050f00b048407a00d1303a441118040220907805080480c0d00d00c0b403100002100d0b07900c422011041c107034260342d2030025981c0102904aa05503981c1350301140740780301da4445488442a02000744495801c040001c4424428001c0c0d41c2c0c2d641d4440c0300103002c180e42d41055a034035840c05070a18040d10484102c543d8a0420000d09220264004a183e080d07171100c180c180815032009111400f000302c14006c90b0507820300d013003683d90841500d4008c2d41e81c071030420314500141c0b44615940c0c0c0c05150708100400031030304c0018080c0e901104610f48652140004000903803450803d06006d00240c0c20120040140314150b40c00034002c41c0b1f81c1c0d004020841841d100390361688207090015103002e001084540200b4051120550103401c20020645042c0c001e6000070220b513015940080c01045032011003040090114621405504010042c00000e89490000b8030212b001031200000c80b130300032103140c400803100c00d40314081c0080b5080340300341080302008160390315920311408460384a50503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 46600238 1250 46598988 46598999
    0x6030c0c010b040b0901032a0611060108070e060904080910050301050306070f090b071a010e0402100c0203030702040b030118031d0a080607030e07080106060201140601170a05100509160306 83
    0x22820400480c090085d00d8940c0c86e50b150002111042c40c40304051140d4600c080d00d0f691024000c80c0090f0000c0c0d240d481c2d0551950707035040c0c500382c0140c00100c070380c0e44258014080292104000d5074080c00444180d551540c40d0700c1c080d015409604601500400d1105078040100e400c00c0c051410b0321029002c40301d41d95605401100d400b0038047c03000b0b011400007403007844418a5280104a00317406105d07103aa001c4810400c000701c02800b613120600001c640342c00c3c00110f19100e201100900c845181c0b0070a03038080b43d00003130703124416640020300c16540c0c0c26100256031403c2d0414013400d40c181c94035201072201410007410741483c04d82420800614140400c10174903001540805030780c2110000e080d2583d80c840c00360018801007500ea09244600c010000c5d580c8024010f18002e40107039400450350350040c81c2c015900360703006410b59051100e0b100f284944046012050740c2d0180c012100840c5c140c50301c5040c2081952660040c0360070103245801c020900b84800c0c3d0109403150550b80820120390b444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 46601488 1250 46600238 46600241
    0xd091a0304020a03021003020c0f0109020306010b07110108040c05040c030c08010b040e0a09080c0a050c010807050a08060f190306021305030f0a030806210109060c09080c0103020304080906030c0c010b04 89
    0x4441c000c0d44801041020701c09418424100c0b10010118200149003029480e803151520101600c03075507081e91a142036000710309042c01224010206007140b0360a0580702c1e610b601e007041405490f40e0400c86103600040c10b000c0b00d0741c400802400054800c009200318514024003400b03a4818003400318031844000a0030107000400c503003c0f40c20031085402262203113003000c809002d8a134402e0710a01c2c000d00000c10440310510036107070040d201b0070007440300c4003080f40017614034100148400d003440790511446d0700141d0480c03100c076441a000c0745c0303c0d90b4665917500042c4510105200b840000c2900c1c2c0004000c02006034000e00d01221240c00010506d99600c082641d51010100e007004142c02c41d47e500d8001901400806400c81b20007044c0f4046070515005004070a220462046e103aa0745800e0084188103032480b40c145444003610341182c00d181400d82095841540b019024109580000020180302c40601624520000145150f0b0b0f40d0402c8514001c454102e95000c90a039481c015540ba4285040e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 46602738 1250 46601488 46601491
    0xf0106050a08030d0b060c03040605030f0906040c0e0402040e010f0b010e0307030507051c12030504030f02010501150c080c010908070c090501030b04080703030f1b030b010206060d080a050c0d091a03 87
    0x7042c1c000c41c5000c0c0c450310001d0140006a02c266007000060002c044403100500180010700b502e0f550b550380741d00d04507075600100c08000c1c1003600d03103410801c03d01000c20400c40c0309206171011a940d0031607a8036140f0116008080d14041c2014039440e0441000510515030860010210240c2e1100038210003c01059102c038202e10005005a03c060700400c0282089542c0030640361540d910b075070340e04000d500c40c01503080440c1d00d0b102c00030b030f61481007004160b041001c2402d0000148003c10031981404001d0300c04880d1011800c05104294600c60100704034078040714110a182c04c001d000407a001c0c41c060142e0f81100e40210b89a00d10040003080c130851500c1000e0499800c00c4e00420070f44c80365191b1030201d0f0b1001e4401d0b401c1644540c064107a1020070701075803070b140043c001d0b4040304040c005d03001405c4501640e0110304540003002440079640e104050342400c00d4109143e29600c40685070240e8030f9108248400d511406040400350540b500131030a5021600c01d002c220030700390052400055903110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 46603988 1250 46602738 46602749
    0xd0608071409090c011b060204030c0501110114010e06040204030c030503030a050702030a0e010315090903091e0302090609060406120305070308100323070f0305030306030f0c09070815040e0f0106050a 88
    0x20100c440c4c40d6540c030446100380424641a04031400e400a5202d50702039034416001600c82c90503818081046503401448050303060b2415008210943e01e0000c5117014030018410034442c03500d02c0b80400c1155480f91304403001141d07c00d060075450750f902c2c038049440e5001180c1d5199201d141800003085903001204452525910741e0b600300b011254800190b00500b022400e4a00e0f00386690700201c0c3c4203009101d00803020307000c3c1e180c1e0080385140401100103900d440c03200351125034080c2407c00042c0c840310441a04500c1c1242d43c84102c1c2d035014080390040455503c502100d003002c1d02742a041c15003000080c01000d00996842c00c0310354500410f5403100e0040c0c44003c21094406645005404042a0b03102074103040c0d005880c2e48640c3c514019655200c280c0007990039400c000f05205061a04003c44083c07039007900d0191202d20f09030302c00030b521300300000c1030710042c80307074420000303848010026940004503402001000342005503609140e4074407000340030064940c030b00386010600345072100d00c041c110740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 46605238 1250 46603988 46603993
    0x9070e01020d051c06121106090f01030e010b0d080711030604021c05010608070807090f05010605030103170903060708041a10060f05070c0905040201020d030506060901080405030d060807140909 85
    0x380901c0b0803a0315610000960422a002c0446800000c005000d103c009000803018603840303800c142040d011100c0700c000110711030102042020740d1070b00c400030600b200b1102401c00040d00c0f40310001e10341c007501c0f030070f070350a40d010140c111140c080101d4000a080300c036000e40034120b00c402da80c8040c5a41e407082564041d60088001d8000280380c4d50707175001080807a105100125145640303000c100e240440a42042c0100e4100200901c124081441044058580c00ae001d200035498840090010b1106000160010044183c20382a02c20000e040302d80302140078044806500e071290300101081010741e000c855981c1400340000303100311002c0d0304070f000f4400855039034555840c008041d0303074060844d4195414882c043c020040410b100c0c1040d0001490711003000f041510b0548002030910f8607c1031003409140c6800f080c00001d44464090f40d19450342820860043d880703c0c103040b0300e91b000e902c000c840b405041c520b01003485480811100120340c20000206500a0000d040000c411801c84074a4000e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 46606488 1250 46605238 46605253
    0x601030312020f16111503010f0909030908030d02030604050921130b070506040302010b030304060903080a0e04020705010e1e060f10080a0503120a020a0807180b0c06010509070e0102 80
    0x114240d401404140e9040303208030701c4e2a00c10007400d40040306080c002d41e0b080b0042d182c444d040d4146a0752004510008140452566041103500403e4a44038020300001d03d584d4120001010300030400c26002d000248101c070b498100f44a010006544210b503058081d605100100d0031200307001440c080e011244441e034105028541c41c4d009640e4114046a1407115045400041d540e180d240040c806035001c0c03c0640501e10b080c1c1006801c1d607a018100d680207a0040104102591740454614150781d4480c4109070f440c02400000c0701c4d14292480201d0b4843d00c0000c0c41c00c104501584612100d2080380160b58040c40303c0c01039000c14600c4640c010480da000640092440340c086922254407440c525400c0e0402516402e486140c00c0b5419400c0365a13a01c000794502617011802c1c0360304d60000d84070505500c1c000c18507a000308100c001070030b158140a0f0788190890981340e46840c40700a014440001515030910b00c1031640c1d6645c081c0710b024060301402d000300702028400e40200003010030680040421 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 46607738 1250 46606488 46606517
    0x303020309150f0d0905010e0c01090b030a020906030a0c08160507020d0804030615080f0703080403081602030f010c17090a15140f04210e04020a03150f03031106010303 74
    0x248901d951000d80002d004004480302042a20301500e20303e80d4426000a44006525040d400c40300a8450703000350781d11583d1041d48170381e4449580d01c16640c007021280c0d101d44580c000070700a4050035801c0c41c0d00a41c04000c22109180f03aa0142042807902e60350b41400c1d0b21104006498106031004490006004024450150074841010b19440f071050015514042d5241c9800046801030343e8520305841c0c0900c020802e080003082000a80c040c554040c015091a40d61010040d114070b100c0140500c5002c02c0541d940001c0d42d407200b051540182c1034840100032900350780e000b840d85905038004680c00c2000150200c4401101e1403094800800402a40c911516030040040d0800102618552134100140c9a0085907154074003401040035110180d042515201103840b1101d9a45103056100c03004a01000783d201001c1101c140068500580c0c4284a110880182c01d00c290000e615000c0c1510008840b05503d00c050101e03802640c4e008041303440e0182c010f440e024213100182c00a086034010510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 46608988 1250 46607738 46607749
    0x806040b010c020901091506020312041e0b010602010e07060903080a030b0d060906020a0e090f0601080705070b0103080a030507050f031b0910080f061008040b040501020f120603010f0203010303020309 88
    0x410038050400b980701c010305500041040000360413a00e400c948800214a13104000c4503001c0c040e14280c0091800e000e52803500c0d040c1c2000050024180ca03007802840344031001e66050501c89070f60001c070401c50942c0c454030082d0190045442d541940d2080c03943c0000c03000d00c60400502a294070030249071034000e00341c900710003a00d0a14119640240d800e854007001032018850200c1041c4282c0025856511091f0080c04800512031454000c603045e02c100002c3c4140c6004203503110300d0900304502540c6401104541c0d40c010380c0d03030052095944c4070010007442040c40180104000701d075014000307990381490841d00350081c0815041c000c9000e1000c98500c1420608181c2d4846400400c87c0c1882140e100180701c81d1810070300741e004580008140314030045030050041d402041690741c2201001d40300320080c40c26000170400340c980000c460106080080c01e40440f4003000d0800c0f85141c581d40c801c030001090900c00e980103440ba6103881a407076003074001402900d0403660113030061818404040c05104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 46610238 1250 46608988 46609001
    0x602030901062d0501090501120903050d0e0c0f0f01080c09030c041d060a050c07030503180d020607021020031503070b04091a0f010c03180b03061008010501080604 72
    0x115555240d0002051103014155000c03903a51140700c5002032614901d2400d04140e1098004c2030402c01c501c80144100d9070050507111503114601c1e800070346d011943c14100c6860280c0303003800d0100c0341030000c0f80e507103c04002900d001405048614032800040d403400c100c0000302c03080d00c00d40802d041100180340c18003040d010f041401005410365080741c2c21540000c08480344c0540d98100c03103003400c401c8400d66808112856200d02c085d0f0041109042c0303200984218010440c0050400c82c0c0080026040d844032440200880c00400c201e80c41070300d000001a4882c0400c80c0d221006100300c052134040703820607006940203040e05009040d0618440d52203c18181d00003000c800e20340d0342e400841d40841d1010000800142a075240290b01c40d4109101d04042c0c0c0c02d0742c60390035124107120005e10100d0360f5404030b100c244202401c04c0c070901030481c80c0507a40080400e00b50000f48030000b5002513628190002540300c0d95044601300c80030f82c2c01c0c01090314070074400e008142c00154007400140307243c00c00740d0088 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 46611488 1250 46610238 46610251
    0x40f0c0c150603050a0c0602060a05012303010221010e240103180210020610140a060810030503130302010e04091709030f01050c0a030b09010614030a0902060a03050718050d060203 79
    0x202d820b60b2251585440c003c64144229240308002c0005c026513541409480d40144030307038405001c2549040e500810742800b9441e01c2c0313160f5400e110540b40540c1c3c254122541440b050541404800045d0218581ca0b10700b407103101545680000001ca525a84044022111040408035189051030000440090811504401d10582001010310241c1e44000164981c1c1e40d556004003603624000c030349425061400e40c00054505084a00c0d04000d549000440b41030381c502d4541100550f89040c90402e00203a9584003802d85e000c00036480a0100e41a60b105003a24001c2c0c81d0341d04541c0c001020700040350102c40300034051341852441601000c0c110801002e410100a04842810500b4003040f421600280d4110070071060005440ca0b1050b00742c014007403191022039004a03550b00d0010003610300481c00108541c15000003001601c2c01a940d8495502541c007d01710300e40b00c03811224050002c04042c0d8100c008965000c444038424400181c0010507940080c01c650000c010030f94410000c3e400140c03c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 46612738 1250 46611488 46611491
    0x190c0c18091b050102010605030705030a060b030a02130906060605070b0412020319080103050724030e120c030d05150f0f0a17031201060813081305130b040f0c0c15 72
    0x302021804084202c400200d59001c494052440e00e800a4216002c41d8005402a049007404100641e4041498224650000400706a030216400060b0400207207041c02940490341850300f006948103640640e00d0144941010002680ca46a090300c2a00403444010104074040300002d002601481a07000d1a0b502401103a00b00541da980c59082d0000c041c0528000400311030040062260420050b40100601990120307a005e021110440c141d14a54840051580703c0c0554820680304100110b81d0001c840c04c941d842e84100b00200381c80c1d030300440030707052141d09200c0824103061000c4078010709150020720325011411013400744100c0c0c039441886154018413901d0300040e0f0b200e9800d21510f0418810000d107564854050f6403200c180c0040e0001001c000d055410000c0748940754140700764007170304001003503100c80300140c0d14142a03d00e50089a0445a100c3c7c00c3d01c03c3d0070ba1a0407000301003200316418054586402a00002ca400c040034050009101181140c003240e03181c00071509645c0308260 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 46613988 1250 46612738 46612751
    0x6020903101d01050c0702011e050c1501050f0102010c020c011b080a0305061c020d0803040516080303060a0602030f030606161205120108010506010c080f0d050c190c0c18 75
    0x12403004481850b0018407100c05811040c8502d10b8081c0301c0c082e80041400021410100700390002400b89203c0010f1155544405112982d810700030402c1e900410080021581d2100700d550070005504401e11440f0b02074400203800382d0300c0d0360043c003075482040c0480d401440801c20100044400032414080c02401c01c10810f900c0c800300300310360001d0140c0344580d1004141400e05409104603800c4036a045102e50204000b40001a61054070902100750071411080d02d9465500b805401d02c0c0340201e01d1004050b00240c001346445010000d103205410448400884680d038801c1079849114501c102e880040b0200700188040c40c100c40a00586a0220320070103001500c0da682c12008010012440007190f0041270b01e00081015250640c09042c4000c000d001500b00301002074140b08003080e008041c0354021407400016007295007603c9400c04403280910690905c09500385082e4030500b00c040c0046140308010300098000c0700c040401c10f80c02210904018a0041500070703070950b0142e01d203081500c03003030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 46615238 1250 46613988 46614013
    0x1c0e010f05030a1d070f050603090601090203060105090d0c03050c010315050d0c050303030c09040605120a0609020415030309030b090102040608011a0418020c01060801050106020a0b1510090305010509010203060a0306020903 98
    0xc8141080780c8040c002480307181d00348210310507006c1d5076138442031081400300104900800c02240440c115000c00c0000740e02e0f61100c00051b9900d000309030441d42c01101285142080c070040d80005c1c03003283c4c050340c10b0794400d0b800c010045041c0d031a4540310b1000e02c000d109082216003800c000c0000b1881c000c0f455040c00a444000003421540240c1c0d800000b8100410142c00c54582407003081c000f8042118024102c8400c0c914242e11043c0030795014100320743c0c0e95080000d649030b0350400075211605c0345000b118075440340b0b40507001c45801d001c240c49420344800060880141482100e050300c01c541c0700c50699a203400e014945402d00d4001c0c05074804400e01000401d058101c2440661000e4202c002d6200c00b0340c4105142104c0c0740d5032203a075071681081d0040024907000307d141c40103d90001000c00c03155440c03905802501100100340c0f0717040014820407440f0607500c0031150003600e20413002030000b5110a01c0f69802d0340030542d00694001000041040080c600342d004000254015069424100200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 46616488 1250 46615238 46615271
    0x102030103031d0121051503031603200c10021609020a0f08010e0711030421050d020105280b0d061505012102031b0a021c0e010f05030a 60
    0x81c0d10440c00b0a0351078502400300d4072070101d4806286002e1030180c440d4001350594480d1a61404030207440d2030760780c80106040c402000b5907940b2840005e001c603642c5032a01c3d40c0400d40030b6a500300640000d880b2041e0900f10100341c1b511461901c010500a000303405c001d404011451401c4020b01c82903128103691326212042e240740f5000100706086005841d00c802c240e01400e200c1c0750b440c1c040100445103005010401812030300c217801101910f46446400b13100d04001d841e52140d0b030466040c41e80c1d075070340c400c4040c0d0155690201c0c95100d8800e0711103030080d002c81070f4280e50054907103500d0421000e0344184280f03500c82e0f001d440c0040c0d201e400704460441c20302068032140704250684519482d9005c41d211080c02c4211360006000a10300300340004404030465400d6001000c0c0035214580020105440340f8010300f95486506455042c070342d650b031745500013030343c0d5070099212803080d08501c20262000c40e0081d681d818011006855200032414007010032105070740001c04181c2d50b19079406d1a1220f16000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 46617738 1250 46616488 46616491
    0x115141902010911040c090b090a03060e0a0314040b09010f0512040f0506010812040902091801060c0b060607021011120a051c050106090308030a20071103030313110d05010203 77
    0x3540001070483c401c0e0a01c100c92450700481e507806139041940c501411540680101c0c21240d486d4042502c4800c0d01c5c00064082c0100d0380060009030520448405000b800300b14131a58910075101e0010001e4115035820680c0110b00c00e01c8801c004c20311035852954061a0540d44101407490030625184030417821000d008000d43d0144c54244c410002c1408010b0200103442c05031100300c0080504403000b1804007024807450148003041900490204e1413a124042c2aa2549030032502d8040b8544e100d81004244c0300034404107889200c01c0030f0201d12142000b904444549030041d0100c82d041044010545d000d1001044003c110b20a0440031251080a1005802c00061550b0b03030315035800c403072003400010300300b085075521180349841d004000081e001355028040701c0d0701c1030280d40c0301d40d00c0c22024402080071904040d02035001800701000740c0440d400030801144a281c2c01c50701e8113003900c107050f80c81c00200c3e50080755180e991040d0b4041085502e04400b40d6000801d01641e500c031541e140c9099810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 46618988 1250 46617738 46617787
    0x204060b0703030c02010f060f0b0d110a110c0405040314070203070306020f0702010810060509090403020f070b04170c0a05040f09050d03020403030212090618030a0501090308010501030b0405011514 87
    0x130b58001c900359083c2e0a00a044018602030410302c8032078106100064440102c0c4542c0000020004034422a441640c00402002d20840d1116449003000e000281824224800380c401501405021903460f1070148100d5004a8141e034858000702d046100d0340b02d0682c0141e2090b0b0303040c4200302c0b00200041190004050f0201d0a0740c000e51580c640d48000344c80c00d034024064103116100d1b4001070003059030110a6424124046910040d42c1e11142000d0b07003030224070100c2402030300441c8004240028803400400468103c60300180306406070b4100c00d0380b078503c2030481c56480a80e80104200900e09600910541000c081c400507826000740e031042c0c071308039440503800082034020404000313154043c48031200c4103007403403e480c0c034000c400d5000600d244540c205041e0782c0c2c82880502c0a640e1400c118008800d94490020010402281009420071501b4461940040d0428600810504050288c54100c400c140d0345410580c1b00610241c0d482e48241802c829030080900519034052664060900d1000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 46620238 1250 46618988 46618991
    0x708070e030d0f0e0a180908070b0106090f080f0d0f02070902070f02040b01020601080606100c1b030b0903090619020a02060310060e040b030c041d01091a0709030503070602070204060b070303 84
    0x43c80143c01400a0f1607006406124040302e8404115600107011000310142032000009810111454a443c083c0203c00e406007040c0003590012580c5031f08002c10f0300c240c8800d640c404020541d203601c07880c2d4510b59054110b800e504405810344550f4090100000240200d0060b1044191504100800ca0700300f01070a8544054080508046d03040a11031070700044002c2c07016007407641c100b1200541c0c42002401260103020880084c407501d620030103c0307101c1e940e4850020341d581400c038508400c6c0d900f070a000030341d0b1810055000c01e00700003000040340c01d00040a04054200301d1405ca01d00d00b1a1070511842065004030300300a0010703941c50000f10322840141172070320304c3c0502303041e4001c10483c00501c905004a1515034500c49681e00002e442086500840303020039042c40c8040c07001c0d00945a04403080c080d41c00c0c0b500040411800014400c204140140850415514141e046070f8103101ea01c0003800a4204201c0c071000320345184c008011580c0058004100740f55107031212606684401810741c0042d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 46621488 1250 46620238 46620257
    0x507230d022a010204030b01170a021e010e030705010e0603041104060315050a020a0c020402030601090305010e012403120815060d02120604050105060d0b0103090c080601050a0b0708030708070e030d 87
    0x2903122003420340040c0e041000840c05d040c2980e888110810060060f0460103501c42c000b10030b022400c0048080c0c040e401f0307203946490034016a208a80d030f02444c440501141f0301c3d0115907000e04000406204448059681819280020b03082c0812940084c1c1705952401e0413180c0c0d030055490f14000c1000461084c2541400c480b1360400380e0045460241400c0450b0740100300000185501001003541a50100c0300182d0341d8460b840103803030ba01c070b8940c030060495003000c0881a28242c103500003a07a401c00000d003406c000b5030f500a00e030a0b07011140130040c0b41c0c061002c43c070030100d0300c10195654007154403001602c0d5030075041d00152668012881101e00780390001100840500e1107004a604000c0076507050003554107180c0001d0560080c4040541915550b2b01c404041d61f1198100b1292140c20282d034a8030f107034503580f8a5131100b500340a02406030f0303052640003a00100d4481105c55260f001165903046455000e01214003250180ca001d007007000307410aa0b0911745c1c05101d140d00e804419160003451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 46622738 1250 46621488 46621537
    0x30307020d0e090402040b0d0b15030f01110d0207050a080c0607110105070f110115120209010b030403120902060c10050601030617060105040c050c0a03050408100507230d02 76
    0x40800c0710840c201001051942540c01e6210a80b610b5009a0304540119140807030b580455112a49561302504415810003484180c40c0600c00001800b101601520107501c000c1b40401e00769580d900700e00000741030401c19180480400d901800c0c03074a10400584440040341e4030f60413525000f044001c0b00300c1d001413080c400d0742d80e04410a0b050340c0500c48004e01140c5001e10780030386221045091801070100c07000b50701101c0802940b219001c01d030480500041c1e15120f252500210f8803140301203000b0008138001141410b072403425a403085505a80d40e1540c4040500310801416040404a8211006004148513510144640703000d01c9102075001699140040c00101501d80607440001802c0800a81c02d500d6030000c22154151801030350042005018080110703100d00c10407402c0e07012406000e032914109070303001000340200e0314a07030121a610a541c042180403500252842000b207021110000d55404400880c039111100c08040c09051603862401d510a03607100e4948004100c0700718440b00c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 46623988 1250 46622738 46622743
    0x13140405011418091c020c04050901061a091f050c0c0a0510050f0c0304060807020d0e060306040c02010906060f0303080c03010806060111010204030602132909041e0c0203030702 78
    0x40c544111007420010311071010800548907055100d43c42c000310000203224031001c001c1c43d09950020010a08503207940040251280040050a4810f07402c040228107445014054041611484540d890300c1042d683c3c44030105902c0003410980001c0c00400901295080c0c00025114800e1a00c8165a80700031843d03071818501d00c1c20b880e6208426519083c456622811301ba405024023030305050740d990385520303410045405558004c02c400d12000078082411580500418002c21954003240c6443c2c50100c01a06d1101000d180103800c07035014000a05603151980010801c0c0c4818000002c40f035596803181800e4078031030381140745000d013080e10800815900c40d01c3c00f5800b080070600e942c03c6504020301d5035120300d00503140504004040200401300ea0302135045400441d8031440455844440701320488030700045105000050507502039000044030141024000500700320f20360b901d003010030401c020042c181d818a0300c0e55850760790304d080244507440c81540d2081016400651302c0c0d1030003050007132 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 46625238 1250 46623988 46623991
    0x51c18061b080601030f090f24020a0c03081905010308030603121303020103050606040b030a06060f0302160b1801060305010501030b0603070f0e13050303070804050c060f090409060213140405 84
    0x2000031000c480201d50a680b218030b0701e802c88400d180c0440d940c0d1048071440040e01c3c62000141c82c800c007003501d90040201c00d291070b0000d418042601d080d0394403a803224608038000d58a182010440c0c118072080003a02c14100280d200018813041444444452161012a0000d030000c51301c1d160000144902c52404001e0044035040c45280e581c0307004d841000c80c890181252000a06240e10b8401003441a61750200b610f02a02110504a4036880c045040c00050040d911404c0041000081d224041c0c611038001c0302e0074803038103601c103501c0e2101c0e903510400704c40c0300101782d4030320010014150b880070103003030003014000c0d40688c0004c2159410340c1815280301c85c002c0c20f07032031007640325080401001e00400c2c4944100c1c1d48030782d00b82100d40c4c0c40034019209184044002801404000100480d10344c02000e428000c0e805002103842000414052000b0b910526901c607190740340a200380c44c2c1c20300d02500700161a81c842d010142c00c00c3d001418851001c0420740000e041c3d0141c0800f40e05550a061040d076 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 46626488 1250 46625238 46625261
    0x3020f0703021c0311030f0a03050606041d06040f0c0302090405061c0f050a02090420040213090209031204030f11060304030507033903080c0c0607051c1806 69
    0x30080c00349158001942c100241107400c0b1030045142c1ca5405150050b0701384044041043c0a617503444500c048030b00b0155000c2d11105010030715040200f000c40c103010003174034203881942d248100380086c40c2c40d5050140ca00101026442610f40a0040740c5c1105401182160f05240e14090303180ca40b078108120540d02c004100038000d944442c02008818003640d2044444d5410400703401080199040041c108250240040d410808200a01003040052000700c0700c0111110220300c4950841d004020581c802c030003000e88405070b5808140142200c0c2c0d801400c03102002421144c001c2d03441d0020100d10f070059070080c0c0b02111140101c505011040e440c5440c0500c04455007440c610341590040c1c0f1030b00546101908000707841e44406020510380b480c0700c00001400040c601440c014901e08680c41a2407241140012101400b2034040012402030f100c4607241c03140078000fa0ba441c08421125a006001486141512240301d101d0114043c41003209208548501100501d05401c02405860454420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 46627738 1250 46626488 46626493
    0x906030b2202010804030306030615080d020c030705010f020a0203070303032702150901051308010218062503021e0d030c0e010e012105090a060506090103080405100908011803020f 79
    0x101c01a00100d50354811403a40c2c2400c101d1416151400d085008010a400c003c144524200401e01140e01d6112860111203004045650040440307030101e8440341c2203216140c150340400c0080c4110f6000300d84400c0410400c0c41103442c1031019400207460b04841d944258046a51800101b6600381c03084c020f6104891280d016511100062340030034451091640071800360341000c51540010381c400c0c022141c0420a00602c000e2003900c400425000b0b40c05003066070b00001c00d0824003c2e031800c1510070b0300c0d000c911030b07020003005c10b008034151210010110000c1701107001d02e6100c4c00c070101ca01b9410550804105000b403205590141c00078048a079100144401d010a60030051101c2c0c1c2d000c00d034224040401e10b4400c61001000c102c50b40c0769044070b41b17480040c500300000c2210401d0300141d1740c841c25005d4041800745850f80402c2c040419420300000e40340700f000308014840c074201103800070034840040c43c10141c0307141e403000d00c18215048891519032814468030f02d2030038503504018031525446100d01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46628988 1250 46627738 46627771
    0xc0c060709060f0807110307060c020c0f09010b0906090a03030e0102070504090506060127080102070209060402040302090f040c03140313080c06090114070501050c03040507090b060a080901150906030b 88
    0x14102c0001d0f58103800411803100001041c0b603118290008040c941803003100d88500d01351070701c44003500007031442100500c05c03044000d4951414041c0082031801c00b070907880380b03642801075000c00c903400251400e42100c0c040200345440d4440014120081d030182e590703040f00718607900c0028181000e0f9442180b180d170401d1074900c003141c1c01069079a044902406c18030603101d86000071848082d000440d11506180c080c0000802c008190001d110700c3d4821901c81c00d01d0764810b17081100308e0240c0e010194000c0401d80024503d40303102c41d96030b13420501860b6904203142c2daa6990000c41814461940071a40020640e1604407240301d1920010340f0000c00a4920100c5640102d03441c3d010f88000681001080032800d40051501002c45007100d4002c0c000b8011882c000032845460b60056070200c80502c01c0d1071300060100d500d4410722007540c1000300801c2c039016a81d80b04445002026009003100d558903c5c0607142d80c0e0030b400480004000d200030224140d03140d801c104140c603030001d03d02e0707090350882c21 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 46630238 1250 46628988 46628999
    0xa1202070c15020f0d03020c060a06030507030314041503090303051e060d0204020c06010b07031706030303010b030a14090c040f0902060301030807050f120415021b100509090c0c060709 81
    0x544082580c2c141500c2e210910124203089240250a20210115001d40040181e0780d9034150010810010201c0882c1e945407180c150200440ea40391001070241d8000a9091001070303c50074960301d41c0c448540041d81040c1c2c0703c208072910f0344803103904000801c0c1c0e224441d0003019003600030360303501c03040d448030a0000f0b540c103d0b007a61020900800300e5128400041181d011941c45605403001e43c00d901b0101d07607180d0784450b80f40006074000031058020426280046501e0320880704a0f5104000c090041c0d41942d00e4503d0300c100343d400140c1281d41081e111420700002e403000706405445082003030010100c54500c0c00911044450400c8041c01003810584d03c903003d0f0700c82e203048904483d40401007a07540c3c65607090031414103507441d20070740c46030007243c1c41c14601c8203030341c4054420396038041b4400034045c080c510103036a200d4050048820100124050744000e10341402107451100030360801c1071800708007000251070b00008540d800390000000c284034620303800c00c00c0141c2c2c0c0950582401e00c045801c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 46631488 1250 46630238 46630253
    0x221d091e01020c0102030a06080c09070e0f0109090f0c0305090c09060607111c1709031b120d0903050d030507120906140108060f0a180b04020d0c0b0a120207 69
    0x58500081400180c0d04a000e400254119080381c45440c0003151681040b40c1c054001e01050f202e0300140340b264180d0301d21140341440e4100d0003903806841c1d04112050f00c000740054401074868444c10310500b600c00290300107039401911040f0442601c0044c0b0010781e0301001c0c007101d01c058074842083c0c0c031188900001e51104c105064001c0c0045811b9a1912680d181010900140344800340e00f08103046041030f0a0a0f100d440c00c29114420810407220744140f40c00ca0003c0d01403042281d6150307001c100c0030a041501503050940650014050840409102a040d85040d4041d0b800900041d80c0701c10410a00c101882030707260741c3e0001d140c00d1001d410459001044d145a490500614603500c0e200c030410058035900034184154400c204021075a0f40e12880b40d241c480480e001e0443d408980300042c0010701d0303403240e2403988500c0420000c1c40f480b103403035031510354100620403a000500610a5000310f00c48400900041c040c56006070360314990079000900d148075200554060a00512a0b01c0008904 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 46632738 1250 46631488 46631503
    0x70603020a020318061909140306061c0218010b1309020901050301060503090106030c0306020c0f060103080f0c0f0f0c120d050906030411041d0c010c0503040614221d09 74
    0x2007401c5000c40c5400c0000d0800e2080511040000302c2d80814a00001d4201547c50b040300c001032003c3d05444410024540c640b0300442c1c00c90340c88015a550f6108a01210500460260015055044441c0e40c2c0000c110383d02800c0e00071030100040454149032003405a401d950251242440960030416203200207081408180100d40a102d00440040c81031038003588488011500700400c2040650340341050340c0250310505002d0ad007402504004100034000080b5503040303a0307002125918000d00e0010b0300c280d40d008030300f51521a00403100c5150303d441c0200401703851585820301400500c14007808102d11204a01500425500808001d041e00b0b5005000d80f0b180d000c043d21a60b40e01e07a1a4940440c0c0c51b101817130400d5000b0f20700b25580d23100541607120540d8607580481100c3d401c3d15820300542d102c900440c0010f080798000c00c418412644201030001c101854a1100c81c10300010094045e410b0480942c0c541c4002e015103000c00c2548010003008000c0e80c2c00104600340c5013042605562076441c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 46633988 1250 46632738 46632757
    0x302040323030f0d0203040311191103030d140130110f03030315040c0e0904020d0201020a050712050706031e050907051804200603070c030c06060303030c02070603020a0203 76
    0x680203100700395014000c031010400e40c030640641d280100d81d001030080d0425201500001c08284405004920003e07241e02031210b000d000005a035060313983c410303409080b0342000d038141c04240310269130b0100c1da000c0c01c00046030504100c8807541c10862055070503644a10380c0350f0070145c2c604800c1074412840c0304058040743c2100c664040200c1001c081480004840341c078540521002040150122003540c0c0c6840c1c41d9421a07003400b100e8003005049880010031040c0c141d00c0212000403e0040c60810807441441e48180190b43c0f10205a884490901486602084c0ca2116503080b030301c00c00109006020107001c0c00e00701000031b40c0a1044850f41c682a2017840104682e03188041103408000f0020303072004240c014460000d0050440c28a400c94005450445003040c1e0440320301e011811401c40351034044800f0345102e0540c0eaa0410498000016a0341681030055500f0f00c031011071128014040994000d4602085141c4180f500034549207541d80000d00705031041c85500b080700d50110480d110781c0c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 46635238 1250 46633988 46634033
    0xc0f0606031516051201060503150f1c0501090503040b1309060e010b0a030b04020c03040503070b09090f0709030506040308040b09060405031e09030102040905160c0c050402031f030c0f0603020403 86
    0x84442c00305584a1113140d903505d211010340d5000080e5103610400441c441e00c40705d0100020382035210180309840c0c1304010038036400501c0154120030410007030141c0c1c1170b29004800125500c1100d4842c0c900f9580207402803c0304000004022480740038041f000f4000300001c04081011920703108805420843c1070055616206000a03401c0d4a1403003600b10700421040180219039414101d4486070383d0f80d00a1290b00d00900030400c0000d55101c001066070310006000c2e10040c0142e071504090070b181c10b0001d141d481030040400e004030101d00308001c1d451066210752580c1e000341c1400d042c180b20443c002001303006294403103c01c110000b500841a61002c0b140c031503004181c04400c0c0d544900d58000da44d4101e41643c4003141c00541c2d041039810075409480d9015442c02000e00c510b10031902c5900c00900503080b112164000c120780e05240e40110380c1706d022808941c010503001020303404800f505c2e60094458241c0b08e00244501e101852600e00140b005080c11845c0a186a48108011a0303c071440200340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 46636488 1250 46635238 46635271
    0x5100203070204060f051503090703080a090e040807060e06130201030c0e060c010609060f0b0f03060604051c02030c0402070b060904030203070c06110d0e01121509020c0f06060315 79
    0x140200250351000c0c2e0b00402c1070007010349462005200c2c0c0c6051103001c1c440c481004440c0b01134040d01003160b0050794044040c00c180d5046845400142c1e12036030150080100054000480400510116008600c1100d04660b244083c1c1080000c0d41c80c501d40e54102c80e0001c8091004402d000761402c0300e210b90a09000c6100400400c040d500d03001d0038045d40d0380240340040e2100000e4019030014050751040041080740c25110202e04007004264082c01e140c40c54200100c252244440c40a0742c0d0060004041a00c2c054441000c10b101031181404903240e5400c12014204621f0107001d17181c0e060314240e41c1142881c0f0141c03940008418003506080c02034554030003040c00d01d031081c01101c01c882e0700400041d07122640c4040003050151054118182801ba48450980040c4909122119200140e642420609812110708000c100003103201003504000f800006500319140003400461039560050312580540c01c04807400c00030002d0060388260418880349041a410042d0b603608005e40c811f07015440e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 46637738 1250 46636488 46636519
    0xe0919060b060c100501060c0b19061206021201140d0204020c0a0b0c070b060d240b2107090203040803010303110a060515010e0a08070b0721090f0b0c060105 69
    0x14000c01c4500e542001002400c815545400144140002000c0c5400c02140e07076560070440e05010a00c0c40208440306079004242d8603075140c404d002078401c032900001103560b590072410703040e0b50024604841003034000c21141e41101e01c0c0780f8560300405a007014014080c5050300006c070040c0580070002e21035940815a64180202084801c851561002c0d41c1802170501d4100c18442c0d0b003280400315240c1c003c032400550241000c0f52112186075225501e50a0101240410604491201d900e000c0300742d681e0b00c9050301556070802109104c81c80c4180d400c1003201507000e040c01d00405800c85030318180100f0600c00050740201c116030450b80c05150640302083d482e9440d07418021101c9018002034200401c0c400e88440c60840540185001d8880702183c030107510502070144050305c24000190000441000f500f07403050000c1c0001c038868440b042c0b0000a1043c281c4d5600c4c02c80c0c02c5080012068601400158020700c400400f404032030a005003880c00c5020360550b00c2c001409064041c180c5c0500c586103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 46638988 1250 46637738 46637741
    0x1030f0207060c09051302040513021b0a0b07120504020d021c1b090501090b0108010e0903091305010503070b040305060114040b03010203041202011503031707051306020601030302070e091906 84
    0x121554000c1c01805080f61100000346001280d009840c803502c41c0740e04070f0010540c140308a6040300d1000d44180ba24281700001d1500a400005800f614000b00e10340841c0d2004090191410152003011000c02508040f10000c1818580044592490740381c0010300c005a42c4400d004010503504940d040e07107010a4811866100fa01420000c00c3d04000d1105100c2c0c50f141a0046800d861007008108143c0c0e03a52480320069a008108050124079030f8001800107080e001c1000358451030701310031a4903103650761000c140960240041000850350383c0006002c10300d801c0c4442ca009118404004d4142800e540b00d680d103584062140c80041881c0c0f400c04002926182c10230741c0e215000078000c540741c0c03615042c520080900090010019480d1031020191180d82521120941b90141e981101c500c5401c1c6581068810281128080c8807040c48071807500b01c1c5c011040d40c090601e550241c8050b5140d8680a803070010315420201c02c07498080c003003091841001402d4202c90b80d40303420483c60f40740b40f07052520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 46640238 1250 46638988 46638997
    0x1401110304080c1516030f02031306090804050310020c060105150a05090f040c050304120801080d0e130207031107080615130608030a020a02130204080a080a091508010602160605030601030f02 84
    0x3d0180303a07034040000c030400d00c810440e039171002501d0500c107608929000c0c40c02c0784011145a6428461044041c01080030741d072010f80d450384215141440c060312540000d1900c1e1240d658440015000106041406400c0c800140107000a031a40350081c8003079440304800c0d01a041c0d0302d0040003004203c88081e80e1b1411030340e00240901501c1003218080d01400201150700c115020f6500300340c11800440c03408d101d00003981c102d410190240040d030b00400c0d03007160907108000c400382d07210b00e0301401040603a0040c80200421480794507003101c030400d942200303401c20100c1d07880000341c0d800550420100c0c3c2c41d00d4030066605401195070a4580400105010050215800c00c841610021400c4512242c00048120109001300c48140c123071001003000340142d02c1036000b0183d19400c013101c9000040ca203038002d007017008440e0030701c0401607032901045ca000d840c203010200d001032108401040900d07014002035054504400140240c0c0e400c1c40005803071f0b0304c0007826180c10581d484482154a44c80780e41a103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 46641488 1250 46640238 46640263
    0x1416080403080403051606021207030509040e030a1b02010509151308030a03060506041203140d0c0903031d01020a0209100305011d070b040305070e0402040b1c1401110304080c 77
    0x65859507200e0400410640090008441d140300b4460400e0001c4e512032664011a204d40e03008003502883e0343d00c07000c05900007007401c40c180181031220900c1a0344a006084d03002c01014010354417031540000080c907968a0507000a01c0c0248104103c0150741d0104c11521030400503981c081182442a9400d035042c440c1c401052410f1087c06000304403d60084000c00c26030301255001d02140b43ca0340304001c018412481080b01d903503178094034240000d0180d8403510ba00300c4001059400c140d2003c60341400e66110302c074000001460480706004068001070240610000703c48600611080040040d40e500020344020303201300810340002c0c0da410b1425403800080d50317000f0000d202c0000700d054031030328907005c0888680741802001e4012610f00c0d041c40c00d45003140d070032000416060346054920303007565501520030307a0419200c03050305019032150358075407005a60b5000024210212400e0110b02c507007151060420a03410480440c82451521040c3c070b422542010303006680d8103079840748030314021051041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 46642738 1250 46641488 46641503
    0xa0311040b07020919090b07140408100b040908040f030203011104120b0a0f09061e0905060703020315090c090f09010b0406050c0703060608060106020601090c080c09030f03030112020a08010c1416 86
    0x11b0400c000c20105858003485030f40d1101c140d039400e0802102c1c0340d1b003e54042e40d04c40354007000540703804400c180c006c0003400340094000030303400145890b00915035026802c40c48003210404420000c5081c00d00c6503035002040c0f0380316203080505010489043c9040324001800761580320020600d600d4141e0700c0040c1100104804120704041c602d0800c01a1a50058019420f81241031501480c0ca032030045200702c95000300580156910b840042e0002c1d08043d1054808100784a0040c41d143c4442d14028000c60240103038507103c2c22441e040110b903600000040f800356621000400035041174034141c4e010f03100d003400c005881d00c0e607109410b0b00e0b21f5000d900281010741070000000c1d0100010031090f06a403020342c01d8034420380c1c0304c000c83c9041e15024100c800015a4000009024081d00000303007618a1300101a1492006035980d4249142c00a8004510880074039400b44218500203400e100108400c44c0240180c011940002c0c04907804800118000070000811141100302c0104810403543e00000303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 46643988 1250 46642738 46642751
    0xa060e090109050105090606030a030f090f1d090f0c1302071709030f0a030914030f070602010507030e0f070302040207050307050609010f141005060a02031c020a0311040b07020919 79
    0xc540a40032001c01a1115481e200108401c0301c00803030424801c6130040c0c0102001806540c00716401d0300007030404020007141c0040440c2040c80014800000c00120824004043d401c8203078107455070003d4000000382e4007094010001c000c002c10140d440c000c0444d11034080c240040201c070301a103d101001000a00800c0c00080500074a5001d07211b1108103504403512042540c4441e5580c18000c2c40140c00302e44009001c001300026615404c40a4401406551481072980400c40c5403440c50f400c9080540d4590f0100f00c20f2580c18802c07402800c0301c2000405080b0f1a1403805a190b5000d03000c080d0290390005902410b00108004980500c0e074048220b811514224085600810046d1814100503003444004110381002c43c02840c01110a0840340450314135007010402c80b540425625400c0d40011300010000e2410315081d042c01c08807284000da07030340010b58030040031505500401c5000c000140300c203020701030202c4151041c0560542d1260042e4491034a80300b02600c8900c001c101150a000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 46645238 1250 46643988 46644001
    0x12110c06120f0606070809060904140901090311010603030e06070303020903060c22080c01030f0b030708030d050c190e01030b1012060906050325080307050a0c060201110d02030a060e 80
    0x80064032815046030119a951103d5041081910944001828002c801e02008403103182c88070080c40c070358200600008544070380182c504d40f109001c603001000e0b65519618a000d1640080c2064040000d01000700422070035030307070051308580c01c00018501031840840c0b18010940030340d040395000c1c48010100c500301d00e40707507500c20940e82c00b2540080d201840e40f0311002c2c000220190b00300c00c2c2c1c0d00440103070005d015550f0044000382811001021442d40b43d00042c00c2c682c500717015070700140202d0345c0507668032104035822800b90b0310b0140c4120702c0703000d0170040000c400b03540b4050b40550200c40c0c074002d016131030102c2c0102d01801415023180d41c0b003c100c0d074041b1181a08608415856140320310f0602c41c5568802142040324074030b102c3e940d05a040841a460400c449000c901030303a120341a035070700e03551b07032030f810402d14503040414111038580c000f2106109004001d4110b40003040d46d44000e0103400c00c000360741e6186024240918807031503008004600b2030704944e0409005000d40d40540d460501d080d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 46646488 1250 46645238 46645267
    0x8040902190e0604030803010b03060a03150605010215060f2202030f061009052b0c060302090310050907030f030201140c0d060b2106012610060203030412110c06 71
    0x250441c4001c100d00100c070700e420782072400c00e581c12a07070080002411a07103001c202031056880149865801401d291001c400204d200000f42c0000c1e069010005007107080200191404400009106c503201c07a64081100694464090880c181c3c002d94082100f80d10401c04040b80d00d40c561126000140041700308103000c1d040b42e00181c410f01e02261050341c0e000b07902703606581c6a0ba0358000e1580015800c40c498940b601018030040c28041c500c0c20204010000d03440c2c02608010070341180001a0b00001c6112591604001c50f01c04811411410000c83c141034803041d544501c03a05c00102211080c0e00700d401454001e500c4a9448010159926482c2c9044410f200950b8071420603001d84900c0c084c8080f895003d03000603101500000b1544c02c4920420340341d1740700d40c4000108010b040100e510031b6100f543d119201d0200701e2605900040b041c504100c1034007101a04241c007d41e0840d031040c000c1101044030b06400d100d030307100071341403010600d090f000d446820120594000d50b00300000062005071145030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 46647738 1250 46646488 46646527
    0x3020c1f0c030f0e061321031b050324010507020405010306060f0b040f0608060103180f0303050705090108010311030304050d0c09060b03090a060c0306080a050a0606050a1235090102070e0601091208040902 90
    0x6c0080f0b5440d6800c0270300b001c0d01c9500066442c00c8003500c1c80b00d686609245000b801800207401414900d050240c513600007000d03188240c000301d40e00ca890b45010040c608602290030098801001000e00b05420b160f855003441c00d040c407030341e002c00602d5804140740d81d000ea80030516000f00b0503d41b4203030310301c18248079203640da010204800003403030200006c140341c0c45042681d02010f416540c089040e4a1621b4060301e400c20230304e80301d515000030840060f0942d02d000340780070a0b07031144d1031586505190054400032209550310004507001d0070410415150710100c0d00c00d10103a80808001028600c803d011001442c03582c100300c00d688210402802402000500905201c1c41040288001c94a80043c001401a18406c1603001c0b5154190031000514101e0100614100ca100e041c42911005207810440c140c00c03950b110090302c001541d1587da5a05210441c080c1020504c10080c50a022000034101102031003a000400054511841000114811980101a1100e056480b9000030200c100c88401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 46648988 1250 46647738 46647761
    0x1204030f020f011505190803041203020c0108060603010509040c03080408100e0a11090a0b06180906030a17070c0302031006050a060216030303020c1f0c030f0e06132103 74
    0x819036055401c02e014054182190072440c00319010300d25060a1060000000055206588407210049020001000500020580e280300501c0d0001da609019003401d80e00b4203280e0401004008102c0705840c0c1c01c003280d0440d982542c20706405e50f100e082000340075009810050030f24000080c0010100000200c50a0300b4884500402c40a680d07a528a5600d0004084c0280307407011118807410720707103800c3c1d1905505c44204100411a8500031002072800d6020301060040354055003045240c6040418140754060802e80040011030072644038504007501e40700290706540c50000385d000c100610700307000300c2c001c65010b42203038070342c1c1c00c105404000361005010317140c0501003080300007950742d00c0043c50803409181c96440c60400f90071500c04801079400812282401c0c412202801c5104a04941c2213020180740040040c0c0b50f4000000101030314002c4506d050035500340500100112000708100b50800c0f0002c002007459804e915200404441540c00d07540f510a44150b85000160140c006000040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 46650238 1250 46648988 46648993
    0xa1406060a21060908041203090f0e0906160504090f02040302090609150409290f010603110f090411030a0c020601230f01141809100506030f07051204030f02 69
    0x82d110203154051045005440c104001a540e02c0404254244e1200070300c14000d07014149069141c0001a2100c41a4082200003401c030400402032007045081c1c41001d8100d9515030300e16130034030250340d5903200301c09070202c0b0140da042109040140d000e05c080b9401003d100600f40140081c100804000703400070300c001d90040280c0400502d07581350287c1d409201d9004200d001c102004680c00b8031005100e8603d0803260103480c80400101c2c1c250f04c024860174152165088001841c00d88003558420f401a8001010f240c14082300c07031081900c0c1c00a40700310171007560016488544110014025101c4c100b840712030f8210010601000d540150400c41000c40c040c1c080398400d981c0d40b100000c000c40e080f00f00320703030010700e90060f0300c3d10389810345d00c4400c035000c1407400c102581c0d09004081825803099610545055450711042035500341491255844800381d800c9011031440d01010a200c0d100c020100c480c03941c15000010a9a40a00243d07440390b031120703151400516103071901030800021013000c0405403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 46651488 1250 46650238 46650259
    0xd06120309030312020409050906270a0605190504120305070503010509130309031b1a0316080a0608030703030204031a0903160302010f09050c010908030a021b01020a140606 76
    0x240008202012140d03155454804680c51078038200c81d0038070030742e403202240c6400f00000999888a8003400703001d04200c501500c0036061000b40d03c03529446040103540d07007451004d0601100c180100ea00e03e285900180082060b5540440741b00800c242a5a010781d0b0318501000d000c00c2c0600040c1040c100515602e08000f5900c52031000d440a00091040940c008401000611480c1680a5181e00d203482030400808441d16560740e2049000d2110b00c050222190038020800e06002e20920500d20aa20420034070b181004055009003080103ca00410306c007020010412940050b404040201915426a902c600c1d440c40c000340603502c684815990310103101d00c80399604542228490080800d04000c51401751400381104000c0000c035401d40c1503560391080c80c52010b10724040c2e100454401c40252901c64000000035040d042c9035005010f01d40d10500074031149580002d142d0210a104d1090840619070741e90040380343c614040c8004103014080c0061601100c80055264001d400440d03151200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 46652738 1250 46651488 46651499
    0x90e060402090f0108070302010c0203010212250302030c030402091b040e0403031a130c03150f050102011808031b070210110705010c150f0b1c120807020a0320010c0201020d06 77
    0x700c0c8003802550178a070400402000158052522030020030f10150015003404140880718540c3d140840750b00d5441412042c5405844007400c0180c407001d0200d003011411030500c40c0c0c0d004241d0000070f00003030107003407800082030f40d0300c205075120707039554170350740304643e521512642c03102042c00080c0c408034003090030040e1006c0b0002d042030080003104405811040703405d200c0b2600034040c10001044109160b40c2e13076010720b504040071716030f44007410b00c03407004a04152900780024211040410914444486032640c034002030803200071250400e6299100901e42100c0c180354881e01c4c8601f400c000d501000008250500507002069004020700c040150b544503551440150384030303011010000c000c0084440b61000700c0089034445928088200d8002070715000410109404801c0e007480c641031082c0c3c0e0220f000400034003d00f031142000c1949411b90180c1001440655210050794004080c404840c41003400f54600802c00458140760710b00074031a03141011300c064000e42c840501c1d400c0340360070880013041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 46653988 1250 46652738 46652761
    0x409020a09050f090f07050c030703200313031103010b10080402040e1c0315030f0503300106080603340b07030f1101090b01060e0f09040215070c090e06040209 70
    0x342250182000b03400390398000d10040170240050014091110a008040c808031042002e0004030b803094490688030f24842c0420540c3d50b41500040c4210781c02000012404021721050800b12607005000250300404103001901401161003c80d411031030421908000c1e6510001581c040c6009443c100001c01030303503003403030745406003c5140c0505c0c070856444041140e02c00c1d40000c42ca918120904111240c40e540d604010300d000543c1902c81d0341c40414020f400483e813082c4210717039070800b11170035000203149501d0340c104010502c074650601111000099003602c040c40404806202500c80c0a034421682c0c0c20700c0d05004442044a80d4001900d001080c1c2d51607000881e00c9541e0103486802c1110801842100c007641800d00d07403400c0b952151503a00002c1d94038032600f80a01601c0d116829028161800c1c00100c415a18005200d05144028000540c842c0304801c0322006513581c1c415521205400c003060040030541c0130091711854001f40ca030803054080380942c0545d100302c03150343d103a44a061140d01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 46655238 1250 46653988 46654009
    0x140d02090d0f140a1101050a0c020303030a02040f08060403120f14040501150e06060306090919051b040b10050d0204080615030c0d111011030d050109060503010204030c12020a0b0409020a0905 84
    0x749170fa51429009a1a58060780241598903818584107003190100e6000c00d08641045d90f41020264010070b0a0040c07240001610000d040741000402151410341c07001404016a840c500f0b00b0f01d5607801309808545000c0e08a0140300303840c0d80410020341064600a4020051400309840040d040100864015503042c0024081c500040c02c060458840908100c84060003504030f0304c09106640d40008164031507112042c210340120060718261404140c0c4a0383c51001c1d8601d039104078a41605900d60356900b41e00032200610038901662180d81c041c0000000f44183d8000301424407035541044400d008200240d50111019429208694280e80600c00600d203001e074000d2900d2640c0840e66481e0400d100000c1c045000b40c54203408405041c140f041c2103922902201104d141c4400050009120394040d200003080281d000b185400d2560715030350028102d0380941040b5400c2e00000b0010766840c1071920014044105219940d56900c4680d44003d42c8609140404a4a4910000b4081c5407000840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 46656488 1250 46655238 46655243
    0x8070302010504090b040b03060f01030204060f060c0b150a080c0a0b030103081c0f0501061e0206190f09060c050403030909020f040b0c0a050105011205011b140d02090d0f140a 77
    0x341824140303400346005d05000051203801681c0c0721141700d0140d604000c141e004020840c08200c80d0350541c0180400d0b103d064010020301c03503030390004000c81d9620049000ca615000200000e940e1500740302801408031452941d50b0000d40900080345041000c61003540e0b8510071030780b410800e42d80ba0410f40f8540001d1001800040040c019010180d0002400300c0019008820000d56408040d401e6000c441d002e030072160020b00c0103031040c141d81d0707400004041c000c1000e0004250b1403400001c2c0b403507201c2140c04803165242d100c07a00b600c504003d035013017009180d52249080c0120444400c00420f0f070303000f520094000810020002440c00c0952084401c81c40c20728602c139140608100c02100301d41d20900d080540d82c0700d000030b21800b00328280b16440c041c1132180d81c2108403985a0629030f0030b50301d101c0301441c9400c031660751040c0c441740c125410f01c5100450f00c1c0c0e40e035290002d1032903c100900409201c0c4d82c000d500c05003018100b01d520b444003028207101e8030325401114141c0042035554080b84a00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 46657738 1250 46656488 46656497
    0x60306010803070201050d0209220507080f01061412070206060108010b0708040501051c110405030c041a0904050f010606050706140601080f0a090f0605040c120510051801020a0f02070807030201 85
    0x50000365111b90f000b070140e00761800d0b02510b44080e440120703119a440708803420b81c030640865032200b041950302070103030001c0c103030b15020440e820000012261041e061240100b40021849440750521403076003030340c20040c44d880c02c403221458481c1020352643d800303c40703460000360100c1c0042407090703c0c48103892840341c004010130704190070b00e0300556440e8000030f21285141120303805520005114010303103042419162040f5241ca02d854240361500d6044241d06125604201b107e6842c0d00e92090b07003810000b0103e80110098035207042003801d060141c01000c0c0c2c15402d01202040003504507000b48060b0b440317090100300d82c400c3c40b101c8034500c00f42603c12034001400800400d090180c48422650013541c1e06000040d02d020550303410040d08204102103950710b03210401c000a00000307840520007401803050410110381c075951016290302d80074204800c23480e919004920503183ca522100101c044941c02195502c42040001e01803908801c503040041c41050742c00324051038045009011254180c48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 46658988 1250 46657738 46657747
    0x15020a030c08030a060503101b0306081b0f03030d0e0c040203011805040201091e030c0801020903030f0a0905040c0e03160602100e120a120e0a020616020a051005040608060306010803 80
    0x2904251540003810000131070780c940e480071455a40034070820b1402141034400091039050ba034420326400c4080e040f00e00078985000810804071001041d8400c0d420214030703185401540800004940080d00c0ca4401e405200100d050400510309034041850741520781c0032144040b01d40401c1106070300c824012102c010300600340c04070403440380703030010794026105041c0384504030b807106502c410850307441c0c51504022604140400a1007411070220002c1e0108000a6141446040c00300313a807071050050401035082e0001e950310a0130f22450070603015101c001c006000f00712500700024101250802400d00ca030042802c840f031030200b80388080045444507005840c52245100900000740318101c20b00455019400d0b00c0110300068400401040001c1d441d550f40d2162a130400710101e81d04102d601d900c980c850081200940c0c0ca000540313203101043c42401a0100007480032640101603644072a03009101e540e4450409078102c4090010f9490a542d80c0419a42d42000c15640d02800c3c8184000ca800800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 46660238 1250 46658988 46658993
    0x51509010810082406030705030d12060504050f0a0506010c0506060607060609060803040812030405190f06050f09010b0103090206070204020a0504150c060b09040b0f070306050411030115020a030c 86
    0x21420b6000ca07503103a5221210b40d81d83d0855080c410301c000800c0e00700b504003265944400401100c190403140039401040b0042c02e00c000300b41d541c12105524000d100c01200c9071000640c0351303040a4091302010b401803009040506c40301603401c2040c0e9401d03200303d081100044284d40320320041d170b2030030740c00100800158950f2000d1011590062909517902d40e146c0c032010803a4480390141000902c01c0000039a41d6034a0510541e0400a4210321082d00e810104248030100707000040314500312042e0b07103507540082c03450302c0d20030740b840c40021000703241700d0030b2004201207815500441441512403400038031810002d0001182240d4060800035400312047c040040541041d90260034000c0d0383e401c0c030707070701d800d4032068542940c40c40030041c140001c0c424082e950030041580100303511528203403220708603818280e460a001c0385005002000700c9120b030000800662082c2c01c42c0c4000d04c40940208140c107000c2181102640c02402885151502c4580480241e440007482081e602d07010b6a85003d030000f00d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 46661488 1250 46660238 46660247
    0x6120a02060d090b040c0305060c03010b0904150e04060b0a1e0b090102190b0420010e12010b060a0908121e070c0e07030207120905030307020d020303130e0f0105150901 74
    0x321800c525aa5403d440c0002604003104240124041c0c410a1002c0d46503280003450940c00400018800506000403c02c1c20404010f03100c10140c1185c020850b00e0102902d181d481c1003d41c098131916503524140401e010a40e804640307090019141d02455a40b214502c540703c480307030300050781d1811607020100103002851001d410940014410b956101140c1c0c506241c91441200c81941c28103208414001004115130400354001465550450b481002000280030b00c2c2e4040c196602a055100d54481c0185007035103d0140541c009141c03d864940485000b0008170150090504e90f20030b10b0180300400710014243e848000700c411884804102020b00c2820a8000d0360084607046980740011405107c19100148160100c1c0c1d070040c1c035039019052055201103820076032070500071021018032a584011080310901034040d98401c0380d40c41d09101007403841c4075611100050044c1c01101080421003150424090401a403043d078099880d0400c000341c070002e04032a844a640d04019448055004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 46662738 1250 46661488 46661497
    0x3050d050f090c0301021903020d0905012a170408030901060e0903040303031104080303010515040503010204090c030b01030c0207050d051f14011d010312051b010221010f090b0a0f06030b010806120a0206 89
    0xad944000c00c3e07040b802c0d501c2c0c50075030b032b0080c010300300700070300b040302c038000540d100045c84e140f49024501414500c41c0e8850302c102015000e4006070561000100190801c130b030075044000280030780c5490300b44038613114000648a41090000b240000c1c10811101001c4c4590000d880507178006101541ca182d10300810005c2510b0380c80134101584205000c0001c0b2036a084c4050700c0104400d07080895500b8009500908840c410f9800d2418145040c004400d80e590020700942a113506540410302080c4608141c0c5c68115580c5102200e0114100484244103454201c05009244091511a581d80f5208122150114104142403848044c001000445c440e6080c55011000905106140c0004400d1203254143d500505001c16900000c000c2c070171728604161007130b49912074038401d03015505003030f420080d045040c400e032200cbc1611503250340c1065644c0f00c661001401046900c0f012543e07202c0380038025002d011281400720303c03503400051483c00c1103074030f070381c0d5a040c01000340000c21019400c11071036400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 46663988 1250 46662738 46662757
    0x10f050d020d0b07020c01110f060703020a090e34020307030c0312050a09020f040204060507060b0102010e0601081507031a0d0c120807060e0a0302071203050d050f090c030102190302 80
    0x10308070690804a0b05449040e03002d070804e41c4c09410444400c10002d0008880d554454180e40d0120568144000c0f000c42e440d600841d0a21f805a0340f946500d00445502009402900c2d4548410b81030081d603030240003140003041b80e00400d43d400d181402c6a0b503103131401651040d1026820070025900041d218840d91543d41c1c0c424240b4407409441c40580004940c811580400c003244d4a000040c1980707410b50304200101e20803541549010300304200101603000702c4d48000c0040d5260440750300d142c3c0c001e401c071198160000e07017150700c80c0d81d560345101e41d500400700a2079881403980d004102c400b4446e000700070341014000400444220000240040c0d1f42100318181e80b00209a40701080d03030a080301000c000f03107002e00344071030b220010b6050590480304860400ca54603030100c046080081e4005c03a80078100c800d80b981c1062015114207050b60240724246104650b5840d04081150031401f10b00294011804541114000b41d0b038401403600f02d11814500020b0070404e0805566080e02c00d4005003220340307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 46665238 1250 46663988 46663999
    0x204060c110d0803010e10140609060702030a0b071e0e0d03080702010b0603010602030408060108030a090b0c0a06231003020120010b0604060309121404051e030f06090c010503010f050d02 82
    0x1400f034554200701d1300300b030700603215250250051044410061101704d01400c0a007001203c5000010001001c0d44511840d044c02504d021924200f9507400307000d086040303038001143c50ba562805000040140ca841004005071000c03211035102e0340d9200d1065540c454201030144a40c0c03c0d510f40741600c029100504442c110b40d2200309410040c0c03109000346008081d81d070019922242407034013003402c00c07105800c651040d0b40144a200040d592000142c000c13141030000c0b032070741c48a0b00c552140c01c03d00c5600010382120309008000f0390a030511001c1e18040581c05850900e243c55241b020344d40540b451001a0014070000b11030150346c2404500d0500400d000000000e018060f00302044158025070302090229580c0c00a000a00014100056030519903140c9100d426080c5402d00c2031501544c01000d00804842c03800550012100c81c00e00f07801130008003201c0c01c21010481b816a92034007110341c40550300840c404880c2075402401540e0590f01680b058a07425828002880404144200141d9000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 46666488 1250 46665238 46665259
    0x50108060c0d151401030c020105060303091203070503130509070201020a0f030509070302130207030906050304030c060b0f090901060f080a020307030f03090e0412020c0d02060306040f022512030204060c11 90
    0x15036010440200130a40903c2c129012000001d42110b002120500669040500308505030b500401152a000400c4a107005003c2040320b8592440c020b00c80000c000307110001340f54000100640d8803504580c07003211540b281d541c0d8a00300300c0c240d000d003402800c081120052066800d902941010303900440200072211079503526000510701820b0303207050380116a40003c11206040d44080a60003502035405c0051443c00c00b40c1d0000c0041d80302040c098042640d81841408030ba0320003160302024080180791b0111800c100c58940d00030203451050700749440054400040c0d408000c07401404043e0020007a16026181d5140c0c40c10300c80703e41404400b00410301070003180d64068102c5641c001da000c0e661161501e8024213000c6d10341240b640d000c910905500c150b40d001a40c030001201d600c60b03016100800c0c00c0d421284044041d000310242c140320412694002d0205000c0413000c203210502039012045806c0204600707a0481c0f060b07000d503500059968502802054008101c4804440301400f4030600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 46667738 1250 46666488 46666511
    0x8030702131a0d1e08190201060f06110102121807060e0a031704030f03080103030206070905090c0d0608031c15080a0f030c050706080105120d0e010e0109030501050901140a050108060c0d 82
    0x1451034090f0850300f501d030115810340c0f03031b54051002c40869002400200320517810440f03440e148034024840c0508000325002c810940c02c0c030a4040d5046a0707590371212519080c003d000011341c08840303840303407440c3c41917980000712184109811034843c000600300c12102070658039811141c0380386410394100c00e03908120010001c1c00f843d0301740d034075180240d0f500800c0d5415490003d00300b16005d4400300c10492003e0087c400e0b030360381d10226030f0000c1c21040c449a030349042c0c100032009064141c2c412132290002103807070030a11560003488042050701020030440406008503c07030401c540743c0140300c003d0b8007110740c5900140030541c540d1000b80c003038101110b9808042d41c2d000d10f80002500800d0000350744600400c0b2600b004c1813181c55150b03842018000c60400da8900800d94036949031454100012900b0708883d50b40510b0019001e590408000c2c46180b8000d40b86074041d18000511078a0643c090000480001c4c03030b489254180e4a40c2405807909442c1d00030b0921064010321451a010703071b9142c101204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 46668988 1250 46667738 46667783
    0x1030209030703030c02031005010e0a0209450c0a0507080708031302040b09040312050c0913050609060d0302120708120a050106030b0301060302090f18030408030702131a0d 76
    0x43d4420742d20340f52940b06a106050034100c1380c4402884240c00c05006200c10301103442076581c4002000401130711130031404006090301c1c59205405036400c03e032002090000b842c0c804c00400c00c07901ca05000c201c008a440f0140611481101c005007002ea0601184001921850040055501452031039003081c065458229144e8015541300c24a40502c1c007800003141000e0041c0a040102110000603034513040d240542000c52512203103070003e9460001950a0150805070f0705504000740c00b41009020841d12000241015601d03141b040f4021000521245840803941c290300b60704d64040c1004c00800907440d20b00c1d4001c00411603039003c0c107200c44040203000700c6c8014406c401a40000c9100e515100c805021201041a81380c041d9052100510242c0c03100403005030000b0075030008036170942d51084540c0e100c1d4803d034040e990a02000400003540ca000001501d2030900840c2d462a603900141d00007021500b070181050a1039030a114a8040740c80c05140c4040c5450080b00c0e60b25008103071400856 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 46670238 1250 46668988 46669003
    0x304050715021f020306011215080a1103010b0f060f0a05040b070b0402040506040203012106020903160e0106051201090902010309060c09061e020a0f1515090507021c0e0103020903 79
    0x590001ca52000b4101c001c10320f0040f090940141145507050040c002402c0349021010b90032800d0303c4020750085001290350700e100900004080e00d4200d0034525008590010f800941031003903081210381002ca1401044e403200c40c020081c5040d1822510001c0b8100c1d40d0001c203007000c2840b0b418800020648a4076000f48481c0d0311030000141c940c90284100002c6035405040d041c040c92040c0014080b124503100e003141a84952a80321210003840d186c007002031711494240903090b00404c1150806007580c804950140d0f614a400403216030b8940004464a000380502d03e480300701200b00400c9407008503404a01d08a006240200c0c240146880301010380740e907402ea00340060b0100000708491a0310441117511195442c9007900c0d0f0480c00c01c0d00030b554081d10f02018044400403400c3e6401c0100d54101003c90a440d028184030305641d16013201c10030600342c8900d020386c0703080c41d0000d808a031010802601c140c442c1d03242e44407926401c6008171400c0e070503000c20f14141030703081001c640305a03000c12040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 46671488 1250 46670238 46670279
    0x2010612030306031202010e3412050609010b030606010e030c04091b080a0c2601050a0b12150c03090708120702100c0c03030509130218030106060c051203040507 71
    0x10807650300e980340030074074000d074813640710b085924084500070740408c0401c444101801010740b0009074032141081d84018241444c0303511040441400004443c0510041840080e005034140c881550717680c07400301e0a803150001d5042c3d15401c40c80000340c856005495240b00c646000d001c4130803d852040224040b1031000c03500390342041402c40c90050020000008001900b80b040140020048682d595074100c5914010700080c01400340d002030100310715240007040148c1c0c150081c03000e81001d400020042900e007140d10300031480741d07030300c102c3c0c503000001e07a040d45c007040e0100a81250b4030f4144031525500090031183e400d001d04040060703107160800401030900c1c80c14209a40d1001c071841082402c0c2d000e003400c2e206129840c0c050700c000c01c1d000380c800700072680c240c14100e0313480305480300003149a00e1180e42102d52510114110000f0103000423040300c4080154000c019640e15058152004008282c0007065a400300b4a550b402d007010380040c5400030b12800880f01801e4807a06003a4424510a04a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 46672738 1250 46671488 46671491
    0x130602030a090506010807080312090307050a0804030c06080f0703050903130303020601170a0305030a0f021c0504060b060c03070f1401060b0324090a0221010611011506051603020106120303 83
    0x4441480400d004c4240108071200060030114a0a14a03903107a0007200e510100d07031084100068444601407007202c043c0c503400340039104034099601c0c2c100c3d45a0040d0000781c03540310101c9030105401e030113503a1982c0180211640c901441d901c0301070031005080002c0c1004824007041c00140d103035040c0303241c403031028601c260003800003581032034446840080d9904462200d5480001080082034000040340c1e080200c00324049254051070780d80d03034042e218040ca01c0c11450011304a4200003a41030f1302050103a031103250140000341c2c106040040340c1c040c60350704240680040010a00260801e265601d2492040780c258818080080f491405c444840d4040d40d1024000000c000e800d03d0101005007201005503802a082445071000c00c90750741c802001c01c442160300203190450240010f428002040030901400000d68645900409000c0d10540112896080400c400440302a005281c4265100e070340d0342c0750030441c0c0d500d07040354002c4211030280c2c155581d5490110320030f40301001c43c007a59030003501c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 46673988 1250 46672738 46672751
    0x7021609020a030f112205060d020a030e0c0105090409061103040b01031703160503131704091512020f0607060504060b0108060f0307090c170a09051213030b130602030a 74
    0x5002c3c0996410f944030542e032030b241c8409010380380c84030415103039000610480fa00061000c80c00d240d041c8140d90b0007195025002044451641c6403540080a400c54203660900545a14126140d6948109443e182c00b2600c01d00c48009241042e500c10403115004440200d01907883c54011541c41c1c1c001e60782680d844840c1d20042c018410f100442c0e59065602e16442465071402c0d8020007004003401c0450b408001c40000849e429510b4115900c40440e0131602c040c400c096030303c03500030003039001c0d11031005101d0410403d040c4440f404480b02c0111101004001c00a031501da0130030030200f0b000d2a00aa210805110100100d00d040c8a01c5200714411640015541045000941400c50052102c6d02c01e4011702013030006901e010071b140d4110f820554020801c64030718030080c0d40c00c101c0c044860600d914007000b00510f004080e00304490590181c82500c0c2400c10844a5407071520600c1c000d06201c9528110400000703058070389060780140c400d44258004041079a40c00c0607a441034903041652500d621 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 46675238 1250 46673988 46674007
    0x6020a051b0d17010b070204020306040207080a0206010303110a1703180a0305040519061205060a1502030301090f0b0a031401090606030b0f07030e0a020d06090f0c090c05090f090702160902 83
    0x403144088611504407007030941c581010303000c5d54402c104009005503000300c08200180c5860b0160b0740e0b400e0784103150039210550750f00025500c07642440144c000404108152903080c0b4042907004004c0c0d0803100052100f6409000d12046500191040c0200011581a544401401c2c400b2840b40c0f40f295813916580c1c1d190208100c15444040c140315002c0c2e54002c801c0182c1e036003000c000742000500b00310100e40d640c1d58100150441030280c2c002400254102091003030180d0200c001c0d4165070710144100807081014003001d040b90700711060a5080550b120341840030900002800440c0c4e54114008528400d4964408050b07810b99401281d036010090140103400ca14095000c0c0d00080c1880d00300880e81c4500652651010050780c0640101488110101840100c1d0022105590807140d480380646151030030041486452181000251514004596052080085900201c0c0c02801d01d81c070105007008128102c038000d0001c400f54451150400c0d624214618108001d00a007000141c40d5001003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 46676488 1250 46675238 46675247
    0x307020706030e0309010801060c030309380103050c01050d060b0a051b0f07090b06040506030f0405070608070c080307170a06090c0206011d07170c0409140405070306020a051b0d 78
    0x14085600f850300305010111007640d20041490444107686015040404503040035001841c400030054002c51441380e03544011181c042c070010082d9004803650aa038001e80114000000e400c0c00010029000020780e058650301c00c802400f400c2440400000c1d2a03581c680000003c0d612400702040810008a110303021466011400c402143d0b0301000360081c03000308050f140d1941820b000e030158250351004107000d151a65030589010302005461140d0f40d0070107032058411510700729401c6680384902c00000c6403040c803d60380170380511006d0f15680042e0000352741d4010360780c00042500c000c0100c0d4490340602c006650b120240030300e11a000c00617101d820300c1019020790360040f0302c080c02c1d90301a200400142900c40b4076800c0038449803102d4460754407018022a01800c01c1d540c0b0910043c40c90040c0100c21441c440140700f1185501010040d040b4141d40410444800b140c0c06410b9070026842000401d2482d0014085001e4514101c0e16101484100b100c80000907211005142d104442e01c0d0000ad410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 46677738 1250 46676488 46676501
    0x801030b0606070c090c030e01020c060f0c120105130f051603050c0a020a080706020705062503060605030f0a06051203130e01180903090b070f020a090506030a0609020a05030102030702070603 84
    0x20b48205241062075203411500451034450b512109544484007002c2c00d12980c0009058401c6100139992400441c1e20255a90b109403480d05070b5080840100d150012120100c4620000059450600703a203424200318511950b01840703401c10341c54800c03141114410340710303842c0b040303500c007c0e40b03180d20b490000300504aa00082c01c146070040d0401c00d000d0080d0f0000351503c0c0d103d50000080b83d90708400c0c03801c02c0290182c000d0003041881204c082c81141d590b0103603400c0321040d4141c104c9035542e45402044017900d4291081e900890020008961407a11103098244d02452800300404c8a40e540e00109240e50030b05040705520b03800101c1c1c0204201d4610124100601c0c01c003851040d5541000e011000c5034501d403407100d001c9540c901d14001014021414440181000741455440c0d90306400e1068014511207403c80c442c1112101c04503001d2203d1003000e020b428003400a00c241c2c100f55649100820b10241c080ea8802d0403c480041d403650240021403290170f096014040c00c0c0d11707000300582034405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 46678988 1250 46677738 46677751
    0x501140d020f21070206150603041406010807030302010b03060f040803041412130e04030509121005010f030302010b18150604030f060b03190f080a03090609080301060e04050103050a030e120601060801030b 90
    0x4201440301143ca10807d209a200c000c4410959a45591900c1d005140408508011502421000140f01c0c4004114102180d020760000c0c803c0203120010940c4910007140ca4511101c00040400c011500c081c02840c5d01511801004000744500d98405260002140301c01501ca500040e0502660b8403001c2d4403070007400c1071408000c1c5030034503907005480c2e0300075144418001c88044c400081000020000c1c00e40c0c180003803404001550f103c106100b5200198007040e0059800c2035196121400c00100948031110600315000540c0c6400203150400d488081100358000000d010100204956100204100e4032034400003d10007002d505050412001c001080341000d02101207a02055a6000c2462181c1d8020324071a903c02c802c00b81030b4028009258003401044c5070800b21010405010001c5041e240161640c2d00708054007000c00040d0b82d02400020f28640007001d00b1000240144003410074444020084071040800030511361900d0005d034010800205a10300400c01c0c003080840b415082072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 46680238 1250 46678988 46678993
    0xf0c05160305060601111203071b120801170610090f11030a020903070807030b06060703090314070801050a0204080312060105070b0f15010305090319050c030d06050909070501140d020f210702 84
    0xd0101a861590300000f800c00041c02040d00901034030820320744081040a41c0b101c1c082d0444100c2e80310040a00c0c03400d020350000703020090300c2d47c0e07040c40ec00603030b40303120f28031640945188a04204181c000f03080309411030318000307403a4010b0307140306041030014600c128498080103031038004840c109868190103500948054000711014004904602c02e1036522200039079410360b42d4407a40c902203c510429500103002035111a0304c54401d0b0f0808101c0344c04030f40d00c07200240100d0b10b0b1219000300302d114910491646034003c020782030310b2404060714a03038000414140941404110340389c10482441c11160410220b00c0c03401044562404444540d00b60344083c60204003d24012200c5540e0340300d8000500104030342d1043c80080e561090003159080f100c900c0c252511410407148050103030080d80600d84c8107032107800006074040400107110044480c1651494050728101031505031b660305c03451404801d0341c0c08100c1e4100070012070005140307000204000c40d000f9005507000000c8000d02802210071134 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 46681488 1250 46680238 46680253
    0x1a0907020303010b0f07020d0302010e0d0905010e151204080a110c0622090f0e0c03030a050301210f03050a021506090105130b0307120507080d0f0c0516030506060111 73
    0x1503030300000b07982c191071207110329a9690b140322403400e446002e1000004d500004c08501c2004043e410340105202c00000000c42d003070040706460517a0301d208640074071030014036480b02c042101d1a0109000500d03110540c038040c03030008402c1c1d01000585040702c040d1006900003841419a1364171207610904550700b007000c0c000b9820703080001000ba102c0d241d100600d40e10305801151403419013510b0280180240e40d000c00c003820307a80340c4a40142c60701003171003005409401c680c102e950401008071804211140c0d1828a50f078203240071001e1050b00c002001509664040300800055405008468514026140d1544444e070304000203241038051044c070800211214184103c07615180700c10ae041d60802c803445140c990009405070f00515080322150350500c6068400126040003000c2942c2040c09802a1412182c0303910040d6075466000226a000030342070030380c14021910510002c617102d4460030540da04011080a98540e5160703540041d51550040c005110b00d44d030304000b110b01d07041ca942010381201c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 46682738 1250 46681488 46681501
    0xb090315060a12020f0409030809070506070b0f042102030417011a041a060d0b03010e030a0e09190c110d020a15110403080418050606040e04120210020c011a09 70
    0x8055051242c0c1110341d42103c0d030340045540380041c2980c0004040c2c001c00c640c1c119030130000c00380c00042e2440b070b06034014280049260305100f001c0742d01c0150803900704450b98980c0000403456450040050710414405d200b410761052100c07030313407480c90042d550095460764200b141441411090100c40c103103583c90300e01031480c03103840d081301c204d071258007254009044080d291007806200d102c2c015007940b010b40003424580f51809640280f031648829402004030394070311000240c0d00c3c030440140601044501c0c0410302d007032609030805513000c14000c12608a0764075007910b0209a821600050020941c14281001d41450422011600c80d20b280700514542c0c0254566500301120592240441a1601c840303030f2802c4920000c580003968482f00385581d80340e0301c4400301c2c00c034803030070190796030b440e003040c011491501d0000309480944d0b4400030000320355201c640c3c0d0140032105240c401820f5008240d64101d413003103d403002c1c1181035800700010608034190251020402c0515481d10700c200114402e0000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 46683988 1250 46682738 46682749
    0x40504020f100207050301021611040507050d020702041d01021e03100303080a020c0a03020303040b0a0911090601020a0b070f020f12160503070b0103030f080f04020906190f0b09031506 81
    0x301000c0540b08122116014074003241000e045400c0a5050f60001070001c0050303c00a180f00501800307100080005c410074420001510000d03034071100028001d02c00b6040d4590b560b4003c154052004000042240051f00309a4125000c59000104c50b540482d00d5410026100780e50300c1001e0035028100e02d5490a68140c1900b0b0503940005810050407400140b800209035040703902942140d4101c0350310b60034624000359203074022641142da00030a000840e0703000c0000d014103c0381683c40714100c042281c025041c440f5983c0010b10150440c401c0ba064000421000140e0343d0041c400d80d9111000d514951001900d059000c0b24540c0b80d80d8400c0d14180c2c803c0140400742c2d13030705052042c1c0717a0781180c0f100d0401c40d00d0f40c040d102c409045c05c040c0302c0000003010b0b00481c008041c2d018a8441c80700f2542e0312141e91003101803c0b90040c0d040304115001800a29000e43c64480c00120303401400c040707980b1452480e03d0000340d038201b5110a0b000013182d00013450300300702100f002007441c94400c60502c0c1ca403001c941c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 46685238 1250 46683988 46684009
    0x30e060711070803030c0a020d2c040207060501090506040b011403040308060a030c080102091309030206040816080f0c061003030915111507030b01050c06180c18060103050604050402 80
    0x1004641d80a00c0d1000c581400410020801601160b440781404401507007580d11404a0601510901200c80d400500541c01d80c48000405403003d002e06050800241a052041b14515480f07039081003810000f86213882802d010788050040001d451825200f800704417082e0301542414070911145a15103060500c0840381c0c420350603c1c09500326111302c0302050f50382040f500000e100e0034818801196082055029140307941d41121aa61415446400f13181118040300028005802c004002004150901c00400319404069203c01d2400c001e030300d40108a80010304014412480001d803846c40340700802503960006180ca4802090600d107a4014040b0121072050100d10701008a0703518403070b40a0745240310002a00300c2500c44900f13032561080c0d082d800444d140d130b001c20300d0010840c6a95201d1070640c1c0d038900c40c0300300910f050313190000e4000c0441262004e100c201e11440d0082d41c01501c82d10607000c0f40400c913440305442400c0c02400942900c00042620340a241303007804101c0075075a02c00004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 46686488 1250 46685238 46685251
    0x90103080901230901020601051512070203040801060b040905010605090306040b04020103020f0406030b0130110403050d020d080f070f0e2805092427010609030203010c030e06 77
    0x16559440000010780726070020000700c14009010001240f01007002e40002c01003e40c0982c2643e01c0d50b82c030b0b0420800c10001031401c40096401c10302078240b404000e02d003a1500650705004480c10036030754245003802d41e45503070045007210f00003040c204002001802040e000d00501e00308541040c0000021aa0303d41d40100050090b44800c0c021405590081d4111020f8a48a82a40b599661100340180207400c086003904e0010748031011840c1209034030102e85208440411100341c00304590f04202002c1e202580034400c456604003c0007002546c02c020300504c80303000e90060188008d410034050203500c001858001501a071008110400f07038805290b20085280f4107081c40388100150100d01e005000da2504224007402e50490b200e15249819482d08070780044031090384994425000b41261080800703407450440d403c02c1081c6030f5242c10005c1a01000b140b6801080c0f20f4604c1017880c018170030a80c010408034603032890a00c250b00b002c0c09000c0c0ea00c0c1c1a804c0070701c50351300300d0940150b48035001020b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 46687738 1250 46686488 46686503
    0x110705010219060b040501170d110309010f050904050f060916020a17070b01091a0604080703030807020a0b070327050703060b150f0a030b090106020304090f0b0319051b090103 77
    0xb10070007145921000c09414040d03c03c00a541c0c507900c00c1c410f00341c400a003c2525106075145203610313600c91482c2e01190b400603001345090800210040d41e01d0125004603c0030302c4070601510340903859a10640384075440512040a060400070309012008601034180c00b0702c001d00603691713400c2d0743d00001c6090819900401c0601c0300100441400150301031403030020806055038000040154130740d000a0b80d42d1074540159603942828034100311b041e200301d205008550300050303c10008030380074802d0703203500c201c0f140107588210880303568004094004031505c00109603907814600380c25045002414191100c9014014802038980b1460750740e0007a40b000074a01c644451924200b51680407c0118010f0364000d105d031030750792000e44010981c10140010340041e1a1880d0340880e840c01c204490704846c4550003461401d030920941c07001400340701f10a80d1019880d07640301d00440d1401c2011080c407402a010100b50105240f51450414840094a1011480c09001200140d07244840d060469500004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 46688988 1250 46687738 46687783
    0x230706081906170a020103050a0911040f110307020d0f03090503030a0506060c030406090306051608010e0a09020d08030a0c080622090506130b01060305010332030a0f1107050102 78
    0x11000060051038003e24401e0103c1d01d801c0b10751100000b0140b110038400d8a09101c26600c020809003140e100620250083d0035880004000382019800704059001e102004181469140c190051a50081e50030800507400301240100300c0313500c10b0301400204480d1400380301c055859241c0c41da89001c06442c1401e02903881003c100e140e924641107070b0170600c1207410303170351203643c2d45102520005c0c0e1880705842060410001900f80742812101650750360700d07506da2a41c1030b402d0004842607203c0003410151043ea94001c0e081c09030b69000722288400c0d2055840075524980341c0c0c012029114450741080600c070b4100148a010394960601d0f003a0b03115011030006150744640468405042c1c003110151030713401024140300d401c504103500064060701540c107450403641d075810120304427282440080d11211203454a90410400c2d4206d00460b00480c0705101d003c0c00002a2460441e804402002d001c11150150301d0b000c65000301083c240d442906000d0702401e441c050020f03440f0480850003410000170140b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 46690238 1250 46688988 46689031
    0x1611031c0906091707060503040303140115020c012c0a09050a02070c0b0307020d03110d110a0306140f0105030705190306031716020f06070f23070608 66
    0x420484489152103004840311065440942a44480e000388000103800764000710b0003d9014090604035100304008084540c9880340490301030300041c00440805490b6060b0442c48030b51442518043c14010b034410090030030303040000c2e01d8441a003c40c103050024030040059040e103000d4000c00029022200c4c00f4000582200168082c403094000c0707001189807401381312002041d40d002e040d06078407403000880e0440c0c841444420a020850313100b401a8032103441d80c44164800d0300000000118900058104016501d140082c1c0b02da13070a008001041c0404d14072030329030307141c02104014002a6035141c0c962052a01085140c030190091505014001021690091040013119400000b00b03108203c000302102000307003d08070328030041d0788407241d5000441d88076108804803403500c002c3c400714044a00355503003440080014941e045902c04400d11035000404d4500180404052041c06850300b11545041d00e02203000f00c452140300340740d11840050200c00c0c1c1001d010394110340308072002c00000c207044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 46691488 1250 46690238 46690243
    0x90b15040f020c0c0a060203030108030406050a0c051504020415031a090a0212030a09061403060409020109050604091b030b060a030b1f03020a1403060a0501030b0303040f080a05060903161103 84
    0x1007503100100e01c0050030000207000861943d0601000310780c4501c11036941e1104076540d00081c0144200b94100304020804580548018500340d140c03403c0004606200b925007078207008100708043c42d1102031800304811441c040c40798469009180d2581840d80d81103840381d004494000340f1070702c0a8001d43e4042030080b02e0030010500b10540c02000c1d000c0d0144d035880c0391522901301a45040110756141c1000c076040b4011554081c1003000a070000c2e0459a80b0010080038048140e0180c1c140080558041001e881c1c1100800c040c058255001c12001c801d9000c60740d0b100640b0180340100b5103424001042a13490740e003220400c454030b16000c07502c0341c1d42c2e8000803403491147c07010f01a03100107200302041e00c0750507401403c02140291142c54205a0220805019100c2107032926448139030b07500300348110346c0a0707403080121000280072203040c59152000c0226004140e00004a00d1b80310800788070402c0300800050ba4000c3e01d0001850a01d20f14010100810002c8403006120a40d0203206842d1500d04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 46692738 1250 46691488 46691501
    0x2010c0f0813050604120803100e01060215070302070f02012106060c0c09020c1e120301060c0201111c0c030201140106020f0709020f040b03070507150c090e040b040308060a1d070909090b1504 84
    0x10031a250f2b4036540d4400c1c0181d0303650420025008040a0040020f41c914000d1081d00c0085400100240c62165942e00440d0110b90300c044020071b020554003400c502807010b10954014041e291240140c070000c41c200740c0d417651604d5000d130607014010405044108000b16640390601c1d811030100c0a0400b170354a80c01d08024000b03800c2460040f001c8000a401a031101032041c2c0035000780c8070703a05c40d4640442c2d03140c1c03038152582540a444203003181044c00746200300c4485d0a91070180c0b00010309440b1020020703006423000c1c0e0150300140e101b8070400700050810701c042070080c828114114940354040c0c07040440d6004074800e00b0b80106004c40042d0030103000301d0840c0c0d001680124100070503000c007101140148991201c9c180010050315000c01d80c86809203c287c020b54200504001941c0e5580d82214412402002980c00003050080010007a450b43d20080c07580c2d00c003008610309480d0041c0014180b1141d036201003906800c280174900402c184944027904004194601d40b0004a4400070070090b00c43c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 46693988 1250 46692738 46692749
    0x5070e0709030b1e060609010206010e0702031b07030302150906010504020d0204120609150e030f0d060e0106020102030108060f2202031204030503030109050c121302010c0f081305060412080310 85
    0x42c00307070800010115031040c0d01c68010b14080d13022a030380c8400d001e00456000c0c0440503405039201c4001400400000d240e099441074880c8112450150301d2800c0700e07455819a61000b010340e000c0c0c081030080540601004000f4a401890703c4803034506a400d0903a110418840d00d40900d034001801c61240c00e0700e030100c0c0e01401b00c00b101880d03000028a850740080c22048400c0d41c50303026014072480f01c03801a000d8200c42d01030031740045060001c000b40d0a90990b21800001101c603030b45400c0026140c1140c10f100e8020141c0340c000680303940c50100e806050070070042c03100e00003031002c0040000c5480049000803071110316840401589080c1d20110746840c0180110100103403000c1000002c0010000080d0b060720b29110007802552111806895203014a01c0380c601c1c80c04480d4002031091001c800891640da005150501030000d59444030306e000b02450500ba104800e00040c0c0c0d20028444c0241d0300000d00c4203848281c50030b880c01c076050100140d100c0c2c00510400001010488441d40c1c099500040c19 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 46695238 1250 46693988 46694003
    0x11040f06060804020f06041409060a050405090604050706021204090507170903210105090c1c15030317010302030303010b0c010e01060608040512040e04021002100c0806031203010305070e070903 85
    0x5841d040040d200b20800c940c12407103502c0d03d090041403814040180d80442c2d044801500410f42d0050801c208100000e04090b00182010000103c80c0d445028040c01074000343c014041c1400c05007001420214103401010540d401100112041b51941702210100c070107a210004442d26805811110788004406140301d088180060240015010000700b40c6c41859031027542c03610945103c3e550000e0024800c030382e80500c41c400011b18031444e6100030b241c8020054034084e48003000d10079403c11a0020b40d615a2503a000140c140105500420107480c3d8410f0082e00301038940c075541c0000d0b80d0f0b04c01400f030118486070119494946543c00d402406107450f40c00000c0c44081d840390780007032280340200c40540ba0703441040c04850b8002e500004450a440309199180d0080e61240c0034404040c081e81611030840c400d010b0030483d11001c41c402c1400001c06030b52059507905001003010715140011a1761024414104010400503034001400320032174114241c05907445c0e9aa9030181d95401ca1540080c1098 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 46696488 1250 46695238 46695251
    0x50306011b02040908040620071203050c0a03030f0506010206040f0213090c080a170c070306110d0e0601080f01111e160803010e010b040b0702011809020f0301050301111611040f 78
    0x171240b07802510555280d82d0710388c50302c1a05460740300d19003800001300e0701103030704120b90030310481c072000b514040036038040d0410902d0030281e8600e0317500c2c00b1505001500001e654000d00340640c07001e1f001303254100800344003c0589062549404c0c41550b9401d400a11542e0ba040e0042c100399010781100683d40c1e081000c4010441e5140c107001c0e120007511a08a0394140c1a2107040740c8802c0f014248e0304400c403440c000308406821551004010718031516061925a41407203200c1c06541d06008150456840c000641410351425202500c0c0101200c00e1650a90424140601244200f070a4501581140c1c105030820b81c03420f414403160744140f50001010700755000b8482d003031010001c0118101e07411902c408840d80c1e40c40c003600600b80181e000310f0207203150400080025600c5105c203104036422214200d242c1b9552080d500e406ca1380000528019150040010401b520f420f100b15400b2141c60b001507440d040300c400c00c03246469422000241092502240c40b03100341c465a001d006146070f06070080195 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 46697738 1250 46696488 46696493
    0x12100518040213140406020703030f050a0e07050312180f0d030207030b0705030c1b07180c090f030c05060703020c03062e1a0904020c010c030203060901090903050306011b020409 78
    0x918804903816030040480b1142c11035010f900d44202c079284255002d070b8400c1034030382da9251006036006000030b0b010581ca40280c06c02e458240c2c8505405280c0c1c4542c000f8401038000d003954180072032540705504c00e800040700540d20341455001c9a0312810b600010106194144001901040c0c5603140c6070341004050544008140d000250442941e0080b0003c0c7e500e652542070440c0c542c4000ca40040d000081440079012078280c00300c02c19a102e010038140c0300150340390798014545100042d041d0009039240c684490313a194000600300050460381d40300100c11802e44c0c803001e507000b0b0144a02b8bc054040010b00809040c0f00b0300c60101ca111005041d03e40c203040c40307088104203010302d030f006404c20000041c80d9411850881c0004044400c00c04070b80c0c00c145800c100c601d0342c581140e02c8a0760003d0b002c100c18040c0c0d500a220381e042c60950381d10300584a05081050110713214050b000b0b03800d45442c0000010120341c110059a40c070220034601503a0310b12416040009407256000000d42050130b04140e0400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 46698988 1250 46697738 46697779
    0x91707081b0601050f010c05010b181501050310140109030b040602030103030e01030504021807020a0b0421170a05060d150507110102040302090414010603082701030b010203121005 79
    0x60845040c1c1d0410000c00040d102a500c031902842801d0b4040c0c490b040c1c1c000c055009010740c06034540114000100c03000b440012860700c0600d61180c444c0b40c00450100304a030904803035401580c1d02e00f07280035411494026000c128003121802801d0702c2c04003a46501034583e104412603005558002c0180b0541c3c04c1c6450310340b002c3e4100707000850104a64001800c6d91754440d00c240780c421358004000b81c10300100305610045210010b0410703011800f51040070350214288090260040b44035450792412031054a05411281501343c1440c41040500841d94002e0700400b003140340c00c07000e103040010380c030340301e80c0000b61400c4162070f4000c2032240f00f8101c06105a4640c0d101c103114600c0380d1214a10042100794003401c07072141c0c0c00002d503c40c0034480401d01040070045100c1c5081c1c04c40000250b03468aa4545c11056081408a0340ca4070030702035958058006100b01c509180d04d02030a050201c00207110000c0d44a0040382080041d1280000014031180320b0041050b0051601400340700d201050401c0c1e803070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 46700238 1250 46698988 46698997
    0x50405030c16030b01050405040b04120e2106010b04080607030b0f130b0f01080606180303090d0f0c060306030b071b12030204031406060a1509030c0f05030d0806060a0309170708 78
    0x460044c540d2000081034100350144610075a03021405140d10303541c0fa6155101d03242d03050001c0c410040d10504142283c1c43d00810794602d800cbc0000081a807160f02e0307050301d2030600160440090640c060008000428000802c250003900500b0041403a090302400302e46210000c0e40c00640c4844002400c000603072940e4802e034141070007034410b1007410307188000641d1004415201240c201000304001e0115001c0d41405040003140107080d00d2038003020000042d0b0917450201c06860210000402c401048170700c0060400428840c2402d002c045d255440c0c42a452800410040a00c500f10000c00100c200c0031001c2000c05170709c01c0001d505420035420050094004c0c7c00212050701d40c40003501100032000a61a00c0f64400030920004907061156100c0e28000821090f018060b80b00d0002c00003c0ba5901035002400060800a10301c0b86003004051402401000001c28000071000b4402652215411511441e03014103011850143d1468040042c0030001106002c4100118048041011210040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 46701488 1250 46700238 46700243
    0xd05182707020105091b13050408040e0f06060702010305091e010617010b03071202011808010b0108250503100803040b03010f05010f0507020d1403031305070f03020a09050405030c1603 81
    0x1012140e940c0c00c0107a088a005480c0000b0320f5015500c009040c002d1031860305400c0c8030280c83c2c1f000006801490500740c03007040d20219401c000210301807003ca803e0211050740010400e86506036810a0004100c1e10f200740c0e8030203410503865034002202e0200400c80d81a80c0701c0300b04403207150a007070048414000d2030395000342d8103015a0444104080681402040424403000300609416480c0c400e4001181000c1c0d00224180f10380c43c00148641c90b0304400c400d000b000500300100302e413400c110005115600003000e012142000c2000a015019985112010440c407070429941d60b450f04050900780b11131302e510140c070910000501099400503035010714100d4030041c01e4004d42c0c64440005440b01d03480e1541c91000a007042c0050b601610b481c14000075428002c0b00f1041da034036005014281554022210400c444007961090010071104028440081003440800d8004904590001e04461510301c80e84402c42d4a403c081014840b0a1080300d04c0116400200c1d025101d1110151140c60a1031105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 46702738 1250 46701488 46701559
    0x4030b130c1502060c03130210020c03060a18020d03021c20010501180b0609040e0303061513050d050106050406030b010e01060f050f1602030303010b0913020a020d0518 74
    0x30382d400d00c51410000c804015000741a080d0b42d0484500102d0300001c140443d0080c05c0174600c40580c032480f6240102d1056075001d400c54002040c18149402006004440b0076481c182c0d0340401070b806c00545500310303a812528040155910b003000c1303240581b07031945ca00d15940403045000b00990030504d41c01d00442c941d803081e8a01d03102110002d0807900240700c2c0c0c0c41e0101c480380c49440001000d0b4842071032201d0040506d8288032401d40460100c44030000c0c624100c0c0e00000074040140b901070052078014150b01011440c00b155000d50521084030342c402c8034000e01080c1d44030700c00c011080d0401005810060302c1005961ba5908004140c4c03242071245405014503040040f0700317a44240a10000c02150342c480a15281e90004680ba169000490309030001501701301480050703038240001d500800101080ca910b500105040250b4040300300c81c000c01c0c1d544100103803075025401003802141003005041c07054903980c003c20503081e05414590110340c45002280c41550600015108003c0390111111 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 46703988 1250 46702738 46702763
    0xb0909090a0209040f031e030c0318081602010c0602130608070306080a080702030f0d02010501050f010302030412030509030f0d09032a02090a0e0601150e0102120904020306040204030b13 82
    0x50540c46241c0720034080d4100c0c0c540d00010b03012840c0d95a010200e503100307180c01e20307550b4203040814600c1950b2100c0316000030f0b142d0038407841c0340f40d241c003808801d03030140e81200c800014142e8030910305100f0070b00c140c0b40755003000d0028000e6a010306034030000c0c1034000781b0071340d503510420002c565101e11902510380407840c1e180c08551514840c0c801d0b0020703502002c004210341d11241d00c82c6202901b10007000c9906d03125900340360306070000601042c01d0496030740c0c001103081c0d4104000c1066204641542c141058030500c1003001191210007d00c41c451400c1c1000180342c2c450360ba0782c0b401e40c8076403200ba04204c7d0000a00030009210380d03000c180418001da607001c41c4002152456511880c41e603400c40c1810310580c0002e00540f900c503a0082d0840140c58000500758420094241410426440036020812070b07441c8a0281e50040a00c5484c800244050010110086031400d800d000301b045d020300440e800310014200f5100c0b0f43c1114091078006002500500e40030303038003105400002c1804c6035114040d06 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 46705238 1250 46703988 46704001
    0x20030406031d030304030507061116141506040506010905030a1217040f020f01020106050d03050418051603020c0703080301030615050306090d081f1206060b0403080a0305090c06040b0909 82
    0x324240c20791480b5401031480e5444039202211250041c407000e81e50a5940c222804181c103c020080508070100c0002401c060030342d090181346058048000540c50304450844900c2c001c030b01c48903541c00786c03044600042d541c071180b00482e04d480250700901e805100310a44807043c004a0b03104040c0300d00e41541e0b00510946807020b00c0100c0803058900510541a21840030010b1510900c04000c807030062000080d080d5a5000080d280d034141a01a808942d000606002001643d4110304c000c03140349a0038405402d00c0903e620045d050903040404141d40403035110707092102030150307400454120752425100c0d6160f00305200142481081002d1000e4450400103147c1800710f8800d200e46501030140a0000c480d200c00c0d100200700800307031800005581c245000650804551101502051507001d411050714034040c81212003070f0b00308183c813110601c0200002902d500446000718100d2802044680b02c034040c10b4941000001c0340d991200010034045400548500074118040e4216001c04890b2a0f40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 46706488 1250 46705238 46705271
    0x10f1508040201030519020301120b0c0403170a120606030608160f050d060b03030403030c02090f0c030a0903050903010501060e040f050c03060d080c03070b0601140a08070e012003040603 82
    0x910002103804000001d001d0b40c02640a594010764000c0700001c40e42c5c815501d88100da000360002c5002e249203c031a54280410180c8145d440040c5c030315114505811a1034420154603594006461040c000400c0740c50b41b845070607080c4840d1041c001c18040c5503103502d1302030080d10403402418858410780038030100b040d07100b0300e00078103e94144008000c603078100b40600040880e0302a040e9403990320341d29020340903241000180000e5010742d0703d1440502c41841000860000500120001030503907003030200305200b00c800ca1b900811038200005400b401d030726044e00d05000300e03e401d0358554685000044c600350480d00402854104036410481888e00710700342400c0750401d0b01d0140e00c011080c000031740a07081100c191642c3c6406101420300700305599024a1440e400294115800041e00c800e000f0f055820401c031182c030022680d0b6641c204128150024200c8200800300f2042001d1160828900e03409011700030480801000005c00821a82d20160b0740ea500ca4401d070b00002e89031406a07228502070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 46707738 1250 46706488 46706519
    0x50106080708070c1502030c04050604090c08060306090c010c062909100f1403030408030d0e160321110a06050405150903040b0304110607050d0f050c070501031d03030f010f 76
    0x2190342c0040b205c0e00504800b009402c02052502461070821000c2595600d4101820040503400300205207909102c600414030301000e850b41c2c1c0298840070034046540c202060101c4003007802c2c43c1c44502e046c814101103010b061a04010071280140361244580d10300c6419100413805000d48000c5115200d83c0b00c9070010030010f01caa17082a60b1078840c18444051240d0340144580c000804403414107880b07620060440d031103482d00009490707841c070340e0307100101c0140000c01c950311906100c500c41500d140c5840c1e030850944081d28031540c035060000200140100700640c003107100700303003210030006282c54500002c080a460a540b184034000c0404429208181c045202e0b0303900001860429107420711040300c0b5000580304450540c2404600080c584810001e4940d42d0f020300000c2c80045040c1d00c0c054004540300414808201040011201c0508000b5002c001c0f11001e20340000c0d159000080380c5402d41610100064601000090150000e000f040305c505136885400c000c400c0c030380d85110b050320032102d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 46708988 1250 46707738 46707743
    0x10b0a14180910082d06070806010c0204060305011d07050409020307060c060b04090f020103050a050129090607080406091d0f090c0a080d0212070803010b091201050106080708070c 79
    0x71109080c016a0801c1c4210b60b40100c08204801c03043d603214280c007030a000484000c2c1405190b403840c1240440c80320550362000d048a840901031a0414190040c50030b000100781e5414040e5000403182152078070b91101006540190003000700c00302c82e507564901002d086600c1e00d228420041c000c00d00d8034003441607880340c0e503004005001c424a0903038160303000e010032042903034810382c2c0d9080e030740540c0c40718060b200340c143c422a032400d038035241440090b04990014158130525850300b07005201059948000842e480002c58030300c1c12001c26205030540c180301e002030705a080707000401c0000030400c00e0300c094415103c3e10345448507c1611003641180c401c400016448804108801092520310603e41a540245051050301c1800b10385001240003012250b0184400d988030148450b02c1c1e075818420300f0032040001504516104175600c0d40b048500040c011084a04000100940a696481d858800d201d130b008009103c250307075911000c0d2151804071384080c003250f0480005820a4800d00d10400c1d40e0b607 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 46710238 1250 46708988 46709017
    0xb0604090b060408010905060610020c0102060a0b0a090603080405040c0f080c1e0a180f0605300a0e0d0302030403020312040c0b0c0f07091104062303010b0a14 70
    0x61500884401800c60000c0c141c0e0020b508010103e07158500f03005c2d00b0400b5008500401040c1054014840c0c24401081c2c54011500306404003040f5a80c0840c0603900900d48480124000c008100015201e2540394058001d403845c025000040203e81405482142d000701c82c10000c0300709101082da06404003401c140001924000000c04030102100508100700003850045411131145415000740d82c44000b1042c00b00c0d03c64424443d04a40d03254858010708568848501111300d40480a0034900030f000204000100d024403610b0f407500a60380e804020080205902e6650603da0340360002004034101500f99805503401c40c0381c00502a000b03c900a580c154015032411140c1001d8030101c000103401100d40481d560300010712000d040010346240d59094000e00142220003244510389031643e80401c2c0c0b4203091054100020201400382c0b801c448080c201060034415410759220b80b03900c114a1f140c0d08900100010481c480c1c01780c09800c03400c1180d282c11150030558840110a070041024030b61b40708 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 46711488 1250 46710238 46710247
    0x8070b030c070803040503070215030610020705010903140102160c06020c06070201080a0b040b030607091707050901030803070309020d0804060e04050c0307050a0c0209040302010e0607090602060a090f0b091b040b06 94
    0x24180d03c000f568801d0040080e00e00380b402c1940090300d0000341c03000005000b0004018403225240c21400003440c4445030004005592500300003800c5460544070161a03601d0511080703a482c1d00039012a1010000c25620212559180c948002c1250840c010440180700c0c0e01c02c800c11078101030049842c8545c0507100c52034140c0e26049200c0142c403004504582042c1c651145407040e40341000031074002d8400780c0340da10129003008002d0000881e1500500c6c406c0d441980104072984451058074150b1750461981c0740c2d41e41e15410185e0140007120002074000092f0f003c0d000c1844407410140007503a410340d4807240498640e50400c010f551054034000440f00081004c92082c602403001080d415070725080120170341c42181c001a95410003103030140d0150351035180c20030034040c0078000b10f94041d1060420201e40e506180303000359104c400130300c0080b0250b9104a16020b000c908182d0501c01548072030f22480502c2e124030015220951030002c0c1601600010882c0310b42c2c54240110041403001030f2503942070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 46712738 1250 46711488 46711493
    0x61015080c070f1b1a0702090a02030405160f091404050c01031a130207110111060412050f0c100506010306030f060903210605030c090f2a040f08070b030c07 69
    0xd980000b0707045618a190007a40000038440d64041d9007401c600350344143d00d052034640c40104154407146088440c030020021940160350b007240039900701c0c0e60002c0040e06c1e60782c0c07403130a2442c0207104884404480f91100c000980701054941c071006a03801000148030103c444038002034864403d0f00d004006801042c9482d880c1d510a0307022520011030440e00501c03228a07440480c04150030700d0724600b140d80c2c0005990b018407000400e4421041e0080c60010400b0031450031054545d44c01900081000b41c5404440302d0092084060341e01080144004941d10045c59141d59580c0c854020705002c024284000500650300030300c22041280c1d00005070100c500b9403683c640004180c10241103050016500030119005844055415114141070780064041c2c1003200301403070a103408140d00e10404801c401c128007082d0240c2c00d1031304440402d100c0500103020f601c01a8402800d10814520781d84007140002d40142c40320011400c03240346100381c070301c00354544d140c0d8000e52108944080481e4402c1040100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 46713988 1250 46712738 46712761
    0x23010305070c06050a1b0c02040b2202090109150201050612061006030e16080f071a04120f1b05150a0f050d0b0a15030510030203120703090807060206101508 69
    0x18084c001c0b1100044009005409610785200c0d000e0310b0740040c7c5065840c0342103040901c40d28024100854846c1c009a410085c2440180e000a8002d0034441c2c010940229690050786c12a002c0c01d1903441001007039803900c6000b170080200700c130924400d043d910030301062504081001400380a980c0301c0d00c503545041400a40140c800540d20407164031828401c1400c5811200355500a0220ba5000d000841c1000300c0c420700d00745c003940203014003003917000e011301000c3d240408860031a4000350901c455000b403400c01d44400709a91401410710b4070601000012402c0a900c0441a41c41c1210481c0400b8501c82080308203000b002140b034081101d8102000d06103000708054000004400300c0800c0440002d000b0610708074065100b41c94144041d2041141c0c541c140c0207456001c10b8501c0b08852951854000a0340c842c0152001c91151000140100a0500c9107080601030450401126841e681d02c02000f03680b88030440700d800600754610008105103400d504100c209a003d82c4c0d81c013132940c1b03602e1078080c0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 46715238 1250 46713988 46713991
    0xd1508030a0e0f0907020a0b180d0e240309070602030c07090b13020706020301170309090403050d0902030a05060109180c0311040921090506040620030405030723010305070c0605 78
    0x940c40440d1101030b42e242c3d6144c01195200707030f030769501030600024240384c5650401c5010f012180381c042d0f400d0141d000c0c001d00044040d0484c000385020400441d40341d01041071190400410710b0f40c52585501c0710140e005010007036000341011400c403000107039500d104a031139008080181c040c64010410030030031094650010001104000e0108100000c1c8088503400c9901c102c0d4111000d903008001001040620301d0140301c8440c0c014050341c600143d5000140884800900c000c0900101050f03803400e20189511080130303e07901034100d90b0464050b00303280c1ea407050300344200b0090740d04000f22002d080e980c0c0443c4a4040b0390040c45c0303101080c21559404c803403605102103940c019549085c00808142171142e0780600c81c12409010f1810b84a90400810b18000c035042203000360000c1004203c4c80d644064200700f58607100b940b800314503079805809030451040354031540d418401e240d808039044030644850a10400c0000340d403850304001400545c2a9841241d2920120380e458401402080c803e40003607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 46716488 1250 46715238 46715267
    0x60309020a0e04110904050c010e3012040303020303010302040b0a030503070308070c020603010e0403110f03040b0705010f02040f06080604050c03060904050a1e150509070302060f0c0a080d1508030a 87
    0x76403804c0307107000407a8000c0030848081d5a2944500305010403540c000490203002002540d03591821211030140f0641c24885a041d0802100d01c803004035008a001d01c100d920025030841c0706d80c1d8441d502d0800a5482c0c0083c04164407588c0303040701c0d03112070303242005040007141d41c04409141070078890707101941c001c4001041d000c18010301080810060b40c41c08001c50103081051180c420754106800c0003030102c00c2c4860031103225401041b01d640d01500002c143c0d000c480c0d00d50080c5d130355681c9a2078800e015241d4040b52011850012030042440480a564103041d18480d50355401155594401c10090300c405446090209504101094441c104522402d078018000c00840d00d41740d071299500032851001e901944005010145a10108a49440450b462074031045c4107105034207110780307100d03102c0090744002486040c0c001484a0300744c24007002d0b03542000e021025641d82c111a81006c0c03946500c8414203044451034150081d15104584207448103981d8030b10020b60412500c40c5003518102e0188840 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 46717738 1250 46716488 46716503
    0x6090b0307210204080c03120d0e070905040c05100f0801050f010c050a060605120109050c06030603070b0d0b0a0b070c060503100e09010f05010e0408030c0d0b09160801060309020a0e04 81
    0x41028092022442c0c0307640c042c4940005030f50744e141c17801c007608000c050619140f1030b41142c200c2c80c540200182c1564038284141c0400221003040044083c5800740350343c0b0503000319003054200400d0043c04480f07034007195416100000d14004808040300e880884000300317804114540014006400c14800e004440d9106042010401c1042d445180c9003000d00703541214070949860f014004e03418201032100503036007401c1c028000e5402036601c03e600c0f00c10840b00319000c1c50011001030030360342d0308100003001454155107881d5902c0421813108007506010010b40d00507166003034005101c0c1841c0c000c41e5050384d00902500e0004d0304107002202c440e800a08804c0d08001d0795880842d140b12010609402451031030000070f010b603441c0c641e01c41a80d1050b8024641c61000710100000326000d0703012207600c2607241850940c0c0358111032040004200c40000941c0083d403060800544440d40c4640440c0030000f5114200246c0e07807502c1c110305441c0f81202c029000020141c042000301d0803400712541151040c0301d0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 46718988 1250 46717738 46717757
    0x16030609090c06090b040b0301140127050109060f080703090507090c050315040e0304090b06041518080607090b07020d020d03051b01140c03070c051609050a0606090b0307 75
    0x120030356001c1ea00070703900c1840c0c039442003140541041c4d2900040161211441c20503240602c0490a0f01052003640728440c41850988201da1041c041140c158070300e424500070782c5024160700202844240102d07070100d101003c02089050207442d200c016003049903502e080580c0c485004402401032010201e40a104080c0c0100710401030f800383c444168019030320385e61613203490369054407100ca1f41c3c0030007030003145011210100d0010100855013507500d2508045807120425020030202e00c00c0d07510909503c0701303001501c81d1032548026008000d9410303141454529480f0f1040507101c1005850040c04034690480c01c00c07100010380080c00700c0c2c500040010000326415004621030b10300099085000860000da101c0900640402803505500d10900811440442d140b280c1e208400161080420901c080b0000b84801c0c4241c0c0129206130340181610f0700c107038654032040303040b80c864090300c0266800d08001441101107842400100c4000350360350b0b401249032042c0c9281c664070242850040101c0a90f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 46720238 1250 46718988 46718999
    0x2120c030304081516051e040b0d020301051828021201080d021501030b060d020303090a0b0a0f020a0819050c060928150c1101050a14130b160306 64
    0x80c00040103040041c2401c1c41d80440d1a100d901d40c01010150281000c41c0350300d0030581e00ca41501d0454007041480305c0d003070b030500c4080b461f14016035100d0a8449400a9490f0010941d50091812100251880f8500c1140204127540d4050100c42c6042c007541c030b121441002d0411a503502d1420484d0250041c500310001c05506110b52090300700403010f13072000740300c10700c007550410844d202e0819849440d000c950650f41c58505000c006481c0300d03c81e50a1444100a41d070f0144100c8007190001041001c40d07a5036541d0744409a044101850082854003a582004a00100780c44c0441e617071000840e071030310701900b000b4a6403c0185209a08202c0e0038404003c01900c100041c0b401402c400c002000d035001c186034081d200502c0c80ea2019950703080c0c03080c01c0e40012410090410547c003000c2c0085820211000708a41031404001507028039800c1000740040c07c00158010890861400511151991070100201d0b1128102c0310090000900340c0c00105541020164a680c416161401060040e83d070b5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 46721488 1250 46720238 46720243
    0x60b01030e2508120a050315030a0b06010809010603080f03220c0302090a0e03091011070603091203090f06091a01091a0f010e0d051603050708010c1b02120c03 70
    0xa00c84140e800c819000030019520340d104000901c1038400130410522004480b804034058400c1600c03c2c04008400716060090b0482d0880c203002002c0e003210300e40480f07410007601816041d1100381c00f0038001d00104054a106001e22802e403030b0002c901c030780761011802c03803242d15a000514030380c1d510400d0009507610000c000e199000840c0600e84070b200880c150300402004d8440030700031740401c600c0d0881c4c1e4148064003106030750383c3c0b030300465020184a03085030301501e00700e0b501c00c00e8103418000c649002c62010b0700f40d404001181d029090034020000900001c0d4100c4080c0700000c1c0400013107002d2400003c0841c0c0180c40325a2185081e00c481040d02c1103009601002031b088241d00e45e0715604071810765021150f0030102490f08444081e08904602d0000c0d107409110400f19008034000b58550090200c00c020716425003818200111000c2e40e45c0c00e1454984486004040c1d1359400c144410010902c220000f040340044441c0c5501c0c80f08955080100d854242c0c0021320003401845101c500650b4103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 46722738 1250 46721488 46721503
    0x1202150d09140c0402090d020d02030a08190905040c02030f0c03040b07030f0f0c03050904020a02070b04060f08010e01230310050703061403070f06080601051b0a110d0f060b01030e 79
    0x25000d24071906042034031182c01c00050143c0240070f14130510505180b9074070245103450150f0140c0380710720070064500104c2d051100c00f036400b40038282d00140c1000704120207c40842c904040392345d10404183c0780c4041005550f40200e504005030b005010f081032801c0c41c0001012032981c101c0403203203850740e0313014180080c2e00040800d40200302241cac03c0089654002e03040710703442145807501000d2101e103684c0143c071501886414601440d808220000081d00820004010740f070018402d0b40c8881d51a04000d102e030200180c000d00184801d8000243c0040100040303040c0c5101c44c81d0350800306001d1104104803400c50070b0030b0781c3c140318004281a21508610945002d25400e58000c500c460070148166294106083c1c510b009620601c0c0c100a040840341c0360382c0544d000c80c030380968140c903507c004803203601404406051040d540a500c407020f410005001040300e106e140d1114a10b41d01c541082411826803201070020034070782c154000019036940c81112924014140016580b96856209180450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 46723988 1250 46722738 46722743
    0x11060a18030c06080c0306090f070c020a0b130f060c0609080d02030a051501020a05060c0309011d06010810020403110f03010612060506040f02190c02010203040509090d0f05041202150d09 82
    0xb000d11042c400240d02081e81907000003d0100f06103141040008940002c01c014910025000000d0206024034444c002d11411a500200101100e6443e0309003082181d01540e003604044038001c0340000d240002c507403030004403009034945603074070703141074403050040c01a1601c115089001000009501192840a5809603010803000100c0b441d0045150a0303003080f1072040740c19507101c1c1403c0030010340f0004035203502c01030fa4500c01e601c0380c03511108540034002c1010400201070407402869200c0c0310010380316040720000302c1240e070001520910502244180c2c00f01520b000d221054050b840c0c00d021501d100003201c040c0c000141142e40f000c0f42529002c080e107017124081e4403038081c4201c5240600903058034507010038007103207420904c0015401030341240120100f2f0140c0392240301c0c00d580c0244141e07401010f0143c0000d07401d00d0400031544c0c54180103000000410b10401d0000a0b0303a1003202610151814546040b22002140e02040040308681038414200f02013003240502c400d0480c001c003217402d803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 46725238 1250 46723988 46724003
    0x614130602010207050f030f04030609060b03011e0f0c0503160207090e01020703030b031203040b0901020d0207062a0f140409020d0b0117040c230d05160603060311060a1803 76
    0x2900c0ca4443d00b4030105207907106c3d060b4000d11014a0341c3c08140b00710f07005c89522501c005411000703071078070001900c2c0c501c0c1300a5040d4a0440039592514034040d4a400020300b4203002c00c41c10038400c41c15011207500e1841030707001410030f20000c1d1100d151100e1a040d00d40e030300d0044400d0f40d039446110710103580c1482001c0f00141d4010600c10704141e0503000d12860108101d014201451184400c3c40d05400014406005c144001d400b20380c00316030031743c11500003401c00c1a080d9073b5120182002e80107841344000369201e40c0da11000c1500341d00071009000b10003501c90303990044a03000c03070181119804c042d20301480781030004101c0002c403004a44020400d5650311038010948441c401d0000d0160641d1200c401e540725100d00802c40012101004070042c0c40f480ca210000c000c054107048407400070740401d5a500444948100c80a00c400003c7d040ca42c3c00c094050b100409458140890036105140310003400d100c004031102d07000d450280e0140045480750304c1c001031b108080c0301e40549140000e5005940c02e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 46726488 1250 46725238 46725247
    0x2010f1d010c081603110403050a081903090203060c090a05030a050d020c030d0c03260f090c0f0a090507050c0d030606020c0d11010c060b0a09060503061602060106141306020102 78
    0x101080c021400d41078082e082c0078181e0b14295900e130807000c81031014201016980e0461491102d9924141d80c06550060102d40c014141490300c48041d41c8007071004a00310540b20400c81d90385100b07003d05504990f01801030080d50b15610036481186e04031490003617001038a1a004150340c2c0301000b12501484c09907006115110041c8030107410003200383e00a5010f074100d40074003000c0c2904000304400d80e035414900020000c007560411000c01c1025200b124481050f2014450076106400d1428080c64802d0141c41000450900700440f0b861a91403013504a02200800c0184000c180c0c03002d0f0740072149040161a00e8032004515081c252503d40042c007081d6289001d004c0d041e8100070716a6848402d8803015880311498603100050078800302c00701c3c10451000c60150401c412904961080800500340700038864070355003c1000303000c2d14080c0318064801c034400160b842d45448400005041b0305e40140c842c82e428505c04681074404502210450342e010072100c96061a002c910700c00030685a030005880307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 46727738 1250 46726488 46726541
    0x20303060f0d02010c0b09010216030201020c010507180509100b0304030c061512060f0b03010e0a02010e1905091f170f060c1909170313080106060e1002010f 69
    0x50004071000c003400307807450703240010044c0d030801000705000742c002a92402c80c3d61a004400c1c064400c011900c50905500d0340510f04058054001d8040c40c0620002071250790b880c1d4404a03002c0307240310075181410790034140810850070807541d8280c00c250504201160691a40380c529926881520110000703012541e11030207024446c8104401c00b25051280000c152610034001d08030040c0c0030002c1c00700799403182001307240880d0754040b4002410142c000c0c0241042c4020359500e58180420a82c0411030a402c00c1302c0c1403030500f141d070f110902e060385500c22990901e002d01640000c02400702d03000c1580d080c0e00000c0101d24204020051401c054680d05851024198130f0a1080702c1502138a0359010005105505070f4010a440070401c0c00c4070143d0b03c0d4044501c0496212116512081c44410704200002c1c0082002c80181098410102000041381da507100660880d02039220b00d10002da843e2000c81c01601e0401c0c040e51001400e4800850400740075007601c000c90f2101045032120614242102a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 46728988 1250 46727738 46727749
    0x911030115020a05100c020c0a08010f060515120603100e03030412020d0c0201030e0a14070e0601090303020303060121051302011202090f12070e0c071a01150c080d0c02030306 77
    0x111007405201400380c105965580603524031380c081282144544a020750f61a1b18400c04c403059107010018203e00d406651a10f015008000041c0303034690841c1441c6002c1054241561040b10012807461190b240078090340ca035954800014010342e0741401074810340c402803056405001c415a030000c5c003855070703428646040700103403c1c03c0154a0554001d40b103410740c00760300558541160f035028280801c010011081c014280300d0040b40040c0342c480c2d0440c0014001c034000131a44242c0382400c500390b030b982e00c42c10015226070b68180b0000f00140d204000103607a55106000000852104101d0010350324140c01e154400e541d4111030403910425801410740956034000c003007031850301300301c501145440764407804281d21041119030ba5018200d500c5510504c0d8004001090003015103803031421440c1480c0e48680d9140d40002c0c0261064075002070340581c0000354041c882e040300c805900920080701c082c50246c075001900303070341a2003082c000e021000f201c42242c0100b44419996601556136071810604025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 46730238 1250 46728988 46729019
    0x1204050f09010b030a1104090e01020315010206010f180b0d03050306040525110f03070309081002040f171e0c12030c0c01080a0207020a03030e03100c0e0d0201050409110301 76
    0x1e00ca11949001000b80c1a4400200d071780245681002107428581c808003c0504c0c807469120b00211440c042c1d0b8003445080640c05503004138003d2900d205189101d070012a542d0780203025000724500000d004008001d20b04001c089110302200c00485e0603400c800c00202c6440c11a8070640200e40700000b04401d614052080d142c3c0007110f501600d081003031103000808500c1c0b420b40e581c1c0900c918055107129080040008002401c94402140e0b0741705071034a40108a9001403140725020721500c40e000c00020010f009540944a000c0c0c42100350038038000341150703102e00a101c0b0022501541504066501440c1c881e020307403502000007800914804000d01c024040031034540c500d150018009450b0303012002c10a03403944502441e206440e611041c1c0b0103030091040c038000a60015000d00000700301038000350840000c1800724256000100b006000106584d1003100d83c6001940b00751400d40c1510b481088071031290300601d4102d09040e29146000d01b1210070b1b60984000140120040002544d08c01703802 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 46731488 1250 46730238 46730269
    0x30403021006030302030a0507051204090e071502030d0c050c0106060201061503140106050a120c020a120c020916030204030c0e0a06060f0f030f0e010203070806090610020303060d030201020c120405 87
    0xc200c101c0c0f0319103000303403a8000c461881040110009016050103402c0051a6131684203070340403580c0c0c680d04d841010081083d85030824a41c02140780c0001d80c050f0007100c7c160040307526000f841c40c0c0108000c940b4010310b050050b1006101d01840018130f012002d10690014014a0300006545802c00700d13084c075141c1c1081100800c041c00c3c41902441c9200120b160f6045603e0341c01c0803034641d200fa01007a00d203180b841d948000041c1c0b034448501983d80d0300068010b07015020358202c9142c203c0c206c8086071610f1b103025020350170014540c080350007006240304903491846980340043c103158595950101803e40b5500200d0140340324410f21100070044e00c00c2c00018421801d20001c0950308040c040c00c40000c42c0161420706030f48040c103289000c0c80b90028440408280021941d0346400300780a0b1020006542481c001c094540004140f8244406400d46801072034000350f0031035a400d0704201052000c0300080301155024008070f8800003040092000714402044190745403420001031040010300f030110b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 46732738 1250 46731488 46731491
    0x2040b060a090306051b0a02150114090403120f180b0604060f060f0e0d03030c11031e070c050306040b07022406010c020d170c060a0603111002210304030210 69
    0x801d0150700012001c0481c0e80c003080c00304007a510344d6803400d0840c650341c1d503451940a000541400c00d0f58041030042c0000820602c90810741d072155480c44201c44204100f5400c545154081307400302e80a024030449020078000d002c50a982d0030391014080d110380c1802441000303594009a800c001c03261070080c1c0c0c0964141d42c101709551410ba00820100010310410091103400c039003064005108407254072403050043e00041c03062090349802070042a02c21100c034005000400100c1103c5408001c542000b11000210b2260000130004084983c5c01500211441201d410001540d92820b010340c510403800307603070840c00da03140241e00a401c00140703183c105e540f04100d002098000b554000c0c1640c02c8103003860060800581071020401c1c4030229203001d040e103880e103808201081341c4240107000c41c8280006513821611894049802c0c2e03030340c40c000104011500300f8605980d0600051000c08a90144122a0b601040310704511808050750000c003004040001000181501040440c002d001701010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 46733988 1250 46732738 46732747
    0x13110c0c090a05090a12050403020a0323072904030605090f060901050103020916051e090418080307030b0604030c090f05090c01020709020d0b03030316030606050f180406180902040b06 81
    0x1010b034171001c0c40c00e80140035075107000341998038502c11000c0d44e000e1580580050710b06d170b0b100e08000c01c0c64698a00003480401d905004490b0400340483c6040c100d441112048100000c910b103501c68540030b0200b4000003681c2072000002283c10340c000c09000d2000e81c40034003400a2402c1c100c6081c00002000300d140c90381094010030040e07d80a8410307038003414007581c80014440d031003002c40c1c452240880d190b4111803035000f004040c0151400926801404407404c1082054044120604050303840b40179080400601c000b40900340a40c000f44e01e601030007403c8a240c20b46a1755400c0014115401c000c030190b0790b6448010070a4264130690380c000b01950300500da2040c820300004d5603034400e4002e1149052700400e42000150f00d41d000801185001016281c403490072600310141000300c8001d03000040e0030048005440380c003410803039401040040050385855002e6016003540e514002d038171600150f84440005007108104015450100580f1021480c118503004020a440d801e0410783d01c603000401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 46735238 1250 46733988 46734001
    0x5070513030206090112021b06060a030804050d03030e0f1b0d020d0210030e0d02060a0615020d0c020a0504050f040203010b0f1c2603040302070602030304080913110c0c090a05 77
    0x11900040301e0b4101c0e4119601e4036060012036070b000b2419860054180003194440c0203100e4000b0460304000100304481d45907907a20100041102c0d00e110281520004200500c41401d20002c1030482c83c1c007900b00407500a0501040505c1e0040184194071590411403481000207203009241106000845904150200ca9000590381c500d5400b03000784160b041c00c820034502ca02941040c500004e5610503200a03185082c4003945524040303500103000f600e001d00105141603c80168100081c02d40d0080850841100d0141c0318556060070030703648002041800501c03960703940941d030b110322800803440c4901c1c00e140c4181801c1d0344040c403100e803103080e0300d1448001a8176403145000351040180008080070704079080000c90001542e50281c2407d40981c040c0484075005802540079603c02e5003282c550959441049880b80800e0ba0020400c60041103842c1003860074000c075408030406000009511450b00802e001c5030340c05200800120341142000142500e00903a9032907202050203400d20141c0703040c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 46736488 1250 46735238 46735267
    0x10f060f05040b0d0b030105151807020a030f020f0d05071406010303080615130303050a021018080f0910020706032007120507060509010b040c020a030903080c030d021303020301050705 81
    0x1d0043c401c8080c000310740c16a0700d000c240c20801e002c1001400811007410900780329000c140180500c0383c001d002c0d102c80c0080d90100d600740703507200300000d074042e10071000e8543e01203540307000c03c1000104500c01c1504a600701c5d24240b0081c65141825203030a0381c1d40c1c56031718040e488054400c100100d513800c500c6c01040420b40100000e51720100c02c81e0002d146c0488402d8100007401283c60f200d2545110040100401da013040c014001611207408071012078182003c040113075681e8000c42040311206803d000000340ba001c02401c0410840c2c04182d04010000c0e0100d007901000600320001a032112108002a5070507105d51a040302c52240d40708034904000c60319041901c41c032940141441000169207072040e100781306a560b6254440001d2206041c16440280a40300301000d8030711461a24422204090000900348005507054441c41c124a1950f1200b5207103410040c1c040078640410080c001d401b0400d44010300600800300c0c0c1004090f41540185802c4600007440102808400c010004015050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 46737738 1250 46736488 46736497
    0x6010f031a071718060408030109051605070609030e0306040506060a1707120201180e0a1b0c060f0b06070c0306111e030406022502031203100e040f02060c06010f060f05 74
    0xb56120300f40c0300e44c03502028040b01c02c0510080f501a2409100400400000450494a408030240080d450b04410304189c03081c010724281c0403c8081202400150140d0491300206009050148004020202103400c21104440c121a0340c3c20640030020700c2e16000006c040603140f08803071995034246c00900303580d55804d40d0080c9224080c04058000442e84540392200845a276070342c811403100d82e40c51000b0010310b0152014800c0d9410302845a11070b20418450004402860342e4501c0c42d2051604c0300002061408665046151110250b80e4035071240c100030318980c5e11854400705407900e1070404070100e8090750f411030004401000244d030141c104000144401d42c60005860f03032034540d803800e400244520350740100c107525800540c42030011005c00420340c25000b6810344c0c22071100d40e809040e41d44030486403015814844042802600c80b4811a80e0384188a40b01c1c0e50001c0c4d030190000303078071608030060309100359000100500c0340d00365406203040145140c0c241a001510b0f0741101401c140103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 46738988 1250 46737738 46737767
    0xb030105180d050c030403080f190203070c05010e040e030a0203071a06090c0a02011404080d050f0408030a0b04181101021507021209131406010e0d0f020409030c0506010f031a07 78
    0x4011541004141307003401218020b5501c017082503940c404554a2601503000b9814070303074496030500c800b0b00301c0600100c00c80b401258040081c841040c2804015075051850111498200342e403224010754109081008042d881659001162218600e242114082070070054401e00d400b40d510a11005803624035031341d900b041228038036a44038482c02c1000c900401d800c404040581e0401810311050084010080ca0340320040030b01441503035070301d50320b03105100341c192001043c4001c200001140364959500020410100900105400680700d0303001005110001d01a104101d9910018005680410560381f04d07944d503210032899441d00c03140181d124500c0070702020103180c00017040c0c55559920130040f001d148032400204a4036440b00e8034588054802c8815a0101e0b01c1c6071101c99240c5000103040f040203a1003001640014256401c0c00007602007000120207202080b40308100149083c40514007070881c003048001d44520354100800020707a030303404080e00c05038804203100c0f5240d88080c4001d100301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 46740238 1250 46738988 46738997
    0x130b03030d0506010507050d0c0b090c0a030201050c030705120d050906160302070c0503030a0206010e060d170a030b090415060e040305070f08160303050f0109060807090b0d02040903030b030105180d 87
    0x1541e0f000184c90500c9400001040303402440002e1511130303000b01c00111594010901502c4070303034404051a950305504d803c0d19034400515003040005601c980001c101c0202c500d02980d080221903640c5034505034903100c030020030704000700d0100103c070801d104441d403180c2607600901d05030609c4405001c1082542140c0c20070913400081c50000c1c00320f0088181c000700400380441c0c1e83c0e03002d103001c020340300c400a0280108404c040303404110f003484d0400c0d5414203260003a203014403403402c9030118406940700c00c020344241034442269240564686425612503402040050149000e102c40241194100e812401708a06540c0074440440c2d0b0040c11b82c0d80d46e03940140c1c10342c0d1940f6a400d003000c0f18012502a8495401d281c1040750070903600d608020301595910400980603620340c1c0681050742d10364002c2002c20345c070500c02001201039640040d00c0500d0040c0c0400c0303028411745c01140942c3c11f4404150003003501c2d10100c40c1903040902c41c40b684030022400118030580803002c101c0d05e41c1600d030910804c11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 46741488 1250 46740238 46740241
    0x20f040902060319110408010b0f0f10081b030412020106080307080724050a020405011b0203030a0f0e0a060503090d0903020a090e0c04050a0510090e060105120c03010515130b03030d05 81
    0x500c015803028214040951840386c0b1113560782016806004810342c0c40d40504a010038034030b202e05258000109400e00102042d40032040c8400441d5444001480740e40d60103d1418080e1140c808600258040c5008444460090081d100702a094a8480d4007481301503000300618804500e07100103a501c0e2035480401c20042e90915101b82e1803411401c01800074580ca0107083c05a0400c45900400888070280c0724580d100f83c0e080141d495440f04224082d4040c0c00c2003210040c02440398159010707000050400500280c01c01020603520552031b0081001b007500041403142c1d883d0f080140350304904036440d00c0c1c034600e400c56000c0f03281403107140700310a200c0340c40c1c0038201850401449921100040500200003500d06042c41201524040ea080c0c0102801c100d4013040e0700002e400f42c140b0301103a1030020704541e4a44410300802c06041b0035401e005005007000006039030b800380141806543c00e10f100e02c620040d08000c00450440d241e160440d03d40c80c0c180c2c80c00407a00c1c04415103001400500300007405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 46742738 1250 46741488 46741531
    0x601150309020d02030607030506100207050f01080423070e010b21090102072f010c0f0f030509060d050901050a140a0b0411070317070302030601082701020c010207020f0409020603 79
    0x60040460009506006e03400c200880e090303055200710310807601180c00921b040c10640043c1c0e181d0049006603034100750212441c0415502521105400601c00d04100c4549d00b98503251850050180f07413240c00540248004228025402d0080307405001c442000b580b41c044400025040c0101c10030f03d1919400102c000585184400c0d4140c1e0002c0e50400c0210000b0f00d083c401740d0340101042c90a040380c88200c8075502e5055442400742c000322a500044800b890441500d503142030300b201c14000c03410060100010040307600d5a20180ca580300c2e040c000820242041804542511402024140d16600e0249a80c88060b4000c1d1071175000441600000b4540c1c01040105010b04803a001e1000d0f11034000424404040e4054685140013201c0f1884000e25110034108030140c0c44162802d900103100c10000c40c101d10701c00c0c1c11040d0010714a2003032070707010146043c9081c2a6005120340f00320595001c0f030b0705025810200c40704e00c0142001c45040045d240907070f001418601000d007200145001c84a1102d50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 46743988 1250 46742738 46742749
    0xf2e0e030a030314011a030c0306060f1605010c0f200102090d03080406050a02040f0e060f03010f0e0705100f08130b01090902010e0d030f030902030c180f09060115030902 75
    0x4400400340550741018110708024014140444200303540c510510000a0360301e00060303040d01400e2048140d1461921140505030107600041c21156222104024031a28440c800000f44100c9092514510320f9800b076045c080e003100d848a241a0501007816142c0b24055402600c0c0c11009000c0c1c1000d5200005582c1094020700a500010350080b074001d2201080c103400c0307000e0a2241e031007424140310f00c1e40c5502d05041030340218443c0d080361100082040c88101e261484480e03000a001d450b548400e40800002400c0d500b4400107100d0459598140709100642480040c0190405407114035041c00b8084004209060701c601903020001002d01050069000f00607040b20fa54201d11905c0340c550311030326850001d0404c02422800700740300041022071401d100c81c1c080e010507010b0b100d01c0702c601001802030380a440c00120481e8140500c0c1c440e07000c0d0742c1d54105d140080c1c03903500412205c1b61401281840441e072026203155010b600000041241c050030a00300400210903140105901142c0e101061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 46745238 1250 46743988 46744007
    0x160609020303040905041202010e030d020702060d090602030621060106033210140907030b0109050a0305030a11070e071202070506090f07090605010c140307050d020a020f2e 76
    0x30751600000070000343c0700505802c01c81c000c9018400300c0001c2030800c03105070300300c1d014141401420b4105008298100c0310350b40c06403480e103002912031441e01d8000d2282504480d040c8404456069001c814404117040c88000882907400c1c1124100204a803220042c1e0744200504c1a0130802d0340b5080d0071040c00c0001195203041e0b04041031201d078502040d14100221101c01c941e000611185c00c0380005001000308164010b03484054400c81b002d441e40780d0100e000d000903232401c9040c00040700d070000e442e4407140e40d000b0007035004d8406183c40f1361058600501c1d2610740c03d02c2c20603170350001e90140721002e01d210700e2076000080d50501c0001840240c03c0100680284003019260303020700002c02059010220300409038400c0c007030070fa54948d030300d50756640c0894100b4000e403400900c034200482e00040324641340b140c403000303800112810810f695803810b242c84804942c900c01600400e01020031800e1046100300a04411a1043e01101c1928113180207502c00b841800c05034002200441c5209021383c0280 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 46746488 1250 46745238 46745243
    0x31504020d0c03060504270c0b12040204050f04030518120706120506010e0901170a060e010b010809010c0f050f120408070b01120b070302070f020307140a0b0406080606180301021305030f060606160609 88
    0x1d8030390540700c0d8441c070100c00444bc00e0340034a0400f00000e5503c4001d103c414407803941511101c1c101f10608440d8000c6801d0b550031141c00c07511003207001c1c2d4811801c1000c0c2c1d005041c00c0e924054988903240c204420b0301d0019100a060040b03200c40c0304055540c0c0080281590039030005141c40d048441071031482c05a815801034002441d00078000b050708019080ba0550050a0303c0f4000c454903000482c034200d9451a4030301e800550107070016800c0500c00c40060035005c44d149003030b0f0300f042c1c07014410b141a01825641140c01c800c0018030542000900704180b401480e02060410600e01603894035107044000614034820154002a00c6007000400110342c600740b0340190488861648404940c0c4044600c00341c01031203000a100700240b102c04081c1124182c17100d640e0f0346455134a0b510f0610040c1c0e0851080c1c0003a1803c0990500c07030381c0d00c00b40301505580081142032000549004145402c0c0090300c3c14000c2180c101000300151601d0705c0342290700c01101000400b14240c030b241412002840180b000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 46747738 1250 46746488 46746509
    0x6031a0a060302090f090c0306090c040c090e09010c0f03060602030703050a030216060506030c040203130b090a1208010303030f02180906030f07080105180f060606031504020d0c03060504270c 84
    0x1e2100148850b030049104206d00c03002c40d4222143c0c94201036442008851900c1c081c1d04c00003d80d00c507070810760486403806034a400c19014050302c0362240345a01c0811035500010303a545840d00075000381c3c0800756460401203810204800d07030030944000d4171303403140d000054107000c40000d1603102d0922030b07070440c0c850f150074002e810f480741d01070300d0100094981660b10314401e00c2801c03013030255840d091084078001c0321018515011500e142c1d0741c2040b43d0100500c4011107014500c0c040d4049455107107a081c048859940da040d896041d407030302070112244030072200022441030006a01e42405070104c0024080229030090903981c0c0c04000a01d002c0c2c0310f0b5609100350103115000074a060707054102a00030107060720078514049060000135a100102414071340203502007004900703d41018401140c00c440c043c20111681a107440c017003016648001d01c200c049580e10131500504540c1840303408042e0500711380602140d240000c1c0103901c880c250300001b03003d642c0c5207450700400451a210300c0c01032045401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 46748988 1250 46747738 46747741
    0xf0516050c03010c0521040204090c06020606090a020406050909060622050a0b09060a03020304050106030204050106050a0306080309030307173f060603071211040902041806031a0a06030209 83
    0x8106484000e0800749500960810460306805030041c000e4511001c0b00c1c0e44c070304070202440074403152040c00140c0b050380c101d17655004020200d085170b6402805842d0b5034004005a061610a0100511004028406041c8180400d12985a200088810319082155501d115444040005842c0d204804c001d00c1500c1c0740e070444401134250750310802c6c1100ca0444d03500303c8040c0d03103026110355407081c0b0b5000c41e48010204122030355580254007640d0018081d03c000a0f0071038480e801710b02204e0b001c0c2c100b24003049000c82c024071499418040c80020703103e91409103017000e06401c0400d50ba070040020003001015648828210200c2076000d50b02c3d08443e81907401403180c22099291011545d0010b115008000322101d010381c0c03412804114040c801c0904810b26660f285881115808401546200029101c1440c00380e0003110b000070f0805802c01001c0161340f1440c01c000003406a11400d020b80301c4504186042010840c80294074080010a1454502d181e03941e491100051105810080d0710400c0d440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 46750238 1250 46748988 46748993
    0x130f032f010608030406080f0c0405030109030302041401181502031210031502040506030a0209030c04090506150a080303010504021e0a020a030801091a040b0109050402070503070b0106080403050403030f0516 91
    0x4802600c45440400801480d91103100650316441180a0340740410000e8001c5100d40b144041c00720303401720348014110300f01900d51000078250b88441005800117500400d043c0300b07241c40d5a0007168925000d09000084081441e00108410494456001d10304008030540069500a001301e501780340844400390002d203440011695003034142d000a443c140449400030400d1007052007224281c682c000e00c4242103580741c00080000c4e40c0442800764150090084401c0390b5101c5018400f2514442c8000e8446407800b0001941e05005410300d141c4a1000050108000400402124191502990702581d0f4003201d440c01c0c01400840a0906003203100001d044007400c1d404148447e14a110b43d80c0c4174170903680c0d1100807042d1907442e44181c80191407004a900c15117080d41c84120300b01c1d018100b510321707941c1d100c000404030382140a040c0c941340c03c006a66070400510b80031450140c200e60620084508003901c00030402d0150303020080c2400700103107030841150700950980c2da001008a01000c8070700202d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 46751488 1250 46750238 46750307
    0x2b1a040b040b0a0923010803030f060a03021009030b09011109060a090f0611010f0c120b01030605062106010507200a030c170c030613200d0f1a130f03 66
    0x1c00024142c3e185200b62080348805c1245118101c0304210003d40c219103071900030f0103000e00041d0060742e02010341540000140c4980b4000d805030012a1500b9190700c1c80c500b04425a07103001060351000341d142002611101144905440150905844190b11014149001c1e1818103064200d1340940160900004000d64041c0d10020a4180c901c000c0c40180a000c0c01641030307401c0410803201191184200f203085010703550206040d0041454041a80340ea43c1d00490b506500c01a451680c00d55801e00c1003440c100c408140d990081420b1a0041c40c0c452192541503400380c0610140c1d100320000c98202201e83c3d5103020900156070844625a000d44e900c484c02c1840d8601c140d1920800d0244d64a02d510a180220707103144901400e011010040d00540d4070039005c91a2850b00d401110305e041444d20041d2580b1004c580102c0c843d524100c9000200d0401400c40c801000c0c811410306a0703101005001c140c0010855040c5502c6903c0009010301e902d000ea50307200000789081401e03045805040369140c1071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 46752738 1250 46751488 46751501
    0x90a030b24010306060f11070906090c09080706051c0e06011d06030601080606040906020c0a051e010204050f0907021903020c041a03060f06030703082b1a040b040b0a09 74
    0x207041c82034200d201160065080d00ca2a00c5044049403641c1086402c1ca4007030143c3c00007000328402580c0c1910b44606045007181e001d90013040050740d480c0880c03030865402850141c06480348400520015180c990014140c0c481e080d40d035880e80c2c401520050880304182c200440044240080e20b10310368440c1c0f61110005600c10301640e400040c100494110304022a0490581d529440a03000b1507844905001c0504600700086521179400c00c069030b8034990a0000c007468910440c003030800750360b01c02605c40c144400440511b4541c1d2040000700520750350b281d41014806810f4840e8045a69200010780c109001c9004402070041c1003032000f4105680403c905400c0c60080b10200003100f51444140d41c840444850b4035016400304010400d00e5894519180e4072000040486061544a5444841f650001881c0b03500105540003030002c2214072010032202150b802c80e04100c0f0480b01c000703140010a000760414021a034400c070620150300d594214015881d40500034210a680ea0025075008106 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 46753988 1250 46752738 46752781
    0x228050c07180b10020a0b0c09030a0b0a14070804060b0a050402070f05061003030c0f0c0f0303020303040b0a0e0a020409060b041a04060902070201021507020a140d0807020c0114090a030b 82
    0x1a00340d100040d403070100504d602d64610355005004455807503079034041d8240003038144e014201090103802e20644d401c201b40c2250f18030440300c1d00000d0609101a03810350380f111064108041c01c85003004041680900e071207071b2054101c100131442c4103122000c01c1c500d0303e003600810f801600029000e800c0c0b0401100d140641c0340704404980300c5030f5443c07200518441e482d0100900280d80c0c03035812400b0840580040d020311f80501c040302d40480e034030320302e202c04090603500c101c3c09600040708210512960b0301c4205c3d44816035100622800c4002c01e05503444408100000344625074829101051002c0b550003890042009042000010214800907403003101e019805171241d8107041c0e000c600c0d148940241d68140340d044c4c00800d20b01078118200c0115100060032182148110b41105000c03403e590403283c0f10b8005c4c3e0300503040c01c90b00703d05d004080040c001c00c0c0f40705652003131940c46003e9a00c0361041944a0001107019112080c45001800105460780081d00c003a4810051140d00b82040c14031100711113 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 46755238 1250 46753988 46753991
    0x303021203040f0803090a120516030e0f0901080a0b06010306060503060409060605040507030e010b06090a0506160204050a09050c090903030c0d1b031b0309020907081f0e01050a08010228050c0718 86
    0x41c52210300700c0343c512510b00612b9071903510844103000640a5800300501c5407008000101900428002c03501103400ad0344904080c0d0300c4440c400341805009803640307400010a280034401c0d01e04014001d0a02c2c0b1014040030300603507a0b011124117004da84d40c02400031380741c010024417550501c141d00502620350b201d001c00d56035180148d034021034a000403c03251160b101030085454030307162008110343d507000031651801c041d208920070001680c03035200710352241004250000c4d4003001c5040c1549800008600c2134002c070101010310034581c0b0300100313481d807101e10b8a40b0982d403203003a4000c890107000982080e42c080f180c4003034818045601600320035030301d9403078a4075980d99594840d000c80503160001c1c8081d400c100b40e04041140343e449403420590100040c918141c03201151740c4c89412610305940701202c92801d00e40140110f2a091400c48020a8140300a605012006040c03141144269a400024000c8009150540c0d4020800d070381041c00c00c0001d590210f5903400319644402c48405c855110035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 46756488 1250 46755238 46755263
    0x1808070f080c03100e100c030f05060f030a0b0604090c0306060e090307110904030311190906020f03031614131e0803090108040305090607050a120503010303021203040f0803090a 78
    0xd28001038410b12440024018198840304400500c01040b003190015114007a0400c03044005d6101d009030710024000b5a000200200c14850302c404680f40986030f20310500344440c480700e0036a00092440d88a0750401c0b1031a07400c1d140c03d800138008201c0c07245c0c018a0821525400024400e50b030b03100c4400c8840c0320560390441e41d240c2c00e80070b40300c7c0b003079120041c403c120800f09144d1a04020592b41c3c0c0c040e00c00c0c06c000038074254444c059402d40c0c109520300848540700440c482d0904d540b200801e0010301480c00100424500210760325201c0c00000d11450000c1901810550b0303171482031070b0400401d903401a0096803101c1c03a203007d001c08001802402c1003243c00c00c03030120480074242d0380502110400c13000385081059150045500d0708001d071041c2c0400c0010300c40008640d580c0e000a10a15100347d0080110700c1081ca03049841c0b4a0640d8104203000e0144010800b0a4010036048508803030f014a4564031f0f501d03403900130303580c0740360360300c041d140d10745c0482080719038900051030b40708940c01610408140c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 46757738 1250 46756488 46756499
    0x806040b0307050607060e07050603090102070203010b0f0a0909050c060a0504080c060f030705130305070803070302060a1505060f07050a0c030b060a14010c02040216061d010c0c0b071808070f 84
    0xe07840d0503c14035410030010442580491003540c480041403158000b5203008a54903000202c03690825035400b070b400c1e50700141c503000318682407041d4100b80d9000d4424501411004000403500ca901d80b2450341c2464803040c2c20420031030f040c001102030180c020803003031b260201140028400d42250140d417131203100b059040403442c80e00c03800781c40316401e5000200e4915500d00000726901d400c40c1c3d00304101015402004800114140b0009028000e030000964032a4010300300207150010207040840303c10302d080000444000d4094484043ea5002e840d1155105103035400c400c41c0e4814000c0152240c0903004c0031004000380c808024049902841c8140c28645800c401c2101405c0d5500c00c0d8581003610304140c0c48154003403900d480179140001c000500701145100070007c0360034442d004441881c0d0710030302114009035000d0038140e0b00d1042e4000b0095080d84040103008042c00e8140074095044140000344405d2203201ea00c85902d10791003640b941b4a42c0c810750540e0305c0c0018066600c1c1c03540c2d41640400c2c1e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 46758988 1250 46757738 46757743
    0xe16020705030a06090203010b090c030709050a12110102150c0711030d0e0418060207080406020727050402040219120b010e0d0f0305040f1509060806010215090102190806040b03 78
    0x1e031400100a400b0451550340c64800525114004a8042d501c2d500714020790340d42c1c10400c0344100f4410460b80d03a64134180c54000d1008140303400031032050041c1da101f404812240d061070b40a0766440210b1807d01800540141d24109500d01100d24290302700c82080405807040016000b082d20401d269800c5082e40380415844240507180c0c0e01c0012288926203100c1e142ca034000b0801060240c0d0a80b00f00501c64403800c040e81d215500645c0c00d910002002c006031513040007608010180449429503007080c3c00b50201c5189408020f03907600726190380210b020365030780d641180c1c005503011001c2a00300402c441301420f1b01a5490400302154901002c1030510f500450000407100300040c0405000616551412211a030640d403e5082240521001c5100c5481d5460000640f204041c442c04401f488100209441c102d50000303c03c000800c1c3c10b03c400c0780d80014101426414400c0b0086880d540c80d0030341c6009000c1c07140050650800c2041c000c100d0740d080311465020789800d450900000e51302805065 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 46760238 1250 46758988 46759003
    0xa080f0615062a0102070503090a1203320d050a0f0e0c01110102091206101a030606070204090204020a030c03050a02030c071704091416020706120c030212010e1602 72
    0x98000504100c07031a0488109801d280d44981c001501c03283c0c62503290382103070890f0401c84c4100c4080c0d100003901c3d80180b619005060081101c07841600e03040100d550001e08078103408035079040022214451000d8800003040000b02c00480d050007581b0740790640b01c26009410143d4480c1045e5152014030307440160b190083c4d199002e800c2d402010000401001102e000428860782800d6540c240035120540da924204011450030f554010310290410201a8401c14140e91019456070103030420070680121501c15280d0046d000c660051326003946002140c0074180d010002507210b4400504d0002d11038041d0300c814051403650ba401c01855440c01c0498007248420b40e03a49058140a00907a00000e908050800743e10f0b03440ca090b1400d05948428a4050326080a20722110411443c00c001c80400c50801c0f030340c41c0081c288001c2824a28000018050110303040c800c103034482e03c0e52103aa1351540a5011240040c90f94040c01074250b80d43d820140c40c480003a24061380d82940302030096502c602c0020b522 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 46761488 1250 46760238 46760281
    0xb0102030a0f0201060b0d060503070b07020a030201080411120102030901180c09090f0512030a0b0d0c050f0402070c080d0906021f0902220e190809090a0b0a080f06 72
    0x462800c14000c1080c0e90202c0680212011992141d8002c10b00c80c140708058002802c03800e501103806418181054100030a40e001405c050740240030200240c0d90701c0c22620103ca4080c20228001d480f107042c07801020103071403265034004070805c2014020580560003144503000c803100030846d4075071081040e0100d5446420207001b02c40c5440c2c0900500a565005500d410701c06c201c07500006240d42d5845040001180c80c204008102204000911520303001d181a0910111445c90200304075640780d40c07031401c1500503503004c0d041c1040050741030f8880d603049840c1650803401c9055001d40d5020794640c0d0b401003420410024011500c0091120b000127019051150314900721101c8005041c3c150004003842c01042e40d01844005110042250720000711010407090000411420b006400d454645540c14440350141145031214202041910b001d035010114101d40d003180b075807a40d4581802901c5500402d6900c2542c0c030300001847da00c00204542240c031144142c03402a95003c190400a15808510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 46762594 1106 46761488 46761493
    0x206041e0f030f020f010302160609020f0612060a050405040302030406030c090e090a030e0603060a0e060303040815010602010501060503190b0a08030406050d06050405010501140307020a12170a0b0102 88
    0x6440e82c801e0a0075450321140103027540035030340c10041c00f0305503591300d8011030119070303900d24800103108c00108030513150296109015411201951014031030b0f184a01c00150604082c0601c40c401e982540155003880d1500320160050960b0030305000800c42c2e4484007150301030401d0305480c007078841c14004100c00c0702c00d0b18000d0021411100520711900c0140200044c03641d0304401e82050742d4600b100c01d20b0503110000400d1450050740c003d000e07540642c0881c44032a00c25100b680d4102c4251354000d02c0243d903907034000e4032188015510120001030007a007450b258429500080104c0501070407044d6426903d10a1500f150016040b4a001a8000a0500d8040407900070304024001c21039080106500d0480040d01001d8540b2094041280210000d04201e00a20842d0001c40e0890000d59000d0340c3c40b80e008040c20400d0203441704504005020410f40301641c8504041c0f0302043c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 46582738 46762594 := by
  have h0 := BRFrame.cov_init 46582738
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46582738 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 46582738 ≤ n) (h2 : n < 46762594) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
