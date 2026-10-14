-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0353
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:22:16.096609+00:00
-- url     : https://prove2.me/submissions/0c20d287-8c35-4ff4-8d2f-f3811cf20a3f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 63309355 ≤ n < 63489211 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 63310605 1250 63309355 63309397
    0xe030702011101140403080c0c0304030b0a05180607030f021c0c021b100f021e01050a0b010513141504060203090a05030606030c01050d060b0301080a11090106050f0a1103 75
    0x81c100b00440840301090b030081c01802e0350032401014140005200900b844209804108201280c105803881e1703888003403c5070758442c0c1b02d0800da44039a50499070358400c1418840055492603103d645182c0f0514190000c1180d600d419400b64050202c8161304412240d0030303c100c841141182442d404054010880000e40c3c551080c0000e0400700b0f010030081b1712540320034880c14140c403410420801c00d403c40c41d0682d8503201d14a022414603116000700d00e100207851717100041407501944100e000e40305036002005621500c0c0010f444c280201229400d11208000042207061054a490406c01400900701d6030000c0c81d610704440a0341042d00010010383c00400c00e000c117800c21004072406405c00310000d04070b501d480d10010760780d00060011a4100000442c4904d940c484d0b603044407001e4401840000d17100e41e111214240d40c1c90890300d05030303941512400e501d6000c1c2050000e0030b0696055a030303050302e00300c080041940c8991101c1d19850401071802c00c0c040241505101801104003620345542c0104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 63311855 1250 63310605 63310607
    0x70605010504061a0a0305070509040f1512051e0c13090c05040b0f010f0e0307140a1505040b070c090c0e030c010e030c0f0f0d1a0c040302010c020f040f0e03070201 72
    0x2d242e84c000d068002c1200008101400150054805084280c500826141c0d6600002c03141e500610380c0003600a801c1154181b800507407600400f0f2080011041c2c201c0840d40d407030420f030040d10305180161040d0021061543c6034041c02c071180c07a00030a1081281c01e0460501c01090a030010112000682650340d00c80383c040020906242c00102801c80c0d0034040c1c203031282c0008084003070405030745060200001c40c443c1c0702405a5007a200004008056808590b0788190050075000c80085903482141d20b10700100e245d54a0b021001d103d0b0519070784250401c0e00302504a8025402450b003501c0c041d11004000401d0790f083d0007014903980107507503601e01c4250000d0507d40f80801148400e03041c0f040301300c00c92040d83c40015656000603002c44442480c14400400315903d020501034540c0c01c03c441914540a0017215220b40f02c0d880300107000060140e44202503002140035502000f4002083d041091f070240c940f111b940d0101042c0100700240103910481010201e804074904594643c00100d8040295 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 63313105 1250 63311855 63311861
    0xa080d0e0102011a010c02044a070b07080c07060f1101060305101109040e1e01090507050103020c0102120a0b01020d05041a031b1206040e150403030c0e0303070605010504 75
    0xc40c0207000030b0241d068a85a9400f1121100428034100204140418255075841d00b0444a81d80c40c2c00042918100028404094106540e2002498a2260300c0d000d01c8030170751020000000c801402901c00a414042648010b51044105441e08030050000340d00d82d4900380714020080086485043c64a0851403000e49000000f407000a5a03034907004081000c24170219802e030000351000340000e48030422020b01d41c420f021349000303030390080e1a080d02200c4803800007945040e444198481744a032a03190b40351040c26207205c500001c0140e0000703030040084c2d50003a0094103003400b400c400075003490981c055842545504035401624262502d030007801ca560140000140c0c4405031916619060503c11007d568411200712544a140004001000700610007060b03076450364a20006a03880340b81d803030000a00c4000b5141030344076500d064038a0350140000580361910403d1040e868116035143d403001d0300201042980c04081c010050313514501d0342c0d803e00c001c040480c401c4c2000a41941008180701c11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 63314355 1250 63313105 63313127
    0x31f14011101020c0c010f0c0c0e070816050901030f091e02090115080402060f070206030415140124140a02011a0105041a030406090204020316020c150d09050a020a080d 74
    0xc82e4410000c1c0030244801050b07007840e454080c24003400c41c0d45060000c41e24004191405488040c0404001c00d034030014048880c01105107941e628855101c2c041c4014500840000c1100802c1d410403c00c6000e5000b50881d18150240c60000500501261221a010700000e40c00d4101303d540703010990110b107018442a8050414090050072854101d40040c001c010b01404c0a0302c24500803da002c80c0c281c0709401c4031701d81d43d8041c11007926400c061401c8011040038103c00f1041d581001e5642e240144c04080032412945240d100021460700ca80600110f14a142c10341020072100c2240f030b4000c08454030003030909648030f42c000180d601c84180010800b441800b0b0780f90412004010411000000744540c0814212031518241e990300c0b603142103030003042c21a8000b90024004001c0103600c044a90b01a420400b10b0313000d841c0d030b07400c68a041004500c094804000f16900c00d002d01110b42100d58040c169551194085a0021740b403900040c4880003968031400042d403200003558090781d446180040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 63315605 1250 63314355 63314387
    0x151110020c070e0c0c01022805070206090103050a0b03010606020309011706100503070509030604030507050f060601120f090203030705010902180c0d0e0316050106051008060906010302031f1401 85
    0x1c2007220a038005516650741e8803c00c11490f03c100e0102d180c440c00d00044581c1610707184021551240031604103102c8455410b14422051400030402402e2402003040f00c1c00d45600502c60307840d00c22030100640080101818100701c69a40d41264644d0761400d1050380080c00082e0000c54a84007600001442010f1000c2d060307104900040c00c0c0119034036106034a1a00006500b4030310344a0307a03051030031a618000c180455a242c03044c01e00348401d168002c00244103031401101038505040b580888103581c2d01c0250754090015503107e040140009080d0b1042c02d00c031808103000300c1c030144c00c0c0d00082e1840d040740d04155616556000d10104514102558030402c00d8100000c03030040c6090107191140e8040d05100003e52902c9802d5209116003c0c01100c0c28524a00d229102e200b200b4240f060080c0304d24000c4030b0248500c241d00310304132801521414400c800c020006140c80d41c0d203500440280d04040c1021125200724405070400745101500400070348000b07540fa8086260384800103148541144400d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 63316855 1250 63315605 63315607
    0x19140105130e030405010309050f0a0309030218240a0305030729130221160303030f110409090f0b04050321060d060905030c03040603060f0b09090114040615111002 72
    0x88a0b00020040d18101c032424207002400c560740b0706206007010600c0e8035002c5680200c28444040603041a14101030b00d0003514845c804200083c84041c0b40b0000b5030312100c007a004414038508104401075510170304000600140c0410381c2c1c81d0383c0c1600d180c001e450200c2da8040301001005020400350840800d10758000d05580c0755042048010740031005000d0082d000703c41c0ea000c074055401800c007a0842007551101203412100c518a80300344410200c1c0000c800090800342803c030131100340d000d848030007664804100d261501e4145400002c010341041110361800d0304101c0c401091400b043d00d44298060300185944030b0000c0042e611103034071202900e40d41101042403100e0354540840c04110254484000100000345003401e904d507001b026100c0a99200000e0042100f95141d0004070883d51545800e10f00e03243c541f1074991643c0608090a5081140c800041000141c01121a00355020151002480c50341354001910b8654841c805100450252030300c3c614403130001c011494031008003000c11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 63318105 1250 63316855 63316871
    0xc050c010e070308160503040b030f070206090726190f11030d05070209070909051503060615070b130206042d05090c07060f0219120501060203121914010513 69
    0x104100340280c00c3d0400c0e2405c14030310507a0801504108032006030204584250722440c011000001c007680807610a00103010f5080420041c141c0020943c040d200e84000c6507a00d1114038180c4040703e400241244031a201e01850603400031442414410418052001014284254113001d01084101c4001500960003041c20501e011b03881740554044c00e038121007203112902c8101048a545039503401c4810079510700814001540580386031640c0402090f01034510740d03555135080150140000c180c190243d0300030014840002d92800b60282d11248a840703500414071160041200758016070803140b40100c6240002c1c034200341090942000c00c0111f200700070004d0900010400c8200301402c11010036102040726410402d054009103510b2401100464465003c01c1c0c10b90055618442070b0f03c007145c03d641c8120000004e034000c090699025030000d51800415661040f8800001002c1c94000c94a1003004400c81070a0300401e0a00c10740b4000c81c1c130013541400c0410214014008400640703520302540c1e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 63319355 1250 63318105 63318113
    0x160809010207080f1e031c1d0a1203020a0c1515080f100203190515090903070519030e03060901150506040e04020603250306080c01030501082104090c050c010e0703 72
    0x2800406000c0a40c0201181003091450080001d0050742c801038030358007d10084207a00c800400c41000078002440c1d0a80c5022a072582a01030b006030061072083d2110050394040d4008103101809450007212000d0603840364090300003000901e818880c0c403000c1d120100c51401c0c1e014009000c0f128007614800941d0201c1c2e9036608511103240ca406500400042c901d082d20542c1003800004c43c840a00840c50024800b907040c0f000c0511403441000080d0200b01e0080001081e42c81d007d61120042c80300d00009841d1003002e81e00aa42202081220308030304445407810300c05d46001d00345020000c5201054000014452122600110b0080c1411d220411401d003410840070782264050360b00e50b0b500c2d1a00d86c2e0030b840d0410300c9600b112501460302ca060030410380c568044811603040200b170343c0110000000441c1651030a1083c0c80c02c2d64402050406502c03108500001580940c0309014a02940d40c1901000e480d890005080410320204141c1550311007806608184500c2e400074200b090308581e0303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 63320605 1250 63319355 63319363
    0x140105070314240a0311030111040303090e13020d120806011b11131401060311090d060e010f0c02010911060705060f1b0d0c030f060302030c04020708160809010207080f 74
    0x801103a0440300056288185801c81c0840720042d9005080780c4c0382c440d144e05010700325610000e41c0c02c1c069841c003801016120202c4060f54180c3e0b41c56905c20141914101c2125007060010341040180c0500e20b80b00b10050760f030b0030b01840881c4d100c1c0308030001401c20500060070005004150506000000741800806510a040c038102d8951020000e82c1030000c1c040416000d210300c20007231001c6482e00345900100603403242003034101c0780107030350a210050a210b0300c0d544501403d21960b4100200c1d421a000282c610b4200002841c100f200024503100b40c1014a410307034501e640c500c0e0146c0d65a40340b103002d02c03020006441d0358807000d41d091450a295039481c141c0d254401001c3c0e80701440b550010480042c50b6060322804c19a1120300161280703040c05c1c00ca4010401454001c01080c0f81940b1801d070052580540d00c1140d400070040d20407166001d040c00080c1d4002442200c2115080086000281c0852840400d40307000e40300c4a03448501c4080064070b094055001480c0c994072001c03c0c5100060001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 63321855 1250 63320605 63320611
    0xb0307060e0d031710150c0c030204181506090f0b06070210110109060507080114010212030c0c030d05041b0f12060e010212220c0524030103140105070314 68
    0xa1505000d516050800f241d10401100c2e60803520f481a2003408810305031074a0b003205482c46c0c2d100e00100c14503220750903a82408150300042c074a8129032805c0004d460150703c4036003103144190302c105003029195508d2801d03801c0d040410244e292307995014400c1820714400c40b00300d0200c01800304201d1a4180000d8510b0044e4000248240408009600ca141c450300c801c604428101000344070030001751030840003400045444070008bd000b100005a0026001130f044646c0c441a0060901040d042528850301d5000505510200008100101c01d40400700024441c24159560016407410145806109200c5407010113400d2099a2028040d40401c071440c00126020511486048100d0b85405000b0300307449103405c142d80d4400309988084407140c90241c1e101c0d4042508c02196517918040c0b20a012000031806040c000300a00c0a02890428004c03c0710314055215852440300080c818000540e4401d8004440d141c00c101a00c2040200900550f030b00828941000d00c42070311032620280b0188001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 63323105 1250 63321855 63321859
    0x50a0e0105090403050910020706080c04050d0b1510020f07090905060f09011104030b18011e050a1113030c0e0402090a0203060f0915010206090d1e021f0905010b0307060e 75
    0xc00c0c00f2904140c014001c4504041c000f41568042d142c5641e0003a485000f14418800850320082c0060850000c98044600340c49004180c00411855030b21200216403004041c88c20034040a400c242803036032071904c07507d207c3c05140c3c0184a100380003017005081c0070196014484503420318082c08001032010075001da04c1044c890610603255581d00405000d0304541e00905952900000c01000b40650109054030071103620360541c61810112401600720342c802245400902031003c2010340f11381ca43d4201c2504544104408281501101802e10b0380f0741c000301061100503050801001040003c00e210001000424030404092400d500810b08260009058401e110b60000000d11a075440000354942400050f041c0c81e481d1600302804003002098400f1507015200e1000000c051600c00507a003000455141c0d2030303201c0c04900c0c5c0f02c858990340416006c00c09600548035020003e6542c10030602005000c030001080c1101d050500030308451500414074040e8001c1c03003085c001290003d811000054007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 63324355 1250 63323105 63323119
    0x11509051003081606021b19021f0507080a020304080f0106060816030e010c020c031e1207021302030c0307030608031603050f0405060f0703080105030d02062d070c030801050a0e0105 80
    0x1310080d20140e00c0e513a580024071041c804152108a0300b4000c0164580d00e1541e41280c8188030800b0348522040d002110083d0310445610740b610042c014811400200c0140c1d00307045041400642d0f0f40c400b15040706080c500164000306003042001401c005244414101c20020080d040c00c1c10340080036601c008040745000c0f83e0500382c060507030784240d0040324142240d00c000c2100e4110040000d440341c41c0552120f103e8419040c941c8044110409055000b8000000400510740d12200c05c0000c3d401c12030007a64032504032400c1464221003400103602c02e007034075000e407130341c03840d00301c030302a084618a41107082c1540c030a02804070301b07411124042180315010704020380c84003a0f411080c2c0007441950001c6810810118901203002a054064040c0034480e031580d0016a8864060541d54100d2112034030041c0d2101c00801c0340300a04045981c2c4000041400085000c40c1c0b000102c0581c00075644e120010380400901d5091544c000601c9001d4801220090415803034111403081050040c0034452082c80c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 63325605 1250 63324355 63324367
    0x9061c090507270b0f031f0507090e06091e0a06060206070804051f020405040603050a11030c130203060d060507050c0d0f0903060b06120705040801110301060c08031b0c01150905100308 81
    0x5a0240c81d28035165000302100e407000000140480354852047c103090066080101203001140900046000d651040e811440c0c0b0756200d001b00410070b00064007800341404c01c04680040340782c207001860b10584201c08081505c514000f0024a0200018244010403003c1c3c07082c0400900c01103440605403003c4426403440450307500c00e46009119550029502501d0400c000080060200f2400c81c07050041c640021140800f9050540790756046507020352044100940c00003c22441c0e0196401140150034005030700d1040da80e4030101e5005444580100d0f00101d040b80c8034040030042d03292a88150314052800c400c2450014104086500004040781e4540c2a81c403041d8445d030303094030501040d0f80840c110609108901405903402402041c3c069402c0c080300082855190040704c0c104c8005030384003e00c2460640350b100c81600080c000b144182d48140740416503480784e00c05042e844c0c1340da000004400e40e0111a10f03000d0b240f05d40c800003c80c0d040c001086803a100640404ac01c40703030050f511309e036100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 63326855 1250 63325605 63325609
    0xf030c11130b010305180601030b041502030103030509040c0f021903111b180402060301060507020409060c0302030a0b09060d0204020307020718020409230c09061c090507270b 77
    0x5094251064020560746551a8424403a400020980100382c074104019160444804682c1c000c2e00240c020a91010004200007891800c3e038990041c010348620083c20000000c420680e0300c2a401540015008607803426a45003501c110341340c401c05030600100400404201035107841f940000c1c024442c0044c4100c8041c035001e03044460380d80c800d0800f510171344a83d0038010481c00041400b00d41c0110540210b64510a0040d042c10b8092500200154290f80c600907040300d80d61300403802243c2040e2a0045500014024001c02d510040c0e030752005030700d074031380b2003160000c69001001a901c9161003100740282c0740c403203100c9007c0b40d075016a80560307a41d80e080d8003a40361490962010b81c488040c213600410105030359018000b45d404180c01400104140c60b840200451401400031150603054041215260104005c20700031101400c01410600900424400120701800d00600ca070780b41e030188000c00c1400d01c11900900004550404524401d64070100500341c000d500205880c0d0394002c5030015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 63328105 1250 63326855 63326873
    0x203060c0f0d090b0106180602061609170604021507170d020405030f06040302010606030b0303031906050a1206050606040803030a0203060d2a060806101809050c04080d08040f030c 79
    0x78000002d014000000c00703150200400009200c0d102c00598141c02c1c00ca80316005c4103440f0100c51140d4000c200540b104914803060800c0c051488060194021001039000c403004501c00f141c100780c10207000149000d00600186a4080b43c50340703001d0700200403000002d0f088096503414080f503008880c0d00d903041680d2400c02031080303410540c0e2600c03e00c40002107038540096100e12a6100c2e034024000c8a68032001542078450b900303490366041e0401c0c000160086403046c0c050680380c0000c4008251580e071000421162200354002410400944020300f00340880b43c01015008002078513a14589403a15030b13110b80300e020251009032a1900000400e810765290300d454062280c0040d2361002c41c8038040d00400c01394000c129600c000b4026240300042150060700d203540309135000382c2019192100d21004849500355540d080380c8035480c90101080c4865148035152180450b07074542e9656905010b10645440e80c2440c0000070890b00104000005034061584072109900d03040441044919107805445 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 63329355 1250 63328105 63328117
    0x30b061203070f05010b1804030c1b090c03200f070c0e0a0b03010507030506030c15040e010609050901080a02010c0212030c0f06060109050a08120901050d0204030c140d0203060c0f 79
    0x28901c030101c0c0410510008000b5910400d106100070050802c0c03010501c407005000000d0b00c910403032004000ba0209015230703104245c040c460100142243c03506a450000000030f5008500c1d603d64840015140030303010722a9020300041c060f00b2054800d0307108c034499154420880d814154038000701d140c0c400c210f03121a0380b2000e0303c800302e01c10800c0d00d07101d003125005125810389140300350300701401715030258020b1240d43c0c000c1c40b001c1c0240a400e500d0406010038203211210a6900d00c5080200140c1446e01e41070b030318003034582c980c2d540014605d401c00704603d00106030480c14441d00b002107041d0050ba040800f032005158160703218039500340780440460650003840d42900e02c502640c0d0400c40142004504544162000d8840b015089e403604240900700140d030081d01d00c1a4020f00600d00c031284176101502d600c07801454900d00c2d01c4160f140e000d09981080d0700407204203500034028041d1f51040c0c00c404681c964140ca14103811041174002a40d100005400818242c4001070a860b458000504440d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 63330605 1250 63329355 63329389
    0xf011404080607090b12060909070e09060105040606020304140103110705010f06030b0109060602030f180d0311010507030c051b010b04060e0a060605190e030c0a06030506010305090f07030b06 84
    0x24456949401c61511500c084800c90006114a4004201010b4402c03d5601c801c0e910f80741d5072156035a65090041070b00c0c016000211911502200003214004003110b144039007544000f174606549001d003030000b03860b52030b08401d095400502050040b20105030039003500c0942460082002040040b40b0300403481104c00240055090040c107070090166034001c001200d00c02d080030070300d0781c1c0d90f451740f1310443e141401200c006820810404584040c41c0b00034000c012904d0030380f0b0444606080c00100300103112442140070500c010703030300c0e600c0440130301c41d0310360024480c2014030240c10066001007181c072032080c0f801001444a121003481c100c0c2588148688400508204030305504d45868440c1c0d00d808850001650f800c141011031000e101d0807d13540c10014650714044142c048500568008224100184d0584a44100000c842d0341d24144200141440d1f2030014071410310724001029030300c00600d901031036030040001c0c41c8140301c005500c804481d040140f005e590f456400000ea485110300c80d0403c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 63331855 1250 63330605 63330607
    0x604120507080d06080105040c05091608150a03051015060504030209070221070b100518040f210e0f09070f020705060c060603061e0a0207080d1a0f030303010308090f0114 75
    0x4201748034158005409a401006007180c9150745504229a10004a1b048880b403103034054028101405001d41c2078214600d40075200c50711500340301041c514a1943d00aa4465003c1080c1c00c0c8000078034452101c00c1401d41643c03403203403828a54041c11074480c44c030000303004000e1000041d44183c4284510018000c6440ca040820098004c43d129036420042d0103403640303000600800c080000242c01780c4201c1e0300140c10300640390b91424202c440b264004200750f400402002c0c1000008030700441c0316050440103054046034280c0200010080c60b00b0305080c074003500c050030100c8115a00e107103c459104000740707400740d09080005d0049040c01c51075844030b5001400812419141480494400d100e40025002c4071110f603511078451030032100218408030008028400f141081d2102d07002841000d014402c154030308000240c91108440110805500d00c10304000808014500b4504010a043c0100c00030b606550443d1076462140c07261b00031040c0320314180c000607100c41e4011060004c1e00b001d600552 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 63333105 1250 63331855 63331859
    0x308041401060b0a090605040e060d051207080301090f0504320304030b090d08040f08070f1a0a0c050c071403070509010b0d0510061205071b03020307050c030604120507080d06 77
    0xb50054111580d1100424501d43e00480e22a1142040e81e0450303441c02c81c020419162203040c00b983d00c2021a0503038cc2e03800b9801e0086141640d000040020512540c050340e40e941c5072a04038011590130f42124511141040113010115030340c09480d442c0e50741e5030440e09000c00030b000034200000075000c605284a00011400105100c0c0303001c02d140c490366a5105480004454500c1200c4070b00007142c00400d01c4041c0300d80740e8042400f94025049040c8039046c0c5603811849902c4405800200c0005600c41210000410440300d805019029000440d4100541040105034009440386290700031401014040071401c0b0480d03a0801c0104010000a0048049035868101110f030590103110189003040c00c200204080301c8003d05918119515503031035a4491241401c3d040c094440a000b01e420858040141c0b041c031200c252a50b008036100380c0003541d5510b0036103402810009407200c005e00c41d801c040c0c10003010860301c6030403004c1e0380c58070f20700715583d200c041ca00000180034841d01507510728135007200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 63334355 1250 63333105 63333119
    0x40305060604052a1201290f0d0608011506210504020a030f0308010306111204240e10060504060b0a0f02030f1306080f0c0d0906140403170907050d030804140106 71
    0x240039240d82071005c00602d03a00d8080782956042c507035041c0b105000c00c2445074034001d5070390001b400340200d90565061038603c00c0700700d0a007074401c240c00105482c0d46d20203543c42085100c0320305d440208042d0401d0901505031211040402010b003501d44000c5490b200090110343d075641c0464069507100c0c062000c040540d060040c003403d800d0008403080c03454440e60710341040407401645e0001403d4040075000b981d86681d0291280b5803036802c000c5116440b0240142c502c818003a10714994580b40041096002045428042d81c6450380014061880e212082c0301001c6000f044640f5058142800354000c010004200e15621a1103c905404600860001e149807180d003003020448005503194036840c0c035108601c05c180303441600e600311140401c12202c0841c9440d5005100201c2c001e50b00001ea01e180e01d02d0303c1248110032242180052581d40b081c0c2450341d400c9a44c03a80220415000303020301c0f4100004110407035280140502071000e0403000401300401a19400d014050340f4000740092030741c8040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 63335605 1250 63334355 63334357
    0xc050c010204170d0804112823040209030705011817030d0507050310030209070e030f0d080709030f020609120a0f030e06070302060609130b0903090a0902040305060604052a 76
    0x4251100d600840d140d091460f1711902180b8000c64001103000c2d08000184200029125a111041c1084901690300244900e4207044a4000c0041c0c80c00b0b8840c40c8084201e0401d0040d2621200e0f00c02d510500c0909141e480004104040d90700a0800c0441d400d0041c01c04110055160300c1081141c1c1c0010b11107049440203c040d14910021301024015600c444c0000d131014007084440004400c0e5624040002d441c280c003040c0d400442a04007682850071031400b013400c08007050b086044a0744294907013488039031302084641d440403092801ca06003030b04503903d90b20380784000003020744288030206030f440140d907410504038000000c03a003c8800110852811075144441d03218141d001c134443e80e0321081761b4100502180e00c01c0350b1650141075182d90354000c1050b414000f0304101c5915014100c0e00000451480312517002d00201070046031030b45540c4007008141809500140c1042d801071100704000740000030346603000b030340c211400b003000e42d2840352940c03022010800d004000703491410030855101d0000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 63336855 1250 63335605 63335639
    0x106051011010c0503011410030f14010e01050a0e0c03060609040c030b012a03050d09020604030b040b060a0e010b090f03060c07020112020703020a0305070c050d1101020d14030105040c050c010204 86
    0x210003072000f06480c05055a460000f41700380c001806070034040e480f85140c401c2081c44c0c201d900e0308000407001500a0701d4021212020102c244071000300005004105420140c0750040404a0791080168140b4260b14030400000d018030316004000700105105546045c10b8a0504130042d004001c041030841c070013005029150503032030101d03000038010200402000024400c0c072403019031090059405d513404880544c0f01042d0707291020380d103c21500c0140c2e030300c030005d0004600400503080c0300c4c00d017400c2405052401601c800d00c200030411f0101720144643c03114504480c00d29144580320811000440e5411090010040e4540034800421040014800260418034000c0c0d86845a042d140d8441e03008922a8160280250f804010b040002920440082c0b816512880c00e1460b0381d0f5642c0b0104407680d40150040302c5006071600c03d00300d5964104080c045050803440d000c542035080369440a0380d8401809403034000d90b00d403460703214240d0242c0d0032116010104e02c021503585588240b80c4141071079007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 63338105 1250 63336855 63336887
    0x2070b0f0403150c1407030c0b0a05040b010603090b04020f010c12030e07080f032203050a0c06080f2a041e0303030e060c04060804020a33170112030201060510 70
    0x100708400c4518000d11414034118540d4940016000d0005d03c0c5200d9a00904400c80401ca200d40d08140060021020309000b007001c09004507481c102860040d50b5800140c00100406180c25650340210300e1080718283c1094054031422024140c0400403100441c0d00d51015103440c41000c0404002d9a01d0341c0101c80d1390200406503511152100c100c0d54686100c40c61840d41d50748140500c500c03000700f00c01c0c05140185110595400c85036241d460b181001501c80094401010030311040111032741060465a00000744002c011562501003c4260520411030510400c0807602521f210301c543c40d0303011075010b06004546921200c02803050202c28100318001240021304000119104080c00140d0b1030081d040e801d4402e00b0107003003c1003100c40300801041680d11810900340040d522003840500d40d000e02d101c1d0540a401c1003220f140806006400800a0400c000000f0700740740700d4107a0703c4050564200c05412a030901c202d08040b40500020b4024175800401d90701c900a0b040c3d0410101e40541e810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 63339355 1250 63338105 63338123
    0x3040507060e0303070c0e07051c05040b06040506100f1202042405030118050402041d030a030e030a0507020904110a060f090816051003090b07050d0e03041a0a02070b0f0403 76
    0x4a007062503205c3c00b600340d00030030312101801c0c203000d007031070204442d9413042c01c61404604040381c0b9151926507540c40301d00318001d5651002400144099401a140c0c03004060760288070301c2c205400403800040c18000d12004000b56012a10000e80c031880b40000c40385248041951502d890b84000b0b588058841e8041600b0700c213041d90004ca181c0600c0c1505d04035881e09141c3c894840001040c600502802441264459555860b010081d903141400710050180400110348817984242c01404442c0a2040e00c10658014001403042550000407100c1c1c0c151706076410380d01622149414501c5040d03030150765501280c541008030b1026404107001c89403c4161791203110160b42c1c0d0466684500c01c1a8141030020148501030000e410411650030710341200d0305c0e00040a00550311050000b0328150340300d100041000901c16a070340700c18022183c101d803414000e103141502d4200720340d040036042400d40d01c1303100d0042080d20089009005e80002002c420680740d5481c0751102503a003890f40940402c03140100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 63340605 1250 63339355 63339377
    0x1e0415080109270302030c0d031a01030915020f0903010207060e060c130b0703020a06111809010e150303040f030f0b0106020f060a1a041b030e0d170a0b060304050706 73
    0x22060190144006882d482e220f040c09803820004200c0d88101070540a61004000000c0d1807901004001c08900150b0390021340c60004020741c4568400c41b421060401d41806206030206d4034072a2824064070041d40c00580e02ca4482c08541e070300e8050501c415915500c0483ca04d428408280c014029004808003600c0056880710180415405041100100d425007040c1c1884400d99a6004092450281c0100c4915103c999580001d407107a560000e03004072400b1469501a40c0501c0c16052030040480d0701081c03d42c1042d05801880c0f43c01842d4101d01c146c0d030000d900031620240200c1d000390024000441d909078890600c3c003903591514808a80c80c8203a8000041e0140c4045030b04014265000701820464130350120b48400b402681c20f44103d0600c0b400c508000703d81d61031090b10028440007501c150341c0c51025201070300721401d042c00380b00b19400171150703003501c640c0c04540601c1e0111000e1600f207003078491000000c010044854090303003240b0004144024084002205012914241c0d60152800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 63341855 1250 63340605 63340619
    0x30f3d0203091e03030606031b0a110628050604090812060906060901050a0f02030c0f1c020304080d0f050415030f1d03070204020c01140705070308010905060112021e04150801 77
    0x608400b030300070f5040e0000d1021408500e00ba05c002c40d000440341c0805041c18800301000580380c0d2044248501241104402040440c428004594441895002d45082c0d403000b0301b40501802403040800011607407100010060390b03d690207610001d800003001505c07018070b01141204400282d8031f051041d0800340000c0c5c900e03d0100100c81900d20103a55080c10910b1300351059401d0710710318044c0015400b062100d00e46a800400404030040380200c000c0c6910310814807100c282010042031001190010441030040120005031291120494903091a400c3c0c00500102c403980100d4119042c240b0b82d65982e0b01c842949030b0000d0110240c111802c010018500050741115148602c1c01405608140420000351901d640900000c0c056400007250401c010003c2d00103442040b110800851408911310080c164090070700c50140160314420042803d05c20000b070f11040840304040141600011165651b100218400002c43c400c02041b030f4980343c1f02d91100e03040446c09070451000034001d4000103808 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 63343105 1250 63341855 63341893
    0x90c050c100c0f1d060c031806070c0b0d060e070f0f090303081506090904051606030b0307030602071103070303021f020909040f14030c01021206030f3d020309 70
    0xa403855203510000c0304400e6000c1c0d801c0c01600509081190744c420b8841070603181c120040030030102c000c029554403548103c8210f02110301c21a828000d003814000d402c005441c500031401511a4040320944440d80030250401401c1e07e50003407010010340006000b20b217604007510032940d550075142c1344401c032008070003190280745912000d000680310002041030403507802c100d0060290003a018a1920f0303280d00208500304001d60b030407207040c0e01100360300c01c44440107804280074001920b000d00040c655040040c0ea505102d000150819500050041c104461071000e6240c0b43d0000c1e09072800c040c6e590030040e45560f5410080501c061801d0040b00390318206201300d404c1400d00034050302d05515292100011103d005404803a0105600c624900804082015200c00134410300050f0303a5400c0390708091943c09018008078000c1d48603c03500c00e00b403800031801d040408440c1102180850440300c0c100708203620042084812002c400c0c0c2c000254003540c0003103100303482d1001100e0700003101c441c0c90a41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 63344355 1250 63343105 63343121
    0x1060609060f0f0503090a051603020f0603040302060f06010512100608100501050d0209031504080705070510020c36010321090902031b0d0203060102010b030d0f18090c050c10 77
    0x1031915080c200702e94044c8000d9500803c035241243e50750501c507920140b03454400c0c1845a0311a038841005c01c110301d4816100301001906803400c41c11401d05a80296517190301900b011000642c481c0010000d034881e41c2924400341d84a14003a0050404000400d2580c4035401032030000341450700066124115252414100d42040c4d4455280c80b01c0040d20100a4105003002e60b0725000c2d00014100301c990700b41440f0300a030f01075003103180c1d10101c0b4a0318900e04204c41c0e01c50b9000b0105204181860394002c1403228861505446003220b640000381590a1008250820040c482d5002c0300c0701910080514101d040c1c07841010802c03100f000c00d040043c07034403d408460800040280006200300903194014640150b188030000c104000b6103103801d070103500102c0c00300c22520340c048208081c42d030b4240541c009801003907000d424060101040103042d0400c03100c0200500800c2c9502091a0a9040e146002400e046408001c0f800c81039100600551042401c040300e485100041c0c1000ca81c2c41c410030b00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 63345605 1250 63344355 63344357
    0x1b020102031302061b011506020f060c09010305040507080106121a010321020111030a020a17060a090b0a050303030c1e040e0a05071112040801060e04020f0402070f0c03030201060609060f 82
    0xb200015401c01506920101420140607001c0222501c0a08240500c0c500602c1c1400040d0589042c440001d1902d04559540001c59120350305201c0440000e1040b203400c0c10080ca00440c1c05d603103e0810900d804c401e980044000e41c03034000c0000d0807000c52803801940d648148c01c5448584006000f48804040078080034094088105080155a800207004006c2c1402c0d800041241005030418042c03070b400c01c0715002902900082e0b07118086a2011142c410803080c00c0600c003607400c0c8440231030102800c50141064440e80c409001100f45c0c0d92915178001440001c044a64901e00b00031b0704099901700c51200b54848549071410382c21001190103a0b41900d00b40b0101d8100340e625942c441c005401d000d04110140028080721b0000d1a0041c400b16100d105c0f11440690b0307442c502403001742185d881d640002412030409052200503030301c0040e6080c05d003104a44c05616400c20741000c0403402c0090344000d0903100303590310020800d50190400c0c02280c44503100c0011351a40c90b02d05171200c03521400008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 63346855 1250 63345605 63345631
    0x70608061c0c0915030b0705041715061507080f0912030c0a0615150801140a03020d060207111c0501050105040c170405070b0d0203090706050703050406080604090f061b02010203 78
    0x802202401c0d0b10807104d40c503d00010403c0140c1e40d4503074841c803402c1691190300003000010248a94a0920202c401211020005000081c40780e0b0444482e05000351200c3d100d402940d04a58024814a068400032a08109826602c100c2c0d44a500310765405008124061070080400102010000c01170711087c001d110702501c0040c2c51a913481000b40706000c0b84407080c00096101190070341e2081d13045411350031302d40c8540c0300e15410705456006c1005e40806141c42590005414030050f190003034a0800e0769480000903071502840d240c94607903401c0c3c09950a401c22030b0595403a0420114002e03016040e0f005000070032150340c07544184419903141031040c20119500c1800b050344628418a460350041c001c8056808480d25070b6520701c4551311000750180755903000300600000038014001c04005003414281140341044642d4082d02c103000d584100340c10702c214200040c540307884a4001440300340d4404a080c001404d18a0031600078580d001c44900c04050000034506598014030861b401414410040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 63348105 1250 63346855 63346859
    0xb040611070c03030e09090607050403060e0c0603040c09050901090c05101101050723040f260114070315140609030c09040b090f060c0a0507020111070608061c0c 71
    0x9440a000158104102403504000800c0400c01802e40d101c0510300c00d54858400d1000071040083ea5503021b40801c001b908201e05000c041c9410104480480f54003a2012031000035180400307040010b007035155a0411000800c00c001c200303421421105540d40d02c03408200e140c03101d00e11036080b01e100c4007000706254082e8406200c1e9241080040b51400c040745015040c00c20f806c10000d007985d10a441010110700014005020018081800780410b04000c00e0982402e240450146c203241c883d10030b4442c0040b15412840d416a0032040072800c41200400911250040030030360f0500903403c9518600007441d1003d00c210200c405101e080c12140f1280e003500d680c40609040008a5019000700c55140c0705200e044074464541e0300d1058070860060044108900e08101d913b420301d20b404615407001d1704250108141410042d05036080301f089450029200e203090310042c0c441880b8210027070a10b2040c0700c000103019038070a10745403064006403445192800031402800e180c00000704000d100c0e024101c82 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 63349355 1250 63348105 63348113
    0x10602060106050903010f0f051005060702030c240f0a030c0305060a090509070e040c05040b01050c1507051209070513060503070306020a05040b040603060e060108040203150a0609020a05070c050307030b04 90
    0x21341420f400c0100005101641d43c6900320848490b90071030240142c0f2142000f040318080045940148016600249814050b80c0065152841c1015161080030040340001642c0c262811002a10805404c041d94820300e51721440e0701a0000b01540000038202165100f2891280c0107882c01000064210b4030709031f040a8810010f44002800c01c2c6080c896044001118240088140e001c0c40c018000c401c4024100004c1c0800c1d01e040209071814040e04121900c0103000c001783c40070030081200d00e1031806441d040ba040322144600002040c1c10040c91041c4030b50408041407040c04c5801c100c44082c0004480b2284070250f0700c1c0c5204035a459005081c0800101c0d1241d0001d0030307031180502e001d5260a1f140c084600c0c580c0c006130001030010b50784a0003845050b0400b12500d8002000b401c00004529066001035510800c41c8680e032400c0c00b501c07003c1754103ca0a80c020b0300141032600c40c155100c01c0116801031441d00102c40035074100103501c0c00080c00b401c02181400c1a240c114492152954031911 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 63350605 1250 63349355 63349357
    0x1050d0507020f2407080c030a0c090509040501050a151802030a02071208090c0a12030f212408030405060f04080a0317150a140a05041a12030301060206010605 70
    0x2200154000c0a03ea1461a14284090782c94003010144111840d810f5207a03d58500500030100c20500c41d10f1410712082120b80030691354040960000411410441c0004a0f40c071215540001c0d080001c2009001c1000701c1900980d100d5644d505042011564117a81d9180e80c5029104088160075144d0281e80c1700c811540040d640f29400c48005894040250340310040003603001c81d44400200e0a07000c0c003c0e4032406010f03000c84000100d440340c011a041c048071200c405481c081c0182444095003954604902441c0c242d524409072507829a00c1010354180036010380806848a081e0180c4444c40050f294101c00444081e0303414003005600341410902449140e43c00018072542d003070f809000005034684c04001201e900d51082c0e031009000914541c1034040d40744003600011003210114101d20300c64654a84880c01c072158800c15200910014020869590071074200315001400c2a0902c64103009007260412240b00945007901111002400380c1e490380000c7c000c120058202900410000f84528 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 63351855 1250 63350605 63350611
    0xb0f0f01111905030c0601061d09270c0307081203180a0b10050901050103020a210b03060f0702062406030601090801021206010f020a020109030b04051606020a051b01050d05 76
    0x80442d8a1007203440b000e11000b000e00b09044070240d01c006160f5160500511210b0700400550030b00740c2042140152480c43c10901c2c68840d0b000c0c1c00013200081102c002104881e6a407900181d15000c3d04402030701c401e844082c0302004c1e6010b032280c0400091403140c005035480c1020901d041d40e41c15a180e010707040e180340308803a40d1311001c8c3c0304900000c4082801520f0040c040ca00e25440052403a240c078040c0f020050050340070318181441842103501e00c94000321608401600203518411210244001000400c240707034019070580b08010412502c0701003d0b007001c0c003c40d1642c00300d54082d5607108071801070b0344a5800f0402610300480009a45080c400051604003805042005e11191a0742d1668220703048600c070300a00b540e0040070300116507000303c034010980e1941e1000d0482c44a02d6000a4010001e0b440000d1446d2441c1001409200f01848a050360b06484200307600c2865a4020096552807a1031068460b80606101c500d80d00006e01b0320019181c0e0180c54907410038600c40d850100900e001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 63353105 1250 63351855 63351887
    0x5070207030b09012405031f1806020706060506071a0402010302070807030e0a0501140f070602070606080303010f0801020a08060904020310230f06150703020a020603010b0c010b0f0f01 81
    0x1490044001801500120b100f8040c040001800082076045a03914041441400c81d000310340032820b004549001c5040d0341c80d10094480001500f031100d00c45001400e200a51042c0c0391030158a8004004c503940003060001c0c0900c1d000d0101c1926903042161510a1a01c02040300d000300d1201b00310b01400b54000e65010340141001401c10049449500496100c40c03000c8002501c0080c03100c0c02072511841c56005444280307001c0c01c085040d0003420b112481101c040d9200e1002c041082002c00c0580c3c0c040315032840e4000d00c18000d8a030745050880e620b400c203020300464461008004a02c81c1c0d01403082d01d14040040d5900040c1780c40c2c040034415080805001079030540114a1040b0388451240900e42c2280701142c0228001a44404a100d0408000e001200041100c17418131a41d07554824015100c1c1824091a070303500c2406141c10703481c00c40000e4000b904502e02000004400d90080040e1120007080b10080c008003a1040c200310003a242c556070343c4d40c400d01903004050f042d40b140200304400380407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 63354355 1250 63353105 63353113
    0x30b06090f01350a050901090c06031e060803031008011e0902010c0b010b0a030e01180206160b091b03030a090314010e070305010c020c0d03050f030408090d031d010c03050d050702 79
    0x31034050800d5150141c03840480900300f03041800501c0c120f9110b900c0c1d01920b8031000304030b1032680c1c0c1c5c1da0411920319441342e4020562221000b520103403a20322010a0000c6100301080400e69801c43d25890350400c803a805414441c04400040f20030041c040c6500f010600c81b002c0b1801900f165641000b4003907160207904104020500c0f01c00103543d06205030107800912103040e159000140c00500b51188040281da090b410f00d100303414034500b100e000001969040303074140e4946480a0305c0c020204440440030b00502c0f04982484100100070942c0600036240d00b0004410710072000c1856074a02c112801280006c40c070071420008104000440c08100c18800c0000c40c050000f5201030b032a115054100f580c8a0355258100c40d00749030108842051b81c44250780792709645415032809405801450004030b0f2191b00040001d082040440444010403030040010b08004c00710f0400030304d01d02c2000f0403000451004101e0300b04640c0100300d000c054541c183d940914002088110740007070304000e4503010640c81 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 63355605 1250 63354355 63354407
    0xf0c080f0405061b07140105010305160e040b0703110d06060f031e0504020604051002010209040609060605040303030b010302070c0602060f0c18011404030b0106050d0b0d1a1b0a0f030b06090f01 85
    0x4171b190802031030510010010540754110304213241000c0c0b800e9804001180140317400c00c01e44402101310790b40719402c145001d031039543e00f140a03000340910300b00320303460303110300183c904401c48069110b402542c045075200031450441020541c00c807408000400d801c01c006040950714102d03136400103540584007030705541c10301fa80c400215000b98404002600543d401040c00000e50a1620582000f0040c0c1141402a14507003c000341c114416408060100354035190701c90a164000d804444400350300ca21082c1e0100e540b614025110b0b01c003a0340384070b014030361000859065034a00c1e090b00c5404031940d034914a48420400113441c040c04440c1d280307004800a010010101d00c0e2041d001d070090441c1c0d202d280daa900061803410450310f00c0c6100714480c0d815105d00340080742002c004020700c4c201000910702d8035228280321210024800003500d00c03c800001d00141034640c400c0c04440000041d44080c003101801d41e04000d024000c60702515006032400404000c0c6c0c3d032182488034580e1440d204100b01c990 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 63356855 1250 63355605 63355613
    0x3020d030e03010f020c1015060503040606030b150108090705010e060702010306090c05030613020705070b07080904050712060515030a09031403010609060905030d080604110d0f0c080f0405061b07 86
    0x120013500740e012856010818800526044c041351642216a01080265400702c00b041961315019000f12010801301000113010803500b684180702540c1c10850320345003850315046000d0110a03240c45d0758009020000814280c1000083d84005d443c0305843c1c181200700140207012a039001a0340c142c0c101902c0754000102982c052048007903508555403850b503245040e0303040c00101d060b001c1000300720f03a104100300b6000c14800703d80b50341590031220906a80304143c0c00c04400300d01940342801d500078a000284071071139400c8503801800f100d000300c09001440e034620030890040809085a40c44d00810000500703541c20641c0000c800c1c910a04214500121800982d02c080e00240c10010114112040910010b07400009900041000310010040a2241c5400400310880584168040c40e00d076100490f010282c03409461130b00c034143c481045540d5581200c0d1000c0e118601d8010301244a80001c1501c0b0078441c41018072582d002030003080303142c81d8042c900200c126803400d0403001d01c2090010310002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 63358105 1250 63356855 63356861
    0x30c050909011203020607020a050d08130206030a05010920221203081b030c09010e010504082d0712080d091401050a0c050c151009110301181503020d030e0301 70
    0x83c2c0814007518260204a02e0082c3c50000c010700404259030001c0000c0000840c00188008091001d140403050f40c0c41d0141401520340c88030000a51000000c0200100e12056610480c1200c030002401d0208800780400d000201c3c0e0000303031410506504110007103420900d03e1400100300d078001d00004040c2d0383d88111500001d071700322007180001c24102c18484c0c00c50701640c122aa244141000700c0c61401c0c840b803400707807510a4001c1c1c00d040c84031051802075182c1c05002510000c000c0101605c410004000249115162001981105243d84800b90320143c13000507410090752500c0d5904560640c0d1601c1c0c01d4140d0704858a0318882c0381e151007454000401c4281c240c542910340c3c0c40040b4850800c130400b135041e9000c903008803041140c14081466560030014681c8184101c5500105003503c3d02c03407000b412810150040398109040c0400e5034810410500114103d5880c0110030009105100c00001502d545141103601452800014405407a012802c2da15141c8a4182001c400001ca0086030039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 63359355 1250 63358105 63358109
    0x804030506010305100e07050901050f040e060108030a090f0b0405120a02060f03040308060d02030601091a030607020d020f030f030a0e24150d050703060513050a0b040309051f030c05090901 83
    0x25400071071108040020900135024586c0d03504000d09030b418100383c0407a844800512500740304900c0e071042d902e071549584d4013050700320312a00f042d11825a1181d010a650341e1144271890001610a0400101019040b000c0d006940108011a141c00d1410007042000b4505400d40d0b0a540944400c0b01c0040e03803154018122018408141900c0349014100507080001c02808a406072404180f1a030051b9008204103041d904460740008000002d40d400c0c00c0c62041000d901c075050700c10031041c032010580000c0e0101505801e6400c17161030f080e05281c00c07a128010110340c0792000c0818004203405600541150850400e070108840b814002d00002d50907008480280c0c1110704254000d01a840c41c0780d010103000351f6400c1c3c3c0d80e421248220b40c0c0e001d40d21000c81c400608010ba4600c081500b4a501c030b60503440d01d070342080482d0200c12845c140a5511030096500700c0c046070911f0000038240c00c12071284000e15002445003030b0039103044030094015103860b01a61003001010031041401e99192103403140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 63360605 1250 63359355 63359363
    0x30c010c0c02090a1a060d09020307031a0c180f040e0a060615050a021b03120f030a0b0405010506090d03050f070507050310050c03071b0804031202010c050405060d0908040305060103 80
    0x20781034900502551502c00350041c2107141c18101008141c07421449a600c0c101e10540341580d9038617055954000501544070000c0d814041c5081c00802e1280c400e00980030040b9005449440d40c80d010200085440f40120002040c0000030081c041407070440c41c4014650000b030400301d00320b22030200b03490400540e000d00300c5070b0980d104018044185600c00e070300000d00c4c42e420300078600080340c48040c1da207042580c000f280c83c440d40f58201c5495181031041c0c4000d0740c03100c85465164622405040380780c1d002204d50340c3c4501c0c1340c10082241d602d03050180034102d4a002e02421329025440c0103206074070002510603401c1c8a402c01a00802000200080c40c00d6806980640344031400e000415043c42d816205d004101c90500085c8514014100203c0350040400d081c5840d4400410119410003a6106030182c503080011600005214145d0803001420741198000c110406505c2c0f4292040e0040e030180035000801032040340c6203e4001e03801141890b00038000582015a00d0350380c00c3c03034030000741c204507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 63361855 1250 63360605 63360617
    0x519050c010b0312161e03020609010e0d0906050307020f06100e090114010b070606030611041502150114010c05010603050715050c1906090204090302010c090b0708030703020a02030c010c 82
    0xd064444207101e419084030303003140545115a41852550780754050081140d81d5203003904500b904028065910300d400500d600c03041d840c407010a040203520340c01d0882c6c4402841d401c1c03040d10140d00e440458270b0040a1500c0d00d646000c20304005089403103400c010012410351284624031090700d1000c008c801d10505444041101c042d007085110884440041d010341a03a80c141007400c034440030803240707960540310251881d40c0c80300428113002d4003a0010740d0014000078030341400b42e1040500c81e40100103441100c4c42c03044209100e03d10403039513644120200c3c1c1c81d1001a1005010701d5149044107e41c0d0381051611080c0850700b40c541500316040c0c2d0303000700c64560045004100d28800303001103030502d10036030818a081144d90f40001e07864451070803c0030001c96810381e06904204071588041e64032a00134008102518040c036005e8028446032a00d040400d100312030010b0340e1507403001101d0323160794048056800e54031245c400342d01940042c00800194002400605080c078802d208800c0603440f01e80d204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 63363105 1250 63361855 63361867
    0x2070b031905091f0506090c09010912200303120c0c150a0c09050108040503040608040204111204141f0e0a02090a020405010f050408150406110406090504050a0902150901051905 78
    0x408030f101800c01801075414245006c02009941d408400c0e03a0208007400002e43d070300d4540004884502a5402c2409009203003e500c0c0140494003081290360a242030300180e00440032401c040d030728000d4010b40c08200383c1340e40014140010440140103030350034650450b20908000820341e0f02d81c520445000c61800e0b80c84000850b5594444260b00003070030282046900ca0801c4d4480366260321aa002e03410501a5441c04181103444076032100f01030200d50341c4015187d0401c40209071b5511802da030143ca10414030502900da03c680800e48841c00170030b980d070003100c010b6480544000b918154a04400c240607902c1c0040c051307251003103464440c0d00d041c2e030016691030501c0005400540020300d41c4080140500051025000c001506100c1f285c0a03844652a80d840d480e00c1009003900c2c080008000001140c0029013a030007500302c4054400403a018481036030341c00700035400c884c9003920182d40017000c5084484814141d5000340b40c0884185001d034030b400754480d0f000c0d180380c6c0c0315168200020400250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 63364355 1250 63363105 63363133
    0x6060b1209010605180703020c1501090c270905130501020c031321031d040f0629070209070e0604030b0601020f120f0d060306050a020306011e02070b03190509 70
    0x4120151030304079505c654507040c0500c85074031050f004100f02c0c24164001141c04950a0811242d642c200015495038040d40e11100558050700c42c0032079075804100214903540b082c20002100e00d9460f00c8a02401160a10f82911030300684405400d18426902640c0c036000402c80a00084c20300b061100000c0d030f6208586d002402001c0d825501035823440c502c0254140c0300211a2002c2c804071034041c0781c8800620000c1c0601100c4145003003249500901d4002c81c0440e1814a4101c0d0044814011034841c43c00050241c4007500ca21030310ba02c1d2624001088500010315040745c02c250850302c24a40700c07408110b0580411401d40c4150800d82e0640003100800000e0741c3c1c104520f80d82410100080c0044099042205015004500c1c41c03e04c05900400e0842c503640b0241d020070011504840b06001da820300c0c1546200030350088c1c4009000400442070403403150012540389030340325507a81c01800200c0c41d1031a5070442c1d800c09080c0704200181504c0b400720003051405454080d01c00c0710081d00c001003003182 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 63365605 1250 63364355 63364361
    0xc0f030209090a020d08030603010b0d0b0108010e0a0c050103110f030406050f061c031112030103060608011b050301180605040f05010e0610020601031b0e09030903150402090a0906060b120901 84
    0x31042c1c84991011a07840e005840302d4198400c0e0650141031591280c80b802d00203405400b207080c42070340041c0909040300c1030002c0724407920704a4074504001c12041488029598881880b40d001408551500000b008194071039400305809000041950303040102c01d9102e55260ba00549040d1059503c44090107c0b010710b01010541140d81201d400320031a01c0e441d41007903060800d01c030180c00d00043d01901c0c40e40500a100c0d8a00b41390f64215070320b559603120300e809002802175004043c415031030900200c111102420b01140b000505444880c2168601140e000d190141c10200d110101d403188000183ca4036907010340314000300f14843c0030445604000180e0072600004010ac1d10a40b04010034000403038010440700d064035001503041c03c582c2c0301b040408400b0695030788082c40103914101002170108002c0090070f10b49030110140c0384440c480a0000007400e4064901a51090344030020500000b620340c0110100e44c4104c01c01b00d0320540d600420400743c1c1000700050506940f141c10052810400e01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 63366855 1250 63365605 63365611
    0x504030206031f0603091104230a060b07050a0b010e060904060c02031314040b0109120201120209061207020601060305040b070c0f08030a0207020a0e0c07020607031b0f02010f020d14160c0f030209 86
    0x5901000200103002d51046107030727510409400e0010031040481c05908264022a002e44600c200095481b48103150a686e9a0310403941502c00170781010000c0340d0030611900550203040001c1c0503102a4503aa240c0c14000c0c08403081c804d06610040080c1c801084c1a0030841d0700600c1a85030b08503210541c1800d1105480303440017580c0c100220702e2414404140030306880340a450b020b00c4c0c10048022051a85802403040c0c00e1866070081c000315441e840c070f0350360440240c07141d074181d400c1e200e007640c0c0c610b0b082d0181e94041d5001885050f600000a000b207103e0000e1000d82405401000c190314495128006264015505548080d40005100055081400b1880d0040004c4021085140f80c090404840d500610310300034802d0f0340000307000c01490311840e0f2a0614844120b0301807003040b864a080c030b50307200c0d501d403040380810941c9448030086400460700300c0d4200e0761034580700c0c0c2584e40741d65850303002c0d0300c54880400204100c5c020074006c03841d40e0f000070010b00303e04245035119a08500400465503401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 63368105 1250 63366855 63366859
    0x9060602010b220e03070605010801020309120c101e0507050301170c13050709030803090303061011070e07120e010c02071e0b03100509040f060509010902010504030206031f06030911 80
    0x14a01c0b154207215060f40907182e06030003c0041c80415402d4554114818004040c040504000003c5102c803010760096005040072030855240140c2001401d1180c02030000c1e400b92608082401d02105c061a0452400e076040c3c03000b0503031080e0715210075100300c4074180c805000045012005000700140c00ea84007071300c106400014940000c0325000501c00c0b0300f0381240c00c1e0b0b40944401c04206142c0c0240c0700d5502079684409496201c0c5880784525a0300d0304219400c500c5105010706148065006a9958003010442006030160b6804c00801c440e03104405450392040040352419891030a40c51b00c80c040c01c1c05440d40c000300e202c2801000c000d02d0440260001d035180e083e00d0080405110581f103003001141e6140c080242c4913544e11a06900001d0203522040d04600074004002c1004551000b949d00c03030f840380800b0011a122155020b00300c0f2148507000780895000c02040c00545042c0020355400555100300e04941000c201a000300542c0c079910000100792144005810401500242822800e003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 63369355 1250 63368105 63368119
    0x5010912020c0904080a03020405120f010b0121240905060a0519060804051e030904140115050304020d0f050708011413080d0615050d050121200a09060602010b 70
    0x400000200083c201034001001c088002440301105c0e130103034040d030300100001884a001100c054401544801c0854070b403641551070000d08503440d60040c9510590403038884011516009500c41000046c007185e458004140001c1a6250351141081040c4024011005021031107082000034403400e4001500180d00c140e44515880840c0081d0b5102c08003201e070310303151003a2a52640d080c020301f42f402c0600310111041007030840070f00058001004201c52030741610102b10707404801c2d11b5128207003001c3c02111342807482604090441c1744110080c580260005241c21203190647c0c1e5042c80c1b41907080c90868590304020000c111002c400c3c0300b288034840300c080600c0803d01d0701000c0d1090004200600901501c0e0101e854103090070282d0000019160200039400400c401920141058004000b40690241054004500c121104542800c0130743e00302040100c40445946101c030703003000d4140303802101d40b068900d0b0b503450761081c41d070780000e1088000024820307051400080c00d41d041c0d041c030030380a560 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 63370605 1250 63369355 63369373
    0x51005061f1205070503190c02030a050703090816081005131e140318120c0d1a070302070b060405040c03030807020309151210030f02060307030603020303070501091202 74
    0x850400d00070744000908101079105441081c1514115001c0c441840e51a103000c0400035002d03009001540909541d0f1750b410320b00250900944207039000c00d02c0510058000340442c21301c03503014801803e80c0620a0038402d11706601c4070211490901c1214010060340d0072070604102461060000715a80c40360510140254a08201101d00b0306106400061524032800401c0d14180010b0508114040c1d02000c260806041e03030481795669004021201240900b0840d61401c0d85031881104010b500f030500504001c01800080101140c028036060300c0e566020f03c03c4201c010504d808980c07090456850040e150011410003501c00c10001704114015480c010600003c03c803035502da40100c0f58940f8000110740e440020480c11800723503d0010340c211101035214070a0b464184054442d0381f044dc0b100b04501c2d0b4902848038405c46191201a04500380c43d07200b0005414800011603200031541000300c1d406550b079000c00e1459000601c10741e621396403001c0b45c80030001c2c040390309014800f4510042c52022 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 63371855 1250 63370605 63370609
    0x81c060b03010e13080904050f07080a0e100203061c0605040303061502060402211501051003060513020903010612140706030b01050901080603010e060702060906010602060c04270e030705100506 85
    0x5601901c2c2c00d013404c003030114403000c100001c001c541c2c4241c00a130050200342005144c20100420640e120004900d02c413000030341000709442450801e020701d00017400030303010700c0200200075440608802d030041c0c01288201c2420303007407103004007100303114490000343c0b0314250074010129034079070f0015209408a00402c003403150340016210380092301207074175a10101e10200440c0c1403001008000140c0c1c0500c0c240e980400d500700c0400d030f040f40d07415a40700061034070f441c0c0200e003240c40c0c602605a100c042c0049200710002c56a0107441a200050000113070a40c5440340c4049100340e1540881d01181c034041e02c4561400306101881c000d100e5404c05000110740ca030000f13023103801a01c14250403c090400014403071382e000d40040d8012611007050360315900340714500940b9500c0494400c44c0f140304541c00040c215100041e0284680348a00120781058200020b024000050030140c01c140e007140e02e8031046003099803041c0e104951140c0c0003507a487c0140c0c42d120703041c0303d0000400150645002c0030801d1503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63373105 1250 63371855 63371879
    0x20607030806010c120903031d101112030a0b01030b0910090915060e0402011d130504030513090608010b0118090216050a0609020f06090a0e0c0403081c060b0301 71
    0x40d0345400c1a442964401d4012100010b6841c4042c1026035503185110702c00e900418804262800f07540c4040c01c6910502e103405030002d07103110720742d000140c030300390a20b04511813259446c45101d40c1c410359120760103000a07600075810a446090004d5964065000ca41d0303050b00c10003c01c01419500da102c1860301152a14242c4900d1290512141d01e0301d00403000c00c0040030074011010300c9400b003040510707242d88071500201e00807103080380403414650410881e0b50f0b40780520a945003008064000c80105160f03100081e290250003101801010b10040d40c1850f0b12000d00400350240003400038501d80b402c4c10700c2d800d50b940724981a0501c0703181402c02040304c5440038500c040d10940c03000545d8031000c1d00e1081d280144d1b43e41c00a04580180300e68402000f40a8007e003155034003c89d9a0030104002c841045070301e2082d104031692002d52280c0030040880244c80f0160f00150752038002c3d04041d40c0f9101c640e03003a80041101c3c822000c0381701d0400300c01c2007076100f0310001e00001c0c1d40e40da0456051100c03001c08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 63374355 1250 63373105 63373117
    0x7031a010503070e06160605010509040f1104020405090f04020307060e011209080f12010e0a0203070c11040b1302041703040503030706181a07030b010807020c01080402030a061401080f03070206 85
    0x1001000030020f207002c0d0043c120012145000780c00265a0a42c604130554041c2c02c051040b91024107240000541f41351504195004940218507842071b101d55550303d07200444801ca440307030056002d200000f034664409400c5445121050541c0c80149490f10403d41040c0003908120700380030700201c00510a0b40c0c4401550700c201c03042d83c00060714050714140f01c0d190f0300492010071000c2d140003400c600c4d44541000032604030b698101c110982500d485507000183d0104440490000f02107905000c0405d007140755604400c44040c100003640d00d5064085685102a082070b00540c50f0005003c00041d04a801d00f8444801072001940c1014101b2000984a12450a01500d03090f21b03101b04c0d8881c2a00689080030702580310303003281d249540c4015402441041100c840740400c0c6043c00040d4254010010075104d10100da0180820312041001510084400b4106076007500c204a8440c0001e03203107110788036159003c05055511503252088103480c0900c00413003501690401d00107400162110016100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 63375605 1250 63374355 63374357
    0x50403020f19020f12030f0a020d0507032c0307120201080a1a01050304110406090905061501080612010f0509010b031b0a0e09010f06090e10050103080403020d0503070606060206060907031a01 84
    0x4c00d02071581c00218021801080301010b4003000030502100500c07000100300c0000719409031620081c2103e001d942034002c070071018000c10600c0000260009520b80150800107102c3c04040b010412640400c1c640612500319203081c452500c3c11005660b00504015400704030f1714001e004c000c081a50401c090040080050305100000c4040350070802540080200d00801500400c912680c0300030384405044c4909042c1c916001b0000442c20381c000400c01101300980c1a100e10045403240000d021344c0d010841c140005a543c0c3e042d405407203090714082c0c2c80c00340190300f0020172030944c05000c00d8100b1440c0c5541c03d14005548440b0101a11030900c0c42044030000100c0b9040380d91080c4040f40503040408c0c44000740c51421a0100d1344e005a644904640c034109011262000c081c1803070381d4121002800043c05805c8244000c00042c42c1071100740c120a4415401e0f2420151a90b4490302a986241c1007800075801120030400346060080c25079070701000600d800d100c9405000c10b02c403440b003154000740e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 63376855 1250 63375605 63375619
    0x705010c051c0503040303060b120c0a05040807030809030111030708040b100506070c0e06060c100b010e06040e09120a0c060914070303030f1109090a091a0a050403020f1902 76
    0x828858288550b150207040406070841540301d0701e0000705140d00480c3c084012900d04030020401821103000c2d034200b1003c00c1c1c00c2c86600e445151507154150416107001c41000403c100204900500784000801580300f8204551a0740030601094291000d10021100c0e2010503c10042c2865220fa00541c026400c0062201c003038545607607030034440c0d90940085802410004000c020012359403003c00807249061810060f40d00c83c1009c00c403552068500203441c0d6800204480c002c80314582c044607a8600504008a50285000200d044c90308a0b91003009600408000c101c03903e10103205540741030551281c400c0c504003040704040e0103280c04690290030269502010700402c0020b00300d01c0c8000801c0c2d0100c901680c5c0d130340340c000c0c054000130b081040d0050414144644e2800c0e4a07059030310f1034400410100c0c49607605044103000706512071040d2044d40078481c084000d01034a442090141801c041c01090030301d810f040107498248c1441350000c45a001c0e04407441c0c2c041c0d402c620110700a604880d0b003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 63378105 1250 63376855 63376877
    0xf120405010908180301150506070b0a140103030203070303050c070321111c1407050a1206051008040b070c02060a0c060e0708010903080c040b030106030209030f060a0f0608010e070501 81
    0x4540100742c0208000d1180400150240301d51010001c030910408084009104041c0c0c1e581c812041c80000348180e5400c18414000303e40020b01c201105079200e000104005150a041d01e40000301010a038825400b507000000c040702419814003901c3da020681c010391030705c0e21056940003440c005484c0c4c610990b0b1000003181541012490f0040030ba81e600c0f401c0e4654aa1001551102d8902d05000b51844440e1030070f00545011070250842e01d1003005903865160070442180c9061710000d15200600400d141d036414049401d6442c2402940d29050b16038070b88209150615044070070644c00b4011100307100800002100694580044481c43e241e00d24202c0f01c881c400b440c2c040d01401580400c1d440703600400134042100380055104000301c030301036510040395441d03203a61100c4602c05d80c040c0c0f01ba500381c1000140006806500204040d04000d41103031000001c40c0ba0090070b00c40252009021961a4078000c00d03c0c44d000c2c000d00b405043c002008012450408801541d6541035101e5241400039003295 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 63379355 1250 63378105 63378113
    0xd030b01020f060a0605030120161e1a132a0302090406050411010f020604030e0d080a12050106020c0105040509180601060c1a010e060d05120f0408120f1204 69
    0xc030158420401c800c5070007031308000c0e004c403003d0056802031354001e40c0307040c0340708001c6481e190100d505038000b40c10ba2450005496245031841c0c001000681c2c482c0000c20703000e03803070264644425114070700850356240400d10703860070704880c0007000d898085145038490000b008599000c01024441d4183c1c420100c070948103526284440005603c01b2754045410000c20060151a401103845284950060038104aa043c015900e01948030510030040c2c1c404030000700024000d03040c0c2a02c1405c001e0104e001c07402299a480d00c07551140b00c1c8800003900501d8050f40c40c05c0e07035000362800b600343c500160506010000000388940580d1003160300c11030070440820b0780c402041006503180d581502c01c0d100d07190303160040a00301c502404001ca42580781403d42d01d0b4030285840185040e566091640c1d0155260300f410018001a80e010aa5250050300803003d070718140306006140914503c0034aa032510714040140f0308000313540c1142c05030740208004901d0342400314011121000c0031802d0041d082e85032030030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 63380605 1250 63379355 63379363
    0x1050d0b16021606021005090105010303050d0903020309040905030d0e0c0d0b0a020702100f0215130f02120f010606090905072102040906140906040b030304090f0e0a03050306100905030d030b0102 86
    0x80d0f0030071841c1001c000401d5407540401c0b29200d120001c60180000c0c2c4403550481d080703800900c00940000c00a01c0300028060700f0f07400a0b0a043d002e84101d0781001001c40005085840380d610071102c40d0b00c00118034070600f240c5e000340d4005860b81c0e40a0005a204040802e03a0803d91100c01051141c0c00000190b1400b6980c1c19600519005407012440301d84164014002c203e00ba404a07002d8801d0b0604003040c860140e0005100e03008600340c481d90f0510030350b1201c010030b410380c201b01d034041084943c8086801c0c0c10444024008508000414603600d4000040c0515519410403142d43c0d04003000c000c1d003240c012503400c843c20703000f01c03110b8030a07642c9000c400b0081c02640c004144250401c01c001030056101c28583d14a5a000c9514034216210803040004440c1903210a41e00750304184400c001c01000b070b0f40401d0300d030744120102240c0340300010704003405e2401d001003c40c08a02c020091003140d0070021002c145000d0641064a4410305000004c0c0e81c44810b03c412400301354071002341c140980d1080c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 63381855 1250 63380605 63380623
    0x902041401030302010e1002070807080c010902150d060801020c0d0e130504050d0e010c0201090b030a02070203120406030b030d02070506070c031202071703090609270f060901050d0b1602 82
    0x5a040c181540c40c0e01e0300074080c05500d006442a889000885040b0180700d100b143ca003190b100000d1403408c10316070307561041e6810420110807176540e0741010700050b0b15070707028007050700701c1110791321341d45507080182e274000ca4165400c200c03881c0e032051003110080c0c84002024075100d031480c10058401071384180062508824000383c04081c0b410309050004000d4001681c01c039108242e141c0c4c101000d9101c0046405515080300a03000820b003000412951003034400441e0085455880580340c05416004289005c1d91800e1002503a03400280402016a05100c3da004c020000c5026043d0300008040003503482c901801780134807034500090715404011409450800031680300682e040d042d0b40c2c610000c0c1d00c501c582e124a801182c08a86a0b2030346000c00b02c00c44101400042c4440d042503c00000c0c4144c540c0030042da401800400e4182074121280d805c0003078810741050442811320303c1d2040500c140040b069102c0e80c0200d0034403545d00c0000710080000c96202c000d09001e0035121540880880c5828820 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 63383105 1250 63381855 63381881
    0x10204081009030e06030609070e06210f010909020a030803061f0f02100e030a0c11030f0607030e0703170c0a02090903040503160509040311150c0405031603030210090204 75
    0x101c9054152201035400881100d4000c1c0c0702d2031210b401c44c5085c00450b01c42103540c55401000800014000b0f07000c0d800c0c03c40310600181c629420001c00031101d0a9104401140c0f074484c0c1c00c10070810403600080011030740584010f881c18450340c0c2c040ea0102c0e10b18035180c000140208008070001d40745464503c1b0200c130490000c09140340e49405214050082c2c00c01501c030f04014041c140f16801c40710458010383d04445140300c02113161118454086a4040020400f2103070b09540d08100c020300c0d54100141e01b0300160000243c04581460040a82201d0300103401c141c2c91341010b0300400100b11103040032400000282c1c051a5600c4040514500742041e01d18000d6100f40f9207024080d04250010107030040c0d03607082c0c3c00c85a0030300d01050103986640d450301c03138250300c00d0700c000000380001c0c4601245125210a01e0072500c01c07440c10b603a015000001207681c44000751001c07404018501c3d08012912420000f840a61038060964034000d445030790303c0c0741c52520141c0360440c01045445035404040140a5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 63384355 1250 63383105 63383113
    0xa0219080301090506090702061506040306021b06160804060902011e03020901022b111002030108011a040b0904031803020a15030c0206090a06150b0712090602010c05090f0301020408 80
    0x8545000c0660790070070300504845070328120010340071b41400000580200d01c01e400500090392004040700e607a0444488841e00480180070000008941e80068559241d1072840d40810f001e090701e0143c81c221004280e21a400d00030101001d0968001c11519000340d0480340c0800d80c0034081c0016101201c034411a581110000c00c42c148030750780c5c907601400311820240d00f6201242940000c1d81e49081210650041080c84922102401070141d58001d0940d80c1c070a090350100c1c00900030b103c080703801c2607000400c03a94680c03440f40030914050032a103a100504071401c020075a0210007061440300d0040008013032103021000030b2800c0d0950907521000b950300508100e4010f884649440728054841003003000300b400c060040041c0d07400800c2c2180304e114940010718000e8041d864400c080c00619140c4420700c21038030408102040e40500034541580500c1d14003002850f0400018080c0940703500541c11079162180e480315481c0e04c6412130305055400c8415681c00350422000034021320032581300b0042885 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 63385605 1250 63384355 63384403
    0x1060e034c06030c090b0307090506010c0519050d03090b060f010905040204032307030b0f10030606171002040605160c050301020714010c0e150a11070b0705010b060c030702060a02 79
    0x101c03540003a0306480c441c410452210b591a04841c09032800d5141031a0b150300420001c3c40745d00c80b198003680d40040c05152042c00040c0c0c58a03480d092203015414401c00d03001030864401400010840902d499400749000c0060803c20340761100c100038098a090312031b15142e517401c4042c1c0c2c89980464041c0500401c00c6541d0383d070307030b00d04594026881081c1c1c407140c441069a411949601117150412641c000003006800c0c0d80780b40611980040c001c22494603180b0744c100101c04151030344074010140514141d1500a40c24240d04689401c5041d01d600d044140104414005254400f003076030401c4000c0c1c034940d46060107038a4074044c8140180c020360382640c0b01040340001e00029021340265000d0b084020080405024812980d00c1c01c92000290001c0c6100d0200000b2034004001f0004942d452808541c1d0b0754403c4907290030400c031503105000c0c1e40004241c8000340f202c2031040d40c0c1c03200802c5980610303100e540403034141c490003000c5001c0c0c864140854400a130f00e000303004403803050180513005101c0d44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 63386855 1250 63385605 63385753
    0x403020c1512010812070b0a02040e010605040306050f0103050c10050f0307030c170606030105091807080c0f09010e0a09210203070605060907140903010b04050f01060e03 75
    0x6084400d5041102d00460000144118081388000c5800c8102c3d080c5490181c01c0d07112102c6c1c403076019100b06181c0f40d0801000503011105074440e03019229950300c00b82d40c0e038603508081003a904083c21008924801d0401040005c9001a081c1d074140740c195140d02212059010694a0340500007450340d1b0b201e030000810500b00da01d41e00c046a00c00e11900c518100c0c80444151500400084131103d41112017040180800d02c1d00340c0742507a10404580281c1c0602e1001e615850070000c403076019640310f0740038840703040d06403801045050640302c0c140c4100384550316015851003a104090420b550749036548000c0c000303002e10311100e4040546001024842c24081c10f40003562540940d0701562200d281001194486c64500c180c507010b210325907924004170880b035400345a6640a00f14043d03040d9a5803644031072684071401550712511540e80092110b41c540000540300f80078030311007540320342c0100204568007122110b40380c640d4403510040705c01000c6002c0764010a42d080b501c10403a40341400481050300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 63388105 1250 63386855 63386857
    0xa0e0102120108060c030403081f0503100603140a0b1501030204050306090604030305070e010e042a0503060a0e01030203062a28020304050622050d050d020f03030c04030b0403020c15 80
    0x2900200204c0f6416500c050080800d400241c1c1c3c000c0016080e540030076004104090790800060628060b140c04a0782c13100002e1412400001643c1c2c02a19400100240f10107110841c0f0013014100103401107510a544a03011034034000c1191200044001003812544d22070350603034000c0c01015040750194240911266900c000844003140028200000200318900c1072080403071644041e115208014002010403020303005205000c11200060f0001c80004141cad5807858800742c0c45604c585950381400b0007400300d134518540000d40016507490040005840000d909540542003054004135690000c072402e070400003089840080b210b01041c61402d0749000700241c501d1201c1c0c10a001401000e8100a1383c40e40264464242d03c2001403107010400301007100c43c180780030440b41401189030740751800101b0608540c00103031201d620031052100307020340400c4038101d8101c2100081d401d528069a5801c440e200d1404018200041000807604150080004d07044000008120000c0c0781000600700c241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 63389355 1250 63388105 63388109
    0x50a0609021c0b0f0a15030906060b04060e0906010503040f060b0406090b04140603060105011107090504051c0503010b0301050f03150c0a020c01080910020906041208190509180a0e01021201 83
    0x2e8030302c3d0001c440c03030a2810b03c0b110441d181c40545014412494003902846a00f03841c1d44100c1419140c1c1d040d0300001300140301c0d1502420205801c19100c03030810400030106000b0b84803290250a02c40d0601001340e81140903603510a500c01542c41d40e140403403400c2d030301502c4108412074000b4241440400d090611381c00040310580c09032010083d200c3c010780d840702c04800030340701d294043e040035005100c207510849120340e410107408215404640d4a0504008442d811201901c01ea003140381c43c00b103121041041c12101c600343e031a105041d0b50520201089074881072007243c1c490214482e0300440358400748819040484100300c007141c2407074041c003040080d40c02490f10000500400e410395990358040e0040c030703000d400c050380240b40750960b4000d500b000703601c5910200e902004c28000006c25000045260400c144281070b140d84030f4500a04d21400340f80c8010f22501130003c240500007440d00d03035210007819641e000d4040112a03c40d162058004d085c080d210705c500703500004100a0118161074a541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 63390605 1250 63389355 63389407
    0xc030305060402030402090a05090a0c0b031f060219170d0f1112060d02010c02030706090e06100e010c0303020f180a1d131b0306200c10050a060902 65
    0x440d0781da860082000300d00c4100d6009500100700f6011460310b0300c0c1a13224a82c4114410700300c40740806c40751510000c440c001c0d400381c81c0c0007000004000c030a4050f20b20081040092050314081e681c10200f000c0d45419640ca02c0d0341d0191005c940340b1040c0000581241610280c907245c00303030743d511300000d59000f0703107030004403001e0407410f005d5564400d075056011100302c81c1440310448034540f2540200046100500b038240c1c104644a400080541c5c1c0500001c40203048a407075440c502031411241002c0444024407440c1b2408145656140b036903009000c0071364040c3d0034600500502040d01d000e4000b8051080d0030075a00070007140c0450820340c090b02c070341c01ca1001252918242591210000e44a20301d04640c4207400e0402070200d00040c20611411508078422002191080b0b00e000441003c448203601c10381e440d40c3ca8045c0d681c500050a03140d0010150904003003440c0482000d4880c0d6107046000101000568840004000110a5100c1c0e009404e490000355552080020103850404900764544 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 63391855 1250 63390605 63390611
    0x110109170c0a0b090a0501050c010b210c010e0d0b040c0801050901060504060f03020a0b0f0915070b070908071701020702040c0302090102070b090a0501080402030c030601090e0f0f0303011a040305030a0c0303 91
    0x3c0b072122110025039090280041035100300074245401103070180c00c0f51000442e40e6403180d074140c030765a642c4030320601d81d2140180700150245610f00306d40e1502d00305903400307418001c000340c0700d01c0c1544a00801808190300448441c0c3c142c0c4072458060b000170f6980d0322481c841e5280c202031014041d010b402000c211481101c0512100340c983c0320441411141c1d1000a60280000100300640980b00001d04105115011b505041400303180c081000d82100d0032420250b07074070005103281006001480d903900120180362514a0b2800e25002d29550000c900451340c0c00390b00701c8813800038080c0c2501100e141c0c540c003030000c2c8418040c1480c007901940105000070b026000c2c8910104403d20b1500c01c2d14194040141101d00c0149010700554003890060010ba800d03000d80c20760038003a91003c00c0b480d4000c0c0105000010441c4111403030314100100c0301812005d5421031220341a41000020989054514600d040b00c0754181c5954403281c944213941c4024514003000c9000c1001d960400c405914440c001d840c28 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 63393105 1250 63391855 63391859
    0xb010803030115020c060301030f0206041d0414010e0607082701090519030903030f0c0602181c110415080a0605060418020319060b04060b0306120604020d110109170c0a 74
    0x84e80c56102800304150441018001003000c18110300350070000500140800d0300d040e89810300d1090f808240f26060b98040810001e200c10400d200340142c0190400f40000c106c21408070b500741c2e88984014000d0740030004a100440d43d00c40020652180a06038a44183c413004019180d10340603214440d402d64150003201e02d03e600420304280c40040706a8036641c0c50500d0341c110707501940c10307002c0c200c05101044410810100010340910040030f48601820f44032111804d01c0b010000d03400500d00031115590180c0320024000340c032030756005c0070009013243c001c107034201d1645080c44022542e40c410300e01e900c200e40e4140e05004142e4840c5010b220140c80c1071186001c0c101d814500341590040094040c1d001c40c82205c0903556125050700350302e00c1040f002c15803038250400142901c0702c68120700790340384000040c8041c40c64080a20711110718140054562850590000b900c9070700e2400024050b00d11b42c44038121540c0c480e20a8501800b0040703040a411010901010381d6000303008590b60050800440c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 63394355 1250 63393105 63393107
    0xd061d0f0910020a030b220507020c130b0612070810050f10080a0b0a080705030613050a0209090f010c03050103110301060b0a030b0301090501020a020c13050103030903060b0d0b010803030115 84
    0x18039841080aa002080da080001003140c00035071207810402c0426543e211a00d0f115500c18070220903a0b10100714030080d8038250075210b030880304003620b080300b0f5601843c0c0c4030038551038080101400013059074000400301d40b40ca003c5082d62003907000e00a4140b411008010016130401150344c002c069400304181e407140c031803050020f250050303620700c0da20501c0c50b90501c5115204882c2e040d8081d0700024085003001000c03010807182d001c40c0c1c10081c9207401c407010a00c41d13070400700f02140c0d02040e4000032410b812100c0d10780a80b0742c0306044c0082d004021180002e580098100201880352042304001c0107071200904000b00244001e000c100e07040090542d10541626050251005417004803120714901030268005500800c802000036407d5501d40e0b407941c011520a10140452000d01d40180001442d5030040102c41041d0340740180c141882e0100500100381e0281e0f000c82500c0c0d0100c40041c29050081c006500d5004030030000b400d0510000001c40e05110200181d0304862a01c0d40802c0b400c911854 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 63395605 1250 63394355 63394381
    0x1210060507150207020d02031507120203100603020a0c0b0405030405090106021b190503010504050607080601020318010e0a0918051009050c090a02040b0a020102070314030f0f0c0d061d 81
    0x3030070b468140004122404074a5005280320f40c802003d80d01c0800681d0f000c03a05041110412800020321041041401c40e007041c1100c40b604100c407421891494005c4605000201b54003030711003050760205244901c40d0144e1080c0314000c4d007003000305036031746400d1400c42d640380c0c032501549000300010000020042e000050344d0001e900081c00404441440030705110110703d03a1316405c03403100c0402d40001400d49080c4200b500450081c406001a8170b0100c0015081d400e014208a04540c070070040559014400451140d4030700c42403a04c110300d0350907103000882081d640d13004914540d1920621200040c89600b0502c50203204906454030307440f500c1c85500840300007480140840c0c101d5024614903151401d0900e42c082810f450050502e51660007160b400c0e0044140240503030350001d0400d0615401c03003007603890004805001d0780313140b5000350924040800036103007130a48000c40700401c050075503070420395202e00f244850400c2030036620243c8243c0101c2d004e4030071000700c0b588000301d03643c0ca024075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 63396855 1250 63395605 63395617
    0x80d0e06040b160309170c0f01050406050703110a230606040b030c0f0607060c0801060207240503040302010912030603060f06080307080c0a0606171005010f060509031212100605 78
    0x1041c01c9040252407028210920f9150700118204809020081040d140071100d008901e00103000502c140d50100c2c00340500d480700701e48642c0c103010b8203201c1081043c1e4804104c0318a5989171074014083d10f0200001e0b884d0284208000f00002001440c1062000c400100409464080c81c102d0b0900c1d212802800f040390b90882c00305805402c004c503a0404e5007041c182100013440d020717054603d09640380c1c4400d011506100380550001d5222001001507a6040000034080c18040304105112441c0c0d0f01c0c065083c09091a6803424000040001410b00d4002e50088103043c2d004207490044a9031403c00400030f103c0c1d8001186c0e198034000b0f201107906107611441056403d00402035180c100c0c2c648402220360040c4986464030712944041c54005402c0d405020f00600c2c0e02e4a01c0f850f11a1130744d0540d0300307100f40700301c001c101c852410004011040152025030100e5070300d4203100f5038489002c0007280c140380fa4603040680040001945100c418120800b20b44204111440302e01c0341603d40b441180e0f244201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 63398105 1250 63396855 63396869
    0x305190e0d030207020d06060b0a08161b0f0210091701090b0103030509060d0903030902040c020a020d03080c04170706030e03071703151c050106050a0609030f08040807080d0e0604 79
    0x40755445040340280d000b029468002017801103510b0301991420244d90391900054641400441d000194540141364181c021481303098105600444000080041c0359030410310074240c00711035010050200c00d10829000b00d4020b400b0700c860307111814000d442c1080070320668a580486003c0c0041046040c803c0c0d255513940075005070080e9185440458030b035003100040c140d100100300700980081003a8030503600524400e4601007081120340c010441160621a038660954105543c1c48006903140c091000398035a05040080041d2220720781c40c0514000c0d5000070030003000344d00c003806051000203201c01c1280c0316a0341c00c0c050050225440c039200c0c010310500501d0400c1400c46081e400d04008080d540c010011014896200031480003d5001300c1e000c007040d10340e9440b10b4201c0c01400002c1c080c550142c84140c0d0208603003841e010004000e045c10f4880500032000c0c82d440c032020401d2200440b80101000e00407104102e0700da05d1419111404000e50030080380390149681c502d410128141c40460f604 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 63399355 1250 63398105 63398113
    0x7030503010e10180b01030c05070203461202030703140a021005010b18040203090c1e0a031209060206060d1e05060717151f0314070305190e 62
    0x80c0240b00a41010042d001c000000c12040000c10740c030b5561241510b00d160920408500200e1800024003210001d40c001010010104400340141e01c0c002011041d200b1400405a10b0000350380341040c4046480ca0343c00d00ca80003104400c21002d40b2a0183c9200d1801000f0340882240103a0040e0b84d2803041920080104410324481c005c0c1400042c082c0035240b88900540d90b42c41000c0c0110340455000360800214070f4804502000c082c006c0c00304000c40340e48165011440c5003426000e195071401100600e0748103880d50b05031034079000c40340400c4250b24000980214406501d03417a08403036501001c205140040d05124000981502c0010880d0082c0c40c003526100c00f1649030703140da841d481d0065048521043c2d00540800003e081042240e2140c106a0303117209030410a03018500142001814030541f04c030000505050b079507610381031300b5255805040014000c0c0341d0408281c001d00003074a6401e20300d01128040100c200c5d0580c001a105002500ca0107141103400c0d4018002c07120b0110000c1e002b0740c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 63400605 1250 63399355 63399359
    0x905010e060f010f050f040e090105060301060308090f060c071d10030c14042306120304030210030e100e01020703080f0f0106030c050c01051008060f040807020603060a1805010501140703050301 85
    0x409104d55029030065440d125150040c80345540d603103031b402a0b200240603090b02040000303d56081c840d86400410450003841002e04d103489540b498016641e049100d03c40f1824030101d507585000440f03030800300c0501038a580c20382da68006001921103d0700c802c1191564000035028900804500081d02d910515104903e41012041c14031801078000c0b594000e591840d03002c8c0405030b030350740d9a4000300e8400c502c0200c07442c052040c0320035081c2c030080a8a04c0d52080c0f0007800144e9032114802c40c0b200c03440c0ba000494060441c00c0c0381c03419041e0110310940a1806010a031b00c0e00064005003499806074039031100e1034950441c20003001d079080300c100160041040041c0b0985110f0341102103460124640300c0e05002090340c289084460640b40f8603844204078500b0881c130f0300d05000e0180d200c40e809039480460b1074030307032a40c040764494140028812203000000074079a40d118107140c1c010b0002da0880c04030b495400c2c00140020102800f03400d0204111007891b0491200303400441d036240341d00d41d03607031802d5034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 63401855 1250 63400605 63400607
    0x1d060f060909061302150d05011403010207081803150403021005010f06020d030b0a051e13020f0708090d060f050406060506030603190203120a05070c1e0b0703020109020603100905010e060f01 84
    0x2404c40340e8126444200b40c044c14414155410241454203100303c800140c651400c1c1c40750850a00c0b01e0300283c0607034014090030000c207007404141c5901e0812400445c594031100070003c1d00f0302071200b031001c0103400d0359014081859400102c564013540010800c01140e40c0b41c20708981e101c4014421800183e03c00054080014860b0b042034044e07880140c001980f05450700c000400f00c0e28003506110310306080c12903039441450003455510b09000390700b40c214507000059014440c1c03485000c001404070100040c0302c0b052501c582c20175020301500310b2410880c009031380c3d0780c030005003409590070390701182420404030342c1d841c0040c21680210b00050043c0600404414407003601c04920700b0503a41405206000c0303109052a10042500c3d841070790b1074903642c1109281c0b8801603002500070b1001000740a0350000160b64595158060b1350180d036049484003ca40741c124058100321400a40003031001c014440c68510b031611480030341d44281e00c284401da0300c8904801560701e04658040d8420044d424a10141d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 63403105 1250 63401855 63401881
    0x30b0a050103090f05061608100501080705031003080f07031706010509040b0a0810090201020d0305010609050d050f01092301180b0408040b0309031b0606030715031d060f06090906 79
    0x107612961600150100e40c3e1074107401c024045407c06400c0c4100d5a07080c0d0b0159108040e29845000b60040c603910a050400081561000501d0750060210010200705412040c2c0000380086500c001d40b81d0780e9a111543d0308001e40c002040071404559032061100861128040030f40c07291106035592400d2851210800001e8014040610b801440030080810b072440144050784044074201c8010a500000c4e100083c03a05449002c000101480c010050058036805081c900032902c040f106001c84000c80c0c10aa0309001108031400b00c55071031b06015204000b40b80107440645c511502601480e0010740700800d0980b96541503003a02c0c40f60803480200050b0100108607003160195050f1800e01751150452150342d4003d40340d4410a60011840b14454a00800030044440411000d491103007000310100b80d48410b1070041010b4040d2085642203030600c60b60158007071200000d0141c202c504625030654031080113950114070b80483c0f4001805504040500900440621008010540d0340c000c0c04014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 63404355 1250 63403105 63403121
    0x11d01081f0f0b0a0f0608010803040f0905060406121a010b04081207050304030b190f02120a2703080f011a0403030e15040e070906030b030d0311090d051c030b0a050103 74
    0x151981d07a00120f00700c0d444400c03060300a404002483d0b15204c0c00c119014284040503840b201e03241d4820482801000001e00071601100e103851004034150300c410000030040c1071107400003d14100c00c104001c05120703071001410380400c00344001020301e9898409403070040c0320714040c0710030a0740020107203c40b02104e030f0010310a00d4058404e43e81446d07281d54550110180a94911180314880856010748080300d1050941c7d81001e940c0071440c203c103555041030641c0009000300640ca40d100c01c2c1c40d0425000800f4400503429501040c061f462240c0740180c00042c098441c180f800749150004184001079104040301c00006564417405c06196079400c0310304056403440250030085608040d91104102400340c000340103130214250b01d1f850304000c01000d00c44668003280070035003030441240c426200410107920510051030f02050707044401c00b000486100e0800c42c5c50704400318000210a00c03c0104a803c0200c96230504200c0e10b11030700600b202030345d11607079005a1100302c8610070040c6600980c86080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 63405605 1250 63404355 63404381
    0x6020a1103010905070e15010503070905041e0c111b03070e07140f0d0b01080c040b070c030812090f0606090c0a0c1b060f0311090103020c15011d01081f 67
    0x114900356030345080c2091441c1d0300c65040c1b80d00320b400388189005001e48111444c0001e103003850941c900840028103c0016200e142d001c2c170f5894004c050384030740350b0f455200d54508150742842901d5006100602500742c4100c546c0440c001c00e030305107802445c03542020ba21428010000c0c40310900704180400103a0001c2c2184080c01148819200b00050385405801d0000d41500000d0301d46504000702c000b910038085215040100b558100024080380c1000d50f400e41d001000110b84418841c80c0155004030f183d08007070408040440c514505189002d080c80c071442c802c405960071030348a200419940c04c81905c25580c005200c40018882c1c0740c181c0d014121013602890030043e001c0807500c400007070101d0301d215950242400d0409005e402d400c8511011070303012a180810416140a0a0034414010700410504140e000110b16100800c1000003004982032801d604c940755039a03d44c140d0070b4904a06a44004000d0705000040f00c81c00480d05080046184082e01f6043e980344450701d00030070a20740d0046c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 63406855 1250 63405605 63405611
    0x406033305090a1a060919060b1c0c0207061704030e0603070c0303050105030309010207030209070e0a080706020d0509181009020c070e090705030d030f060902030a0504061506020a110301 82
    0x51003202540165030080b549400a000280c1140c02d06010203a2141458040000340d0f40601c0f81c1d43e1100f2064507441590349524010030f0360010b1482000d40f03c2c80c0c0c4038101942d400b1414400c90491815508542c082e6141e0801075213080b00003c0e42ca0300501e00c101404205c0c000d80c90b40345031040351602903000d440b034500f10704043c041c6400161160402e03501c0b040052801c51001041581500c41c1c0b80c05000120000c3d8101880000000e68640c010f02001380030304240000700b01c056000b0f85130a40107100060640c0da4442d21414803a0f0b440ac480c0c8611130041c171494605154030f0717006100710b8102e104041d00200b800d428002c00c190074040d02820085c2d072507605000c00610041c46201410704a0320140243c40d10514000324076440c0d0201602041058105030b200704255070380060802c40a0707685090100340018008140002441298802c0b2995070000080000c44040d643c07120344074034071808041000fa40d00b0000390303844940070b006260150b8451140d103c0455586010a42c0a000080000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 63408105 1250 63406855 63406943
    0x4080405090103030c0209090715051b0d02160504060501080103082b02070303050603030c060121060c0c06051317160615060f020d0f030507030906050123040603 71
    0x1061071a042640141e000800704c909131011490560304054025684400800025003000c0102d84590315080d000b80500c1000526100342001042e4070081d61481c00c4252070070711000c18400707502c609401000300d043c840c1f9500c0101c2c29203803510804040d680180c0d1446100da00b10fa0315039a00c4da001d185c44040c1d5060382c030000f14a04201c05002180d107961000e001d0f88a50340c91030054180c440151115109401c00e100c1c4142d40b5030000380d52030466600422001403500060594400440c00c1000980028241703820102000e400586d6580011310411f030400c582c0c1d48071148000c180462410003840c4150410b415443c030200c4030f014108211005403240381c5403445603540021114108060b0150340b0041400704440394100019030030201c600d0024001080c880e007001000c1d03070010f0340040141139a44012866081c440c0d4001da540f02d500c80c0d0304101235611602c4602104105550f0200d52036483c01d8841c40b9400c050040c03070116644401c60303060b603030311020480c008800c0840458020ba503444000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 63409355 1250 63408105 63408109
    0xb0d020a0c0c03061d0309030a060b1206090102130605090a0608091207050c030705120601120f0822060302040503060a0207030c0827010e0102060411061c0509010c020613080304080405 81
    0x240c800a40c86034200044940655844001708141c00940017410342007030103041c1a40d1004500c1c4581135034803010000d400c2c210000001c10310724181941941c10710901c0104100c500c0154000c0112222611011059507a5044200c0d40b03403040c102e0240c1c00c1000390f0703410402d05e405403940541182c22241a1040c035403040e1020041030b0480101a1020380c40705c10f082480c1d0600740f11f040041d10064071200c10100e11100328035034960303042c030039000d03007070704c042d04d98010b00125416002a05501003410703079640c2d03581c00b40c03403004102c01c600140013050110b8000600c1406807084500312000030300600410384d00c8045004c006d400290b01582400a400c86100009002a0040c0182d070312500c240386281048002000d00c0cae805010495050021348154a01e05a1f000900282d0041c2d004916240c0c0c45000804110140503104801070341c003904e030406845042d40c941000b4494a00c2d013001300070720103240b001282da455003a00d040c48103191074040e080203d402c0030001d5a0040c0660146480c2c61360b5280 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 63410605 1250 63409355 63409373
    0x1081801090624060507170d09050c0a0e060112111303030f02070b070803060d05010b04050a090302100c080f070c020d200a030b070c0309150801081005010b0d020a0c 73
    0x30341190b1841c3d4420a0f10910400c1c1c6080010f0300c10240900c032101d60074164080c01d20701c503001025100c4554200710001d101c0070a02114102c44003108103000d42405840d1440d9200020103002d4030030310741d601c004079401031940003083c42481c05030744075040e03004007c844500802e00c803603003428021001c001c036001100c403148480000b180b10350b44d08a41c2d0305260314001d0400703025412403540c6680821403080400c580c00d003900c2d04110110340320a055046464420300403c1e100f82a960410f0800c410442d010001d90f01010b0224001c3d000d1300c404002c094074050445014a25403400704204c000030a6008408900650344840c0038101800f55010a40008080040c20b02d0219407441d44944c28580b01804140c0f070b2520300382c003510a04040c0b421580e61b42e034007003c004d103454108015200a0401d02d4070034001c2c0002815618510072000f0502140200000300901401520f480340c48031186a40781c1a1040504a0303502c280c810f4285261200c03004081d51003601110108403443e04e042000c680300c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 63411855 1250 63410605 63410621
    0x70c022d0d0317090105010303091a1605030307020c0108060307030f02011b0b071d01080103030305060f0406030501020304020405060d030e19030b15040b03030f030a09051603050102070302071a0901081801 90
    0x5181c1c0c00c1c51400b01d5607004041c43c4010034000c0f81d64100307030040001942150b0b510b1300382d0350300e8410100352007441580c0b42c8550044a00c0303075240442120015040c040e0100085008154907425904a146400c0043d288100155600398140c0e1080030f0030800b14030f141c4030401050384145480320000c082c0310103010706481d41e84000e0350f403c980c2c1c40c14020195003002d80a03201d8540313480920304940031500042e00d2190140301c05000e00d034039071700010415942c15901c0c00000800610030007440e070b200c2c24060b000307400445089009520f807a01080c01482c000c3c036555140d40e81a500c5045031000c910134003981141000064844c1000f6241c040b0026603240501489030124010344e800c11800701041209076020300040c54000e400420051480086040c1225401f112086020455504515146240c008042940b09010980c00404000c100041d0010000140660300300c907522602ea941c2d04c1e940082a00e03a954805000f0050307219254014602c1035403120300da42c0304080b40f01d007404945003551a80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 63413105 1250 63411855 63411857
    0x50a060b0c030a0f080402011205060402090a0b070606060e03070311130509060403080c0307050904090f05010203040503130503070b03060d1407062006100b0d0b0607060501050405070c022d0d03 85
    0xb142c0030305180d44c80000b40750b40c43d1040c64a060641455000030344500d044018045240c0e0710766000820301d443d2034041390800040a06030390815940c0d5030500c55203410031003045540a00700040017503224880c00c400010018000c0c06406907601e9079843e0211400d0f8107441503000b406e03ca51040c5c413544544100c500c15641c10028252600d042e18008000010003480c200c460001841032014082d4083c0540391030a0094800080300d42060030103c103902c184500042240d030002041000300007000c000340c481ca40d1070f03004d030101041d1100205500c0344d00358005c480d9524800d00c0002d90500c1c0030b03165410803900840b8201e10340c002d80c1101509042603600b00c400070946200e254501c0c18003085a240c0e20441c0c40b0040c01e01410203000740c0d400101c1510420200903001f00305036846c801e2990280404640042246940391501d140a1020309401d108041c40b4034a03100014003450b01410940030364940c01031a0a0400707014080c0c0902c0300740f92a0304400880d40d9108a200311707403510904900e40301d0123 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 63414355 1250 63413105 63413107
    0x9062d06111006030819180515040e040825050303040215130b04050f0405040b0403080408042706090911090a0f060308030603010507020d2c040510051002070612050a060b0c03 77
    0x140390012101098143c80c104200f00c10300c0e0147e84c21000141e00d400039180d08030385207420840b81c00d003040c1d401d0244c5d8102c9440c0d1a010301c1400200b040003030003040c0301040d0034040030301c0c00d448400c07807050b10301d041002802a810400002d401890700003072221100b8590200182800b0444101060886d8079030030040318824001000c2c00a80303003c0d801c1c40c0021000312800c0c00300e407805035a015492000030f0002824440110301003410402404240d4001d0a000d000c040d2401000c0020003229a4465188480042c035121010481041c54009c1000c616040640540c1148800c800c3c021074950061031409403507503031100a0141240c42c080c0c0c000960050544640700d00b0480308141c01c5072000b4190100390b50000340b070421131075005042c81861040705030a6420700c01400c085c0800512170002e15030f81c020310b00f808020740f07007000022000503107405807121026818200300c140c3e581e1085010300004a0982044503031460401d41000b540710100c84804507410340e65404c0600c0070f8115030b80608040d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 63415605 1250 63414355 63414367
    0xd0f03020f0a020f010f11070f061e060f0b0a02030a0e010e12030322020307060c0501090c030b04050f0c01051b070911071a04110d021909062d061110060308 69
    0x1409001d811806c0e0048034040100340201e0704007454034407441d00d00400c942d02051100e0b040c007080d40d01c08450b002035005c00c081030381180d11071a00101021700913040c03190036034000070401070342c4102580c03418051a001140740242c201000e41e007a40a00c0c491504010002d95016240d0310364900b42c0d0301c3c4840200083d0703181e0901d11500780c14042601d005891500d8582040000359600254084c200e820f0350400040c0804c07031f403d01901401000c00098449480d1010003c10090b1114449100e14005e03c196030171942d02c034183c29140c100e150721490000782d00780510940c1c240400d510000b02811402100e0304241da45c074080050702c0d0a06169541070750003080000a001e03050400c0f1807032042c0c4107596002032400ba0340307010300c01000407013881c0241c071465140d03400c6403281b0319040100c076010000300392001d544d841d0400c040c041d540150300044482441d0a1140880c00070020304849407a03050720002030408030f0480d070742007688600c5803030703889902c0324101c0d40ba000c2c0c403440d1301540c00340704825a900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 63416855 1250 63415605 63415633
    0x20405030708010b060a080411040c081e01050306061c060510030312020f0d02070206070512030a0e06010f0909080d0207030309020a061701140d020405130203011103090d0f03020f0a02 81
    0x1d41580445500e034100f0340d220a060359010119803010129082c0884107441e03034101030548242c010140c0350024070b004520880140c2120840740f16034203104007103d01d01500d0340040e59044081c03103002e0b0140c1c0003402141d020315000194902d0328510303c006c0901402651a124180c4905640d04580030880c2c040c180706044c0d000007624503000c118007003513241a00410341d180492007080710a003840d6501160240c2103581e564202c07080300b130300903045984d03801c869002001158010384020749640e1500744800101c000c08a54641203403081e60003450740314540029a009001c0403581103915103402c025114009600341b01406200f03029036000500c50343d451050050800c1990030407414420300c1002c8400348860710402d241592100007072800700f20340b002c0c04201c110000c0340e0020b42c030a0502c4108010110400f042d0003046000b04e00074410705800c10390325920742c401503808106540003200800b00c128017a692102440d03844e80780c014a060000a41030b8125004503c5080045c0c1080101000030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 63418105 1250 63416855 63416863
    0x7020309090f1e01030c05040941010e0c06030a06031a0405070f0b0304020f010201060504240e1b0313020603070206180106150c17120f090d05090915040f02040503 72
    0x902d2103e42075216550441c0c4407022046100d10480d445140c891070030800300a2714008903020106010b001010491800e040d00c4c42c11450300c54020326482c092802d500c203005050284c5007940350307075501600260302014140074055100410304003916803a039900000041f10280c141c820b0700d854002102c800c1c100791514030305040c020761056201c55000a820b101c0b4801040490340c22030382c11508c01c110710f0009001070340507084c294801c5502038907181d54405106544a0711503880764000c103986120644401001c081c0076025981c10540301403210040c4540d035607400007950401d01c003018011082010380d0010764247d100b1113001006802460511001c400204036100d900d4007800000d0100310b0401500c4840d00381151007240c10040e56044000034440c11725800c1c5810050a260940d0702c042202084a28000a5442040802518000540300200414504a001059920b03646414421070802070100d1028284642031691f00034110166520361060b8a002c90241402507201e0346003000f09410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 63419355 1250 63418105 63418141
    0x71503060e0705130b04080a030212070503040512030405040603120806040603030509150c010c030c080c090d0221100c02190803010e180a030221070f060507020309090f 74
    0x141410280c0901c11a0740c03501c0415407014251505039201d58291400e1610750704198407880d2003940008000c26461030104040341c0e414065000c661200c146002200f22070320643d0000351094000340400d100e5440d00281c181441428003040324200b030b88940004003101e40075481100c03e4a0074103451200c40750000c0c511a80710008403020408a45140ca0281642c85000c955900c01c5010103400c1103c51180000c0c4d0b18420141c4d0000c0040d100c220b0070290007450350280300300200380300c100061900000c16080f520380c8074001e0314030b42c80314040d5403d000c56110f83c80d04c4000c19003032025a010b0052005c01c102e85420540c544040b802003c0c58902a0074400750b50360b0000600309075216000407030851000c49046a016452403a1039170381d00007100320392080030308840b0003502903a400c00007030541c000b0342100305006c1c99520000c4884000302c1b1003428480d1920080c5442109103203d0003040d03196006607800f5444d401502e00e40a0a0300015540707403011210003203010410000d0000d0a06c25070340c5124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 63420605 1250 63419355 63419357
    0x20a02090a021305040c052a010e0d0905040f06050d0c050a0609080c060d0e100603060606050703020d031a2106010801050c03150303040b0c0606090601021606030902041d0715 77
    0x3c0342409090308660b5598040c0030f001e000d25101c000c0c00118034803900884140121400070300d40341480084140320010b01e000030725821b96080014100b80007401103001e00d0155401d0304c440314102d24250500000d4000d6420100f5007950303038480002c0e2074603512010f640143c4910341841542d41001c0c200458400150064000c020f441e90302030100541c0051948000760b8211801c1c0d4136041c500312204040c090704a8000b00700d0065208d008192150340e00b251095170b200780000d00c541d07612060101d800e4041c03c0005001640110152100c0718000d0344140c04040c54407007010102c98821020402c100001c2c0a82d410040c240110700610b00c4050040602400700b00d0000d100c03d09261082e072000b8040a041d42c18000400365801c122694204210350003450003080c0b89850700d4030446119105e29023114518050490100007138025803000c039240d201100441d2a00342c400c1d040007c101c1c010a40380c04100d0300142d0396141243d03056001141c05000045550080250710301b0400c2980141350f81c514884 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 63421855 1250 63420605 63420607
    0xd06080109052109060c030d06030503070302150f040209040606170a05070503070303050405150403050d200706081f05030a0501050108070e09060a05060303160b01082112060d080a020a02090a02 85
    0x4202100f1904030342400e5011a078003611002c11491280c214810903803082d0360705290010000400501001a0072a60f01070340995500d090b0644480b45102000c6525601409030703040002c005241800380780d1703001401380000117103154440014203413084490040403d00e40c030881c035400820000300b000d03002402c416405003102504d541e4000d0818052805054400d2a80034040c468048180e01a6801150001d040720f1380c01c1d6020602800c800c483c071030162090600124000784c4001700003421800c0311465924010340303588a0b03040400c1154580d08019101c0c8240c07800280b1550301704000d0400c50b020710000a150752501d010245000c445034456080c0b02078120400142c0800402c405611003078650011070b075540d41c00b0001c0c1c11407003603035036002003120060004024040e0700d01415060f03410550448050055080c01c400040c1144501d00c49418001c11400320000301422415800150103001d1114010455a03109441e400201070040181e00c240b52900a61a01d0520203400202d900411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 63423105 1250 63421855 63421903
    0xf0613020f0405010f0512010605090a080c010f0302090103090b01031208220204110f07120206060d021c2105030a110405031504140a0602030a0b03030327030d0608010905 75
    0x218038012481002c4c1030110020075100c0d498000c500315000503209411075070440d038484001405582103102c810b4081c0040780408158840009410441180c05843c0c0d95600f40060034200c3c0a980900512410103444003002400940110f07030403070103540320b03421022141d0000c03040101019001441f5102c40c0614103800040d1455002069004503010794002c030b41415862404160780c803400403869510007000a8400600420040010003250300340d081c0da44980398902008108003904801950102c4400c5d06500c081b20004c0c01041d116200b0b448416020109565070102c0e07041404401006c54400001c22180281c68451340076400031881060341841e041401090780c511012150000b000c0c25803010a080c8491460200010400d103011600d06184510f807240c007940003030b039100311094140f400d4064280707004401d40344600e01119000018a100d402c0c07100f10303150a507613100c200b8002041607140c030405900500d0003a245100000c240f00f80985011485e00c40c81002d0401c0c40e035a10205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 63424355 1250 63423105 63423127
    0x30a02030c150421090b0c01020901020d05041a030a1113080f030406051219020c0d030b06030103050d051e03010e01030b0f0403090605131701060e09010509060415140f061302 77
    0x121244c0c140166804148103030b074225090301d15410f1070304515210360000c0340707890101c20150000d10445e8402c1e0b007030310080c2080780030503140750080e0300410180514401031118081028000355a100007074a20106164008224800030b86e40200d0960102001081d0140035503034042044802c503404a000a5280034078111004056000d883c1c40740751000c50506c0495060f017614288814409800e140c110b58601d18040c0725603441c107191000001103414111022001c1ca4a5415213040340c0e0000040c0580ca0081d4030700300c40d1680f03c50700c2d015181d1000395014a00070f101e00040e6000e000d01c90740d040425411400d000300d150000030034403a05031411104010000b54085049401c480807401c00c551180c0c0c958111044500b003070740041420b50208071a0480c00c000542110007120032008541300f075512040c240500741d0b08210741c0080240e0280c0b01160001d02034010000c0c00200302d030070008004440785d200c41c1245100f940c0ca5252100d8a0043c400c20745082c0004c1d00040d42205400c610789185491 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 63425605 1250 63424355 63424373
    0x3030603020901120b060d03110f031305012c0a09060e0604050609060102070e06030c120304060809190209071202070b0702160602120d2c0c010305010302010c0f02060c030a02030c1504 81
    0x3130390081c01e600b480d07c010540610700c95400e5541c08001d640704c803020000059500d80200c602d502c0d80078104240000c1550199080c2c0800c1301013130680da1925200c0200f000c003003540c42003083d07030400140703180000d1981c150303c030707040107844a1a43c0e04000e08224003080f094841c081c0280c3d114900e503409200140c4e8001410340101c0c1c200c038070840c00c0c0c1d655100c00039040207034021025405c12601001c1c011503807404002442a28465207131451661a0381d00201d54a07540700000d000d00348882140300c4090303d800340140c0e6200c2070030f16080d0202d0500c002100c00b41c2e046448202d42c2035818200380308130b49405100d0640b024880341e0317142d030603180b40c440006d549804461a2001c1e41c40001590084000203422566a1240e519914040200511118040001d1078049080b542c00381c080d418a8562090060394102c03034050751140b2040201e1b40710700e4001c803888402240d008500300600654107800307002800381001710380c02454894070b03040b41990810710761403030903c4100e40d40410840010340c419 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 63426855 1250 63425605 63425611
    0xa0c020907031e020c070b0f0a11030409020412020306060415031e0209040302060f06100e0910030b0c2502031914010515010f0f080c0a020109060903030603020901120b 74
    0xc92004107030325640025402401504511a6040010000403d01500b650000c0c80c0400c400c00c21190020b50f40c1d0f040d2101030042d5100d0810700da0040100d41d00e4540310700c0c4224824820751090300d02e043d58074101d0004982c0b0603404620031828a03041c01040d8038050000b079605c017405841c14000400203080d07000310105e003408010b010b070300700480c502041c5180800111300c0d1980030342150302030700702401d0280d030310b8408840e600903050301c200000d6068204078000c4242a000c5031200e00b160139400c410400c2e001001800110694172001001000c83e0902c89001e0103221800c140301c4e0ba074100310000e50a01c4600c0d5540c00d50b40440b01440d40b005880c006101e031074040a980324410102042d2034240d441c03549214ac4103420f91b003400c080c404008062500c90400400c240c072241d004480a00040d0b80594005c000d460120322007900040081600e0001003c0d4420b251000044403006a40e80b501200c102d020140d002a90398181442141059420203026244038000d60407403200300e6440c0042a1070007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 63428105 1250 63426855 63426859
    0x30603021003090c0506030103141b010203041512050a020912010216020d140a050304090b01020a05060c1b01060b130609080d050f120f0703050709050306010b13050a090e060105060a0c02 82
    0x40c0b40701c03d06000070520600c0140100402440ea40d50392410608103103070200f00844094090090b5035601400340190468180106030095070400703143c54852656080040301d1001030200c407a00b040c82d080c85500c2622b210f0080003100588421840c2c0c02e020700c604003105407103c00d03881046810180c4c1c07814225250f826504980c44000c450951034503004500c2c014100507079a1240c0e400c01401c0213000300140058503c000c50410070b81a00100480e902e6400c40c1000c0c0640c0c003c50b010032545248040140341181540c1d054120f0003d00ca510036003151400d40c4a0382d181d08000c50344181c200748681c101c90050007140760400d1002c1c201741001c1c0d1190a0015004140304000401d00004107070742c02900c2c40d13440c101c91040264a001c0c118010880e03002c440440000c2d1400340010301c814010038514090b250040c00034070304e5a0138680307008c040740e0048036402e40340c01c080c10000800f070f61201e0100014162489012034110070108160b0314106068028520500302800403581d8240e01c082d104400e40c3e01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 63429355 1250 63428105 63428111
    0x50d210b0d02130504020301051014040b03030c0a030c0c05010c030807110a0b070309060b04020301060e010806041b02030c060c040b0304080912030a181401270518011401030603021003 81
    0x11a40000c030341c4480610300a400500484080440c00c195500251003603009400030711540c0d9031180c4580d613044840c000c60081410200003c44142480e41c0104003070840601101c0c50601103080d158035160340301c0c2c000c8001420107204201006034003c88140102401c1c203001c40d02c49a550350180c00c0c044024590404c12003900e02d0045140d10401c415504550000180d1800d420400d0000f4050181b074103094554a0a24402944504080c0b007264101c4141d642c8012603c2492401180c0c440e001400c05680107440c0c0328035071a4030701c0f0a5240500c40c0c00300e070021030b90b88a100c600c85041c1030b0020241011080d042c042080202c0100b41140d0348254400b10003560748000c400055494607484400d10000e100120b000e81d801a0050f015401c0311450001c1c0280301903540c00030b400e0111a0007602030004612452469491941580514150000303410201082d511100070420580441156031284003500d8010000d03c451340215001c42d18080c64140a641c2c02c1d5001728100008241c0280c00300341c2c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 63430605 1250 63429355 63429371
    0x50a02010c0809040f0606020609120405040b0103140903070b0c0405090402060318070f06020708120a0806030f15040201080109050411130b090406020705010c0801030309030b06130f0603050d21 85
    0x290b00216a08000014000c0120319403208940c0000d003446c1c000c400140c404c0310f01103481c000c0d0008000c0c401c55500ca041da440c25007000148000707400120406810706480b1200344481c0f051480010780300e8200480107645500c52400e0148140e0800341042170070307401c208400d02c400d403121640b040c0d1203501600c0c681e559455200204d550300c404554401c446015030480802e810314a02e0242085512540c22914410f480b0301b002a100c04031180411301e880404c112100880f809030f290319502c810000c05490801c401d8407280d41c18445851081e0b0304d11a0018100411503030050059800740803486020005883c1541c1c0701c01403ca040714219105200d68038412140b0b040a82054050b24805408011f203410b281c50481c001c0e4002410440c1d0950801c0103d0000501c561002d5040381d4140d618800b1091a5440e000411240a40ba680d00403259050740228001b4030701900b0404000c400c80011441e1031810524140203001822a0070801181e0290704d2100c04a8a0b00b14180004032002174220 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 63431855 1250 63430605 63430613
    0x1090c0509060c060103050c041401050f01031e02030a0f0209030604021912080306030d1b1e080f031b0c121b060705030901050a0603020d030804020409060e01020711030307050a02010c 81
    0x40a9110310729441080041d00380700d030101c007190b058100c0348182c048a000d00060000c0000344c440a0482d2801c0c0c0807110300401507840c141810301d44c01c07101810009004101c0d14003041c0207404010000c04c03099000000e010020b41c15125601c2d00842e03003a000c42c1054840320002c0d4542e500500040d100701d11420b1100102109541d8400080069450100c1d01e0400e52600c1281034104860681c0700e0b006015100180c5406840d00d5410308000f640080300d42c510a94500380c00700140704002119194440c8840000ba01c5d20f0003c00d855203000c4070035a00c9141940c0552140aa0a03074035119010701448000702c3c9460004a985c00d043c0c2c0c108105440c0c80e10504804102008514034208034480c1d030090102c3ca6800000450003080b081d03000f8080d680c3c54460740c00c256446840000d41000300c110b003603c0030903c180c2c070040d00584002e1000c103076042c19448100079240c0c1c03100d2040159500140c96004c11100754646c01c42c618080d8065418030340300b03031580c075101c050010300039040c0082031721918200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 63433105 1250 63431855 63431857
    0xa050105040b1b1009060b0a0303091a0c060f090c030c06090d02040f18050607030c0909110c01090c06020f0c15031b1c06170601090b030a06020d050708070c080301090c05 75
    0xf00c0c4141100e060007080c1c11400c010b400008000c4c0ca89515001001075982407144080095941507110052140c3c901813001580e101811212641c060050100c420300d100141b104d140502402c200d41145400d007503015a040c1170b03000301c5d494403a510070184400d4035181c08040d214050400c9941660201300f41c00494040e10507918000d018514000712240c4801241100030341c1035008034102d5aa580d12054150b0071a1611948a030101d8410081082012402d07000211444410000142412100031202e130a50f40380e810204c0b48000d4107501841816070400003203950100500041011403000f0f000710350051340d070681c00e0032080d000000040380045418404490f42d007240000d80e13030b02c10700d800d08140e40c507141c2d0070131138081030402d140001e10349a5240300c500031103201006017a40e40d18210380c00004000803071400d0b4043c01002c074842c01041c220710151961a81e885008030741d620300001300403ca00801844d4506015030a09048041941c0307070203603415104582c1000a262403154015551 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 63434355 1250 63433105 63433147
    0x51b100e0f030f100603030306150504030210030e0607020601090509012906090603071206050d050607111e100b0103021312020103022b0c050901050d0b0609040204030c0e060a050105040b 82
    0x45105641d15a035820340c00c0d0f4405c00440340203507020070010752240800e00c0002e02181e43c140000c0d0083c4411700161a1a185199107001c2c0340c103001500110020030f05042640c11a88940981c001500401100000d80104c542c002d20040c001c00c0590103010114104030745810441c011004500352504154403030104072000c040340140b1180e12443c0800703008000880703c000b1010300c241045400102810b11407c02c01c08160b1220191010799075590040b54403d000002e003003480e204807141e003003035060f046140c9042001800080c24941126901d074500b50b0740c240d5040e40c101841002408280440c494501050f00c940d48460f415410441c00105e01034001d500b2040c034a10071103c01008901c40c180040c0c01da807858004148200c1c000b824050328503000382e000990128a081004103960581d40d8480f0000e080b00409060800c070034403011408070317002500100c2e90104882c005000041d954005950301540c100c42c4420410b091000081450003144512003c1440125004040d030000c0300040c11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 63435605 1250 63434355 63434383
    0x1505101103040b041e060206040c03081303060f02091804120c03030213090c2c06072102010b01080903031b090105090d0302010b18010806072703051b100e0f03 70
    0x13072142d450311100080000d50801100034000503d40004810f8004510305104941040000303041d5441d548601e40254042c0d0700c0d181000102c500c010000038103d1040c9010744c41c00031700042c0c88130b2480701400f28009001c8548407402500d401000001074100702d0300400710b43d030761902ca1803070845403400394041e0045042101d101e1085a2020814100581c000343c030310074140c0e8903100e007180f101e40d844842d80c100300b88040d545290f9103500e00d16818140010040325100d00c1c0940d4044034900300311103541c01001400d00041c0d4484490802941c2c2c440a05ca03041031094025518508100440390311403d070000a03c806407502246072402c036801803050341d900001c00744c0154019440c510300280204104002c9600c01c803a00178107144a48110039002d07050390f040e0002441562620481a01c482c000c00d44403140c1c0180d0380c4031607860300f600c0a686100071407154004140c10151541d41c0058881d8001c1280c2c091800800b0301c2c10708941c84011010101016500700300d904080401003401c280000703c07540b03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 63436855 1250 63435605 63435607
    0x70c0203031e0d14130201030c0207090207060515010906080609220b070306080705061b03040b0c01050603060117100908041d0f0901020909040305180a0312031505101103040b 77
    0x1210601d00940105044035070782c0c3c1e08000715102c0740182c0d072094505403450400842c9401d00c907030040d4020391010783d2a21050040300c603800c0d41c40e00c1c140113a90050b03030211566170321303903041c064180d40414040d000b1950034289861140d003081c1d0010003544006215a105002c0e002c00b0550194001641c1d02d1180400f00c0036443c01c23080e41c02c1410040006030b4070540001d2a128000407e80408146d49068a0006013080d03c2c0005668001103c00c21002038001030b8003040000161010092004107003140007100042aa884c0450401d410a101607019807202402c44020044000011514042d8503000490020302120f460a240250b0700441d0450404190b0f1080421340c0344291504603441400000303821015980d600c15500c1c240c0c01990078031030f0800c4001c40070400207030040024011044a00703941c21202d90002d0300040882c086030384203a0380c0c5040701011411050f494040d042080006002c0440a00d14100125003c12a101401000c01000a0800a005000340102d03001400d20a81c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 63438105 1250 63436855 63436897
    0xe01050f130312021b01030506030309090405010608030301080706080702012706061701060e0c0c06010e09030f07080705151b09010c0b0406060e0709060206011716060801140d0b070c020303 83
    0x1070741d0f1724608810240d0078840c8800a60701507100307005142c451140903014605000c0100103005008201034001c071400d54031a8400b146612040000d18005c040513070042c0900ca03d401000380440d4006001074086904040811040f403880544c04410b105440c450a00c01d05054248540200310603009011403001300c50b803102d91098150443c07400d48916850a00c284d13100d280070790700144a456160b501d1034122800400401e80003000740c5500844c1c500030f0300d140650900110200703a1126604036009134010500c4001d000003000403141c0d101c4080415501418000c0f880510048400c0d1311283c0e02500160191150340320300c0c900400540c0c40400d00d1064113080ca000c10191090b4019842c952041c0c0c000290084d108011600444866401401c8180d090804909619003004040c007031314455880403d2012640c0d012810080c444c0f961050f40d02d505000480f4035400c660300b1014403c100d1600f104c1c4c0454214444160041194141007500d1889440828154054500114000107003400d45c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 63439355 1250 63438105 63438107
    0x90f0901031112030910081f03200103090213020c1603050102070204050c1305040b0d0b040302010b0102120702010e0607020a08060c0702040b090403020c24040609050a05010e01050f130312 83
    0x3100c100d00b4030485443e071000d40101101c66803030044d4000326034448010042c1d064503600810110360495500c81c0200710207400e5444a0700d90406a600c2215044c14140f50304407600c84142c1d5501c0302181c24030701030155100e160009601c807141074484195540c0e0000700b0000c203880821000c0071121030800704840d401d90702c1c03c00f00d000f50821039047e401982010009884291900c01315407403680c0d01c40085c0562400c00c030070700c0018070300009015041040d055484004c602240e144500c1988264000700b181070800c3c000a00304017200c0d00542c10070006100480040c0c3e04840e80d85055a420381d40d040d00d0708050700002d0500815644031b4859401040240700d542d000341001050311500a80d400c0c03000341d5243d81070000009007200c0250050b082150020403900d4940d0300791511034a554880030b0000410303480c90300b03254050b501c00c070302250340680300300068180354444200a1100b403c10007400660080007801c584244600304040034000075543c2c0440c0b03a804440c00c055900b212200d103c205032040c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 63440605 1250 63439355 63439373
    0x3020f010b0907080c07062306041401060203180301060b0406090906060c02100e0102010906050112020306011a0307080c04090c080105180403021009030210050408030f09030a05040605090f090103 86
    0x81419401d0280c50011030504919460054007240c3d42d08082d030f0f8541c56031099030f4210040c101c4140d91104004a011007841c80e052140040c0c0504d40b2489081c280b080004941200c802042d4900a04004000544d00401135031829a0074036801e8520024440c002801855550444002c400002c540440d0180c1d00103481800d548172010200b000c507455503408d60700311441000080d806211000d070010701034442c0c10205445081070001244000c1640d0301c0b502030b03c4090f04041c80c61071051071100190328040000a0051100e815500d20080c0740d00c41c00ca1013031000030858814060401c021520440b02101110000d0210740820410f105414000600095088c40703820f20a902841d0500d80d00b010458000307014540c140c0041030b01e030a485039506c0280a034403500341e0642c0981d00d030105022001c0c0c05681c2c4118452039007030360340e03140400854001540c06003144a5a510500141c0002034006045034191122814200c0d21480000c0005806a12050005401c01132050001040251040e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 63441855 1250 63440605 63440623
    0x207020423040c060c150c0c060e160617070804020307090203010e010504060b0a020a1101030908161a010303020703110d150e010c020a0b0109110403051b0a0504050601080a0e07050d0302 82
    0x502241d03000c0c0d62030f0011120040d07017101c09041c520001a107500007003a04d60065603c0da01c1418070004084554860004481c10f03d41e120700d07183c00002c894a07056070702d09520b10140c03000b41041505140d101800c298032a000a190307070103010aa40c040303019980c0800c68180100048102950341e0340e1194030740c01c100482840317414050b40c2492400300b0441200c1c000c2e08d410040d564001d24180b039640c0ca482c40c6440200b40c0c40750515030b0340c1b21003002169401b00200204800004440c0d0350b030040349410412840c80d55404201485180c006000080d408103004048980114450b407000c0d003540005401c081d5a400000d01050005040c0c40b9120850340000b224040d416000f0800440e4890007640c9903100c00c0742c001c101c0d9810343e00521100e11343c0e5211410800c5001031160800380c40b55156407506481e03400c0e00040c00c0b102102c100300c91400b0240341000d81800d6900340194140358001a00b00e03034010740046c0b8013940310491203c004038104614002001e00170050309407803070103040c041d455130701607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 63443105 1250 63441855 63441863
    0xf140a021509010e060708030a1104050d03020312011a0a030c05130914060405011a03090102070212101119030e1005070504050405010e0705030103140a050703110310050613020702042304 82
    0x11341e002d80041ca450701c26600500e0f00001d245145940348010308006005100d04d030044003a0502020880d40c544143e082000361107500155901e142c0d20602c400d1248059102c01d24510009024003d415000d80940b2501c45c0141400b15043e41c0404d420b5030b003401036501c004d40c140412840020b02070100c0c0c0003801d0311141484840003d884800c01d0206844090052034500d001c00100005210307051801964413034000c1c03000504080744c03a4001215108121400503090340700b0104030740b0040c0184500300003a98031f001a60300e007040c0904d0440245101c4a140f10600da0b9901c0d08443c1d180c001e0204000090100e0020840c0c0c1c9890000504250014040c09015601d048008a23054514401c454004c100da501c2d41411a0700c3c680e601d041a41256110320b45901820750080f0010360200401400f45200308044203110f5101000c0c1031a0442154511550720f061a007070000b02e4030780c1c4011401e0380c15040800360f9501c900e400030030042d03c04090a50075078091035042c040b50044400910f4022442 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 63444355 1250 63443105 63443117
    0x10031703070c0b0408091f2c130e060702010c080106050304060905070603020408010b01020105101e0b0c03040611160504020904110c060709120b01120303110a090602010606020a0f140a02150901 85
    0xc7c80300080003c44209400d40003282411000480100702c0c02d8108602514143c40c540c0c4000ea0600170841148003a02c003085400d448100883d8064024040c483d03014202c0d10080180f040c00d40001050080103128001c113000c00003000c00c0510580d42c22442a158214040340c022640d41d440040081d4420311400c1c40f11b510b4022100995841805900d00500e8201e2070020203038184951134078040b01d1202c1c002009110020001280011b440140021082c8800a162124034240000d464203200032041c01c007036048113214880a040345140e2209903281035030016155600c0002241c01481c4076111171a03d0360000c610b8001e06100040c0d55480380f1140d94074102541d54030f0f0800704006d404141d00500851800e401840032141e051443d181e6180245000305244800002100315544150103d40001d0200340f0207011240c1c090041d513005015600c01425110744944903a4440c1850503001031548024804850410300b04101c181d8180341c00611591415034891100d18855000e002c182d07000c625 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 63445605 1250 63444355 63444379
    0x140f01060311070209150d0c03050d0309080a180b0412060e0304080303160306030b010b0a0801060e01021216020402030117010c05040506070f170d09030810031703070c0b040809 78
    0x1c428002d07190324200c0d5006050030311000c0c2e820480700c2c0c07100810103281c240c0d1004a01d11280d99203002c00b004240140d680303403c01d50440c24594184100c8a03417000505042418000010341140121103182280746001d03049401240b1610071380c1c0c1078540c8400c0742d000010901181180c250100a848140f040e04200420700e508034240b504ca0049200d0300205410a100103003801c0b11843c240800301d803062a0005072035499a951120006085c1c110410000020031001c904541101e00350740134140741e0a00f8400702144400003542c0740c0b15000c440f0600c001c0415026403010440c0070000c10150b006206644940e11441e0441456080100030040c0d9820f20720728115050007203040303a00303580001d41194903007075140e26400c1c4e00c009000001c07100704e4003180b20003e005864201504800005003008541440c003810b0040c88032201a007500c2c00403445510810014441d50a414580ba952801c0380b034923640d4200003525003081901d8007428100d2030900b00f01c10444058002e1520010032034018041407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 63446855 1250 63445605 63445607
    0x904060504151a0403050109060218041b120f0f020a1b08090f06070f060b0111060903070212070b07030302040e0a0504020f1309020618040513050a1203090204140f0106 74
    0x81d540c928003002d4840d00e01030921100ba00469149911805044441c2c40e2968a076211401c560040800799180341c0d000c1442c458811600c041500b40b600119010f005107900810842e1141111403012024400380d0300000b40b9851a5400240c00a9405a0108422159a611080070354040d03480040040c440e010300b15240f50803c1414107003541c01034449420a9802800c0c4824030380d034400650340c02a414064480003a03000601002c1441c0714100c04191101004005089030012044c0c280ca5a046201005261600001665210354044501c001c02c09541d082080c1882e91071740003010659000101c0009158041d0001c0c0211800c0c00015001d43d6160099081100c0050310001c0d4000c3c60703aa200c070903624190f0904140e0b01103407080000c8054251b4000f880c141d008903a59940403003442d01300d144510b007521405da4491501840518250200da441c15103038045a24001d001c5a45602440401e074803a5002c1100e0682c080c108001c41051110341c3c18134103030100c40200e00808480300101d022 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 63448105 1250 63446855 63446861
    0x1080709080d08060a03020d06060501080c0a0804080307050909100302030601150c1103010b03101a0402070302030a031a12030712050a090905150901030f030318080901031a0a09020904060504 84
    0x1c0d070168020707010041801600b266000d80141c0801e07441101804080007581c6d5040740039082e54417942d40005c0c41458080050030301740c00140343d6440d441050003000b02c030981101d21154065880910247d61b83d03505107003962103010740c00c0070030340200300c210401055640c000150790a4038005c6080740d46030380e46c904820110f0b00200340c507003000070209021a000100c0c00020402d40c40401000400c036115600003081c81d10401c0d02c80c10b21001c0d244d2501400746060500c0e9084059015101580b801c1c0d96510060366038401c0c94400400c050f036540c3c0b01007083c0240101c07203040001c010808910b44c000da10000340d403500008401e441701140c0c052415040b42c010300032144980c8258403400175440c41c1204210040c03000500314410000350f00700c8004250b0340d00101c240654030821404c0080440c81c1070050880e03040a6003e03009082d480b0804001c14200310540310072503024600412001c00600020f06900d4010750066001629454041100320761034020300046041924200040c507514820001a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 63449355 1250 63448105 63448109
    0x70605030a11031b0d090b070f120207021c060603050303190e0c0918010209030303010303110d080c0706020306030f0111030718030c15021e03180103020324010e03030d0b01080709 79
    0x802c038040d00ca25407070648000030b0104030250305d40020304078203640c641001214044540400041d0044116483e040d007040107030300a885801011824440540d0204405c0350781030640c0c02012071041080340c100b100c00c4e0003000143d5840010382e5101d040c00d50715440101d5210b041c900c0310328105880701c6294080002e202e0014030707004110820544482d030404c0d540480f07913041c203080ca54007000481c61039102000158001c511036600d070b403050041a20170a042511015101c0f0401c0441c01c284a102d6000d00242c41e2115041100180c0e01c2e00d8003c0043d28003040e02502040c0d17075092001c4400015003410156116050320788820340004001301840c4038000d890f02004240070403080c0309201c400c0811003590460b4001d40111441d11200d9900108240340d04030703441d14158800a02c00403100e5007070342007a01c888002c0c2001d60071818484070040d80e0503450340090000f1492440f8498030b580c41064401c0748680c014090302d42c0d6000e019090005452034650079404110b201c030200701810f10444a07034007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 63450605 1250 63449355 63449371
    0x1050f01090e060a03021f1107181d0a0c1701060513020c0a1a010911070206190212040f08070501021920040c110d090b041a0408070605030a1103 64
    0x314150a20664540b8403001401498111005075008001038a0303088010b084400e541c2400e030307452804100014041c41c401004040c0d6500808020040e039500c0310004012400b070003101045800b60074125402d1a48441c0c4038014510522402009000003510490195140c20300002c55480c00424114213031003142c42181d0b0400300a41484040c2503880d80541043d98145c001d0b180b0120150321110303501ca00100404107080e115000402c0500100d114110100400300802d5042113a0380d000242e2600498015501d10020000350b645214800d01003844511204400d940d03e40352030300800035072003803075020300c088920a200c80400e1070343c000550481810000c01c4603204054150b500c40a118040c41c64401c1072222081c8041c0f59981d65004070341c0ca1101a0351400315a6031040449494a1201a560014000d403100184001c010001c11981995100400000001c01500c0421458440e0b0341c0808c2460281c0301010580c1c0b80d11500940c00303403c40c94030038412140f400803107484522065407182 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 63451855 1250 63450605 63450617
    0x1060c03110a050a2a0b0409020a02010608030c0a02010e040b060f181e010215060102120c07120609031d130b01020c040504030e010f0206011a0c0f0307050a030801050f01 75
    0x10009209200c80d01e00e00800c0015140d9108050743d9481c60444014802c0b84d00700000480146240010201c501c0340f24100d158454a103460265012140e210702c1c0540c20405400148002c1d81c1030003500500c0050170f1010490380d4a5004c01c00090700d1f01c0b0440001c90005844101c18a01880c0034040c1d4034030303500c008100a15100303031142a29501e501c00c41351000c10414801d16114a642c2c5d540b100180b06c02030425040c100140103000900f0505e030803c06420000100050005591340020b045810320f00b0402c0746a502c0c0501e4600d0761801765250300942e141030000708502c0811080f90424510188a91079400c0005036800640f40214501e9170000c1c3c00204c011400840a502500200f0510006006540b4094a0750011034240c490459080c2c0108010400380c11a5580c0440d040c481014940301801c0e041d4103000e0303d20120380d00d913100d0844409000c190341c00341070010700c400100001104101daa43d90140d20306140c84e441e1030300701600480c1e0000000611410000380768011030205079280 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 63453105 1250 63451855 63451877
    0x108011a130c09030606060302040905011d040b0a090203101b0f0e040b150304050105010302100f020c041112010303080601030c09080307022206090501140607050a030c03120c050c0c010302030106 86
    0x1d140104a0b10030035504100008100002240403481000054069a0780240c0d0320703428a0030180580ea01a0700c0140740c0f0348010142d554001071400c0c02c42e0801da1021410806072629072001020b411b0952002c1c2d41401a0007080826410587c82003002d01c40d01481c807802c846034480705480d1030000c3c40d00d03000414100324081d807171482c1940c004101600018039000c81d0030426202181507030001c54084800781e5442006209500c0c0c02211200500e0480c5030034084101104802512004035049003402961280c00c3c51600440d60b81c2542c80980084076590260f6a603410024030f110030558103140403134a89088100c805100d4400038050325011310045107000100e03030a010f80308540b1035402d00802000c030300905400c40180620f0340200a003860200e80765040c040c500048404880315144039210400002c000210045495402c4c29010b042c228901450303400c0966280126042c94009a49012041d1240a400c00d02a0a891140c00c3c112081c00b0858001501207100a00942c000b00d00c0e89003017 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 63454355 1250 63453105 63453139
    0x6040308040b041b0902070209160c150605030a08030403030c0c080a0e030a060c0c05100e06040206030903090405072703080417010e0d020328090e090c0901030302060108011a 77
    0x941c2e5009482102e045401d00c58855406a140109403c901d40316a0006460700a600d042c0140c160001c42c10a00d848011071841d07400f0381103050303443d00140741c054082d0401600504a0348071600406024081d103a070b4410710324240c2410380c01210100c0100b4500002201e80d41e00c034040c060503466008184034603050340424103070703400141074900c1d95040c410480e1210001c0c0040c001c0070040c04060700d03000705155481c541780b8204440460516091441e05051120a034000140c0c142c219805603002a40c90311030850050a6100d085051600141800c0a101c0c800398000e000400c03d0349035810101480f00c040c40e01c00241040c0d8400035160b8031003400305000281c0921032008045181000014101a0144d68581002e4900d021403015030000309900d24520a54004448410b0380020280200d035a85e24018090500a00034121492058000030303621800400903115030040060420000303695078a0001c2d1baa071000d020340c0d50309500708a0a8144220f20100450007180010b0802c0914400015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 63455605 1250 63454355 63454373
    0x307050714101b0503160e061e090108010e060f01030513060614010201050108070e070804020d14060627040206071a010b03060a06090602100908040b0c16080604030804 74
    0x24094442540c5048652101c0400700103400154140d841c000c02c106441c0744200e030000c456242241e003807000c10810414036000014100d00c242006003000b0002e0070300500802d506d4015001c1c40014a00700d03e0805840982d0070b000340c540c5400990341e05c075490ba01c461502c030030304100303032601c40d00070168000190a0303601079001a607000b5040010005002c00c0c2ea00c1d000107a4810303a0210040f03100714160200b4959087c003409002d40300d040b0081210918101d0002541a40180510308103c0105c1c042011959000d03500c10043e5082960500c40d400c110502c15154041664403d104080201c2d0050380010b4000701c001c005440101c016516983d01d4080c8a01c550000b802154801c0f00f0090080ad030b5140c0b60a1140039140240003691030b480c003007007400107440b4aa00040c00f4450208030406ca02503002511030324000074007001084081c5a480c24014900840d04043d448100124103a00407031000074568041a6111155042c903544d5903518944980058070b010f400182c1440c0000c0200d40804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 63456855 1250 63455605 63455617
    0x2042417090f0102070303020d060f0501090b0a090b0f09010305010e0105060901120906091a06030304231210150b09010e010f020a050109030923100e0f0a0e220305030705 75
    0x210685042c0c00c0d80180c1c103422640701e03202c05c50109030b0101d805002681507101e030382c020348207100e00360300c0c00780c2458006800403a561103a10126800012501d4000c0d1150285800034100b203e095600c0d0012004080d10b160400e04001d8000391130300d000050b200c2e100c2681e5604880c2c001c0c00d031600e000512401190740d50741c01508038070584e845445000c00941c9a01c180f80c04039004180e416a0f490703031044107414030080682143c1c4640c0c010320040c412034a9a007031504c0c407042c4002c2441320301c07000300307000c1a40301c40710303001010b06400b40321000c550321220780c2c01554544509e0581c06407466140c1170301020f02d0250b1113800707000580d01d0701031080c03030750142004001c143c081e4011140811025610359094034003072a0114000b41d84100c00308243c3c403648034003c3c0c2095179070218000703035802000421205941216540c0800c54407000f00800e42d08e44002c0d982c0c0a64002d00100d4085071501101040860141d80c41601c1503c0f100c20070107030350820b040c84032079194103640b09803640e01c1c1c1c04011203943d0400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 63458105 1250 63456855 63456871
    0x402070503130308030601111f0504050c0901060e0102010b04110a0e0105040b0c0a0212010c0e010e060c0106090605031207030e091012060c08091f05090312070302042417 75
    0x41003950010008011100000d42c03151003c1c9640b446c040c00018800c04040501c0b607e10350004a58602c41081451107051011451070000354650700e0342042c07894504401c003000c0d00440c48038004600a81d0150380e0008007003003a0001d01036005480c003808103d81c44903002c0d5058102c14441ca0300e00f60322442628481d40c0052400c24142501c6403032065142c0d001c166503c01c1035100c11440320071410301041140d0b2444c01c9038002c1018080f8103002501c40180100c0050400548004014041e41ca6009680e1080600300080007510f4660440c4c0c4020409401054407a05c2a6005284a04107104c115405150f1681d01d400c0034014240501c541c0303600160840301d030b5488281000c5412030f0354900c1c2e095200d008210106410303a03040380c0074141070409480110749402003e010040464480540d2140403455100081c01d541d4021041c1d007035000301d0303d03072a401d405200700b070020070b60703268004d0011340c0c000c08291201c216000a40a5840c04810110800302e219a5810100c0c0e0301401c0081e5444801c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 63459355 1250 63458105 63458107
    0x501050303120a0b040e0f06010614030903070303090201050c01020d0501030c120c09090305070f03020d080603060c07031b050105090d09090b0a14030f0610080712030503040b1e07050a18140402070503 88
    0x220341d80c1842007190384d100052303002400410070203074040070009901007141089861070400091064076842030080c0681819240c3c9882130031079101d142211076940c01d110085440d00c1441e040040502000c3c4400d407a101c00041000c655940e2a4040800240c5e1042550120900e01340040c4041c00743ca00c815001c0c4101803001001142c16174488056081c03013075010b080d80c0d6548200161880b140501030f20f00a621010820a541ea07c0500701c03076809800d81441e91524010184d480d5600100186c020615400c0a0a20101104c001031412404240341c075541180c81d01c941128086800b0f5041c00d55002c501c082e81080005c94484817900d6480c0c000e4192250382421310403051405070281c803062508200758400b0803480106100390009440c0714030507070a074640d543e18000c0c031b0340c000600003420850184003c546001106a6241040c80809074203a005103030a40c00a06103400000100c000304034441e441c80d5400c0b5848084030151000d210401d41220032420500009400c95401200c02d40b00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 63460605 1250 63459355 63459371
    0x31e0a0215181605090703090305040b0906071403030105091503060408030a0e0d020c03070608040507030b180109110405011205070b180402040801060f050915040921020a060501050303120a0b04 85
    0x1000e106015112002043c50380440e450101030090384c0900078900e0b1b04151901ea60600040c0d0301004690450784080a09901c034450301000400a10500b0760041c9504141400c00710100702c01b0001d541201c1e001c54502045690748204c0514003e2000c1c03010380e05401c150002070002e5803490285070800c40c80300001400c4040a07a042d840c0607008503266015910103950001140b40810240d03015240e1454804494145640c0c2c5030703902da045001c01880d9903020000524810009804192000800c200030300180381c150800b050301c405c050f031085000381d02f0000081148070000e1404e040322680800282016413401212021682009041070000c01d49210520310a586900180010b800074100005410b4030700940c3c400510010380c4500e008205107410441c0707036240c0340001900d0041c103682c0460401151b28080703407503001025490202040407104017101a90014085c08224424041080309903241c0e810940d8900501c0d003500500010740300007074000c05841d04070860000c8050320100d5805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 63461855 1250 63460605 63460651
    0x50411030115030506240409050c100309031b030c0b070302090a1e09050610110309040903030e0d030203010b090f190605070302121306210e031e0a0215 67
    0x141d840c00402c1000b40301c215081c01807007010301040c0e4100070b200484444103000103030081c41d6105142009071055559000a6080c06820701c4910700700c00c1c0040040144203004000a0000c004154003540010605e070038954026001500c984081c03034040d150108000001d640b51059110014500f100b0903800740700c0c0880640f122000200940107030025a2100c0c1220b61015104894660000845070309243c14845107454a20541001001501c0c04050000103040e44e180395104070317108d003900700f0310380240c10040c1a41940329884001201003946c806801040045041e40001c6c00f460320325500411101459181081c00a018020043c01041c83c95071100030a52400c0c10b40d521401c00b2890000e0b0a5041541c1031000712030303001410100c14207100b007000a8030f0700c089207402000180082010140728124403140080b01043c00e508081c06072016221700c464581d04440c07025005070b0300f4850715a101032a4903082e1803550032168010040001a40c0380701e0003100b005080f84e01f100e41085034100d201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 63463105 1250 63461855 63461861
    0x90919060b0c070810020702100c1415160201050c0406050912100228050702130f0905010b0307050603191d0604080a090602030a080115020102130f060e091006030504110301 76
    0x300b4031074006003400b545812a52410221007450b0000e1140c81009248010780d28180041c2c0c4881c114079110304004110b14062015200343c0d803480180744111005680c46410a500c1e071407094600441560401c0038080701a400c0c0c0b001603544d09501c2c5014402030102ca885031024009422005000951224200e80c3e803d09000081c01840c1d007958000945c000c40c001031139600201b03114400744e404041105030800a00c1c81c01030900080c816005e5400741d40d803140c455000f1084504006208021104562600302e00030842c0d01b100601900031040300294a02d011420789101d800001e040e9030f000314521103c18014501c0c00300c18094020740002c46809401e0802006100782c3c840c10885a44000082029000c103050368042400c43d4010010820359980c80003000d41181c811070780044410f40048030a901900401801007540d00c143c142c0020000051000c06003210110f03142c03000461200c80501540d40c404489500c0c645c5510704081000c01d100c6e40c880760307215010b4170000d4691158640000e0075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 63464355 1250 63463105 63463117
    0xd020409050f060103050108070e0a02030a0227091f0314031606020306030601051c030305091e01050a05010807030305040b0901020c06040e0a0506060901020a0b040c09022d090919060b 81
    0xb6555038410026156054460b03240580b100e2401040a94a070003041003010500034150711401d50080085109074170250142c6403084076061100420b9800260324503040c20300004903600c910b205001150510a001c2c241848540c0404003c061a81c1552280748596072020320201c01d0788000c10401c0400c0b620316100c0f42c3c0f81442010050b80d641000001c040c078212068002c1392080c01680b600c240b4845860071140e41581e4141808036440c1d60b038014190500305440303041c1000c0106800c002102c0f00c2c065004030710525411904002590720303540c1b6a59121040c0c00001c0c04039404200a2282e41e001ca0042c11100c03105104913900a0340c85404070340190007550012504192050034011039851502405500000c01d54060f0700b015244d00000359500950103000c0d010b1185100414244844d051030580900400d250541d52a00b440c1c500d01026890782e020244111310303100302e00310343e046264122594000000e11014007600e81c0105081035104c140402003003e40d6810000502c8174214000c0c1c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 63465605 1250 63464355 63464371
    0x2803050f0f0406091703160b04020a030b0112061d03040e0c09100c05060f06011b030c06050c03010e0c0a0c08180d060b18090709050403200d1205100501050d02040905 73
    0x30169142c031207a203005c0c044500d90085030b5042804a03070380920750141001e001d03640101d50135096459600228010041e1500068019044000081070803a061260f094515208840804c01139040810300001000009190941500304010400c010510b00c1d01d002d411002344940e4a00c2c0c2000307040018510095000494045484015043c00740441402100c4d0712660201c800c0629240010009000d007546c0c03810580d500d203860400f81c080c184242e50503910580d220f02c0822050501850401a0382c20074451070040200b0b180024030900c41505c1034507050282030b25580f400d9411079031010070681240c40c0c4c1c80c8480001c030404400c90340d540c0092824aa029500020f000d0f00c0d003005001041c50042c85120b0241035400900c0303400e0307500081d1320049400c070038400111034030f0398681210507018880d0f03960495480060314280004002c9090603e111040d107401000d800c2c000602e1058800444a590707041503058030801030b40d4004c900810041010035030040c80c1c540c6030b42c0c80c10211030f800c1c6e441030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 63466855 1250 63465605 63465617
    0x5060a09120b0a0e0d120e010204080105040c1403030403030503060f040b0d21030b011e0c080c07060f0f02030712021c090503010e01020c070303030b04021b0f2803050f0f0406 77
    0x1c0f400341040d1040e030001c440e40d4405480d40703215484000c1c00100b100c0010303081590b9030b00800c20003064294180c034041c00c4030300e0080c08103003054101010104c2060090941a45411184c005646000411030301100d9140c1c4070a03066503205002c000c154140c0b5500f6540007a10340c440090580d0302d410100d00e0280c07150030780c40303959070340c900a983c0c10081c1110b011080c5880c001002e034061b07801004850458030040400d10700041800340c226010310129400420b6000c1c040b03040c0d690900049041c1c42034070080c0c1e40303200d0310720100002216039203140d144038009600300b005207402080d1140d0380b62849070b120340110740440c190f1505915440344208440c03800581700c1d00d0140300c40d24003805166528180d5100950412491106407502c0301400d100c02401d0558901c05110907840700d8047d5141420324450358020101905404e50303d80c44c8003001e1510070300601da941550b52558401d0850917205525a600400c0702030b5805a0315580301c40d240c55070b114418421082030100c2c4200801c06085565186 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 63468105 1250 63466855 63466861
    0x20d12030f05071805060c15010308070312090b0a0507020a05030a03020c0f060105030d0f020f0d0e090f0f0a02070303020f0426030a080609040f0b0a02130f0b0405060a09120b 77
    0x10000c40308041d2002081140c0381c00f60130500101c40744100140c0c1c1044940c141d071059501c01d650b1034855114000c1c001c0c9410000000b040c4a682d03805840c2550082d10380034030505c600390450f000c0761513402d80100b079aa4100b0220303030305281e680c0c0540d0384031115004036080b408507521000e00e075400100358840000e8000603140d0803074070b05024102d003180da00c4000344003550520f000070b612140543c4103038040013000e4881300405807003000400804c20750400de50b1882150544001c1031061b00101c82c1e0b0050240c0d90101f400540150000c40c40741024140d40e0100340c84120140000c2d610540059007056002e1141d154031040d80d800410081000219007884050403c040c1390340c0822000a45400d90001d10200c003d442e00198007643c440c1e0201e48120b4555030b07604c0d02c4081240c0e200c0c40542041543c00811005041d030380d000384500c100354859400040c1d80e803c01e80703405080c203000c2c400c0c4142090001700441e0500c40082c0180001d54140140e00715104d404036002c601200d101034405410140c24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 63469355 1250 63468105 63468131
    0x603080c0706051e031018060314030306030d080c04050916110f0c010804030915020105060f1002100207020d080a030204050f040b180405070f080c040f090b01030807020d1203 77
    0x1e104000d100b142021804d00018100260064282c070801361014140040010769003540c0e610444080c00150742000708248442c2c0302c440052442e070104403802c01c03140d0b03428a140310b4004241c130b00c194030040042503465400c81c0c0458250802800283d404c0b01c0034407010a055030b43c80401032150b1a05440c003030141c8441080108401c0700309a1002c0c11340c2080d00500090030b008540020301c20805c4c00d08104a890710702d011a601d5010707a11003000b444e00380a840700c0c40344e411f4004c03070300886044402c2182191002c0810400580401c00000541d1040501000380c4041760050080c1b20700007004d142c1c4188142d01e802030030358014020000020f0b4000380034011840c2c51400c0090b0018190390070032400c0307030380401b145002e0b0030340104031121602074000804020081080768042c285c0c8404005e501603440101070781d551120a141c038411410008400607054092054203103441e00060802c800c1e03403944e2540d580c55840842c0998000c505482020041004005c4c003042000c295940041e11101c2821 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 63470605 1250 63469355 63469363
    0x1104060e0906060a0c08090609060a02010f0e0c060409050901020702150301030c060503010b0d18080c160503011a010f0504080607080103110a08030901030c0903020d0305040303080c040803040b090102030d0603080c 94
    0x409208020a01085109175802007440c44040d900241482d40c0d50f5158001904034040c024180c1e50100700002c0c1843c8955064000f00d03c80702160000303006090794021360503102c0c02030319030392074000f40d0900c0104168561508080c1c0c005910301c1c00149859200c0d00804e42400a01940400051000004204020210003c94014843ca14040e800c55040107111a5a48102e085500da50303921340c03040344c101449015010f4400350b84000034580c0c80214012860700e554001800301282100004005400d06040c00744400b00007044100b6001d9000741c00c01503442d402061001c80821600f8000840c4640081040d40d002e0341c0c1c0c1d500e40701c0482d03146140c60319101c0e040541c800d0140a40080800044000000703561120401342408254100c0038903003101c0f07160299101139070001220f031018081c560000e0050040e680030b60ba4801c015070380d005984005100f01c0c410858564010032082000340c12480250040c2501441528940141981400d05070f80050308142d0300e403003000802c6650100100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 63471855 1250 63470605 63470611
    0x30b0d12051c09050304120305090a080f010e0a0f020d05100e030310050d020f060306040e03030c0408060f01081c03060b1c0f060803030604090f02030f1c03050f0610031104060e09 79
    0x20340a100e8483c03113581d156124013079440707140c00b400d68044441c02014095020395a1030b403406080d0003161130303139070328008d9680c4540c854516042d480d05000f29484c0c0303c0803030980c0e040c40d00407480460b0307513196030b00b40001100b81c800144d9490040d0b1103506d000300c1c43c0d4021100407071019801944c0f80d00f02502c282c03552260759400f0600c5201c05a0b20790005885a40d846030041e40203c03220790301c0340d8440b0089805000402320801031030000204000e81ca00852010b4415208071a0440701242e03550070701c803001d900003801402000d03070010020886103051800e07000682800d6103408542c2d01d90b106442e8400342c00200450740c1e42340c2005d8509840210b148165109400d4030502401103a02d000caa454403484041e03c100d00594071402d1403000c0c0280111000c5900ba030140840c2c005494130510151184001040015051082c000440e03019202c4e005481c0500c081440180300b40c0c03991300c2044601000f04071404c0030f0540b42d484030041900c10b03038064401804991950400021068201f2101c01002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 63473105 1250 63471855 63471907
    0xa020a0512030f0708090106050301020c0a23060f0603010b060d1d010507050a0302030603070506160c090903050d0e1501080304061e1b050307050703060605030c0916030b0d1205 78
    0x244204039910f4403035007607a50404800d0034400140e8407032100729800742c04590011b541640c0001401055054005005000c0900070214080500e5040c0c0250680340510f0050003102e501c05800f2800b007071501c40312103802c602d0080c00021000d0300c0314041051908400a00129a90b032000d03840488502d483c07604145000c1c14000b000503140c101c1c0c02420f1402006d008404040d070110018641e500d0411014018220007040c8946503501c014045459074540d450031128000150800198898580200280d0583c940c41d05801d1580b2841120001c181158040859100c0c4140c50b17210840108800c5020300f500b1000746503210304000c005019a66003da40e0036414460b4400c025256a0204040c00141c030407030072401e03200c8c1d060300f022440c60041040c0075005001e9035800000304007a540c05142203450640035100c010030410304101c1681c0782200c0c41c041c410203181000300802d110b0750110441481c018101441c2240d01d869210405458004d41d0300070a00001d40202401c41410f410790180b80300d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 63474355 1250 63473105 63473107
    0x15030f010b09070c050f0601080309130b010206040b0403051204080c12040f05010f0c06060b0a120c0e04050604061701051509070e01050f040e100906050a06090e07140a020a0512 78
    0xc07000807400710400185800304124101e6a507000b04a0706210401d8240c00d00303401c8915a503101e100464490340b124a00d94811380500700d001c0c081625070301a003018110141c010f1f04150b03480d9100d03140f0b8460700403c110104103041021911441e2425072040c040d5006003603140d1140c3c00b52401354038049035100340d2100c10209220030440c03000b00000c04415182c00780380205519100301c8041e40c00c6241000010005400d111010401e09040c0002c3d2460440030b584400e03440e540115440c084a082c83c0035500000c400b0f038100c1b5900d040131341006801550207007000410940d80d6403051506d03401a0410551030b5180d0f03091001007442c01400b030402e054210303024806410440405880074102d168014184030011a50711109041d640980f00200b80c810315002e21071600b10b05034002a41203014070f10350319103021000320349414003258400613035840382c031060402030401d500201c07442d900030090000c224030103c0e038411452480c40034040821b250f4000b403a201d642407034820704022003404c4038007640c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 63475605 1250 63474355 63474371
    0x60e19080301030f03030e07060201090201021e0d0305041509240501050102032502091f14060a1107150c0b06040908071b050303041707050d030203040b13090515030f01 74
    0x11528101ca04580e408056088599100d141c103902a020603001000c0034003c21800240007074040d044412118404da080d0380f000f0100362603c45040084c4100354103075511141e00c05c00707154040c2d409650030a0140b02069401c6001c90100d8040c1c0c1c0c900340e002c5135a003040f115054a45003012240b0801c0b00300d0365100707010541c10030300000d54034003072620410095200102e10b04091016803516030305590300945a8650303842e018039507061080343d016141140b11600c90000490f4100da0780340704c1042c0c2000380a1840d29036030170021a600443c004580c402070040c0d100001c0c00c07071035a0100443c8165103441e11860b400352410054007240000b40141d0203a401d05513400b0005000c5400c0b540303001d07801040a142030142019156070005542c1100c0e806200000300818030001c0340050300400e10494040364501c0e511403080c000007140c014401000f581c000d0009004840d00103000d40800000c0b141222000b65994020100350341c0e09456141803c80b9030070380b550725400e051040c00341407402e0b8070090041d84 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 63476855 1250 63475605 63475613
    0xe030403020916090509040605041103010e1b3012040e0a0203040812040b1012050304050904170d0b04060b091815130501060f021507051b0109060e19 66
    0x820062844059006903000b8074016030068403113070301801018040c400203250500d44000108802e44060321507502000f00c070400717460140244028800824080c10041c414a0003070000101c16001555024807600c0300b50301c09203200000701a0010b101c4800d0408401e18810044c1001d9000c440e5005d5154200030901a21549a410b2038100140300340040c2e42e56201e0502c10594001d010f000119903207a038041c8028008500c08450180300303101c03101d1848540d16070300b64481c4a450728004000d40c00510041000d442d10803403c5034440c0c01204c0c601041841c100c03045074254403480e10352000701e40e10703c0c02c0e5200e030416110309005480c405950b04d142500190008140307035001c1814259000380a400078554104000080c0d6804c50064460040d03d11004461405010309002c0ca0b00000c00b0659003162280c030002e200e0b4200141d6140c0505036803544081207505c1d42c0a00d14021a0709107440f810002d04100b44941024140583c3c80010006904807100c0c0c142003200004040c41c40e2072001040210b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 63478105 1250 63476855 63476869
    0x30103050304120f120e04050c042303010e07060c1a010b031609150309110901060807050a0c080703020a050c03060108100f0f14070e0102010911010c030c080c01020c010e03040302 79
    0x245515240240080034607141c2082100030013800200180107130350800a0540e042018070565003400c90b428801d50782c800700c4500b414080c5201e0358070b54020400b15031405802c0380b01405030036500900081840c00c0d50122542c0380c1101903204500040441e1444070610071000d0b0401d90300e0b20a020b101180d549070400c0c0581600010348500341c0c126040c00741c014082e01a50010340200700d030980004010f680c0c040301034024824010103540540400400030358500d0900301240c140c03001926512000d440d07101080314250031411201c800d0007100c130f078440701040c10080901100d030f119a005004a1040e840d005051140d00454a4080c8c0d12980050004060204440ea030301c40108a00091031616100010043c00505103200c005a1074001c00000304800d40388164400c4025880b0350f405a61100012030072500c40d0301000e03040310100c0310082c024ad8403c0c22003004441c06441c0c04a040c40d125106c2c52030640c05183c000c12260760014014034107500c00c0c045d1000c1134240c031001d1800c05280d03801181e10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 63479355 1250 63478105 63478109
    0x708060109031203090501060807030311010b0105120415020f0703021c020616021501091b050304020904061107060c0e0307050607020904110d0501020a020304030c140a09180203010e01090b010b030103050304 91
    0x44100c500f040d060b500c5100b0b0b40b04c070031595000030081c812103987d0525a0f49035101408107070006019500100020381050086001c007500607501c441c074102400449440a640180044400c464002102d05800c81140003408248040c0440c00340c0d14580c0c2d01e40640b4010079540d41441b04112030564800031500403075103551020969406814648429004a0402c0301d90010500310030030b690004160b4440a070b00c01d030744210900c4201514802c4000c0c003941c01d804100c800175409005400028006502d40d00415100b981030341c012030524040344d13200002d4901c1040c142001410318008491140313070402c0700000a20040d11603030701c4d1841c0c075000302e200c0920060014185c0c030000002035040d038403002c0c0004500c1d600240215115203070f184000f9103950241c0301c103070760803045c200c4041282030740301455101e0100001c0c000d2800f1403030204a68050030380c040c080188040a106007002684080c0203880341303108070a000003040455850b04c10344600060b0860021454103000610004000104980c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 63480605 1250 63479355 63479363
    0x120c0801090b0f030f0303010f1d041217070c1e151d070303120609020306011e02012c0d0311041e05060d0b040605060a14130504020304030215070806010903 69
    0x2401c42c008801080c4a0342c03c5601003501880350510800fa2401c001c40914140c075250759505c5445c80c0d6031045500e11060040d04820b409840d0310104c7e0005046020a610100c81e0381044109080c1c0450016601c0a0485040c0c0c0402e0605283d04100700400180c0303240c1c039980f909110312211190b2079100f045030b40c014144540ca0354680d41c49450443c101a0944894058401c56041c10b40f82d01d4010218030300400f10b196003c0c201000840e101459000760380c0708140613926018003640c00ca06c3e600701041d00b550020300795562070384800e0070150724458100c0361440c21a89004200703021014949400c00c2414078a041614001c844e10807513013414121021282c404040c54104019440d201c1000005035000f150300c0b50b400180048049a503800c941603040044804100840d42c5005000c21032283e0402c8200042094000d2029282c0500181c07254640014490100c15101d2002c902264400d96040d030150b400303040b01c21b00704444403040c268406040c0c03a15407024200400080d050400341d0000030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 63481855 1250 63480605 63480611
    0x2030c0c010206090c0f0a09020324011409041509050702031b01051b0c070503031204020f03060106090911070203011404021c0809010804060b0910060e0603010b030604020f040902041401120c080109 87
    0x79142d540d1035001c0048e0008050440d0760b410440c0c1c825102d100c1d154001038022145c045c07825000e40c00744821511045e2000250352801c0030b030b01c0802009010840d1600da40143c24000401e00c0022803203000c2c07084442d41c0055a90307020801000030130309070317084d8140307010b82c103140400441d5400b002d04420304281440440e900c81c00f207401c140d0b040a9440d00b146d90584400308000d203c01144804142c000d42c002e40c1c0714010f03030150b007043c5a1620400d000c0e01001c180328080802002c03100f03a01c00d0000303404051003641400d807160300003400c1d14144903040544005443c01e210640c90201045100703031001c8000545801020742d03604081d4000c0501c0d0905201e042c40005040c072109412410b50640024a244114540400555145c0d5424000d001c0041c42400c9003003003506051007201d0503103c1c82c003c2c842c119540e2604010180d88604403408a440e0107110025402e0342500161028081d518000c509181503003000400444010b80e0180d90181072600c513120160700300072014151480c002001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 63483105 1250 63481855 63481879
    0x90307050d081e03060a0602030703020c13090b0108010c02070803070f081c0e06070e04150504090c080f07060e0a120611090a09020909060f0a060f0c0b0702030c0c010206090c 77
    0x11603026109000140d20f41400c40305442d04941c000031031090900725400b181241e110b90080b070352401410001409640f111421414034501040300349044e01981c40c0c04201f0740310560720b18138000c41c00ea04c1914603a4540ca03c080d03a498040c0150009800140015030501c001c54944410f40341c041c0402522024001840811084104500d0340030064010410702c001c0c0c1480e0f480d150380d01c2d82142c242002400701004000c03685000e000e0940040114003010000606180070440204554007045035203001400d030015204030140052a080b00520018012035440c140014054030210146244108210003084c00213540c40980d546030303c5d4001c00c0000f001c030b0026219008078400d0001480d48584002c50001d40803030315400400d001c0034269141c0801e0748400c01400308044400a14076840008880c0130301072140704a01241d4040c00a00c0d000301c1e495603c0c4c80d403616607001034030301d000140c000141c241d0f2010710801c071700082c0003020701c020b00e01450a52229a129070001e00710620502c040180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 63484355 1250 63483105 63483113
    0xc020d060203100b28030c050d0b0a05120303010e070c0210110a02041b090509010302060a050c0a02100c050606120706120b10030506120604030503040602034602090307050d 76
    0x1090003620142460550b9100070a0041c17140c0400310710b107080300308243c8112400051003801901d404440b00e40300c8601f00f05032004001c010700803008070709030044a070b8100040d40399500440c10342e00902c0b0b41e0107550f403541440e186402d0054000e06034000c0c019010030344801612109a004080c0405280c40c0c0304488020f019142090700b00311002e54854106202044812a1140f48281160300d50329a1848542d4a0083c44a403071800d00c0040d5018206201c104900303401103000b4022400110b00b40e030604001c50340080c0c2509107000c0158000340002915504120081211079008001140e801408034000012030f41e880003036010300c404120241d290320f0b05e00305d000d400c52041c0801c020a60030058034020030050041c00122071082c031403642182c0a580c1000c0100b202c0340207907015941d0602c0d40d9141d4407410080d62018000c280141d003402c007240c00304010303c650386002141e21030f07840180002d0b008500b14689c180c801c0d40c6049520422042000347e03000500c500442d20191158000d803441d82c18 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 63485605 1250 63484355 63484381
    0x901030b210321040c0302010c0206210f010b1306030b19080606091e010302010503060f03190308060303090d02101103040807082109010c170f07120c020d060203 71
    0x10080a10001d090003400188a002c400f8280220030320700c0541803030001da50101c11180050b600a004601c41520a00c0507501c1000c5ca005010b0015007500d203450104440d151074940b490300d0401c0c030900300c00c0601c5400e900f02e9100900415078468907034102005581d00800c08002442401e0070306698080b503c1d003c0c0c40f5002c0c104c502d500d103100f00000f165555a40c5644030502150094810b8168000107114094100c1c4c0315154005807148402040e82036a00569603a072011300741950099004810940130f80d8100010000c070154502038140c0d40e0460310380640500c00161105110760003e0041014079258100422115501213a81c01c06011201380e060700e8428401004042e2800000b8003c1180c080014007a030840d0165421100008e10032203480601000f02c100c0701003080c90405c03021440d50300c2446451141d5000351030708400b0785140c040b00000ca034014a102c1e500341401041c00710a01c2001248001c04600b0750502090480143e03002503540c1d04000c000510075a804004280c20201c250 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 63486855 1250 63485605 63485629
    0x50604111c0612030305100501020a0804090f060504180507061d0d080904020a0c030e04020703170702010f0c02070603050105100801060c0804120f0b07030e071406070b0106080f09070602030901030b 87
    0x12035500415095804c1c014050601110100c1742c0740340700900018039501c0043e100c00581c1c0c2025130a405e19042401c0000a0810304001059041d1542004192588c55201d40401c03540c8200501c010301c0701c18a002424091241d000005003e2141010f85603280e90000e48111310000315034156008460b40780040d4103004550b1090340003840400d01032881504140856005806a15015206032140d001c200c140d204201d8001d00141f481c50000c00750840c0320a1141d0007248500000c02c040d541d48402d9411521050707010401071707019010811002e80c140c0b10322800b411007601e21841c02040500c0c05000c410040c40340300104500c60342c042e4148909102960040d091813040001008040e0400081512244a00780d85880e0207401046070f450203886200c020300c14280c00f405040f45001c85d004090944c00384116000b000c100480d600060032410080d01800c200c0e102e00e01d807810001c10610000b00c0080c14810641d121320014041e4540010980e144100246030104901c028400800c001100303407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 63488105 1250 63486855 63486869
    0x30315080706020709090201120b030a0501110406031a0a0b07230a060b030105090d0f030e060a0603050c150d0216120c020102060a2304030e22050604111c06 69
    0x902004500e0303480104484044580a9085403c940e849070150401c50b08210402408611520400c1c2c512a81c590440624040c0040c143e444181c003507141d00d420f4a0a2451100d0740381070010301480710340d0b0584215000e9012003c034000b14600e9982c041420b5a20a0003006103499004c1004010492030208024010052601e01428000c40d501000d0351194800402c50b4014108020500315080500c40c9510a41030031008001c0e01d001110b00b6138424152810071420581c82d19140341403280c0030003e0074001c2d045c01200180181c035508046081900b05d0100500c20b5982e05245d5240c3c88440341550307942084070400583d100c01b4810042e501407400303400248906021081c41200e16004041c10354032500070307002d460859481c0700b204000c6858a80c01d469500040300805008c3c000840941c40c4e010303211342080002c1201c0c40c00001d00b00140c0a500d2003845000c002421304001c0580034440e000310781503034184241e18441603408414001c41d424028030301030402d010302c00c01c0c100341c018400402d06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 63489211 1106 63488105 63488141
    0x91005070203150a0f0207032a0503030106030c0504050d0302160b031003030507080904090c0609080601050d02100915051206060f070b070c0b0c19030c02030904090303 74
    0xf0190a000702299130b88030b00c101040c0b9500c000d0400a020b0b454080a5403024a0001c03041c9804541d41c1c0c0c00d4449040b00440003c0700041901e0650b51103050104000d21041412103050003140c0c04181d0080c003502c941400d05401203140740501003040780368082c05854004c541c0c2d0600c402c1d10461101c1751050810000300c0d204102402803244a8007005251002102c001002e46682c200c081d203080394854000c01941d50001090801031410794080c140d9907240c600040c41000d5002c801034029803000c6080101e4030712601c5124040d0090302c1c008548001e803d000204945c000c00d44c0d03040520604004034207546420f4090315801000c8464141c9084415540c0140b46000a42840e0602c40e0440c0003100003442c12200c03512600035201e00c1038694480d00d000040261a11100c0d1043c9860540e891408580c00b000b160514102690b000ca40300790140b40807401410154245106420 = true := by decide +kernel

theorem cover : BRFrame.Cov 63309355 63489211 := by
  have h0 := BRFrame.cov_init 63309355
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63309355 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 63309355 ≤ n) (h2 : n < 63489211) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
