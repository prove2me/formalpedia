-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0867
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:16:39.883283+00:00
-- url     : https://prove2.me/submissions/44dd3ac1-e708-4b7b-b045-a694239d1675

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 155755395 ≤ n < 155935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 155756645 1250 155755395 155755399
    0x230904060209090112021201141b040f030507080610060207060f0e0307030507060f0507050a0f17030108010902010f0509150915030108030a08010f0311040504081c09050118031e030902 81
    0x2c03a13561511240341010f242030318124410902d00c3c0ca84101014113020b210319003004212000d43e03980762080c444210b03088214082070700101c00e105c001140c04008803101c00441c000c0014201c1d5904204616041150080100361280c485d60401c00c207895001600c142140c02c1c4aca80158001b0007180210b400603164080c0707a5146c483e002c0013105000010424404403a2030341c982c2c1c043c0c6100b2001c261003034001e841021305181c000c03642e403902041e04c81e0b02c800709040c0302d8030489140d4818020034543d50342017038002045980d5988511b10455030886007481d640010303030401c42c0c1040d003201c0010300320140c0a003000541680c0420484d80d02e8036407402000500102c4a00303e81c807981c50701d04c1c040d601c0e000810128001050384c0c0001400280c0d441d4250b00b80e0350007000700100008403200344406048054411aa40c181c20000d05000b850340e06442d00018028100c04140c041070b0342045801d40e41c80000e101300c1d4809940150340003a030008c442100c400c1c0c1e4024052400d00346100d09800404080d900a9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 155757895 1250 155756645 155756659
    0x5030a03050a051803070605071b050f12070b13050304080304120c05061303060905151306050a0c051b030f0307051c0501060c020d060e030a0201060f230904060209 72
    0x52025901504824030401c8400070401440c1d0b00c0311012180302443c01449010f9800401c8940c0104001d0b4101c2540543c45003080c10803280c08000e02c2a030303121811340c292142c2d0400550492010002c3c44400c1104080102c9103003401c400791170f185140100a418a403008542e000581c00300b100c180151002000c680043d80d0701c5d1596001c00249070030110104994400f01d814021a40b46010000d07140c0900c50500c47e00c040a0456aa28000702680d040a8403d4800c0c0b5003d8140840f0451843e8858410b405108001c0700361440c111050310030207045030300740a0900803580c0c017169010054030094207612051113255900080c40c98210302c83c0c010480019600001042000360300180148070304031164a92204100c0c00354202d008441080c029840054031103114000507150900c03410710717418080c040000304180c1e000b0030f0900e16440b8001ba080541d448950802c11840c1f000583c000030000300182c0b088800422041080e0302003010300341481076006801180a02c603151b03040e5103501c44054800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 155759145 1250 155757895 155757907
    0x1903020310020c120c0d0c060e010203010f050132071403030c0703180506030402060306040e070e0601030e0a080f1312110a05042c030f031510020f0709180503 70
    0x503030180d40034101c0030f40d1500c54103800440c071503a02c0e011601031480c60700184c224030705c1c500c8040f220001809801e0329219103c1000024204003032000f10f000b889450913083d00c40740790070009445101d030b0f00c08564610507082c143c90900b0819880010540700015815541c5101d03911741052998000701c1c0b0002944070110811003185900002008400c2c041d84501d5074141141c2c00e0003810034824052542c1050080c00810010708004002d1038000400034804244031485c013188070301d414110b9201c0403030700d003a24080c400156018801d004412202e580a001c0701c01150711420500d1007040600d0790341a200041c10050400c4188103030000e0020702d100c00491030310070704001c1d2442d02840580303841980c81b400006130074a403900c01d03001c46811038084519846040e4031080e5030369070303080c02c122414002000b404800702840c0008600c00c81902511803252000c440078008402007209002055602c21407071508100800144c010071912594404500703140198064031026010000050440c4004180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 155760395 1250 155759145 155759173
    0x810260714090609040c0b0702010e031c030605030c09040807230307150c0e0d020109051801080f030403150506041806020a0e060f39060f09060c040519030203 70
    0x807245018022034101e445510781c101000754000040e0782c0106550050b4000f000102d4012020740012070050410590803510480801e0901504c00101000220041043c00d03c2e15054440c004c007415041d0001c1c811000040c0103c0d00d14040a000604401400b051800822090001103039411220b1030380256200601c202c0c65590782c02c0110129100780340b00000c80620500e5114429614500d580d400140380a51001c3c010b4203150408280d04208000c84045020748075200e194058904995280400e90f2600078079904002031440310454a4004200400c013007003101d4003030414201d260300000b81540b5004001802003541c4540d40d41c10308528103820003844000c1d0f019103404105030f2641e4140c00312140030403490740f0503200501041070007400501a03c10b6000c191800c14004002c460341ca501c8800c40c010020b00340070ba1003d919600030402c11051703d90098000350070402c00002041030b800c0001540085000740e018950041e18070140d07002c4075000300c5511034010740d00602035900a40325010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 155761645 1250 155760395 155760419
    0x90609080703030c0503060d02010e01020120040f08190b10050d080a030c0801030803070c1703041b06030b0612040203010b130c030614100f05040914040209060108102607 75
    0x64002c44e16102407110720380e01a1045a214900040008400c584030780c2c015030342c100716444d00904642d0384001e0782d08003c083c0070001400003041215207481d50b03c0c21a0701502180160403260080d0401401c907841090340c44807969083c0d91115206038a41d556100740300b030b203803685e40c404c0358440c04d1750318940240b224460003015071907040c1d602400144203010040d61895028840200710780300400005d88900c0c4541005042c4520506034030b421003101c9200408140c10a0320161482c00b01071940110320820f405100000f0101c5003014010703000510000780c200d0064084014032610035400240841d542940081d1850000070444035454030040e400d10001d10b040749880d008207103003000c081100308010300d44903010900200903541862003144200c0b80325019150150070702209001c007250200d0a40110381444412208902003840e0900401c1070102014100c1410300c0030b1030003404003501042c04640d043c0c8404080307511038015599611380010303158086c1142d81d4003d064010a1a81e5418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 155762895 1250 155761645 155761657
    0xf0d1d07060903110906090606030703020405180f0117030304020607171803070801090525180509011b230d0906020705010c0302090a06030c05070c03050607120c02190609060908 78
    0x1480280c1a044c00c0188240c0042c103640b542e501010b244c5c0010018a400d100442c2d100e52145405410305588601145d40c00031520064034141c2074807010007482d4480d4480090043c0194400c3d50990081c250340144c9038480544060b0041e000024a00d044c0700c01801d81213982800c103d10907644480e4048021b03109240312070070074403a000c0c611001034124014001d00800d5038100c1c01600c41a01985078103810344910004100340e50f020004001400b20b011400d61001c0700c014000421180742401400d07003100d290941d4035100a50140c0740900300c517401407001042c0e004500e80501c00043d10629115640980d00082410608101604003000115009000802d201c5d100034010f04400440507400d80c014440b246402c00140340c0c007013101d14805c3c0c029041c484c0c142d00b001446c1c00c0c0e00c0e459943da07030103041e003040c0c469602c03103002d01c01c9441e40090100010b450042081000704c4441d10001d4503006420350790002c1a006460040c14407402e41d2041000c1d9078046410030070048945020a20780d0044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 155764145 1250 155762895 155762903
    0x904120302040f0b0714010c021f0609050403050a09120309061d040f02040303121a0603180111190906140c070801061d0c0408030a030504050102090a0314120f0d1d07060903 76
    0x40300d0704040180050040c00d00723031075482c0c018001980d41c0d002c0303900d606441c09030794001d000d844003000210903d95125440c06503009903540f070b50707030143d20f00050311004941d48665041079a0042483c042680030190b8026507030301e07240a1402e1200006c9203044103c0e4000d1665110717240000c0e1801b450425401402200c0c40703074450750701d0508800c07100000c81d4010b0a02e0500c6403129900883c25103031840046501c031241010710190b590700380400d00d0840e020410f04411420000a1812101d83c04c440b050181e196649000075005013032020007400a442803122000c080404200c07094030850503c500801380100c54000c03c08a90349030180c603202c00c0120001062089000c000c1603214081c041114280e0b40550000c43c64400040c008400510300100103503000d560a2000400c0381da5048440300c0298020109505a14100d0300030300c1c05c0410460b201c000347d401c2000311000025113901901c181c40c0c9102400200e900078982958903070100c22800707594a029000000c2105a000603459040e40d020b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 155765395 1250 155764145 155764163
    0x2190807090801050f0a15120f060b1c030f02010914070609060f0c150204050d050c0f010302070203060f060a05090a0606030b101704021906020105180307020904120302040f0b07 78
    0xb4a005080c2220000d58984c4590913002c40002c1c00800980c001c1d504030b0415800c10074480d030b610500b001c1c1502c80303020215081009003d20206002e428016070200786011100710544641a00d06618928040d1000a0038440d5449803081702c18000e50140c4801d54000714050000701411000603203032503030742c0903020206150340f40105120740700300c8044804a0160b101e400300d03086251589100c4403422101314405a40030000403485031142c40451004520490040051190b41e901700003190781900001810907105120881c056a00014056044118004030758484e460342c40209107954113a410164100703542c038042c801c014440d584a4411122140d07410080601c4603400c2243d0030002c1d40f54400040d0301d02003105113844000210640181c401801c090822181c403115980c410030a40c480b50160350350b1020041000050110407611103900e401644c6420150390001d0080000944040c180c0345900580c1e58075a80079078100da000d005100016684a0b940740702103030b00ca0f40b01e074000316a1540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 155766645 1250 155765395 155765399
    0xd060b1201020c0d0c02060715110c0a020f0f0117040c03081c1104030305030c0c0a14030903120c0d050c0a021f020d0206010609090b211e0601080d050309010219080709 74
    0x4800c10724485c0e2176030f000b020b492034120a034a07407004002c90310f10740e8200707580d4501d0400c032001c12002c01060f444034124098480d6482c2401000908040c0e406040d008030815865810140c0c3d00c07010050807009400360320003107500c99040083ca81d00b41340c0c00c002d100c248002110200c3c00d4030700c000100005810390017400249440c68015010740a030344002808a641030000c039403100207a0307000d03018800031041200c52012054071005a40350720000d01c2d03100c1c3c0d040021280c400307082c14018084140042420355140244442c40d45a441017848440c10810030081044401e456051107a4525650000d000c1d4020002e010a050b00c100d031043d040350058450740324a034113100e001044044c120744403604d5100c013251500d00950701404144000c56400b031001d800c1c445210001000e00710b00c1001e04402401030a1a800342070810106c1c1c0c0000e81c00a9100400400145500049000700400769151640e2a43c50300580f0b140a80100c40c844001000d140800e480380d02c0e80075a6103031144284c0d656007243c1036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 155767895 1250 155766645 155766647
    0x4020306070e010e040e0a0516180204080309010e030709060b1305030606101d0301020d060602061b03010909020a17010c020607050403030e0d02030f1c0f0f05090d060b1201020c0d 79
    0x10b4220582140420315420f070b0121949016400180711410090680360030021030b0f503520b401d2502da0b1144451036421a0030900c10020502c051032000f4100500441c541420541038a990340039640f0524100310610f4a1007115440c00e00c080c600401006905000643e169100d1604580140f00002c3d510039041400180c0c6290018400380200400790401242624010741260100249881138148400c5c041e10ba18580c2c034244010605484030700700c001070903810030130001d08010003d0700c0e031018540d21114205051104c94111383c111040b80301c0000b1075103101d2002c16450011903010641e450810780c0c104100078810740010a045c4029070a41d41c0c10355415100380c0c0e80c4d0040c1c1c003015000600c20442d116071810108040c40c0307000c4c00101241e003400e4002650318900510003d4496415074080301c80143c0540001e09a0308d030581504200760b0103201102c1c010080e00039035158601c1103c1115150b0140702090744280004000508070240ba1955404143d01079441200515035a01c84e40c1d903c03200d0a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 155769145 1250 155767895 155767907
    0x30a0e060a0c0f1d10031d070306050f010810020a03060b0403080d0f150302010509030a02060301060c0b0c0f1204020111060901020403150506090112030509092d0624090907080402030607 82
    0x14416800940107041c11131042c010700520b02c440c1c00092541c0d405281040d540b82041c020140c8440c2d10042c00c0e42811480d0500590318043e10b20001d0b038030881c005000c0910042555800396219080040c0c42d007e281c0c40071000b4206d20780c820444000c00040103c140641d400040816a98028003840080b05242602e03040f1000742c2d5a01c40625011842400198402c0000f010503140c01021a0401e08854002030826031081e44218080356a0390314800801c00e0700d500c495480382c03102c0c003518105120150240c0051142c245000b01c12000c0600060441e13004211810810b00304004a5031a454080030150003580140010385480407240032401007410540074280c868240a0b107000c0107a4a80b130044014000c0c01c0c04100e0500005103c072000f26207520802601c070345068030021a40042401c40ca0307801407132109044a40c0d5144008015003034a0b400c0d00d400c04611541214041c0b8440251000d0882c042c0340c0c5002d0340801c14cc420b205c2440c0d0300200ca1401a4021429644d080d1510000ad03201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 155770395 1250 155769145 155769167
    0x2d05030f07090302100c08090402041d090d0903020108060d06050a1d0703021302130b131a0901020703021c0c0e01080f03030106080619030501020c0a03031b02060103020402030a0e060a0c0f 83
    0x2c8200f180061701080f070700c90039800d0907030f80c41100c0e03d40c1480030030400541130fa003064100c0c0900003074141e000c01c05000300b007d260b60070015100240c01c04008620008040c2101c17408040d040c000600d0108106440c0d04a000e11111b410100412407400e0030b00050000c0c2c140040704144d60010030044c252941c002241800c11281e0050030302c004003e9204182d800f07034004024504080410700360018030040c01e07078014401450144e401c0e104541c20905142a18000801e0000c05003505001a0009903000140c46054a4048a088900c98050740c0c2c808140d84802d90010700d0400d51007000a50191401d161506885202d03050b140c2c042007407140b80d581d07400244141d0780012400c1012840d02e0910b402b00c01c21a1400700e920211150b165200c550a907441903000da81e032603001d03d08400070b1580c54841c07150080300b441c078018184054901d0095903200f06000282c07043d40e000000ca090116164040340c60300990b2815100246031011401c0000d0207a9a4407401080010440328982c1e8030070071032135003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 155771645 1250 155770395 155770399
    0x61305040b1801140f10030902040c0302030f07030504060209040204090603020913150b0402090907051b0c01090e131e06060b04050604180e1f060e010b09012d05030f07090302 77
    0x8143c1c0c608040c00680d080c0d002c5038541c000540c00030080b101c0d100c00d6220303403058440ba1004165012144140000c46e0010300001d030401d4814810303c410b030142d400d40d040d0000300600d404107072a2100d080c000000c0c4108410a170380244001000152040250001c8007164001c0b1107442072565860f08203070142541caa401006445100128655150310340d000092090020304014100290b40d0003250420200f92901c0700030403000b0540c07410042c4441184032503001c503240a05510280140040c000c0c07001c80c003445410072412000510024541035940c2580c40d00301048041c1920800203035026110729174029584103041101c00318212002c20100c5044810103410546000c0ca024403400641d0a000140c0f880e241d2140c01c41e4400c000c0030050301002c0149450f52003180c000a09440742180c5450340716858800d0301c90f004100c0c5ea4141e005841d48000282490300c05101c800d8404140c5188400600c885240c1041d02d1980c0180c9c0500074600c50625142a451103880c0e1290a9a0103d0b417440029 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 155772895 1250 155771645 155771689
    0x105191218060e0c1804030905150405041a0108010614090a030305040501080f040215091206091b0f0307050d020a440607030c030b130e070608040c090515061305040b 73
    0x1703100d0110030f00c5182c3c02801781c580441d029460781c0009010034100d4641010000002c10144058a814030581c417640e8080051003c3d414002d41c000307003000605118a0003448542840c0300d03404506141290811070380144007040207900e80c540540160414060766000844840000d1400c401c0000b4450240c0d4000b440541e01820790442d43e0303000d910a4501c2c91f00103401c0241d24841c0fa50410000b805000000003515106000c58820003041c410800e14078401c004240d0742c0080d5032008070364901a90710542c1c4001003c0d00d10b0012031015900d5030f00c020300315402801d90000c079488541000c4201c03080e440c2024180c0300010742c60441c2403170761000042c95401400205521780c2c00b90303000d0f054200031800d0206d0f00d850a00d0000b44001040c0c0d40600e1191303107540185034881401e10409008e000e01c0e040850203400d00d40c5464403a180d8030301885843c0d07991000130400880c0440340e02c00280030005d04281c0c0d01c10714402c7c440e4032070040f4440c580c081c03420000312590a25081c0040040c0b03400c07070720080c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 155774145 1250 155772895 155772919
    0x40b0606071e030e09060a0b180406051201051f06080f0601031d030301080d142d07030c0219062c0904240203060105191218060e0c 58
    0x4801540507441c200c07103180600d410340078a981c000d6410baa1981c002c0c0c98101c000341894013880156070004100621501100c20f09001400580080d100e601c003034101460b220341d4601c00410b00804081d088194050b0340040d2180c0049015044644101e00c0201d100f60510f81c5180d01a0400405005070004103c0c440005007101e5030884034135600c190145404641501d03c2d4007400196000310010440303a800005c014041060200300e84c4490b080300b49050301251405001d003199a004588940c064103403048075564908924407074020780d0a0710016007564031203035031034050180c2d90b80b20000c0740035411000d054401941441d030443c00710760840d11403882c42050a2401e004035265500042e508400c01c100c4041917842c3c7d043c3c03d5108500c614144000703001344040071601c0102070400c14240314010020042141d91000a5500010490100e0002170f9900300040c0d4440400480c14100a45040c0b04082c154014250729180705019001c20005252170380c030001d0303c0c0d200a030100d9030450241214 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 155775395 1250 155774145 155774149
    0x40e190c082b0201200702150301060306050909030307021f02040f06030903030b0d020306060d0611220f0b04060c050c090403120b091b0a02030c010f0609061202090408160c0b04080105060108040b06 87
    0x401b1070620041051090210130f4244203440c1d00280c00c08030009585a00078001c43c00c001c040b058000808200550552601a6000350388050030320160325009503a20410000c0581074050358090051003071a20003442d00c40030000d00070b150030001a000030703040200340d5166048c113070a0703164022340140290204ea592002400b100c115541c0c0d045449a0f40c4154824210708000c0240c00fa04280107402044000d00c18402400b024043d00030f42c6001150b005c00700300300724245003150100c0b501c2d030904009203011410b115003458401041c0c1d6400c6419003040204142c0c0c8402055015030002e642007060903100750500c00c40d41011960301c200c0800d5550002d414003010b101804408038144102c0c0d10b0039105840050039104400306440c0d64035204d0000384100440c0e4000d2102a242c5003c08881d210042e0300040c599540141000e883e4803070016903540300900aa048441c05c03030b009185030409030b81c2d0300e692400903400b038401c0c01031135440c14000c200250300c5041c415000d10f41207030f0001078a84605007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 155776645 1250 155775395 155775397
    0x9070618030204020f0a081b04030615030203010c080601110309060409020f040b0a0809010605041a0d031103040b0301090f0605030a12020a0b0a0c0e040e190c082b020120 75
    0x280c00110340c440800000040e43d640c001080d9082648074400e840b4a4001800f4014500140070114050b1401c50000070b207021007415501101e030482404a11860305692695400c407040d00f021f034040d420114022010342e0002d107014056182a41c42c04003690000d1851a01c900990344116486a001c0104101200054018003081c2d030805104a00c1d0980e02c040742061a80320743c6031000454030039410000e4604081c4903c0c1e0042130251014022900c43e0500b06050540c0040700d184100c041c021110103140c4900480102c00503034008480d5102e4481d2143c206640003403065241e4242458803022600d8080d024080485001400030603141d40d0f140d0b02c00c000000081042c0c41180300c1c015120022079100d5845a00500f10007030005000d0240900080100f990074480d00d0045041000c12844070a00003490b056440d400d0724034003005151fa18290540020640c40380c00e46101c2d459a40034401c03c0e10b0b00140c5074800e0700400d540d070324144580980c00e8a0038007000b8002613001d800340c103451950980c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 155777895 1250 155776645 155776667
    0x1020903060a15060534061410090203092107050618060c07081611030c0316140d060207050601260d2d0509041a060f0702030a06060305010b0a0905090706 68
    0x1029013010005118260f960704250381e170541000111111003034041c4541f92040100030b03003101c550a21a442c00300350007001260207100c0c009003a40c1c0040010440d040602c500b804c100c0e60b05041038413030010510031318100e8001890035503090050402041500951301d0452488106c240041e2545944824203c00c01c1e41020308103880c1100100840f40c0d1145c0b2680090030039611501c0581071412111003414a48142000421700a92012250b021b100c8031601800c003c4803a02e1403407822501004000c55440004040d00030034076800803614608000020402034181d50020429904500128002003640311a080395403400e60840d41c1901d5600e41708200d02130701c5d00c40e4030510b504106c0c038501d0b40c940c0030710216609130005003011908a00038a400c1c05030b2040601c0e0b03161000c080d12507030000034034603100307450400104400001c0c0410440d10140801885160050000c00500741d0300d040c5075020308492a56244503810020b03001c03a950015101e0b50340070b5400301c030041014608001041d10910707140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 155779145 1250 155777895 155777917
    0x1e091406070c0e060607290f2412100204031202030a0c0f0303180302010504050105060111031206040b061305010801051203070311031308070801060b070f1e0b010801020903060a150605 81
    0x40003440080b880307c0c42c0c0c20005400120545003d52003031103103104a070901034a502185011401444400782c140c20450a01ca804110051403040036280000e416130005100c101c024010038914416114484c0e000d4406c480c00b038102c030850a440c82c10126164415456070901040d8810160400301e503a031884080641d1190500052440c0b03130f004507142c024480c00040700140e45030340820003001402e000742500a0400c0c01d040a8429101000310344a0080e52041090b6010071800502c26980e1a08081c00c240005000350380e54426203084403122040c28011240480c114400020b03d6061071045440d801881c2ca0240d403c1c040b00d0390781165034224030b0040f116035210500c0115a80d0504503605d40007415410000c000c19072410f114182540c0e400d40c00000c03042c20910100022079100b038400b008455000c103404411014001e90491114002c14011f04441c10fa5400031072040c10540c01056144411402c80304590f0f03441e0040d40a982e6002c3d02280001100c03d000c018040c0101c0107000c00034a6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 155780395 1250 155779145 155779147
    0x5040210050f040b0f030709090b0319051203070f020d0c020105040b0313021201060602070e0603030307050d020f0708030402010219080d0b041d0d090b0f191e091406070c0e0606 78
    0xd13a0380390030303c0b903084156840c50b502000000d1014050700801044001d010701041403015031401e200094403500c500d40b2130070004002c1420307c41003003c00e00c40b003000c90780e2407000b0070385034103015500901c04040c0380765001c050310a04010482c214014007a19a41590596406141500b0900b40c165150009410385d0841200e807d400001a61606014148144040000250386141c060001e00e0010180e00c07648840c03601130180041d686000c0200c0707a1103121400c00640e503090031a03800c0020310964507104e001101c08034501042083c0b28005500640c000d0b1b0071180080c0c22010080340d51055440014141081002182d82942c1c464001d4030403c00010800245003140c2125100e10042840308540160030240c50040400e40041d0941c002d031108071002c07800c18030300c02c40208052258041c403503c00c00d20b59580c8a405e07417240344548080080d0341281031300044020b5019004100b140998402c90b0345804091607942062002e403a5201d0700501102c9003189820102086040c0241040c0e81103030b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 155781645 1250 155780395 155780399
    0x303010f0b0d02120a020c071406070803040516030506070e01030219030b030a06110403030327021c12080a0506010c020109051c051e06060103060e1501020f07180f05040210050f04 79
    0x1292001381c45244c80c0a000b5a54890b40410395082c4107854005904a14003a1030085850715440107545a03194400c0c0456500e8545050a920f0807806001c00c0d0185240b054020041110104005010f041641c60301e10134020380c0b40040d416401a0100564051203005940d0401840b0f60050700c9003881c0502a62200072003a16000280c0b205205e00c002c5801300083c0400426505110720031019134142c01e200729905000313082d6000f040032281e010f4401c3c0361080d45209110060b002080b11035511900003604883c00d110040d00901080301c100030064581000510594020303a41c1852003581607403a20209030400080019000040000d4040c0100844040000880402000820260040b0120202ca024010403803400c000103004604040c1003032070400800c036400710b1031900302c455414034540210071800100d1400414000509840c07149403400075030700d58810b00c00005000b00c1d180511802141c1c641f010240c960558009402441e0041314a00e217030300c190007910314280d504d0584d0785026 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 155782895 1250 155781645 155781667
    0x9061706040f110a090e09010504020d17040e04030804020307060219060515040c0c110a0b07030c020d08030a0c02060a020c03030c0c01020c01020706051503060105060423030601060807110303010f0b0d02 89
    0x1c0c04c0300601038045041a4003d0100300540b41c040380d070000d110300003401945441d901080880c030041d40000c1214804802d0204041589010380e000340059010406051505060007028405c0170b41d000d9000b030040c01c88c0810a1032011030b801040401e09021000d90000942e143c3e001400010300c421007046c410080a8000c2c0c3d500e0084217003100f150b558007104042c0d1401c0865503e40c20001036445002e552034200002000e2030203440c03071103415050210b10105103001241c000004524002e2424400000b041a100c50f1580042101103955084814030ba031851050422482142110140c039401480068000010b410080c5456191000007500b00080b88408500f66080f8a800f140d5560f19602040a0804814540d00e20007208034001d0010394500750100784984282d006540d0f84005404042015070841c004c1a182043d0240449500e90395600009001d0402a94101c0c0003030340111001030340308400000e40c2d041c2d074540b03082444540c1c0351031b000c50041d82c000032210700c00c03e8082c00f8100400d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 155784145 1250 155782895 155782897
    0xd0501140106080f0f060a0506030a02070606080102190e0f090414070b0a080a09020a090f02130305340e04060e030a090807080d080604020d06170d09061706040f11 72
    0x38101501d409003d4182644510005800108400c0c045c2040c0c00c00c120f0140d4569656a007202c80a9940541c0d070b45410318250084d04c41c452010f0303c018205600020041015801132100f0040f04c00c0ea045203100c2d03404200d072186042c601300da611225040c241621807a182030320320782203071140c1c100030144040014614201000380d4441c00c80e000300410281003558000c14a254020403c190401142c0344a90000c0c0c2c4181450150a10300c50b9240b014200ca01c0070750f8101d0300c1110190165007405682da10b0b1403a9124001008100b901480c1060808460f00c2c0e86501e101c5011640450149076060101041c004480204191880c0c0d031992407010002c0c1c020b00050003070178559034440303040c9030a0620591818540358090ba103144d001300800031a41d9402985540c200c04100c80150362041c0c501101c0c005001b81e50011038182c1c2c500c03c6142c0001100050314030b00c2d103138640c4405038290781d101c4060301d82d20404101c8034291208000001d90618095200e212241748212002420f2090b5000f0404a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 155785395 1250 155784145 155784149
    0x1103011808040f05090112060b03100e01020306130501030210050706110c0c01090602070f0509040503040801060f23090106050706060317070b09030c07210501050c2107020c0d05011401 81
    0x3407240018207100303000c2d0044040020380001d662031001549451324007034403180c15410240030196104101040c654040c0300d204412800342006002e041e0794901d00385e00275401514a00c0c800c41001c0030070703810000d80b4014603049903001855007400010300042965103600c5124106e84140c0d89140400b80d81c0b0184004d8001598142c00810340190034000140500308982c10640955200c00810420b0103074110700c0c1c006554007a00c0d501145d86030352820a00c1d40c011504881c3c155403c019012a0112818185034200c0d062442c2d0394940c0c1c2d8682c007490f014424454241504501150700500980b4002c00090624030312070302001900580d81e8507010400780403840f0880b200d00b00000d0100500045009041d04131601d803025500c3d14280840e8181d40700c02610405400d924030503040c1d803500c1c034200065410950400300034030691420704044412a030080b998803040d24038103034915016070480d0042ca4450801e0b40c000b800e030a04008100094002c20403000c544230764854000d0301c980e030030540803540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 155786645 1250 155785395 155785403
    0x30c0f0301090207021e0907030903090302030706030c1806020a060506061210150921030203041703070c060206060d0b060a030203030408100b1c020d0303020f03041a060d08040311030118 82
    0x2844007800c0c410803202100403106c0966559405980e800a507a1702000103400c0403090a00142010213442c040d036520003c0ea20207581802070680005034141c054010504036a01035076403d2000d030200e5078140043d201740c0100307401648a1003400d8000b0f03000780c2c051030f0081c200a0226042507094140382c0505132040b1030401d81010521010001c4d50a031540c00102e0090608010000743e0510f400100d89220342e801042e4010003903100001814024012039000c0d24204a00e58501c0e498800c140b69aa8800340045590030280e1000080e03103803000c10481e0180f0b600801080c030b1620551241004503801a007040c2d03014900003070020040c1c0d0108010001000c608000e0014441c15601250848081c600303800d00611107041c000c103110000090790000507034100c2d000c0c0312200141c101100280100e00101925080000500c014842c412648006070000c04400000710740d110000e001e000b2803514401490402d040c8010b0000880345091200c00035005000082c800c00900010401c503015800259 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 155787895 1250 155786645 155786647
    0x60f0603020a1215180b04060905060a02040b0306010e01050d060e0f090d0c08030702010b040e0a021207060903060b12070303050d0f02030601050a1d060a0504060e090417030c0f03010902 82
    0x21400d0032020b5400400040e284a80c40191540392000d070158040600c89606030380d5004819040603c000c0840380c0e6401803910443c500d01407a0500c001c1888034800d5410344030701b0000465081701402150159200c05a101c0d086444d140015258110bc1d0f41587d81400720078400c0380b00d807600703d00c1104000c000404100d0f03c5030400444038588042c0c0034201c4c680d5a0480d42c8200d000355005002500070a034042c410990b00c3d514170b40201d0040421342da06950103418000345a090b0080000c100c07410340d008450000a480e44002030303603515901c61080d0000b0a02528041010034055806400ca02c07001912400024000e218103d003041e81603081180803030000b10744080c1c0b0381582d103c0e14010020f02e1104502d5410041c0000c1c0182c041d5131844420414801e00314803459610500358480a217014000c141c441034001c0c40a841d5403c140501c0001a07050318012043d80783c062040c5000d01d0b0401039030b4003002c108030150700895000a1000c00e10480402058030400c00d400000d50003041e11079801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 155789145 1250 155787895 155787899
    0x905150f0f0303040b070c09020a080105030613111002010f0204060203040602070b031509092d0c0312040e180a060c110312150f1909200a081003060f06 67
    0x4050803050011481c00361600075540c0d100c5840000454040e02c5944080d552510414034003544003180e01d0f0404418a030010400800c00760708011220306a8034101c0070fa1f0103507551034150340c900c45911a0301a00c0c54814060813549402e10744aa0101c00720103100201e9010b5500500d4016a0703c9644201c005900005041000f40d0307043c401c880281c03014105040c55800d052095001510417005810301c541018004038451910800240c00f170a100d02e10700203c0c24840c4020107200904070348106c10180a100705024031850086103c40382c00964814403801d02d4249036288031079642c0284800a680349100c9804c0e1440c0080025008052060001040d290580768000703280070014000701180307610900560360320000d0f80e580258808450340304400808003100016084c02c000b0b82d040f64100714020709514554100c410343c1006c0d07800704901440b03100c43c2240c41d01d100090b400607020014a0500c072101d0400c0c880c10446400440b4543e90841c0a5100d45a00045643c00d10700306e20129910343e41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 155790395 1250 155789145 155789149
    0xa0203071a0d020a0504030b0f0402011b0807140f07080f070b18010f120f0b040b0a050303030a0c09030206030108010c030e031c2c0d140f0711010207090515 69
    0x30308007404003419080111001d144a4901038024003000b008080c2c0c02141c1e20140c944a5400e580007541c028205801d03a04000343c5000c0d0760f070b070161400d90000d20181031004480d004070903144401c6034080c41c41d40c5410842c0d107400e06040c00c00c81c8580d082c0d000f151b060b02c1040908000c2d10010301008006400300d00c8590655528002d442d9001d4448000c0601c1954040351700703070203510309681c1c0a082c03d501e49400c0000032202094014491301c2400d2030038031450f0300201154000c45060b0300603103041140c85011002c000d41c4941620550740d02d503208100051445800c1d40103019512218100754041d1601d07540002c0264209800440a40c0e41d41d06100720540e030715016003600b02c1184000f0314900082e001003808404104c0d0110140141c0341c80d1300c2c0f600c5094a4521615401c0c0d03880b80c40d01d400d9800050b285e00d81c08034500700c000041030317580c000600c4401003003140d04030b03d890040245070002641d81c5d44100880c101680d41540200c6600040074032482c018548101010561030800c01c60b8241 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 155791645 1250 155790395 155790403
    0x405030d180201090510020106180c0221040302120703020405010e0906100503071707050415080d03020301060503190905011e06140a030b1f06050304120e1503130506090a0203 77
    0x150303000d48160814031800142c1d810201e95000e9840a588401b0349120058043e8007501060780140c078140305141c1c82c1340851106601035080040f0030b9003683d8801000b08030703102e001880140e48110880c0204401c10051810884080c0740540b00707010340d100701d5070381c0d00003508440d026880f62a1384842801046500d800900c0440d41c00005000070100b0107042c00003095565185003c1d04125132500da10351707101500b041003000f00409004109201200c1c00b04080c10600401d8414008240f04041c0004003281c0030740243c9060340d40942c2c4460466451200304d040c60752010080e99001c0b80d0b10742c2c003800030170301c00e0152102c0354010080310a03000c40c4000d0f00d402140c0b09503000c080c2e510b511600e02081541d03a00e0116044a40000f20055180c8446003400072076545071303142448080c0c08100000d20745030050090343c0b0480c020f49a041c1d6454006d40142c0d1001010103071290301403040d010b80301e403042d1a00c018541000c0290744941c41d611040e0768861400d42d041d51010f10641c000c00c0300d0021031070200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 155792895 1250 155791645 155791661
    0xa0b01081b030a0b0105091003171306020d0c080d020d09031701080c03060f091204081b0402040b1606020919030b060105070302070320090703020a0809030408032508030405030d 78
    0xe40248412843d41c0c8030b14140711410f010702e912600c01c060210700c54103251320f00b0101540d001000d4a00b24280710b85a400300e41d2001e00d0251600f007010800033041c40c004541c008203103000d80c0f9910301c0034100c1d948100580d4020500c9500d038990038061013400060318887d28894610030b444001d40c200441e00208850740050b4800011a0b101d2600307140c40e62404500ea44d0801080c911b00811074a85484203810f100070fa0004811007000401e001812420010314443c1d00d41c4001958219212044140820780c81640a01c0d10001010480707103800e280131a481e06503907401604018140b50003200000c61118684802c4004400f0481040c000c1c40010014284c03c1b010034280686130070050f0358040d440d22500e00c00a84072800b002c800b40c42400d68070040c0c1032018801080d82c0042e00d00800050001d4010741d1540c000542e1820000d0550301c00007049800761080000210b051407500d00003030801c07865116030701c034611074a1b06542c1c00284040c3c000d503001d54401d4001d103486091284003c02101c40603 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 155794145 1250 155792895 155792899
    0x3231305040626150f04060c09060c0212010617150f13021003060302032406090403020319020102070501110301290711030114091606030203010e0a0506030a0b01081b 73
    0xd0300300510000890043c1c6100714140240401d9415440c0c41410000362684d00d04101c1e03201e1301040b50344894010b5142c0326500c1039408028400c168481200c01d20306c84d024017404550040f0103140580b41c400c1d000541062000300100d40c0a8407942c08000f440903910240761203900c0101c05400700303460a43c00a50106c800b03820179403a460014010a0641e00c1d203803000e4010740c5840c110002541c441c1d0800c502440e001350840e40285062090346103d0380785a592002d084115401003107003480d0081459024035095801117081c022030352800041500380c0400e56055641c20480d0703000252003800b542e646105500406a140d40c9850010102c0d08000342c080700342224000c0845c0b40d0441c84005566400d0b81118404503201c4004011900400d002007501c44c9000468007046a6440c00107280b240e15030705080e6440c400c95561030180d05a0000707010b00700142c03074040b000801d480442d51103180d0000c40141110740d0015651500364440d5400e82103075a8642000354451441116100c1c000d00c14101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 155795395 1250 155794145 155794151
    0x606050a0f080c0403110d060c08060f04090b04060203090a0c150905010801081b011b11100e090402100e0603010605090301051003080712030e01020408030d1a18040323130504 77
    0x8070f00c007021810b104034000100a03409111000c00349441c1d00d80d161018682c4003404002c40c404050000c0c20b0302ea400c451461040d2500f081025007400c10f800b44604442c1d010083d02034986803641d400010b90001080b95040d0301c10000c0c907030042582403a00d000108040c40c41e04e5050350168800401452854200d01d040c030800700b00410144c00c0001d62160f0000203110101400c2c003050b4012130b92030b80d02810014000f0700004100041c0b2050784030001160310308842d02c8804140c0600c042e151084100c5910f070740414080c000601504080601c0c0700502ca0b00c3c6003042001d4502c0001400c0c0350420f800200004601040c44e40d07080c2001d01c84c05800c8504062940106450f42d618100308d44034540004024001d403a40c00c440e034900070f0f000b018261082000a5444a4844584070b82ea41c0100c0250b0a06d241490001b005141544850652600340a00a541811003a400142a11a01400403010480003160302c506445440ba0903108443c0440461540c85017280845131148031260005441146 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 155796645 1250 155795395 155795401
    0x1b03030e0414160c05010204050a03150509060712050c09040507080711061014030c06160c0b030609010b1606090c031b061b02010504031a10090c02060a0504080d0606050a0f08 77
    0x40d18a5010003944400d01d0306404c280d0b540e103000342c0640242d501c0345400c80390240000c01000184070b004507412101d0142044107642d030480c016074908041d41c0d640040341903030a40d44d44070480390700710b0369108103242c1071179140004a40104084a0080b00d401000510b01c1c414011000d9110790f810b03890098074802001103007001d03c155101c0c400070340704e0410048610300d10a046524144980084902c00030000c5443d22800180c84400000c4894202c80d003030050900410500c0c004002e4901502c4068910140c903820420891210707400b021009042d1158038130b0220000310307075014868806100e4400d2030302c1d0b98a1480d11401e10384240c04110545e800c60305007440510b0780202025401c40c8000d51002140d9184e000684152181d504040e14280011005000b28461180f07068042d540c00705038001c0b455921385078101120080950200141c00c40404607000c603645410068103d402124114507107844109000212041ea030700c4480804c00201d08080404d421200180c0703c1c01c00d6040c40c0d0003500d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 155797895 1250 155796645 155796661
    0x50f1e070f05070906180b0d0c080607030c09080705190f0815070f0c26030406060f0602120306060d0f140412030b0102070e040503190801030203010b0111030d091b03030e0414 77
    0x6118034040440b61613480c840340242c0c0c0c0d100342c502d200e120f80001e4141d00c9d107500c409000307072504801c40c1c02002181c201101540c0b618030404602040b1480c0c000a4003185041c4820480c1c00c5102481d080c241c91200c240103d6486d2890612a0041803404010100c0c0030600c0354860b14000c00510304014043d5401d00c3e8104a60070206010036107034006800c24202180c041d21481054500c8904403450b5000300030401045255809181a16518207883c8241c0d41e0b41c00c02242d071031240580110444600340045003035814110007030002442d41c0712000c1640600080b120742145c0000000d94080c0100109010600032107401084500c0c001d894140180b400000020b5503541c202d200311010340f280d010000d401c0c0403007403064503c1c000702c8400c0c480410304000c40c014850342080c001a44654070348501000198040d541110384011110051801d04082d4440381d0700810302c11034203540b24045e0984241742141c00c1940071000d0f40c425101c85006008000174001143e00c0308242071040714810302400229 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 155799145 1250 155797895 155797919
    0x9060807051b0f010c020a05060c0a0512060f06120a050a020f1e070c030309080601050904150c030b03010e0709050105090103020d08070302190c0e090607050f1e070f05070906 77
    0x50312041005182804041c06514900801c60303c000c40554642190802c1c0d0690204131041c030103015404640d09500c800040039180d02c14a54040e012400c10003211070041c59204209600c03500080181440d145004042051a40116051145001c40c50100f043e041458420103800c912842c60840c2003100001c203072801c2c0d1066100f00f40e1a919954114500522410308440115070b015a8400e825592864041c06031a0030303008211483c0101400403a49040450b41144502e03003000c0c5c0b54111241044141005150391210360042548442e00c1c4449500d003406200020b03c403010090261600e482007100032a0410781150344100c410800420260303844514420300ac6401c801d000359610b500c0c0c1b4003a4139080350340040c0c00e01c800f0300113180020301203958880c00c110381402c402e01d07183d030303988440d02500c8041c11640540403440c04d000c910301150800c4007800b564000f284034800c58101c60150807510360048e940894505461700080410003c2c18454a0020821200e05012070b83c2045160303215 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 155800395 1250 155799145 155799157
    0x40305070b100b0f0f1c0605090a0212130516060e030f030702061917011805070509210111130503011506090b0f0d09060e010608070605030c03041b0603020405010906080705 76
    0x1071518040342c1840d985d2411401c9400d207000c0540c440da640a8861442405070410b4400c90340300700400000a000300c0f50038000c035901440d0761240480a683e602881c10001c041d48403003a11113124001502d1000005482c41c1c6014180540759000c2e640b01400801d0315002e015444c1c1c14068000b030000c540141c80d8402a81d0010240031101c040410011000b21020464501040d0140d51030304000540e10a101402980210b0107803018486030b995580192070501c40ca4144581060100040110003030700490b1700810a1070341c00022564100c00c02c00980142c100004220065001c0c0d0410170091809225070700c411090300030311001c0c1524000015010031900e10940c3c000490026680038140040401c032034a0054000c800c02180341c240c1405d10041c030251022072115842c1502c00b00307503102d00141c04403c07144155543c900c0c43c0d1b116048030710981c1002c0d20459070200031400501807140b09103800f4002d00300c0b9540041e22140f030a00014902c440c0c6d58009818040000180000300c5e60010407540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 155801645 1250 155800395 155800417
    0x8030c0c0918060c031824070c020609130209030a030e0f01080906011502010f050f06090604020f0901051309050c12151c11030d0504091a030604020d03090806040305070b100b 77
    0x1840f5556400400c0d41b08101101c1c05465008030350720014040340961a0180c09124061180b031075071746010090f41c0900d01c40130040d5002c5803c0c0040031441c61b00f103c0b01080480344a4000d800c1c03951060102c0e10b40342d80344c02e00b20040780003010781c05100e05050b000103070144000d20b02030016080c0b41410b1a1524010302030341070000a540d04d2041094003d42141c041d5003860002040b0340d2130700c620000000501074550501c01e0b09244081600c40c64180203851240000b80c1c03405280084040064400b07501c010003042180c1484400014483c21520030544102c0500500540c1e0b83d182c030385000f02c0d0010042091220080b4603014042d2a10b50301c0c0e807940003440b9050078990a82881c141040d514604c1540107a1510441d4000c2c502c6980c810b0290088489003441402404408401150f980ea074228030076406610800c0001d01619003d4001072702031380a07052401c105c98030303100a1414030504a5042d0f021072000910f60041186075505182c2c00009100000000d50604000d241d080c0300d01902c00c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 155802895 1250 155801645 155801647
    0x10e06100e070e0d0308060108090a05030a1d1005120c03040f11030109120f0906030b03030706022206030b011e09060815042f040f09110408030c0c0918060c 69
    0x50380d80b6016a450400900c1d0080100d0003c2c44241340080c10140110703501030000d1594030101c5c50046001490304186503021000d94205101e01c2c1e4221030542006505010000a081914049032a04402d002046280765100c81d91407031588a00840001e01a00c0410803100420410011032400c000f5090603917803024a054585c0036450009004d0049110007415481d40d850781a114107800c80c43c003e0500010b9265440070542e80c18003a41244c00c02900c540e015007041050800099180e070040100d10700603030300e020024007040d60030250074840f90099004a40d8032200c1110541c1c0042c0c50020412090f1000324140780e2458004141c003820340310b0395043c003208902007010780c588280c45181140c00544200320b1448078000450310b92482c58200c0522135000c0c1243c0b510100060110703070580e14244600081c0754038045641c0300403c000590560514001d20000c68021000e0000f0201c1c045400000c01c0039a0400d4100005c000014016008280901d4050407050b8008a620340c0d1010030b4400403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 155804145 1250 155802895 155802901
    0x11d0715050c010c09030510110d0209040e0a0503071a0c0a03050405030c0a26190507060204360501050d02040207020a0503120301063b040b060d020a02010e06100e 72
    0xc1d1401d0094806039401542012031a80c042a0701c00103542c101c0c1d0040341101d4040c5c2c41541000d048440345020142c0200007001031042415aa4004105244000e000010090118096241006040c05080702e0580002820b0400d022460031950012030040034020500d060090080d00c40384240c0400509060b152000902404828410381350004101d00903035030000114507103040307920708081c408081d11056013030361011400701c0c501f0f07954a802500d002210688202da0142e9042e044070000b05c0b440f6400304004074080403c06600300c0c80700c92050b0542d40204101c0c003d80304603a0035101d126131143c80c0500410803540c44400440c10180c041d0380c01070382c48029001103008010b06400503038040c4504110031500600000c000e60403a182965007040c54026801000c40000ba189125202d072039081007030360109004691400803156008000080c2d490083c808942d4642040c4a2442069400301305040c0a0f902806229000752420780a030605240100d1078070300401c598062801031b11030500c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 155805395 1250 155804145 155804147
    0x60103051015050a17070e1915030e0d030b0a050d0c030c030b0403020f060402032e0908090f01020c13020903120f09011e09090b0d02120f011d0715 65
    0x240050108400040c8140a4441d400b401540c4282c259000003480c6000c6003000940c024040c0c6d0080d030f0725568450080507200100849181c010412800d0188003640000b1031001910b000580d5480946001c41e417140200c1440b410000032945520a0500380100c0b442190ba641c40660150b410442c0d640c00055010305001401c0d0307640f40c0000f05600c00160340030040c4011010340c984601e10a84c210f03111040e42a201c0c648070b94083c0c400940551040864800c02080180d0f107130f4070941e44020304004c1120104003030301aa19141010f840c8060300180040082c2061000707514045804c0c00182105103034200030450001d1060385071000b0f144d012803020125030b41402b0001d0301124040119441c1c1000e0410150301d83d02c1052180c0c00715844500701402d032010b1031304810201107a40c40e00a0001d00d8102c0c000058140901a103511164921003c0010385c2c0d203014904030303c1d0642000700700303035907207138290600b12020303c05030092801b082100c407481220005880004d81c0d0b0f001030f0b003540d032401e0144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 155806645 1250 155805395 155805421
    0x1501060f0e090c090901080a02040506030304031205072f01030f0606020a0615050a03030302120f0403051803070b0706020c0607030e120a0306180b030c010e0607030c051212012c06010305 82
    0x2c09170302907002400040d00210004084050f140219410811908c0345820103540c2c0c03080d0310004002d0311101085002c0c0d030340500080e01c012402070250800c80101d10021120b06070005074090382101550070340711400e507814850381408941c5c884007085400e00700300000c0d60740d0421f94401004961901d100e86850b000c9252080010b000c00303030658210076143d24001d40650080d10f6081071140c420710020300202c040300c10442c000c1d80c141d203400b480d14051030598a81076001c004100d4051290b50400a80b803d055801040d18601491006854a05c0c0200c407a00341000949004109030820084080e00d480c0490003800586121080c1c941c1c600306010150003038880c991240710300210303111441c1c140820300c4c0c11201c0c1c00c40c400c80a0303d0040f03ca030340040d1142e4a0390301c002c0d80c00c003a00b03002c550700190258181d07840d103601503421510050841c1240d07010b103500004000300c01c441d40c10010410180c0070301350500c07224113220314450048400000c41412840041c01d90341016101c4020400c0103058032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 155807895 1250 155806645 155806657
    0x1207020612010b0c1002070f0312091415060301140606030a060503060c0705010e010606080a0c03090209040501060e07050c06070813020d03091409060a091e06081501060f0e090c 78
    0x1c021407400d50ba5914440300e00e82c2081100c034039140034010318400741c80424400c541500754003490401056006480454981c00320300e5021094075034404001c0c0111b90700107928101d21047c0d030014880c980503000340800880d40900202c0c0030341c3c140b03c0503000041010140c103900c01405d5903140e4596890200c1180600182c0d0b01c100e425001c0c2505018100002000411b58640201c0c024004500c40340e407a5402ca0b0840d104000c0058122000308400c100a600324221001030b500c0d01182c40003a64000a0244205550807a80c60f0354400c03042104808a5008540c06001030408500f8400d11408540d10b50100030302078010070a070000040c44540031180702810b02c5130094058569406c0c00d10300600b20117420f02911400e03580c190102c42061170890340d01881400082c0c8035220091420b100710300540b1603000003d0021642c103200b50740b0303441c0d5849603800a12f100001044c04521103c4010916401a0042c1c0204881d81a55047d0305030003407451a004c540640b90360805595060207040280510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 155809145 1250 155807895 155807917
    0x5160302131505030604060b03060112020c0f061504050705041d0403200609010623090a0207021f1403070203030f090f0f0714120d0c06060f09020d0c080912070206 72
    0x1548407840c200c0ea01c80d021310b108820903203007007001640381d0b10840d02c980411034100c0d0000c1c0c250b002201030a41182c014202d4041000f0840d83c07104280c03c0071900f0110300b151031170804011018009030f14030f881c0c0140c503040541400c0c114174040c01e010818940c0e007444010903504c00c5804010408040c45a2115201601d0181d21800a624100c0388217440b50300948501d450b030741c02c04101040440380311810707065152000035407040c0342c014807050080c030090081c41c00e000d90b5800d0043c032001d40c4810300448440f4516981a0f0141c4160030400792205140000d80a0f50607400e0040004854001040300d4000500000590455460001c120f2602c0302e0360740c20300c02c103000707102504214100000700a01503a150b0019841d4600700c00d000d10012900601c0d644030283d00100b001030ba418040e000c0c3c846101c1c050b08020404030b840710b4000707401c40c445d42d01c45d09080d5800520600d40fa600780c811802c2040c542e1614070b206081400381d9550300e1159140b14101c2c0d0300002010030455480c9000c4a18400320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 155810395 1250 155809145 155809169
    0x41106040b0a050f0909010801090506151012110301060c03031103070e060c07080118020f09090307030f05090409030c031205010302060d0b030a0212070312050f0a05030901020d060b03060a0503010516030213 91
    0x41d032388514042c00034008216154802c55010564078070b042510360706c2610f03000c1d2a524101c0d00078681103401114450794504110355030080c0b0f00a044100f0011806802e43d9200c4032070300c0ca803514000b0112010041001c5201409100f4090b41310340c4402c605298090440c1d0164136880e0b0000039034141007055010060f658a81801c04211b40c000301e20503044140206c850240001212051289611040b1011003154008015a0700064040c00e000000d0012030f28081c2d0500e41e901c0080b0301180c0300d162068020520036000c0204155100e134401103866a181e00a01440d491607005c16198000c0c034031403000c2d00351140c1d84014251020007441e100217800070a1051710301424607103030351210102d000c01c1d140c1030a14401e034010103020303104032490340c40c182c00854a002e204d81402c4805801c0034011f08000d5408000e4090240581d005903405045242d12055407420300e80c0800903044120350000d070007030f41443c04000d4001c0c013091104850000c581405640c0380158026800d102407030703402016440704 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 155811645 1250 155810395 155810399
    0x30d060905060a060903081b070e010902191b0215091302070212060f010e0411060c070e07020d090315090b010806060405060d020d120302040b12041106040b0a050f090901 75
    0x4941c1c1295000c0c0300c2c03c0d10541e10341619008111517048040c00003514004041011014400c402841c5d0441c0341e40520a42e1220754540103c52518582a8840c00c0556000b0030700d00343c0441074445480c0407244c1410000440106030000c1e00140c410041c0184c450b0a050200b14404140902102d4a240004180c00d0756130000c4092103000b9003000744180d02071004915110301c05034000071001e006803150440c2004036883c0075000c5400c910000c00448070500d100540385600e0321020058148245010050098941056188905d60100030304030300c115030240b603a00d40e100f9046445030042e40c0c5c21041c0341c440c0202c00c2c48107001a1040a000800e90942e04c0d0000603000c0011841340d020f590b08540c14070850310740d02e0810100e00b210b02c02c040c0d4080c06d8280c606d000101c4450140803440000c1c04c0260415030790f07003a460342d0b40d00128a40c402c1440d00300100300401044000100784c00f8001c8170000e0900e401c241c040c42d654000d001504d002e10a00050081c0400024401e8812608000f00003880c42e60b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 155812895 1250 155811645 155811659
    0x2070f0605190806011205060f101d0105190305060d0c0303050301060f0905060a0804030c0203102007031b1704030305090414070f03090807050609060f15030309040b0102030d06 78
    0x2610100b82c030b00da40c4101002c048052407282080301d008500c1652051380402203030001c04001d02025203c0c41d444802018040d03019214148280810782d51a01c4843c580d1100d4025001c0008140381c0144c10404d0400c007200d100064000040d02038550b502c0c00181da5522140452000c1c03c000c0c80141550907554800010154001c00440c1038554554603140e070051440b5003134a50000a00410340d01c20810700c91020603620400c6040d82c0140a0701e081e140081282d00400d0400700b040543d541c425490b5188a288035200c01041e04880d0101044d5514010881e140189100c80e0315080300324138920070701d41500344110701481d046007a9480014a503500e070340b441d01500c0d036400b05400758003550610001026000c1e408000701c1c81610591210280d20b025000c040303008104443c0115001c0c04244560004120200002031092048030014044c0c0e0a18042d58520540014000b00c0300c2c000c500d051000c0c5490201c2503074100c100c01d0304d010801100c1000141c0c214021900b95081e21031500800040c60 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 155814145 1250 155812895 155812897
    0x60103090510181509051204140609011b050f0f06090d0806060705030408060703051e0f06010c080706020c011b0c02010c0305120a0603021e06030c033402060109060302090f0702070f0605 82
    0x41481b86e0200c4a860809010030601c0f030007240700b0f0441554003140d0003d4582011002440e000005160550a08003032038010104404100706c10340e041d60001c0c2c80b001c00f00034100a000000041c140040029281000e0b0382c40d91141d80d03480000410280700003246c0350b511508103840f1a03c0d485401d483e02c60380c41d0030419a032180119040b1001a0600010550f654040d15034100b40012495443c0319982c3c6400c03010a032001d000d8139660411001940d02c0c00414020b074003a20010340300e4980076a858810741340c1c4030b00b91803c0d60078005504240312001031031903800942e02d2420b00d0342030030301c8da1080c1e0301424183c459004050144008034030020410034100d40300d900602c10b6070310840d000018a030710408115811251084450340000007080840d600b03850f480051a4450394449070714030002074030240303812107060310b58540410f0b4149000e40000c1e56010301c05540900343c1c010042100307503d50f40024040d00d0014041d050300ca092503022a03000c82c070902c00980a01018000030380340c43d40e11807000f001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 155815395 1250 155814145 155814161
    0x50c06090a0308060906010807030b1201090b04020906041e09110406080d0f0809030406080405010207082101050904080a08040501150f03020406080102040b0406110f100b04050601030905101815 85
    0x2543c948001281d40c5801c0d25140d01548042c0d40300111a560503c0a9004124942d4007580c01018040142c40151090183c200c000e0b200e80070801b000e08151040c01001c24014000e10322842c181941400600660042c0b00c14184110340d02181070b008071304040c405046861245500141041c1000c18001380c0001c201001d00308070342d501c00b17810809502c1140e981d00d05852040203900b04000410546129102541c0c2150160000518003001e640e03c1c43d00503482a07512a04c10001c036181c0e401c4925413410054010700083d01d20682c03e03e01581c0d022000c0c07185103114030501a208010405010003540b00e0303252410400c820341d51203a03c0c4c55869901c10b03500d1004900c41c604001c80411441c40600944048400b41d1084604040c10440141e41d914213034004440c551040e0440c2c0480e0b81e504010700e080880b00c05600045095100e014401070301d00040002c2c0c14181000070b00c2c00000c00016407130340b150007a0600012282c80400c02440304801400015000c03407650500c1c10031081c1c20b5441505 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 155816645 1250 155815395 155815397
    0x30d1109032808130e070c030221221e03020a0603020f09040501060504140402040302100c0201050f180117040f2004060b19020d09030b0a02040909050a1205040321050c06090a03 78
    0x45c00d0390724484212a442065880240103812000c80000100c510b11802ea403e400c0c050f000c07d0030088000026012480400103034080f21100000400a03241c035549101c0e24000c0e5405041c06c00c505540105e1f6400d5440d1150a00b05a800112644c6c6c200f1080144c51030b1100050090001d942d4070a4000d2990b040b501581c22500e400f0b5210f00d080c0c1c5072030301c21501160303400741c05000120160001038881b0209443c0c16814018100859059800f005000f000200c1c0c802401070071250304040010010407111640c058403a00401c00d0001007100a003100b014039a1181c5d03010004104860009030402c450000079800c0f508026001c100e029802c40541090060300c1c950142c0e251a0940882c0d45012050074200230407103c070020701c04600c091541c1c9601c40c280d0f5101518195540d20924102d605158085c0c0e00c9400c600382c22410840c210f5001141c0c2c040c0381c54003600f0207045490304980c090b0103c01c441100140075050450060003102564401c1103c00c050315060300e8102043c58685c3c0114204070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 155817895 1250 155816645 155816669
    0x12010905070302090a2903160206070801030312090302010b030a0303090b06030d080109090204140106020d02071a0f1c0212010906050402030408030a020a09080609030d110903280813 80
    0xa8000c40c40780c404e5030b00c029401842225003500d040070600720703c501100202408103d900000c405051158021070280034070009001029008420090070500080c0407001000450001000031aa210020940c4a41500400284020310345010390040402c040c800d9003500410140c5400d05070194031151243c1d007e1074030f40065030f4a440415444270580f4100b000468500b400510004130707180c0c0300d600e400d031002d000000c082d200402d007946a880c00343e02481c01030b03008804014040d5070600041c40140712070004441c0003003072051620980d001d820070403444501c0100d0000507040b040d01040e582003e206404560390310380781104400c229005d008002c4424144040021181068402c0b01d10594001814605603144d0b01d001202a5100e2000c1c00c04019900000bc80e02c0b5000780000c40c041c07050040203581c1da406d40c20013038081c3e441d441c1240d00019028826110b80380c0307011074072400c0795a03101c44013007060f140082c00c2d080c5641481809069407002203280030b0481e14000d2000182c6144503002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 155819145 1250 155817895 155817901
    0x23060f0a0915050409080307180302030a080403060b0301060602061612020c03090111030c06040201050c0a0b07110f0601180e030d020307030f05091902060903070b030c19020304060c030e0d0812010905 88
    0x1000c241c41172214020981041000018030b501c3c03143d2125034000904881c2005601d550317400181c600402024292103200d0005410000c0145600c10404040d0301a0002e1119601d4024003030348a20000305012001c1d0302c1465059051881400c3d003440101c51502c045403a003810210f090303625007003401105c0c00705070642403a51040342c0c00000d6401e050340e1400286103030366580d401100c00782c01c00340c480c94261049000c0c98001034440740c4c01c1e80c424600b9640d842101e038001c0f20054a0004084081030040c0c000d10010303c244501140309402e03840c3c041c800400c1c41c030308840c0f5052541c400c510400820b10b20101c18032086075815001003001c000a4041488107803911003039039446080c01c0040240c00c911501c152401410018098900400d005054461aa83da01c0828a06030301c01ca51107039046000185ca44000c1030b5800a0501d0514188001c5090905080c0050110112081c020302440000101e4806569038944030f034020b42d900c00701e2903407106501c090a40720440280241c0da4024140000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 155820395 1250 155819145 155819149
    0x40f05041e240f14240f0d050403020d0e041107080906220620060a240f0f06080403020a031b14011508010c051b0106090516110123060f0a091505 64
    0x10f42e8880c04243c4c2480352070a24030305e8000c40d03036200501100000005205500d080341e520b02ca0700d44240d01980180c05401900700004009441c44981244214608001180040803080a440e000355100c0501a40e407410440050001d01501c00008a40000c4210410300f40103604560b00480e5141e4a45d540b4604041452562010b5000c00050385c69110704009401c000103a0081c44601e0b040c1c800340380c40900c07140118108400319810101c2e0081c88190f040011207050f80307086004000c01d29007140c07581050303940207444001e001e01c00340c01c20480382c003440f8585604042070318003158404ca41ca44c41d9040f040400e400f07400409080032266a42c0c14000aa2042c18001c21401100aa85080c0703400764084180202407914080366030150745e40e00d000726130303111070f071113607034019200c20701d25411784c006180005007015000a080c15440c6d040400343d40307120b491044e004500d101c01d080c1035401c0b40e4500021620b0303c4108102d2030342c08524000c00050740d821551000d0f00d00a040540d03042000c3c4c5902c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 155821645 1250 155820395 155820409
    0x40503071214010621021906110c03060403020606010c0c050315150108090c100201060b13150903020d020409081e03180601031a0601020a1205040f05041e240f14 71
    0x10845c1800044c42e080819986100d800840c2c4952001305200010180c0308803020100013240c02903130101c0c500d903a20411a20041050004000c0110024003d500d8240c1d00252102c0e80900388606100148071703a9010026105c0c0020082c005c0501100d5800242c0c0c2044181c1e0042542c620003180041070100f030f52540305482e00e61041c2c03030300c1000b08014100c0d00c00b405022560792005000b15540c0e400c012584148041c001c094001c2002030181c486410004001c003c044460911001d11211010400050b180c201000305c0c0c09030100c500003400d48541c00e0058040c0700e900d035101e541c003e50f10017021059a00001a5018030010074142d5130b40185140465503454003070101510728810301c80c2c010600c3d40d0501070650711006c1072068030141403280d541c0159000302c068805000c00d0000c2024886001c0b41e500c49030040104071003d2000b003600c41860400140400a412406070700c13503541151500c002c0c5003592146100720420b103c85640d507d0710800f059228001e40580d0409200e5900481c503141c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 155822895 1250 155821645 155821649
    0xf040905070e0c0d050405070914071b0314120f010909081b0a0203030c06010303230a1101150b03010314010c1b030207030f030206060a0f1a0306060405030712140106 73
    0x90036014100900c003400400b008040a010240030441450065094003e0038000d51154004040b600c1c1094410001e4801c0c4036103405100008000300b120903030b446038403804006241c0012210a6030300341000c484003111885004026200000c600013500000300859100d031903e00800c1c081c070b980b00c814000540b40605009800d000c003d01032503820341c2100c0c8240c000c4607041b504486a0321b9040d8042400c50b00007100c000c4064018100401c24150010392a1460900c070030343d00c091803050814521105e0003549401e20030461017494a0b1a154000d5114001d545521300301d962601e0750f5001545103540c02400101c0d0074540b0705940b649400070501480001c582c1603120860341c0e1340306081c1070a00031061039040e0300b14455241e00202041c40d006050304114080e0380078004901c3c0c43c07000d011000c1c2c055407250140d0360641108102945401c40c81030f84411000080c103940fa00d0342000142603019980005031b150140007000140504d02d48103864040d44200880f0301c0f4140701340c1c4020700b241c4442c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 155824145 1250 155822895 155822903
    0x1209170f0f01060602210d110703020c03010504031403190509070915030c031203230609060d050303190605030d030207020315060901090905010f14010807081b010c02030a17090f0409 80
    0x2503041c46410a119001d1008081c6d11850081c14120182c00ca9010340c0c54401403ca5402400220101855410b102031104103109038020f1045003842e54004003511f0103003091504d0140003201284092110780000702011800c1c1e541400503081c08404036032100c0303507482114a50351812541401c450300411145007281d800c01044800036155440d5005d0274081d580c10202095a0b500c0e2644807581080702241c0000150149254549080018055003410241840f0f1003038080e11400b40c002100042241d61081d0007071501403101200e21880e0340a41308a400ca00d03414016074505450741c0f545a401303081c140740203c040341c43c68020010311614890302561200c0d082050300c0300600074101250410b034501403141c400068040e909100c40030440c3c022640c00504421018010022402c0800c00000503104a4018000c0c4140da40c0141407000c030003143c0e242c1030002d41b0b0100401c1d03680c03d0060450381600f06d580c00d05c04d00046a4440748550005843c5481985510902955030815100e17090f002d581c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 155825395 1250 155824145 155824153
    0x1a090f0d0207150c0816080910082e0506030a051b0f0a030207020d0f120908010b03071e0b0406020309010801170a020f0f0a03030305060315131209170f0f01060602 72
    0x81c0d5004c9640784109001a02e04020070070140b085200e8550110410f01d014115041d1643c5110080180c03010b0b2003040442000f070b51505007c06880708517242d682525480a1501c10200d0000b84402c148420781d02c0294401c4020040284440302c5411407841207010000d01001802003190344100c90003452085a00d5030020300804006501035402051418002808c115600d100c91740d941c10300308080703d42200c240c0ca50f40c0a400c07070f40d50000c040d0805400e0740310091108907040d42c0802d603580064411130b80001800d50701a00080c3c004040c1401420031103102550311516544069030340da2000c0c4043c0c0c00160300f00000144402e49000c1c02c440e100900016000c0d44145400f002403031180843d405902c1046100c000308155907509030301004510075100462030b45491020503007848100460b01d10703c22561020040000d4064884418040e03206240c000709152440c41100c058080f030308603124002d6242e01c41101c1035030000e50b02d190fa0425104903405d004043c5c02d041c5c2600c1040c852600540c5c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 155826645 1250 155825395 155825429
    0x1c020708120a021501030303020904050c160602030a090506090a030905010c080307030f0b0a120b0c030c0a08190213150c0c14030a02060a030501061101020a090306091a090f0d0207 79
    0x30360080100034104140c4104d4448090020112910200a900480120f40e0004009045081c640155030380940002e150908040280904004465030204010582e90340040040c00e00101980909896a00f2204031115498002c0c202603403100100000d030042504445c00048640c840d1a404110b10380c084c5d215030030b54444407400d402a203280c0303a10140551716030121911603150410004020702e9000e00555942c01141898460074801070301081c41004200100200c1c8041c2c0c10482c0c6192002e4544451141c2d034018040720418030020065030640e00005d941d96954076104644030035035440d031100c2890905046410740d0a0440b01c580102051120b110410a04192540300c4d031145501400345c0303615103000d40c0020056444084090040790741c1c2c0d001480b416621840c820780304810100218981140088090561691484002c0410f80c035100d08404019048a880c1003241c0f400b4419482d41c01c0040210f52150303100d1045500710303c0fa290003000600c0c80007402c0d4080b204411000c03080d544e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 155827895 1250 155826645 155826673
    0xb031207030516140a06020d0f06080705191802040e0c07030f0305060607300f0801050f0109080114070e0a030b0c0903030705060709030c050108012102040b030d021c020708 76
    0x254041c015600010100d80741311007003001784141c80e10103210b48070050303590101034045030440fa00c4d140c0c1c00c00d40a160540c01d101c5040002840400d58504a40346a20072071903400f02480018030b50410301411820303080b0304152511540140c800e4800c3d507203027100165103060425441c0d0081c03940103400035004072030711240d0078000e1748a10780140c4050a82e51a007005512400050202201980c208040781c02005204080180300000c2c0d5121514005900b242e207004000c01d81441030240354810300000720421303030b07581c01403400d0380003000c854009001803002100c49410b1a1400c40c1c0b510081000c038035031700c4601d10b4480c5582e0f040e290700c24a1071480d602c482528a405803c0104841e03018401008200d0105400b00320a030711503a00c035a54001480e096140412010b5409d52101d4140f00000700140051750646962414a181d16001c15000759070030700020380541002681640c00d4014014001da003e54040344440320140880342300e540e0305860140499803000380e0700c1070310181c1d0410300c0554195 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 155829145 1250 155827895 155827927
    0x70b07210f0210110324040e0307020301060f0f031218080d020606010516080d0207050a050d2615011e050406030e03030403050703110304150c0b1006020c011215090b0312070305 78
    0x3213981442d101d46c100880020804840c1000e0983c0066400401c0d0234045103003d00410f4040c2181c07806442c1d4803482c0c0044104540308500005060030700d0010081c004502c11401458078054030702c5008100e0740c0d2a5481500c1b0803c3c4e1a03014014040c0b14001041c1e0b50050f4102c80c0a01840d060300300815980780c66100450300941c4141610039000c004410103e5000c005003000c0b28056801341c8240c00c08864090000d045c5156120900c0300d20040d84c9903001004000b0690102c4400c00c215610b1521700e00480720010006051600c130542c038814071030080c1d482400740c81920b041c0e450800841103010902940da0004a034003c00080f420805413000030310500c90700e41140e100303004990400c0e480740c0c1a003009040c0c40034041d0010b82d56000c0401400b06c00c10700c0980110140c8904c050160030031400944550b030322841241804030004607508841181d074001b48a2055601150316081d494102503000b41403020b0050788248161406120910f01183c1218805c0d58107869061800f01403400560007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 155830395 1250 155829145 155829181
    0xb01030e07180f020f120f0f040b150a060806010e0102030412020d080d0c02100b041505060309030705031903140108060708060a090203040f060617070b07210f02101103 74
    0xc50b40d102c41c8484140180c5001406411800100c4651118000b2440a420010040100c0c005160140c1840b901403400c104058000350801d06220043c1d45000402100c40c00e005191034100d02ca488001901c2a40524140e0040f24240e0382d00044a6403074004990f01d0080e40107004e80c6882d000d40364001032624046910125100b80b0409051150010500c03044036180980c09026030003240004080d0003c0f1701c203000c40b07120111400c1200302070441000c100c410141c002c0030f0041c1400004580444d5041054a64003940401201d0b0b44480112034010400e0aa40411001c60306150b03d05681401032541c544c142d072000c40040510ba030f600309044901c010302038507840d0402c078010800b18280005000644c452030142d4400d604d811403e240c404100c60540d030005000c811110861840c0142c01f0640c10100c400d4111441e803200c8040c2401543c044021210400d80c0e14000034002c040d0f900440c0015810b6070903025540b039039102400c140242d030750440240060b440108000fa001100c40d10725024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 155831645 1250 155830395 155830439
    0xc0203120901140306040b030307060906050618060d08131202030c0402030f1303050405090c070317130308060319050f0607020c010519020a060f1406030f0c010804051203010f090b01030e07 83
    0x82d08180c0d500130a080d5405040d061f900d0725141d03204001400dd4038020660420750070f450940000d01d40c200000c1803e4400b4100c0740c811542c40f450f145c1407001040c02c0c0d8850400f0422000041991904c00d070100c005004000c0380240120010704415141c20706c2906d04c6a86c2c0da80f084c51490b40c40c21410300c180e00d00301d03c0403802c0c01000c1c8000300300c40d1500ca8031240b146031401480750703640c1d005080145c1850315480e403104100c2021401c1202c40c042e0b4014140070182c2c581051807860b180c880c0040d08000816001e0205003400d10aa002840381c0010f00341070206031501518110707103492500700d88400104d0105070215804000310f00981010a1940903018040d03c140c5c3c1c4400b419556140a0750000e0302c0c03840466440b0107200244125825955401840440040c0544c4409840039911400c00341e0a03141403007000c00001f007d000003488560b29080002040c20755a6031130700d1040c811214140280b0840f14500850481254000d03c2030701858a0440000c244e12498640c1a808454404856407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 155832895 1250 155831645 155831651
    0xf02030408120c160b180103020c010903020309010807081003020609060c011a03070b030f011a130618050d020d17040f141206040f020f0418030c020312090114030604 73
    0x10520010b20450900841800c00d10b50394040c0000814500414a00100d1a00c100c010082040410402c126500482030b14021401c0c1900040107a00030300500104001135401c15100c0307810964040000d03c06a04242c0741d111003612911012031700c103a0704a680900ca83d20184047c0058a8908080c01841a0050035146000f0491135200d003514840c0300c43c40300f100000507403030040b86000c2c00010064030881340341900f149042040c2c640c2480d010b114414415448041750141840c854040b00d110044806040c800d2543c1d40c0001800d03401041e03907141010070400d80204061401c6002081c0040d0000e00318245045607449400c0d0368018060186001d841c10400080c003400e82d4404800144074011003800c0c0600710310b040c0b02d14001c0d0024013080c6500311508100008003c104000146030b0140d0b00c807000380c2d4409001c06c00808440006640501640c040c5500305548052861041c030710a90a1720220f90801d250541240a001503036400301c2c1c11b19101d40524018040910f070320550090003c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 155834145 1250 155832895 155832899
    0xd080f0f15040905010e0c0d080f0901050408070b0d050a0c17090f070806040b100b160807020409060504050106080c0f0103050a0b0909060901060b03130308090109150906051605040302010f020304 86
    0x102100c043c05401c44059448192801c8911020320103084d03040c0c07050f280400c44070131139074801e001c070300c5a90011540c42c007012a600c2240d074441c100392009042800200c4801940300c100e000080e4201d101e0031018030f03080c00001260f2000c41c1c0200c1c284000d0301d1301c035003520b054807107011050407030020017030109880b8109036070400d0002004010014071302c6034007914442c10641000742c10351031f00a01000c90004804010040301c51102c4c01c0307c0e021036510340348201c43c28a5180c424014450304401a5225003440c05407024001284d012602444c0b142d002040a83e56400241c1e803245807080c6540d6129010460344410f0754080d81000e81c2c018404200000c0048403400007031070000007034540842c542e20600c00c0002e8400700740300304000740c80f906038280e0031480c1207103c042c468030340d00000404200c00c0c0004075640e03c009401407245103034081c2d528010907000051700001480c400c042a80c0d0282040042101c41c80384000c6565229003581d1410b24184c103640066500305403034200070742144010080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 155835395 1250 155834145 155834149
    0x901050a0503041a130b0c09010f050a11010f0e0f0105010e060616080a020c0901120b0402010c14010501080d14040b0306040509190506010314031c0c030e0f060601020d080f0f15 78
    0x22481c424201c82c8001e0417088024100000500001401c0c4000e15600304035840f40d90ba0088092080c0e143d035403034100e5035181d0240342182c0240e44200d045030a90300346661f0100b0102c80f0b8000c038081c090690304580340d4018103501c09003a02c0083c81101250440b04d000f050090601e0f070000c0280340c0d100d682502c102c500540e5403454562040a0490040c0c000900c19690303490900c0100c0d004140c40c0700000b09034151500c3c2c1c0d0078841806030000f414071148c11005e508001d01301c00564001c8102c1c1c0000c016540c3d4a01417680c5031911030300003100141c10b046c10403558052040541c1d0688a00208141c00d598542c2c0c1448001c10018040d01c019114003217046c000024114664070009202e2000340445500d540b80000100c9085102c649064105008011180e0070003032442c80070402286001c581405a0321042d4010580c000b201c10300360040741b00504028800103101e5000d14000e0303003100ca607181168400c5542c05001d032442c0303120500036004184080e500510302e9401402c141030a882020b91200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 155836645 1250 155835395 155835443
    0x911060a090503070b09011e0e04020a0903051903030f020a02100902010c15022502060d0f06080706020102040e0a0c090e0703060b03161d0a05040e0c0a0b130801020901050a050304 79
    0x8005c01017544009000a525684040034980130b1034810003d803961010140c000c0c0680b01d030304440750301440d4089002c2c0c8070302d40318107240d6008642103020360303038031000c3e51a0000700b4518144d425400700c0d041801e2003100340424401c40d0b5200500c1d03409010380000ca2444140a8908060240d0400500c80e044c4800b03d008451501910b1074107090059660b810103074460000040d00c01500c1248024030380c0f120143e103e0000300d409817049203a00080c1e64441d003048100a10701c0c0e400c2100d0a2140c42404141543c0560040c0141d52910750880c0095903005e40b141e00356407080741444c000405181c4200040c1c850300c3c400f203070460020705012540d15200c5440b818030350400c5a8191040c6040d0030150f0300d403a000803c07402010700100c00300c3d49040c0c07140701061000c5283c0c13103240e00844c2d661410990500302440840300d04c1d40001e0110340703540c0e1360300c0b9004481c3c1c001c0d85c1403004d030b032a03245000602d504c3d0500c00ca5030030910607100c903400c09001d24410355161300000d02c2034034500031600480404040d401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 155837895 1250 155836645 155836649
    0x15120c01210c021b03010b010c03050c01140a0b180103050d051c0906060e070c020a12050c0303030403020c1e01080109023709060302040e0c0f0d0903210911060a09050307 75
    0x1034001e10790709207460041190544d240301414040d0349020103082159a1222841101c0c0b50103003059951410343c201454010f105008160249003121002e2080104007600300088540c01290200e0180580041619482c0310a1100500300e500c0450f0a41e0064000c20241244605801e59a00c40c0b803030518050b800c2e95a10310f02124015035403c1b081c48039407400f4000e02d40102480c64822040d14542d400324800031100c0c040e0030070301207403150b91008000d420010518514405000c1d01e0b03c030708141c503020796909050402c40c2d120740c80c501d4815440b00d884010305481030005075544056a4a0b007400034000390310000e0503088500c121040191141000e64006244402200c1030100780032400100034000c00c115002030381090b004200030005010500d220f0382d00700c050b40c8141641d4204c062154002131060440c801d0246041c903410009041e00000351a03400c80d15015140d403110b0302560f50000302e4a100c48001c10342c45900120b034003a4208880030f4408844942001403000c2c6e02d40c40042d140040607 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 155839145 1250 155837895 155837897
    0xc020f0604081201080d0c0303110d1d15040b2202060a181a040b0f0714100f090519020a0513020301140a0806070c02040f020307030515120c01210c 65
    0x2584402158503000628010072038039000d4035880c151501d004002c18143d1f04060704140d207681c9903090b0f40181100b100c103804240541006004031500011030080c0100352030403024000c003080000c024103070203011845a48d103d034a040d084d6030350001000e0b00c01e000b0683c1c2d61801c41c1e03002c242d10040e110365004204910040e2200c0314455809840c1c40d41c01c90064200c00714440c4038126980c1100110800d1324169075900c1c83c0710303403561800c0091803194001c2c3d01c07001d000042d02c1613003915150b10105400050207103101c018000159282c0311403090b6401e9100052840d40000c103400580201c0080e0242c20a03c000c0200340003690b034000003041800b03103550050695500200411039001400c01c02d94400e44283c449510b100d00d4460400d49550009010800b0b2101c0744048004540e02d5501280c00403004d000115200d0410700c00c024020841151703845510b0020050142807417800c06e04014002c1501001000c0c00d0280c80300469040300300040902c40c0074995500301107010158000d2185034032007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 155840395 1250 155839145 155839147
    0x23040b09031b131a03030f1201050402070201050403081b0f0102131203051e160807061a0a0506070302010e0a0f17040b040b03091504060c17190c020f060408 69
    0x140e00200350078114081841c6003034524682c40240b1948031442d055841a10202d000a80c82c40400100c0d40c03810031522055034076000000355070044c0508603001d407445181c9000b040301e813a0707203c0090004030310030440c010380440d0b020301c010000a030102004200c0088181d80c2054402603140042e80741101194001980d030f5004607130318a11074881c1500800508031000d80100d00903864901900ca1301c2503449a051204c0043e80c1059000440300886840c1101100485010741d0607003881c5409400079401180c1c0c0508100710329400c0b2030030011052075610014030f8031070138a18140c104141603004c0074040b0250354aa0104000c0d405c000d005400034180100701c0500c80c00e10a140501c4008103000311158490301c2400244401030030710041e101500c0540503201c4e41c07a11804030840c50010112082551036040400f00010042c083d00036100b4403003640c03108030241c41800306264503000c00301d50f500c4155118404c038480350905500f10700304020407401910002180715885504000d41203405641c5408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 155841645 1250 155840395 155840407
    0x4050103060605130911100207080303070903030905010804030f1211030a05010906061d0906280504110f03190e03040b030702160501020c240c07170f060723040b 71
    0x81140f481d001c104007112040008803803d903110b1b100003820050360340c051f26104000e201164020040d00c400307403410700704803038403031030281401411038100380002c1713002400490b40000d055000340308490040d40d00d5184d01e041c0000c00c00d8211823001034000c01c079030840e807950000d0780e0300c400c2c16000f5030280110308004a019030519640300c0a581d183d91148080003040407a004e41c07005255505016001e00310ba4000160325000c002a0440d03984240e403002074035003005ca404e40080a2001c420071180265400d020100040350200c40c81c4c00384c50281a1500010030000d0341e6602154401c082504124500050309060180214079581003900003c40c1c03008008144a2242d8040040505044101c41c030319408909010000b0744903401c43c0040c6000d07040c0701c0c64010b1344021410340d220001c026403249039151405a11503a030350700403620070f6422400803851210250131000c54690a640440c80c000d00341c50f10381e094100c40400d07e0060040202121241e104020320118004000402c0b822400b1a100c0d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 155842895 1250 155841645 155841649
    0x608010606020c0105030411011218021008060a0b0c190b01032d060b010e060307021b04091e0615062109050c06090f150714010606022a04050103060605 67
    0x24085400410566110202610040c5e90080c2103a034001e41c000c4041d0251565540141c4d0001721002c099400b4070300340003004205401145e005081c56000712103040c0c280c03082d80710130341300e00781c3c1074425a401034580c4a0522048104030001e106100e00c29048600796100d912062141c0c4008039421214030007503c00402c140044881103581c500294190f0f111403c141c00e00f01c140c071284a4000800444d1a5600154540c4c0588040e034103161700070789910380c1e0f40382002009490b00070b40b0152889401c41d01d0503a4105091a1040940a6921141c0306c021403ca4400c140b060300c1c40040e0454006072219001d1001d02020b600e210010031294645074011004400c51111030036031001d40e201081d03d4070f9900c07000f1a1002500c05000c050946520760741c3d114000100d915101c0d140d000307d400442c500b1440b20300c803200308003c0400324012318680031904ca40510300b40c2607808038803c003401a40689541c1c1041c02a03002d0403440c8400c207117642c1e014641c5080c041400d40b0404da2040d0f5200381d032030500f00032034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 155844145 1250 155842895 155842901
    0xe0a060918020406090504090614190c0201020c030d11071a010f120201080601140409050903030108010510080c210d0e030c0f06070f0206090607050c030c01030b1008040507050d0303060801 83
    0x1107428407015410507040600003003408006228007845503842c1c1060005022a50384a01000b04110007002d080e4582401c030468030725aa5403c0a40d00c1e0701d4101d9030391903144180b0a80c3e4483c042c3c0d0006d103251100e40703583c0102403c9a0b64a064100a0130408007001030100512041015001d1546405c80c0d858080500103542c900d42c0111240038818281d040140e2f444581c882c1c0c80707842420708003090b040303043d00b08071140210b8001c0071308da91514092000d19400000070350b04071446a1300901841c0e4900221103c2084c4510410f017841c1d111001261031443c020040c03030745600011084a080031400f40f41c1c9403810384042000030104400c00c014401c282007d000c84007841c0e1042e2076060728003400c8800300308540b0903580701030040b035040a044011903590b0811220040c0c002000540c845a03503040154458280320400d0f4420f114085031041903500134010440d1819000f4404040d8080c0c280c416582c48000400c216180e018030340b00402c0307698516500d01342c3c00340603503000200075007405100b07421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 155845395 1250 155844145 155844179
    0x9010c030506011704062a02010204050f01030216030e220c090509070f050702030a0f0305130f0608041407090c0e01080f0906011203030609110c1501060503160e0a0609 74
    0x42048070130003810103c804440d10754101d54009000180241244c005264521491490b81403408241e062540b44c82e905401810550b03000f1101015011003440040d0b049200380396480515904641c0c1c01400720f4016080b01801c51400b0f0a0104102801840690203410003402d480318a691002541c18056001511502400c010b660b6215030b03041c00785000c2e016040700505001080000140501191024880652000e0788a86900b210202501c0c02416941080048001c074100d64000000d900020040440841d1302c29214580c1d90348494450741c07034040620320444018460894009500300b040e2181084400c129901c0d404101c500200040c2150005841002e4104034501400028500840d00c24115454015005400203041c03809078040c096680c4030b54101d038030340302d1504d00150440d030003000540b280c142559083c0d51031b00c03100044800c0a01640c400250144005208560740c2c0c205002e003c1103c3c100380910505c9007001603100c0b1500d0304506e00180500c20200401584401340e400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 155846645 1250 155845395 155845397
    0x80a0f050103120f0e1c08070f03200102180d060b100305070e042304150510030c060f020604030e040b12160e010b0a0302130b0706090b090706050d090203070e09010c03050601 77
    0xf20750f00f1000540d4806c410a541c1261079102d00010100001d030003c03980c81e160302880600c1407071840c0c20301810780b804e460b222098100154140c40288201807003100c481c04140c80140b4040b11106052162400c820300c41111807a0b0b0302d02d81070b080d956078154800d5003281c0c02d543c00b140341c0ca41b00400410001c50101058021070801c40144d07020315480c5089d03040c00307403108420000c0ba81d4604000200c040c480d401d0f01d0001d0301c0e04044c00b68074a240b003444402e59005909072a00340c4d030350391070850b6407058a0300e441b0016000305010070002031146600381c6428000901c04507005803210002611225450340d000000e030700c600840e000c414000c00e05200103020302218404a503141841080c824400c1003120000c050b0700052407040c0c00c1c0600318501c06441c45698a03600c0d940d407854810300030540c0000c02d5409210250016010480018503402035a1a5580c2d603030904489030f100c0d20142480420880e414060703036002185401c0681042c0e032099400000210f00b050203040702504960014007054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 155847895 1250 155846645 155846657
    0x2418050d030c0e090105130b0a060903021809030a030f02040801020f030a1b0519020a0605040803100e01210503070206030f010e0f0c03060f0d0803131106090d0201080a0f050103120f 80
    0x101c0c041e13540d001c040341180c00a41711500032000c00007501b4004c1c00c450604a500c80c280400101d2015442464003059174800c0d1040980c6a01e4251a51a484030480d0f003801d09910070807000040a102e60044441e1b82002078001d0b040640310718110f07099030050b5440c109030040110030814103070401c1c0519a110a040140780c0100c84030600c00606911950940000c200385007103c1405051081111041c1316401017000c000c0c030b04040c035001d01641c0c0b00361900400d8203450100402c08080d0a034000d81214010440e290000c000c0d06038000341c1c03045400c000d032420300003030200303c0141c0c54140003188501d801e40761300e412560401020410b11180a85580c0039100b0340b500704800416071004481c0c0082007110008504480d140025038903246441c00186241000b009200350134040742c00c010500c0741b2030080c50511040701e809201c0c6034021a10300741e900c10401c3d52028059409002c1840d04403210760008960180003031801c505440080c0d00485840c8200c694403604d5503442002d498400080d49008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 155849145 1250 155847895 155847917
    0x30b150a053402100f09120c0906141203040806011a070c030605090c01020f0a06110f0a0504091103041718030f0f07122418050d030c 59
    0x41500440c10190248000007a00c0b4240e580c0302e100e42c50040100e40c40a0300e403441402c06900c0c0103510180228042c8541480342a96a8001d000c5058903103032660360602d100c1d04d45403005c141c03202c0308041503500a030891804240d8101901486001d4115100190901c08050081c07120583c6100d54890346034200f407100b880036100100b00071341100c0c840351176000107102c0c454214201d441040d01c024201802e4040000410100c0e0300500d01c900c0007101a1000c0c17191071001640c66124603103010700755400c4503006100080d810380c011400d400d50001014104414001501075540c4150001c00118030080303803c0001103510b01404011030407081403103045040a940b0303044240a0340042d8546580042200c0070443c800c202860040e00d8018119045401c4040407184c4510f1007081c604440d02440401203036160841c2402880c1c0c9602800f5208120f44030103d415401d1a03080a07800c5242d164080c514a86100c45003029030113000708080d0042d02d032100c0001c0c00701c1e961004e008091041040340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 155850395 1250 155849145 155849179
    0x60715020703030e010c030606030605040b031005070201060e07181d130204020d09060608010501290a0311070515070206010f031e020603090a0303050c03060d1b05031b01030b 77
    0x105028800055402507240c0e8002e00e4103401901620121404545c6041103080f0b00581c5038210904950454a04100c03407900c920038042942c50600e0015050760001c102e640041e031103540400d503c26041d100000d82d15407508000c000e0080b00b91001400500900c42200c054441d4212880040482c1200f2030b581c5100c0107101c080c1004c00402d000040100704160f8410364a56404840312409d0005041003010400d160100051005018882c0c10f9840d000c000f040e400000c42c18000242000500070400b040407600382c11031903001802150415860f42000444880400c0c043c1034190700c14809051008488801e0b018007174401045242194070000c010080d440ca030303202e0081540c0e04480071441d00d24444402114000c26010029003041e400810015000008555040c0d42d520076902845240c86000a11825000541c0e0b55a4840000714080000805140c40400c5040310394141100c400c0e6200c0000341819100000700d18080206503141147e5030b410701c2810071044044035005080142502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 155851645 1250 155850395 155850413
    0x102180904020a03061b020c0f09010b071113020c100501180c11070803070b010b120a020c0f01051609050603040507060f051b01060e06040e0c10030e0a0606030209060607 75
    0x290900034104240800e05545078141d41102071500030700c080c001c0c0c107440d0b9074403905081c07268904070041c024040001c8040c07400201c525010403000f00741c5020307a420501500c4265114a40c00c036040d20500d00040f419031940d0380007071082c0720070940042c0c03a0307410911590b003482014071400c0000303460280140810301c05010f01054824404800040300b4080fa00142d40c40c0d0694a040f400c00d101e243c0001907060800001402414803e081c0c0c003501e0f03640e4081e12245802031142c444010610100040d05503050b0b60701500ea8002c00c0000c95005103034100d000d03821501d05440c1c01d00d00400d0b81d0010503005402c40444401000280e6105113103103802d0f25156100e0362280115803c2001d84491042050310840c103451184250002504516000c0c00d24540280748078890300b01d840c00b100c0d000403401d01e841d2042240b40941503000d4071030000707543c00304259000d1007428171080c1503440444040c0c1000401c01a0000781c031504002502504500411601840040c84a480750348100094000511106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 155852895 1250 155851645 155851687
    0x6090a060f0201021303050a05012d0c05072405060102030711040f0b090711060a02270a0902070b1008060601050a0c0c1d1603021905030a090210110d020102 69
    0x45003101c810014420100c2c0640b003415171200c00c40700e030402d020050100105c1c520311032071312540003000302c0c5202d41c0d0103103c803001040c001e8103141c1540c0244810121580c100030590522450580e2909605030f8034101c0c0242a40e06000800c80700d6401480350071500e100b4542c010409000039800c08a861344e4507452060003000c8203000d0b80d00c0e42002d0000501c41d80207490385503402003042000e40f40031000200b01c01d14031107003409a80310314004140c51503041e20858907503d0b00341e1a00454200d030604510091013010003000e4002c0c401700c0d000900c1c03440b188054032102d4480e1400e1209400d2040400c0e480000e6600030606a4210b141804620707a041800c5070829103060908405407019820220842c00147c1d01003101005012000c4500d0900009810300c41d0010728503514016101d060100e0403405282402c005985101c160307255054014070103117500401c290f4020807810003642c040b448c100c42801030140450440c05040d64900024003d280c40440988021800c241c0b500c122250408658 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 155854145 1250 155852895 155852897
    0xd1b091503090c0302100f270b0705100c050909010504020a05040e0702010b130902011b030906030e031905040e180c090405030c060403020706021212010e0603150c120606090a06 78
    0x101c590404004400d810f5074010768004045407825071620001a041da00384648440000742d4000001491140c1000d0008548084250320140c15003040c401c52495441108140c82c2c61260742014010081140030b04200c1e00c00554400b51901c241c04140181190180c0000740300d40d005000405480d54401e00351821078002c4240c01c585078682d220107a0041003895000b83d001aa95611009402c1c2150440800e0f60300c00c2e0395010b009404280c960152541d1104000c000800030601040b2181c441d4000303800900942003500e18200103201d0445d040c010301088500070540c017280400500c00d0114500b60300000140c80c0c00000402c0322480e42c0c0342c401010240348150b1a41c0082403c0c010200300b603458480f261000c68a40303003000d00f030180d9105841d00c10f0100510030084d2800010071000c0c1522101c1c8e22011100d0702c0f40c0d0801c1807030035642200515090f0180324000c01c11805084681065004140f20b40485549058140b600c009091008201034001c5030104289891900ea9518480c1280c41c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 155855395 1250 155854145 155854151
    0xb0f010c140d080f0a0216230601030b04030e0109210f150603020301060b0906121308040b03060108010b0a08040b0a02160614070809070b09010201110d1b091503 71
    0x1107180c110320803091484030390014860490700c00381040d0400d00b540d0191400c661102800d94540c90503600740c0c40b505504108031404000b612001410442145420743e01902c0810842e90b24000442d1500034264401d859240f075150a0000b419080001080c01d29002e19041d40042c0c10f000c0c4000c42651752210030207880504803851802d10404000e00300c0b40c071740c1c80000e50340f620b0b07201d5075560041c0c402400300f40d20a528092000035041000e40c1101da20b050040c01d42820100001c0c1001e00b003010003070142c0c00c4800111200400500f02c0001480506600c240403510303030034002c000400d0107030141c01280d4440c03030802c280064183c001c848a6031195109050700c505030b60f80d050401c0a8041c7d00e03020b4104222580b0f2100c00c1012603000b45650700c40c0c006802260756902c1100b29120380f01a68554182d4100c29014403c42c15404006c0c0301442d81800042000d41c0740780c80720300d091340c88000b0f000289540ca015004800440c4001e044040e01036241400510341440291490030000b400c0d62070034165 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 155856645 1250 155855395 155855417
    0xc0a03080d020f0d020a1106130605040804030807030504080105010501080106201f09020f0f0607021212041202010806030d320703020607091208092710050a090b0f01 73
    0x5050b40480d0078a0301c5140807640c0303440500311400044e421100321180407440c2c0c5505200c446000190091181034083e00902c269840c5884000c01040060030640750024100030200100d5550802801c0d040d104e6a01c40b84e54030700c6c060009086030b106821481c100400c1c2c0004000043d40058280204080303141800611900c0c81d1190b031920350f803a55910580c2050484050b00031899a0000320350a00a45419000359421801c002d04040154200c5910490038010100542424103010202c21100012100910601d001328070781a00240d200380c504c2808082d0260440d6440f0120a4104205500415031441c01030000307003034480005001000841d024040b99010800301604070074031365405021580d99049820000c6d01d9440443c0c80300081840300600044003102411552802c6130043c0f800760030702c01d12200f0030103031701c0001540e9240700340803c14040c902014007013203500075506418400d150a03d84424400d991366554810b050086c544014201c5541720442c401414007800d01c0d00101440d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 155857895 1250 155856645 155856667
    0x6020a020f030a0c09050a0c020309180603070308160212060f070e010903020d08220f031707080c0105010501020c1008040f050a05030307030e070f03080711060c1504060501080c0a0308 81
    0xf034401400607129442c52600040c0030b510380e52119018407209070303083c007200441c80c00c207903924400d01d400250410540d00c1c40c01d03400c8030360780030942d00800014180c82d4a641d07207460303404103070b00000d8407001c0d0b040412074490114500907a1100304281c03540702802140c85d11540302680f940c8020041800d104070740c82203a04a030300c03858000c2d001d50b900408444c840e14171420081c000c3d800400080d0040415000d541084071460b1030050121480c04450b0b01e0080d06503a42c442004402c41c5403a0341600003070180f40e00280800c00a0418540040b000041c5980341100091810300890466401a2180041020307220351201c0c80940c0a07030407182d0b00c102100d552802c04c2c42c0520741c0e9000f400500002c4140048164590842d01d40311100c08e08480c4400d444846813a8100d100c0d200c0180f00f2001004030500291401c40280e440c070302c0080c02c083c00c08601400c2541800487c3c101c034076442d5100c0040108004603441118007400c030210040180f0607c003008583d0300060340c000a0f201c0c03480418850480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 155859145 1250 155857895 155857903
    0x9060910050d06091106090303031b04030f03030f11030105030c011d10180806070813033e0102040e010b0f040504110909090607080c130504020f07020907030606020a020f03 76
    0x81c00040c0c5284032055090410780000c152840040341c5107400c0e154502c0491a00d20240d66144030018080c501c0c50300d0b9400c80e50b2445d024005030070224641400000089048000c0406a150194401203241c0e60785100740411640301342c80400c4000d000740018030854030000707001c0503441030a082803c04d4107043e503a04190001e8400c1410f90000a43c6403004255504c4090800c07400e5150000c000381c07607120795596855420807a1040c00054803d4005501d92002c0382926561a00a051100031840000c03206d012008204182a0b0135400300d03c00d0300c8405a190185200084440d402141410300700740c10a6135000b0b041c0300d480b22807680410385150781801c0e2000c940003080010300810240705c070b40d049000039030003402c100c0c0e02c24071240300020755520000c6002c80c41400156103a1032242c2d42d4850f07400403a0000c0c0700c0c01a00314080700d804900d50301c45100802c0399021030b000f42507c4403ca88100115444000c3c5450101400c1500800c00c1c01e80000d4084101641112407400c05040c5801181c64 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 155860395 1250 155859145 155859149
    0x6040606140f040b0d062408040f030c0b0420060f03010308250c0317032509030506090601090c050f0304060915022212030207090e03040f061e09030209060910 70
    0x20707250009503001e05001707281d009404a42c5100c0c03244407024020744020502d2401c03000220081a001c1c0d0000300050007640d880e0030700f035100341031002845e016601c914180c0e00044408482c00c85d859040030f9014620400d0b440310045d021106a03203414200d500300005400180300080c0071306d5000c07815500088040c0c16444100303c0503c000e144110140c204500074002900c0140c03020103143d0340102e1200c2184044034402d523041400c201882010b80304610440c81d000d502c2a04002c2d0521000c400510140105030288460358000d181550400001c030089071141010202804420007201c0c1d988072110040d6644503403c1580003d0901c2181003c2c2c0c070010900c41000c2d00c0f2440020b18400100e071a5000c03081c803454200303107410400e48413100d0001c80500c10340c0150140c2e100c1c450070008003c0c05d401c140120000030b400e403400c0990303420110705044015040030000c222104040c4840401c0c0202c642041c8020f442c2444426182d5008141ca06001a2145018030706100014003022006021840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 155861645 1250 155860395 155860409
    0x70203070222050a0513020f01020c04020c0f0606220e030f22091107080c0a0506070c1b0b0301090e0a050313081b28050a0306021206040606140f04 65
    0x40030881c1004030b907035426154800300100c1407030040814031410301c0d445050301c22001302501e5040b0b00340a03020000f502c402d030145da604520071030000303210740d4a99001502e4030101c07c10052001c100c4240c0c2a6040000040c4200e016031380e1300003101203802d80700c8005d10088244070070015100a00c128064214420340301041c0800d5000075150340c03e89030301d000c0080e445440800c803c2159484080d1801030315245001003001c5203050000a0109030020f00512891150600300c800c2e0310310710742d909400e200d03040fa00301c004103031003003036000c1440400c641c24240040c03444100200a42092007d0000e03000600a09011f00e40c2d400d01403807528010000341c03203400c0c0c00c00b00b10780d201d5102c1c9864007070b8038102e40580d0889028403045884040c0300c4a095250301c140081c00f40507290390100140505102d110350020300d00039904000203c5498200a100c0554020100542ea03440b40c5040d20081460203020783e03005601c0c1680c104501036100c2e48201c10303031542c120781603600d040354a1000a00d00503a08815 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 155862895 1250 155861645 155861659
    0x110a05010c0e09070903020a150c020405040501050f18120a02011e02040501020f03071112150a1d2b170a15060203070305030f04060609050405060406050903040308120702030702 78
    0x64250341001e03456082c024201c6103002039503181c410407100b00c2034a20000b900302c0440e80c401c0c08840e100d09040b13000c8610502d0490b5601c0c2d00c80c3c0004068807402d49003981c0c103954a2041c004910100c8410561103070b40d088146201050004500da500c18003072480314848500414449001407003034200041050071980c0201718541e1040d01c100c001c0d4454415103026105043e21900c000502006440702d064002a409a20541039000d128603111407840350f4800b409003040310102c0c44004e2030802c2c00303034505500014403155541d03860300d030f0210040618003280e40660b59801080440e001c0841d40c20812860f41100603503551000d40c2c03201c030071220283c2c0b00c6810504106c8131125650100c1c21007078101880c084115603803101642c03030344500103018000500c00c100040c0da140c1c603c0034580e001845814001401d555841043c02201d006a40454035a0842001c0c0b1090003d680500d81c1c00001131000b45142a00d50382e42c040b1a84214060100c00140e2200001c9099000340240c81105401420300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 155864145 1250 155862895 155862911
    0x20304060b010210060b0409090201031d061506090f010c021c030521010b180d08041212030e0c120703020306090a1401090305070803060310060906050f1f110a0501 72
    0x201074606000080c0c014424840c81900d00d0300c85000303000880760042a42803405040c41102d5020300841e103010f1f4140740d1120b0314100c0b215800f15504024500a00c0907116900308a03541440c0c9040703c0d04264850f000500000c051644c03060b504020032102401c02c00344803111440800c11034007410307007200142e1410744100000e054001000345100c010301040032083c142c0d003080203040b04070700f802a4501884180300c5241560301d01c0140e1403101174004e22520000440d43d40c4d40603140d000c0d4101c070521519481108040080071106001c000300182014421114403000d240c1d070700d812030364016101e40a01d202c1c842860009103d1240656009001d5a51a180541e0f46c180d650084040840d4001c200031044020700c0018843d49502661581d20180307000003a40341d400c0140c00107801584c0c10300a45a6001072850248100001000b10900100318545040200b000c80210404003c0c00b41c10003103070707451149648448620509089051464a106a2030340c01490300300e00703148c0103215610700705031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 155865395 1250 155864145 155864153
    0xa020d15080708151b0304030201090803160e040507050d0b0406030501021204230a0b0c0d05070207050102070509040f0f080705030f19020d090b0c03090604030b07020717060408030613020304 84
    0x805040d110078104a6412140b58003454031390007401c5812a48900d00030109080740d2600c44001c5401601a01c004601e84a042d02c401b64a940162103486a007560b60324141250383d002200f4a140800072030b020066490807000203012842070007401014141d54400d0020756039240d42c0241c000e560410000c5460b550300071040b2921200c140c501fa12210a0b1a100d210112401800107a080701c059000c0d0001c0c220704d980c3c2050041c406005116500c3e002c0c450075000a01b40e11a00d403252005500801d5090f2500c000a802e00c2c24179000302d80251201030411020411700e0b021745840c20341c4085101c40707014070f40c14101300a014013603004101d03020015150325034501203009810000071500f0340c0004600a840f05a03900e08c0c00b02418008504a24410800740b0150f070702400c40308140d003094a20b0a03c00400140780d40d4807580048039a0551a814894200c1d8104003140141c0164000d01c0c0070301150400040da42c0c0310003040105020f00000c0044c0c00b035260a41c60348034203800d0f403000755101c1c21f2500d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 155866645 1250 155865395 155865403
    0x70f06020901110a0f030503131b030b07020114010b07030c02030303071d2b0c120303060e1617060a0b07050312060102030f1e0903030301030c150e090a020d1508 71
    0x406540002d0150000c0b02d445000070072614003580e17114100c1d01000321156015502500010261854121020450b00c0482e1540d00030400d8203003000300e013a500d6411460409581040580300030110ba142c01c0000e01144901300c400d0341541c20b807035002911008c461500710340510410000a4040c0004410301c01c880303410030f624001341a050300300282040041014800c04218440003115051048030150b0ba048010388040780c0014000c3d00b01c1c16902e91140720311050b10544d080c0c11800266076203420001c0c0e5450741046500441040c50504020240c00c3c1c3c0100380b00c605065503104615000c001c0703042d079940c01c1c8039100202001031680b621070b81103082003512504030802c074526101008001801c15031000c401c07074070300d500c1921a503401c1808002c0b8940e0380c82010200080c1c0400e0412100f0803540c0c041014600030340c4a212030100130740c104941e82e120702c004e1041f03680c14011994914a00e5949956000c1c0e803082030400010703128410712102c400500703c1080c1c0d2070f0f62070000c108003143c0c0c0d00c4089 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 155867895 1250 155866645 155866657
    0x10c151b09030c061b02040f15140111073209041104051303200109051c090f0506040b0906160803150d08041715070918020c060105010311070f0602 65
    0x15441c4001c403a524402905e42c00c01d6501169036000326850f14000525207a4406a40c044140b1400180c40d8000d801c08034081080c2d4012506580061507269035540e4040d088000c10500f0b0302c0500141c906e051416007000c1a203407481043d515100044680d00440c1c0000c3c1401c200000700808020308050902c91a00f002c0343c40001e0149090000103407085415903811064181e041d5916000e900e081114050200d42d01e592001c3e41c0c2d500c0305800c0022a90802940b01100e508030302c00ea241060103803015082c40300700d17404200c40801890040000b60f40e00d4050b60201caaa441c06660385103100e80000701c140c070802d01104070a0b2480b541344018083d03a40051445074910360702341403071002c0080c2084899044603500500b141010441800301c4550391a070b501e88401e11004031840c1004100d00c0804006044820000150000c401044102400c02440c0e50340003012034210b11380b00800b00f5064a5110500425050580365070070f60341c41419030012070f021150042541c1d01d00c2451071805c0700282d4480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 155869145 1250 155867895 155867903
    0x408040906090209010807050c151009050115021b04090807050a0b0603070b07060c02030f0409020d060909020102061501050c011a040b0105040506030f1b0a0e1905010c151b0903 78
    0x8198007040000051088070400081610f079500c1b5542d41030340480d46540a5945035009004000a030010409a0601d2900902580c100d1000d294240101141141c034160300c035a09051062004010003a004a40c0c450312514081d48584001048030100b00035121580703004103c28400680c00d024400d011824a00f150f209030f140700342588407001003581d0340c04d0902404007103480800c80303000082c019921030b02d40050340340103a0307060172485048242a40c0040c3d000380d04d030301c2c4c0000704401c1d2880c142c401e201c003800c01da41c0108205186178000039644c8c0e80c010003c0c001041c0d4860700d04a560b00030030564500c03480c240000e00540c0c00481000c90204410a05c0034043d505001140380d9540c0220291420390700d000c0d22060440e80ca00000610315600901b1841c2c0320138041c0c0412940317081030740c01041303404800d4840c205240044014800715100300e01c1220001404184240001ea901c8003080c22100d4000a106034035120b128154001040b0314005011005031034614481269005287d10342201d0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 155870395 1250 155869145 155869151
    0x40f0b01080109061d0c040e1c210c0509060903101a0108092b0306090c050304110a08030904020901020309030102040f08100603030905090411090a0218190b0a0c0b04080409 76
    0x4840310340b0105c0340310149400c03600000130380301c030504080e445041a034581004031b500240052089003681104103983e40d000032004c072402c0c141c030404409050a05104190708115100105400a09a011707014010b40702c0d400000348884141d81c1002045003a20f01144200314004c000c03160f00310500c0f00e2030545c41c081000c2d840055540300c804100c5c43c02c0340e208890342407000048800004407505101a9082c1415924000820501c0c000d2050003c1d1203442c0d1501d95030f80c00c1509280c0038801d04480882d200b0400c400d010b000b00c050200540300c0304882030302c000d0b1f01ca102007401030b429030140301c00050b055031001c1000030f075840000b102c660460381a00b0507034155503d1040883c0036113000b0300000d03002c90b80d0040f00308800d08100c850385621500039081007032018a0300002030541a81510b02512507600032403100007425200b21001b805900403a20080302c01c401d8400600c10007224450110704a0010402c5e41c440c0d0301500d51800e00c50b80c05000300f2860b1401c2c1c500762515420034003035942e050785 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 155871645 1250 155870395 155870411
    0x31c020c060a0e01060608010509070513210c0510120209010e090a1a0d1220060403080f070903020d1e05060702030403050c0a0e270f01050402120102031e040f0b0108010906 76
    0x2c0204c0425042c9c0c1c0340a801070885980d40141580c4542c030038151034031140b140400004142c01d84042c880d40343c0e10000d400c4410100d00f810070f451015001d402a510911042d40072030401341c2c1107041c0d07e5410f14000c202507210201040181d17000c0030305011490b0000405010031071075991540c0000709034802215210850751010f0305001790744030600e10003131404052a4040101070f00a1041c0200d0031413031140b402080f001c250815080c02001d960403004900284140f1805d0385001440c290300c08098544110720a2864000480c1d4451104000c0c0c81e2650801c01c0c2c94140642214501e8bc03da00b24080310668144440000c0da264401d12080c0c45600a113004903443c0c1c60007601c600d00b00c0d00d00c84001e0440703843c0c00000c503010420040c0040c04403581d00703074004800c11091010034a11480c40000140510f0240140208992070b0b0070142c007070b6441007041101a148298010034603800d0924003080d10381e903e150a26a42507640d0010b031800120b10b00020341d401e8150031040c420f40c8242c806010f011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 155872895 1250 155871645 155871647
    0x2e140601080c0306040f1404110f0a0b0315100206070e01170a050619091a040e1e030c0304090203011e030209070c020303120c040323031c020c060a0e010606 69
    0x10944605000032401c8010032040948038020b1904040c0041002400d80c001c40690411912104004400f51484034100300c14001050700500510b03e0690f00c11b071b41c0d1203070100012810446401050a10500403020902401c6010820f15038100c020786000c00703404104602941d01c0c20111201c20004162100f1705074154410781c050b548001d541c0c0b400c441d90b5101d04c030a0034041c1c500100f05d560003019060802408047c0d2149001c000d0080ca4000240002c10f551080858043c017046940500d04141940c101e4002c0001c40220500940c0c250401e2154040c18103400c43c801d8041103480da00c4003107004a405e494950045040300c0d0f052002070140c80040394410a05102444041d60000d540700000700014016450188502e1000b403da03440d00155014114013442c0584a40440301c2c0701040c00d01c01c20458a0b01100d05a00060a80c00401c51202d2803ea80744214200038000c03d43d03140c0e006000e03402940503580300181c0d51095600781c0c40c201e10108020000800007207155800d00314009586 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 155874145 1250 155872895 155872931
    0xa030b210f011a1012092102031201030b130b04030e040b0102161a04080304080c0f2b020a08030a022b0c02090405070806010b0901180b07142e 63
    0x3e88035203591940c400d058410000245441d0003c0c0052104918000040c1c080364410030020610905005012484003201d101d400c003502024481907500c200300c44820398115030500d40c11a03030300c03800001d216940d10007542103841003985c008040e00d6120040c03204158000d89c1000002c0c4007a00e0402501e01c140c4012666400000c07142c4040c144600f00a20107159550088101d034014030317500924095403a04210320359070041d030003c031058001036016851031604607000d001c0750324103c03103d80d030310200c07101344182038400a44400900200e07020031404540f40c01810400a21012007542c4d198404c3ca50301035110000000d440e141300144552283c4407840c0a0481c541820440e5603000760044640e003440300004014106940d144200c1d240000c55402c00c0060a002e080700e98421030f00c60402030300250020b0001c40303400403e10141003050000602c20400d4440c9140c101c02c0114240c1480e40805051040c1c0801359051700c501010980708084a05001101d9804403440030440c102d4950030380715613 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 155875395 1250 155874145 155874161
    0x90d0e0121050c1605010e0105010902030c0a0302300f09010c0203180406030503070c0612020910030b010e040c0e09090609070b0f0c031b0c030c0f04020a030b210f01 73
    0x1004400c0d11021140c107035900155005400d0340055280c0200a0000343c00700001007405c6610340e441c0c8449051140c2c00380102401849011070550a50504000f1008070740a500810030070564080348a17410302172000301c24500005c040544254100c00c0021800b27901c0e00c202e43e2008059651804030701007000500c1099002c4215a002e141444600400007580101401d034440d40b01ea221040400820001d00040c84014480d40c02c0b04c42003460850040c01c101020b140e00303070419105100242e503540300d102c440b000d596860300c1d0020740c0d5110140141d622041c0210202e40062420304890b0441d0781041840d042c154003100c19100b5070743c0c1c542c096942c0e002c00300d03400e40d11608061020000c5650400c050800f04c1140700080d400e0a00c000280762179070b004a043d620001080c00c5116503800002c0c41100c1e404901640600000c1030f6601c04a28100c080501060103203a001440c184450300c66809808152b0005000710a51a403031003050350160441000740b4034900507204e00c41ba000a0510411074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 155876645 1250 155875395 155875427
    0x3020a1b0e072c0f0303040b0c0f161a0c0624030705150a02070812030103030306050402070b042901120209060904050a020d06020f1c0c02010204030c031502040b03090d0e01 76
    0x3032075030015440403d040c100c01a10b0b13802c2809030503445542d0f5810300152000d8446600c030561504145004245003140302c0c0000b240c150005483e80c8036000a00015405640c0315020f40c88a1900380b6140088600c0780030004207042c020700742070101074854600c04074103009110180f402c041036642d042680722403140c802e00d43d000350003a080c13540c040d1015001c0c007803c40c030034015945040d40d11f4450b641028940c010139501c0c3d52000006100701a0548129009800e05450860400141c0e0340c40044403680070700050040d040303030300300d42d4401d800c07140200c0b0740b0342c8480d403429070156599192612404c040220891041950300009442402c0c0140d9803881140c000c1300802c5042e00d2502409100c406035807040d12019020001e40704400d100c14000c0150011400d00c2c01d500210311070402003154007080208045900400040020807007803500e43c01600e400c60140902100490500c030000d200315032100d000701d04040200014980082a440d500d503101352030b403080c04d205450046851010714207c1007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 155877895 1250 155876645 155876687
    0x3140c0f041203030207020a08070816140108150a030b040b1b04090e010902090702060403020106080f100b04021303031d0a050105030412020705031204030501060e0c090d03020a1b0e07 81
    0x1420030102042d4585000f07060040c81c0007402e4010980c40701e40c0340c00000c40365011020410045070104071100183c040443c1c0c45075942c0c00c0546400c24001042c040341c0c10000e4a601240c0c0d0030b0703c074078000380104000804003024541e9a291400c1d03001c0b0b085800741d81c422100d00c0051064071762841e403040600c80421000d85458144a803a000520304251404240c0d035991a103400142c81d03540125005000a030004d01140c80c00f0714009013903038496000701301290040c81119001a0b030014088560f245070420205000c203180001c9070003402101194001500e585800109042c2c10a400386014603808150511100d010014045070741d01303601c16030f40054400c01c0080c0106150710610300c0c0340e800e9407066450548c2e49000081c40c0030f5004958260b409800182081000404d1003280024041148440301e5407070041c1c07100c00613020f90f00c403c4d40100c040c4104101014828000a40c0d481d0340410b00130581c000b89400f007503481c0a14003481e6010180100480c42d6a03000d11580141030014804003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 155879145 1250 155877895 155877899
    0x10e070e01030219080318190807182c0d09080304090506040e060f060406060c080a05030414070906210f0215120a050406051312031a1003140c0f04 65
    0x7100304000006803000e1a104000300100300c1780da050000b0849045042c6068420140d0981003040301541d5000203910411000010000c1070341c00300c0c880085500c2d42000c00341c580d80021514000c3d00342503244040d603a041c81108080319551a280031080c5031800704845414800c0c2d5401d494404c401c1c080c0c0d09060780305000801c205240d94125561145000d400411003903108440c0510744201951340b04031010000041100d40e0a2a21400c40240981c0c07400d0b031403c49c000d84400001e44203500001040050020002d0240080c3e880c0f140035603006a4215076500f0b40e40c1603020001c00c802d004802e44103110019010314907030039481a5a00703982000217400b42804035401c1145000c8603000f00500300801740840c03550103115034680f5118102000021842d440c182c54104111a40203000313420286e00f180b800c00100d4101d00c1003940944c07103414000f840b621050701e503019207820128055030040110810f00340041d4076030019202c2103101c4150101d9034480d581012014003c5070b13819454000140303c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 155880395 1250 155879145 155879149
    0xe01240b030432030a030f05090703020a230d050607120228030b040207030504050a05090f0c03040c0b041502060907120b06040b0a0b280801050f01020c09011502010e070e010302 78
    0x1d08040c583e10301506440d550060114a0464000c43c0c400c1c80880d984074414504000c1c0da018030380d84000d0f0f000181800504642c0041d007544500d01230301070840c038000502c07040312000c61003000300700400500c1c0f030700c403004a4a4440d0340c580c021600040090139209541402e49440d0003174810b01e001c800c80c40c0407402c42d2022071946106180e1104c80415444040395005a16a8030088c280103009a0311140d440d421300080c09111201da500090180060408025444a0b450703640740d04010400385240d030703985543c10304032403502d0160800c407140c02c00060f00041c076900c01811400d00d80e40075001d4486030340c1d5420380c1a23203c1d0300c2442203211584505000600040310102260b0307018070020000207083c42500301166994555030410240f00740002800c11550500b203414041c0311200d401d81c46c4040e003480f10024201c803010701c41c5a026280c0003600b4141c0740e000780021009847d026028200f5507a5031801c0c00d20036000040c00c2d1015528007940f01d0700502d004030b00082030751a04034500c450740e461542 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 155881645 1250 155880395 155880443
    0x6070e01080910050106030f0b030606011403041b12030e12060610020f06040501020903120a0c0206071104090312060b04030503040303050901050c010204060806011704050606130e01240b0304 84
    0x40c40c0d91030b000c0c41c0c160209102d42446064061b00e059980003d0301c2c0706030124601119041c18646100f84e01000411030300340e911100250b032800c0741040b41c9403a40c940f1300d40109000c080300b003412460041ca203804504002e003070090484850090313980e19080101d0340d0034084040c003483c03642107a54201d10001691410070301d960490980107441203880320f034400002d142c02c01206a40071501039400003440015450704000d040c1014001001e41c80c41c00003c814050800c0010074802030003203101190500602103415020081c4c0702c0040d1003404403c3d100d2400030701202406501c030100300e10b021030205001d03403410196001c1d203a00c207000390720341400d42e101aa80b0390840e0700349904115007049030036413020082c0041e00007801c0715141ca82e1203080c10310014040381103034107114103060902420007010a900185158200c1410345141d480f80c958200080d0191605803a0401558241660014440351400100b40e0310b0795144407003041c1d2500c8914000d5070f484280d030041c2006020b60f0740780b00c0d480342c01c0d9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 155882895 1250 155881645 155881651
    0x20601030201110a050f0d0908030a050406030b040209030102030a060513020f070620070606030312020c0a030804060b12060402031b0904060e07090507230a0903080304060605040203090a050c010206070e0108 91
    0xf0080701c0c103500e03056460324a04802d0500520207a080100110f5138103820041c1c1c1c00c050403c550146080042003800100309001d2032184d10304240d00d4030346110954a440e41213a01030200500251341e00c3c6417103003040002d0441c40c41068051411031641080b501c2003442a100cda000c1c07035a119281c001140c4841c00900403800107d901826000da104545003005c5004140c20351040e8404a5103d00d181000f52800c401440400c0d0b03a2401000132540342d078808101c460704140e00d42803011480e110390901c000180484003406802000756075903814119400208107110f60710031002c9a100d098111040281a8000c1001e182c10600394004070340007071403070b812141d4103004220407204055039890f11030080c2c0d10300755148004102c450410650140d45444c0400c0002460004146010110880201603005500c0042d082c00c6020012404004046e04034070300910000780195260f0614101482d02c44510b403404a40511801d000b100c829400458818800c1c0c00d1510360054025a440040d9030f0b9110003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 155884145 1250 155882895 155882927
    0x5160302070c05060301030506100509040f08130519051c0b040209040f0210050307031407091e05130608070911030106050a0509120d0f090e0a09050a05060103050a021c03020601030201 81
    0x51008100384d1280700181d4021030052009200030300b40700043d002403555541059000326521401c2201041c000e508180340c60303600428456a81103410380a40748400c00c7e8100d180d0141c24802c41102503941001000300340c0f4411541e00e03500c1c41210f59071020038070042c00300a041c2d290080004015103001706c42d01e50f10900030a0035017100001743d030025195655000440003c188040113100c1c82c0e590600c140c201750030b014100d5031000d041c44440500113200510034000d00301c0b194030030a040441d010904200401c409441c0c4582ea00f541d11041000e4155030013800030724441c801d000252640d050084840e0748101ca40d02d80c1c44c59003484000c441a502c450704007014000c0030405c030101c64032240369200f0203180c541d0140c00048110000103041c11803580c0f5090030417815440c01e01004c03d0024044d504a81e001d140001d0401d1140303801400c00c0d00c00c4101500c1409030078000400c0c450f0110701e24140a10844440001601343d10030a03400c4903039164040e005038401401400194001e2102c3c80074bc01d08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 155885395 1250 155884145 155884163
    0x70b070212030a0503041101020a020312030717181203070509010f031806050103030e0103020f18031501031208061002100b150c030d0507030605010c0b06061e1c0516030207 76
    0x481d040c1500d10792202c5044400108000100300502c0300348054100141009d20250240d4862900065969681c83d01c0740405550000081801c2a004025003101050280010091751901a040c502c2d52800780311841c00502440c001400061103002c1100e01c503802d603403101800c00100c28011900c12038940074440506a4804204003c40640c0114220b814402c0002190300d60440c5401007156216000050500d8018800e541059001c1c000b6110f404c2c50030f000e007030f03101010380000030714004040e103505188240342000401070214101928140842d141c4800b51152900d40034000510b21105400c0c0040c7c000f10145c5c1441c0000d034000e100d10303410041c03940c0c14009082100594641c40701e00400b81c10b82c000612040d520402d4050756910400c01d04003044145c3c60034002030001d900d00c0300000c208032140c4001600950b02d10054948041c14074000d021801203001643c1219400316968000d03a0f908407000c4200e03151140907803446240d940f466120b602c5505441940130f500301410032141c03044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 155886645 1250 155885395 155885419
    0x27031b12010603151e0207060906110405010c020607060204150207090b0603040c2102040e070905060d0809060c1204120201020f06091207050f030a0e12010b102106030c081002040503070b0702 84
    0x85c007070015116440c01180006500c2c5d404d49004170480d6407550744c2000c480c00c1400100400da8100701e01204894055800d00c0c1e03100d40614025009202d26048031403107a02c103840191100754009030b0b9005403244500c080103840300d0582080740c90b0000315802070884034108403d111800f1704540c0d4142451004940c140d140103154005025101c0041604c80a0b5021600400c848040c5000d07098010409440c144400f000360785170300f10b45206d0045181d0241c000011908100402003080180051811000c0d9454945504c0c040c076801e0b2088a00707900604c03500029183c0710f5400701c1c08900a0075420020004001c500304400c41540203c2d40035151402421040c1200c104103000414000d555955604001c401c130f2000c1007200320b19a0504041603141110041c00c540360060340c0c904400507420b0070248200681c0c1e01850705a80d100d29200748078148032000003042405104e0809403010707007003900c0d2618594011141280658400c09601d54003a107001c001d02d2650100a20b101c60019100c4a9000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 155887895 1250 155886645 155886701
    0xf040209091c0e040e060420040e15060a0902120103120503070903170921010509070608011421010b010f020102070209010b0f04030503040608100b0703020327031b1201060315 77
    0x14007c44003520002c40307100c8008015849100528007402040ba07003000000c00004000d030b0380382e0480c0004000c81030a03501041c02070761341c6200e00c00181508402995070351111004081805030a00c4201c40d0101750701c00480d982c40c082e009803881881c00744d0701c0010951131900c90740742c0030202e401340781d00c191000c019082c0f00da101c2039289140001c1c10740170040c803441810380c0c1a08581004200345004d411010080c0080b903030186031281169902c240380c10700840d03d480044c0c0c14806001403405c2c3e103070000c00426109201900030501d014400d072160b004541c46141c0c280e0a0381703d8010003e600641100040c095416490003400034003425070595401d0a890750741e690302d503a110350040404940d464042246c050702c0c07126001c0181001028490600c0c101d558065038900903031400b01403030345621020520810440c019030b5090381c001812900000700d60303c0078050741020400300c6800788088081420280005000781401c132079002d110440c1910000704000e00600711503a03401031070828000564180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 155889145 1250 155887895 155887903
    0x615160606150504050f01260a0605040227090112020904061107051501090c0512280209041d0601030201080907030f0b06041401050a090b0a0902030f040209091c0e040e 74
    0x4001540c460591351401d2004100340001300b00a464104500003204180c54140103c1c8050900e481c0600ca420300d8503803800400c00703840c032908980d0b0010300c08640e5038090f406188104070005a201540100319994a0500402050034054266400c44aa500c400103003010b01c50300d40d0046c050b07200002c1042450112444a510200040d125a800402404041c8580f91240d90040c0b440c400f007000098520900507045005604603808501117150004049600c00c0303008585c200c40101d01c4541c0e1624401d01c0c44002c0d041030341d1081c01107180800d20a082008020340c1c10010b401e40c40208040da282da40112005200108050310701d005a031000170000c0c10798880b0044440c130039018501c03a0b03e4454103120456016401e4080000d040c0c0d001000030391115a02c000c15a070100740003096404014002c0382c406032043d80458410f82c40042045080d03a24001d2140c0124401ca0703140c5e503140c4501c1c40041daa8a40c80c299140c4260380c1c0700b08004514018403d10001c028050070100341d140c01b5114003400c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 155890395 1250 155889145 155889179
    0x301030b07021b030c010309031709010501090b031506040207080d2904090308040b0702120f090307061d09190f09050d02070b07060c170403030609050615160606 71
    0x56040c602060014642e01441041c90740d040906003008078100950020340e40b1081c0d00c0350070381450b6680c006401494403d001c0781183d0f03039552480e9a80760512201c0310340248824400e42801a00e001022400340c0713400700b01d44501d41c04030f01040c2e40c181c0b54001003200940c000201140d80000c05c1040c000480b03c140548881400b040400138140d280e0000103640305841c40b0081c920561500e042d180000ba0090b4485030020f400402088182c0c0d12800c4c00d82c905400c0100304400400e0215007490b66028400c01042c0c0c541040e002c0c1d4203026030302c02050740e5210209076050610340b00400000301500f0031099480e44560300c12110004000d01c0820002140d043c001c5111025450302015401c1c03000400c24815880c0b100c0c40200401d80c40c3c400c1504040c001c0902c010310300d549403060b501c03665200b41d00b120030001100494400b607040a1801500a00340f6118400c0654105000507119142055020050010000380300b07251051180c51105200c46c0f0fa20308441c080d03503411340850441450300d16640 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 155891645 1250 155890395 155890403
    0x50a061e060207060908060703240e01080d09081e03070605090c1504060903020613080f060106080a05010f0611070b030a140f060607020d030c080703050307120608030f0c03040308030103 82
    0xc0541000c0000342402c4213508040e0a004541108005100703001030306a40c040c00700d103400100d00d01e880501c60500c0034010400c6112890f40e00c00410b45604000c080c0e8102c3c5d908104550141e00c9140094880d000d1503c2240e185410500c41420800814040d240c49d2900013001d83e440e140156507581c08842d0240c8010100d68081c09005681e8200f145040b41c81111800201c3d00309807401e14010314880c140d000090040c079011072500341c096071062004024083e0002a83c20710700d100850203a840000b403140300700041c030030303808a00824428841c0c035060740e2028040351492403d000c42654000444041051244101a00001c010001d00040d501584100b0070205003481d107141031100300e010150049000143c0d0b8414450680c0c7c1d1201200c0c2e659605554621548200c0e09040d02c2080c00c00f500500510343c000307000c008155100d4000e40c46003440740c03200031071480c2c040c010900321403a5004036511648204040660000c145029260302d2003034004480c50207449035151201500280c0c0115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 155892895 1250 155891645 155891699
    0x16030207030f140d0e030309010c06090f2901080a080f0c100e160509040308060d080a0c20090a051b040b0703090506030f06040902011e020a0b07020c0306010306050a06 74
    0x3645002c014080c4000e000c1d02c07850b0a00700e10805100003507d910a40c02258180f10010070170301c0c2004450f40200c070a068001d00a050049030f9814010080c101c000e2126008500e0310350081c0400301041081030580786224000e287d0071020f03a45060690303011010b85000e0050a20402800102c1009103405900c40c201d000b10311100b030b584486141c0008100480240b6642440c00c2c0420b071200b000a942c0580c1500e816881038403002c000c1130021228140280c1140da000074126a21504050091280d9200d0319150837003d824100e4034070b0413040ca00d84140c0c071200d120b001c5182c0c100d070790300251303000100c2c01c1207004081c88510244201c0c1e0721a134810021140301041d29010b06400c107240d800108010f4441ca0314510b8410280030b0b0f803030b8000304020711441daa003e8107011b69210f01d6405a140d41c00346044007095840517000b03962904400801c503602000140020480d034404180c0030002400a80108060390031603645801420000b42141c2c2d605649400010f40081826008003060000d042a6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 155894145 1250 155892895 155892923
    0xb040b0402012a0c06020a2105120705041d04080315010e1909050705030709090c05070204050a363009080601060c33110417011116030207030f 63
    0x110350801319592105c41507410900807100032035814509200b00066212004890445007501581c85004144d220707542d1006800800c4191358001c4020000d460061a500340d000515590a07181c0080448004001c808140003280811882288149040005041c8180030111300b20101e16640181d103500494145c9504081142c2c9441d4824030790808050700c0c000707240d441c100358081c0c20300000b4810b000201c2e507910303803040700580714100b651100d030f600a02c00c0c403ca00f4500150009005105414883c401701414514910320180002c11a281074100c89600041080d17150048544031056a1010b801d00b21051116141c610a640c10b041886585070781c881181800d080d5032404405820041c24040000b0754000410480740259222016404911a00a00355000d04042480003245038111070300f00400500e201c0b5001014209a6000c0c4000c03184c1203200d05030701400d80e920034800e503103006001c11404500144440d00b0840c00c0d4043e00440700c509a0f20340e50b188007000c1811003640d50721504111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 155895395 1250 155894145 155894153
    0x3051207060b0607022103120720070608180304031401020c070621050c090a0b1c0b0a0e071b03020114070503040308011e0512060a0b0d0b040b0402012a 67
    0x890503141000d032040f070f0070001194045245000c0082400c0c11b8800f004036400c1680c4003c000700c0b4000101c580c1065800d0820000c0540a851040130f00000d00c070301c000003000801c80003d01541110700c42d0741e928411707458600c1b180f003c1034250800d080c60350104100102c0402e0100002090808680000603075820001c07032410700f0030305290001c13000c00c4030f02c1040e407065502d024030f9104450039140c4001041e8442e40700481081c41110110343d0018001c00000400c40f20702006001240d481d09000c1c2581700402680c4001c4034880f001c0c0590001c01001c09004c1c8060719416039500003514140b06000c5101c80c480c05049089010302100142e45030101c3c442e0045006103c0e54004405080c42811818190740180c005a0140160807000c480017041d141d8042020804100038034001d0140003128101d00ca100d81c030f4200c00c464060040d070424404074000d05080030103001d526081800080c0f40e40f1241c3d60038904a00240c0180d0400c210071800d40d140744142030764180107034440416001c0c002e501d0300d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 155896645 1250 155895395 155895401
    0x11010f05130f0314030301060504090506121f0515280f12050709051312021609020c070f051f20030307030506062104080d0606110106080109110f0a0305120706 70
    0xc04c12807039001800100031a43e0458250b42c15100301500201c0d042d6658001300d101c4155580d4201c0b140e104e00140d10044007140c2c0a40c2c48103c031852014070050b51405141040441709801194000c0d5030017200d8103207005a00104100c03a403298001d4020b25070350310240e0001818540041400c13140107607c02042020400c00a0001c10b8540c40921251600d80c000312010320001d034000c1c1900d804040c14440452003401881e03032000100c0d0014102580f510b8104000790015902c011580c4202c01d404540c103407000300c0e1074041f54001010102001212a4050b9007900800269001c4c0086c42c20601d00101218031010500413000c40115201e01d80044002e00755500605018000d610800c1040b45080720b0040305002c44502c803011400340d80b110b2038201410302c50f240603441014508100440d11716402101525030b649050000e10160341c450400300d0803112107040040050010314030794215810519400c2c11440380003005a00225a00e0f11083d04201000e4000201080002001010415184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 155897895 1250 155896645 155896673
    0xa020d26031801150b090406030203010204090e010b0301060528050618040b01080f0c0f0c0102030a051807050a0311010e031023090c091801090c0501091211010f05130f03 75
    0x2000f844029080303108424030749094002d0006101c000906d00c00e45842e0b42d0040d40c001c6902030003c560b40c41d40c1c3c90403a00188264404803085509000d00081070b8641405132100b52880100065851056001000d405465038901d103448181044000621f03642c4600107000c1c083c888030805420002110204000c0398040200c0b107041c04440018001c0f80038858030030380d50094940d408150744c0d0f120480e078600c071401780c210b1201c0598000000c200040c105600114003903401d050b4601c4102c0c8045040c15111412030281301d40010710300d00101b01180181208203034020040c104449043c0d01c00020a08011604011035411900e68110340041044245c0804055601480005080c1803a42a083d19040b03031020261003000058003150300c406c1c0f15024081c40a05020003040841001e14062004010522810b03002c41d002050004002d02c1042018400a03403003006840c2c561040700040d07441c480d100c41c80008102c401c3c0a448188081e4400302c802070304a0003011000c81d0b19524107801860140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 155899145 1250 155897895 155897941
    0x2090115080c0901050705061509090304030b0703090c3501090503041724041e0206120403020c1216060512011503020906030703020a0216080a020d2603 67
    0x45011184032540c8001041e8004811a0810340c0d24a40000101c0e0b241c003c150001e0868024801400600d50a81c031941d85010304c1070b1850f80d40381e81d5900d2125200c0c0120710000d2718a4806800140840344070342d0004210611403084003c580d0b84503082030f80c1c0320104900021440c1e032249245159020041041428021340703c1c0240078440d060744d01c80c0c0d1a0300071881020071018058803840005101031029402c40301340b005106120360100340200042200580c0d094607003d148080b031f810f03080c0b40000c524100d00d4018020038900100184204081c180c01401941140583c0c9203010b16541d4144031840030722050310051000059003132150800040d2640f0440920600308940a124142c8054450468000c00703d00040203850500541c041d00c2089072040e80450000708001ca203030b0f055805000f0581040e807c564604c403190801000c0e803440f9000e00011035104142e0040103240c682081c0f50803601c1045641d0449082c4101d20090024004091001d001c01004006905800ca107403054a2a03031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 155900395 1250 155899145 155899169
    0x20309010501050f31051905010b031b070203070b0315041803090605280c03080a0915020703030b030f011d0d1e051c050105010306050415050910080a0f020901 70
    0x844070002d01a00d00ca40d80b01c82c5c403940c050348080000130680c100403c070200c2d0241c0502003850104000030581121710b00a044d030918101c00415890650025607100f003034402ca450624106411200384a0303080300404a80c540f0903280c010504e613200310040c50080c132076088208078000100c0200b00030346480154844140d00c2c0d6951030800320340e00826030411a81030307042140e503d012a90880303200c0c00050b020540344241c2e9040000015900c1600e05401034080d41d941c40c156120300e00e189041d200e140e68050101e0406080900500311181d0080c19000d00c00d00b40040c42c034407400082428064000d50310101c9940d54000d21500102807000e0700c52400088000e015411b06013000034000d08440d16000f40c01030801c2c40d80018050241c800c444100080040c4014801c40000d2000003805d000d005050000782018800592810b003405500010610348a0610510382840241303c080c442c01050890040510240014420360611150400354041d80b03480c1e01c051198018480c03559010303401415030303000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 155901645 1250 155900395 155900419
    0x51b010c030f0609020c0c0f0a0b0403030f0806060304020d02040b010e04090f060b1210090311030310051201140606032d1e040506070e01030e07060c0501060803090a1206021c02030901050105 84
    0x100407c0d003054060301100c4c060031413030079803022031607005c41c0d90450707040300400140100902d41c003e280c0326a03503242d070b941720609540c0742c10030301210b0302068400a400c081c15007090001460240c1010713505000c185440c007800b192560004003501c0c6e051405842102c040c4501c8401e110847c0100442c00341c064a040c11400461184c40b0390b55000c0840092505964500103420103203d1281c1e800038100c2c400849440341825440050751032141e00c00c0230b10070700c0044c5032032a00c14810b0007a03545c290040c0c240c0d001d440d5140c005002c0d40354802407141248500c0661410304c0000400c04210b40d1302422407400b182c62a01c4412400c2c0f601c94103d41c40720600c0c0300c10401001420000b0300940c01200d030300d000e040d410800c0005a018100302460f0740800d009004020407815800700310003c5c494000c0000380019071343c420750700e500ca01c00c241c030542d00459050700034031486540200d4428041d204507001450004920b45482a400400c5da0fa4001d542d000800e0001210090140b2400350170110f0b02064280 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 155902895 1250 155901645 155901667
    0xd051803010504020d0b04051e010b09010e010602070303030e0c040c020304061202042709020603180613080406140d0501060302091807020618011803021f02040e0403051b010c030f060902 82
    0x5e0881009008041d894000390410400340440410318500e08a0301c10f400c003041c0f11050181c0311404a681c0500d400c06c0000900c4100742031110304940c11034000c4c0c4080d50030768030100c01030300f9011050f50503403181c00c9a844481c0c40e64410340d40c215050390301641d01c41e403c04800906008a84800c0f200050042c0414848104a94101300701800c0c402c0a4805070801e400817a4060134803c3d002030f40c080c4001c010000017100302c0040c0c2070682801c000b034502c0c3d0395803403503865a60300d04040c000d81a803405100510005000e00070180e980d60b0b0300e1b0141c03810001605454010749900340c000ba400242c000c143c400080c1071000080d0020303410707404e02e18010301c0d000130029610320004101c6848101580340c0088a950f003984101c501c0c005041c410005a02241000b955610094020880b0401d040c241c0058444542c4269010b490f04544900080c0d03c4946045a450b003009e00711440410f00107103200d01611092040f0101c07034110791004110054580f00400444070150b10842226004003c03e60310b46c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 155904145 1250 155902895 155902909
    0x13240611060a09051009050a02040e0f01061a071b17010f06080c0924061201080f0a0b04080307050d050a0e010e07061704080c0604030305061e10030507020f0d05180301050402 77
    0x2005132007000030740c130345a505020340b074101c510b480a2b40052625208010010000c07561110b8100240000d00c015940d850014810340d5004481c03e25003201030091a00103071194010b014944000700751880b603161a140c200c400c2100010440d251a951120380c100400c540740680300c01084501c01501a140c000800310f00202d00041c1410319280c018507011b1107038099000500d00c030401c00b0f011192910b10048003002c07003103006c0c02401c0d070070300c00c521651140c02030004076000380c40e90020f04021952282d60310b140d900d400c041e01c10070030311009124201c1d500d1128460148101c19480d00030410580825a0a0071502d810614a4540d0071050050011030f422261550032124401c403000240d5580b41400c01c080e0140003d2040a400780c50244005c1c5649604010b025140072114503001d425440385460002d4030f440020344e0006070f41d10801101a0203603000507400b08045c016207000b020440092801e016100c002c000200308046041908000c1410138026000c0301074008009500302a0001054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 155905395 1250 155904145 155904163
    0x90601020a0605070908010c0908120702101112070303150504020408030909040c0e0705030103062904020304032a03090b0f0313030201150e01090b01080613240611060a0905 76
    0xf92030f2404298501d119100744001010002c000b04003104401c90000c115003543d100700a414415202d040031a00c000c442103940156000301620010207111000303a400d045000d4000049024502d581c003804140d00c0020702ca814801c2d60001400d4006041d04107901500c0d4001d540078900c184407d10881100000f207070f0600d130f030465042c0074540d9a45020115105140c00162a01c4801024041c80a800c0805103050b41d118100034040d8401e4501843d404007420790038800c0c1c140c90206480c40c135003001e9004642040c0070346060f0700e54404190104e001c010880c0d4070b40316485400c044c004281907000711080c000e0823201b1100e1303141c0041034580c2c004601014040f52111040203007402d040500035480020101070107010b074a40f983d41d410389031040c96801d01c48c241626003030070f00031519903100c0d016041c8140001060090860200c0c91458000c080140014800311074000c400119090380d446050010040b0759030f15400d4040d10f0004509014024191810080c01e02c420b200c0080c1c00440c992603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 155906645 1250 155905395 155905403
    0x403020714060705030c0c01110109020f04020a0c0c030507051215010b0306010903240c0201050f150f04050109021b0703050307030f03181a070e0a09050a0204080f010515090601020a 80
    0x1c0905600d100186042c4502e050084c143d1200242400f4031000c081040d80c03202c0d1090300ca000709840303001032281c00c1c1c9a910380c0095021001c43c070520028513159014254070007a078548a075020480b5a00d00c0780b00c6405810030b41e4150312100c01081241350115014400c0d140200c080c00e42c0180c592184506a078041c010003040800200010740c16034800c031a404011a0000c4410b19500d40c086160301c0303600e0070780b04041e00090034510207081c00b034014011240901c00c510380c0c00c456652589090f42d00c903541c10720807940c001f43c80110b0400c0d5a5840c0281406007003a9600140d9072035400f413040740e41d6110318102c500c050b0000744040020541c0803095420322500360818003c0c041c4500011001070801656400e402844603541c0c2091000a00b45843c0741c0706410060039450700c0750030095a600000d0300d14107074091041d46090124001e02d401c850b80000d99071001600f05038603401424108a0800207d80c0342c0d031340d12820010001040c180503012004103841103106801c121000079160020588050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 155907895 1250 155906645 155906669
    0xf11180103060917030f090d0c03020c13180809090f04080a08040206070c12030305071107061d0d0317010b0a051b0c03060c070506010b04060e1504090908040602010c0804030207 78
    0x5000d00901c4400c03859034500da041070784d90324640b0105001c9282070951f14800103101e1851030b101101d000c1e030442408540c0580081c203160170403100b0420700001440003880070b261608400541a180f1100314466240318030196520b8a10341c5061000c8000001c1c4003805a100c04002d11002c50100c40403900c0e40007841c900007003540c0d0381d80041000d5104402000704145150040060b00300800c80d5040c5543d442a54107002c19103440ea400c0320314401c0924501e0564000d06001c02219004074041d4128000907150107982000100005402290754202580411800340083c68011a42c40c00a8090315800d903044e41890440d18000b17202c2c0c081e45454800c08104c205050343c928200b003250b541c1c803aa009080310745a14114142440070340040e181107034244a9100045007070403502065405448150f51801c046024010030020200c1e0a10b024044d4690100b20210f01c048150103000c0c3c0780c0713029005080d603841c6400c0c002800c444041114000f008007100600001039800304000086944158880d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 155909145 1250 155907895 155907911
    0x70609061206031203050603010c0e03070506090a1701020a140c0604020625120f0305010b0f1b0f0706090b0304020a05060c070914010302040509030304030c12090504090f1118010306 80
    0x81401000c0641001e4a4900e84d0002100302c44e606400070f0313204100c00e038000d0100c1000307800c05550040c56620403a82c1504400000c0c001c84c24540090300b0a54401001e43d001c05540315050b40400e179488540c100e05075000181072a0080c5c10881480c442c201414443e45880c100c2c1c400341e0b4951002900c000e1041400040401c201c00c04e108409101540481043c500d50b80c1d030307252190b032480c151034082011031400d800750848580284165030407182c003100711902d01211103005e683c441e40a84501c2c4c846e060a0f07040c00c0300d180c000b00050404500028028002c00d0f06044002c0c102c07075015070044404860170400c000058440c01d0020049540503104581c03a1203098581600f404102c3c0c00413030a49142420040842a468001c541200d0098a04102c00e4595074038441d1240300448025002c0390101c0010400915042000d2001d00031528204001c1910381c2e0000f815160f00ba9011341d1290740549070b030014413150b00b80140444130100d03a00041d1400705004c4540b080014030024103056542d10413 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155910395 1250 155909145 155909177
    0x80906010b0d1d0f1e03041d1e0108030304020405010918060903140a050304060605011412040201170c0711030102270a0e161409010c02040509070b040603020a1107060906 75
    0x103550f540c502c0003080e01d002c02198902c80b555030800c00c985c41080030032030381d00344610750f4048121025111188205002140800803505070004c0180c408402c0c0c00440e031440c1d0004804040481c0a40b01300d43c0515540c0c00e280c0100025114184c0056003224a02405e00d100443c81c0f80d40c01d05581d41c82040810004d0b86400c2c1500c81000310005103154a00001d1001d4445520200961140d4400d1400304030040c1c4850044800402c0d04142d030380110b4080103400c20400f000c550b050751080c4149020404680354442320381c07004005031802d100070000031900c107040000c41000e03841c10700016002141820703010031080f02403a8031185500310010503080201c8040d2100c41d440303000b520300c9680d001c08074105036035182600b84001003804000303a56100703010b10504915007110150501656840c200711601d8003000001d16001e0f24610040c071840d03400248440021010b071005281c1c0762001a2207103008200503000c1c0990560b04680c540080d8400d00000341c01400c0b0009441003450070360a4400c008030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 155911645 1250 155910395 155910431
    0xb010f0807030e1015080a0b0105150f0d0203040b06150307030f1404080c0601080303041a06010e130b0a0509010510081305030705010b010f0302090d1103101b080906010b0d 76
    0x200e260010f00410350090102d490030b400141d10f811141742005d021603524240c454881c0c4034030000415410046004210a1074441d4108501c102103d03003a514180711040020419800170b008003040c103030080200070a115404000c20b0b07014400741d800340f1190f0714200641c2c5952000400700c2090598a2122440c005101c1d4417500f804585081d11030000d04040c03d0807030441c0c210144c4d040a41c4209030000c500d0102c0030041d2405075a00003002110900000c4c04c482040340014207881c104107545121200c1b40d501c1924800104402e50000203010800c0300600c0005041d40e04283c1c0246001c9004000580701c030401405a00c105142840464030340c003054510f14002240003a2641c4000b041d40d000380301066004042a2100340c0718100714809030308055003a4011040728030f03405146500e90601107420b0101d03040e80110002d060300e41c84446500020200c0d03160060300d05100c10b200404070301d019000f22000b03412001d000002d03e41d41d0b00d00813142036107219280815602c0c640761900d500c45402200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 155912895 1250 155911645 155911661
    0x80309031f0f0e070509070f02120714010c090509060604060c06090302010b03030409020d060e070f0c03030f020d020304060b041e091106030c0a021b131e0912120b010f080703 77
    0x9001800320410010515549132003900855100b8182c0201264205005035060920108039802801603450380c3c3c3c60100d40e03904402016143d50b0262003e01010100a1046ca00b12101c6500d44070089414030f0240814010010b08680c020300782000280801504403d480307102c142d000c0c070007084124691030b08074058094006503641602c030100300401d03500c0494024007c0c0314528070080089a540341110a0707000000d58141d80403c0741551080d075524410b085801d00540a4280803031400c04905d2104101d03800304014690301503006c07044c0700802c440c501030051180400c80b41403242201c000c0254074002201e00001c440265a200130104109910060325500c90000b02001d48034a0321100901c920b521000105006010b204400d82015050050310000c1074006002e8901149441004400404060034080850380300c1c1440c900300c0c016580100c0958034800e8000844109100300064010104503038507002560408201031400d0340c2c050f06c1c0e10710f10b04c2e007444e142483da10303135443c2035000302000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 155914145 1250 155912895 155912921
    0x314070b03070809010b0108070f0c03030b100512060307061e020f0102030406020702180c0a0e03010207080a0908150f161206030605010618030c0504020304080f03040506010906080309031f 83
    0x803003000b1100c0e4200d215a44688600310081c01920b994078011180b00001321400c0d000304030000080c0c0030f018855030304801c01c640300f42800202003416200040128480d043c950b0000340002030072a0507a1310490243e07420001c141c0040c0328160501401400e4109008002c8402116030480c07800105e1007004200b0024550000131943d80c00c0c14200600a90b1107010f05900580304002620384103803501d441c00748900304800c801400c041d10154100c80c1c80c0d99060b4460b9056409104031000305800380014102c0304c1042c3c0b2602072152802080304c0c109230111802100210380c680411044200740803800303911045103074400301c0288070610b065821113200d40d51445003525111000c0304001065106c141038451035141c44100c0150710b14047c5064106020040c518100711008000300d00305a0060343d0800e125070f48a5081020129400301c440c0c00884007581c55502280c01044260118442d032400341c034202c03002c5c510f0b0202c1030001c01c0d9100d640c804491940100000c0003420700d0130301c0d401080c48401c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 155915395 1250 155914145 155914147
    0x1212010915030615031e03141b070e041406040c060302131e06080c0a0903020f061c020a120902030312070e150403020906010509030a080a090e09010903090602060603070314070b 78
    0x1a200c0d00541c03140c46000480360010740e68080101b11282d40c826411a84c0d040e51045052a5154400ba21580020f58001c4440c000c1c0200245508014055400a8800340b904c021741480c180c00c021400a0142102c00003a41211083c0004141812060700580b00c084c00d02582c1c940500400440c407e40035440380c208288582a8031096807541c19042085880740e6841c03010341d890703842451001d449101c01c200040f03407400b1020001400d1035404142030b050000d0019040a0b029a5641d04d06c41891043c3c1c1741007503000545215842d040380b020074002c09450340030048968141e01003941d0f0f00c1140802209007034448001544180300389004401e0740702c0605000900321500790705403060342050100f01d119001d0b000000d102548680300380c4d1000400100107082050494483d2222503100603c10002c000031060080398000300c0c52841e9020b16204000040d8840e1681030040401c0b4003031f01b0020031500194103110305a5000507008090343d40055030407038074200c0303d000340380b07000c0c1568454841160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 155916645 1250 155915395 155915411
    0x14150103050a03022a040e0102040305010207050f07080601061409030703060f09200603010e0c070206031e13030905100912060507080112030c060c1803050303070212120109150306 79
    0x140821810b0780745101c0e40031242011110310300090030003c402c01c210b00144602c00c9aa000d45015044149490800b0340014542601c9485981c260390102c6030070f80782648011381100e400802000003d0040c040324000e00b030554100079008218025800070640c51180108420803d030f641400f40e0b90056900541c100017240500e0030901c050190050281d5044000c6460103c2c11084c00211409400340109054034507801c041c41d8a8180c0307800380000c068203005005003001a1580c0e00114011084002f2811510180940c1e81e041503c00034086c459240c100101213000a1708840084e0554004403036852444520b4501100c100035a41d0001480d0401c0c2d900e10300501c95560b00c4036000c2c0c038071683c45051503a21500b40d0b000550104030014001000006a580800d66983c40400131a100d49002d54620b0f1040243d1683c1c5616a0000e075466000003040c08a520b03010881d90400d213041801d000e0030301d140303d22030821501d030503c070380300c090340d128207c910406151017401006994460810001c2c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 155917895 1250 155916645 155916653
    0xa020307032a020705031b010c0f15020306041a01020a03030b18010312020c060c0a03080402060c06070807110706170601090305030a020c040b0603010b030403030b030f100906180f14150103 83
    0x10300380070308030b0141c001d50700c2c0464141000b04081d0b0a903100c2c10005001030354414011a6150310028080c0c60042c01d031006440042c1c154002c000e10300120315405612814908200300c1142c10b500303200c075513240365400c5d011550f91b000f252040b882601401c001400240c00008611120081119101c000070701f00d0010040224102c14000c0385109a42184c10f1100c0e20001d01c44184a40d0b90007070070320352141205d0000607200d90315069100c0c0c4003415190904c0626240f40b840c001c0241c0e11072021400e80c40c204a580c940c00300c0b5101d24800044001c040706e078603295024007481c000c00e1440d03031b90003001d4000903081c0c2d00801ca01c1e07000350b910408a039661090074200940310b03400c00018510a504180f044c3d9440c1c030f008000e580c16991034001062a540b80e55505400800e004e07a001034040c011407105214120701407101f001d84a50860000c140a1200d1130900100c420310206820a01c420500c11004120381c2c2d1012000c03154441408a0007507a81c04045141040c440d034814101c6244100100c200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 155919145 1250 155917895 155917961
    0x2306041a0304060c0801050120100615020c011b06020304060207080c1c03020a0801150e06190923090c1909150201061a0f04050301020307260f0a02030703 68
    0x8a00030f600412201001d5035046818070700c02c1c800c072400110189071144501c1800e01c904480b50628404940c00549032640038000e41c1c1082e44822595103803145141c409a4050204080c01c01e024039240c7d223541c5950354100254104400003608490340800000c04100030b55040f2000c1c550045901911414903841d65641c5039141b0b2440825000750050303a1020710b00038001d4a050810644424105a00706484910508100e00c048800c101c00d0100d001d499482c4d89008150070b14841c1c01200d040b0400001c064480002b550007411200842280c02408000112003042c80d12001c695008407600d132048021030900079070300610130310b62100c0e80004406070000401070854458002102c1e284007200760513800c8410700e1040f03600316048505042c0c400400d5a00034400c19032003408540c101070b29400400d00326002210413a002c1015903640548051500b10341402c2d14500024048640c9030901c11054252809400c041c030458010001c180030078000c1e00003d55590346000c0c000704c6c0c050442402022 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 155920395 1250 155919145 155919151
    0x30b0117010e0706031e0c09060905010e0310111b060414010504050a02060a0504080303010801060f150203120a0908030a0b01110703022d06030a09020312042306041a03 74
    0x31550406100d2150101070085203081880000504100e51501d2010b5004d440d05401d644180760f1044440c9401c011a885a070260349030503030341e04a02c2404c150303001d8100202500998184400aa5406035940e00020a1040780c10b1025020400e900303500424034141c05080041104046244051080c1c0384000408a00c5140200405801008920301c0c480c2210b400b550080c115402c201500d03400340c05c12000804030104d0320310b440351030a55190750031404c60b007003a006201c490b5181c1c44100500d100c080d150a02412100c00b56560011210704080e58074071407056408280408640010b0030404654070840a058000c4200c603902c5c50300590a000502c540c0d006140070404481004900160003e103c03030682c0ea0140050400340040e00300100d4503034100c4407085200c048400c04007007030b407601d401850043d802c1201c0484e2600c917602c10982080a04045c040840c0014403080140349101c40941008003002d80b407002690402801281151080d604402002030040041d2142c5088007401144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 155921645 1250 155920395 155920409
    0xf0f033011010b01052706090a090615050c07120602070803010e040b09070b0d0902030705190911120403051605030307050d0b0402040317030901090f0c090c08091b0604030c030b01 79
    0x3c03002928019070303c501034440b0340300000d02482e00145400008807081812002c3c010242400e10505e4800140c1804085e00300c00341d0280c035050204040f42c504141e9491300d01c00340c10468200500f028040303070351303104501c01c0134035540c0303007840481c1448074690480712030542181c0060754a603119075103501c4041040d0340c06c480ca000c0300e00000305000804100f000c03d45480885507803400601e80481c2014007814072003a6414011990006016660030f1141047c6000302c1114403100c91411540d01e00300c90645541c08041c0300304000e100c55030b080035002d40e40d0107a0705040003500c2c0c0c000c4404010903110300c400000c2c070922000083c4400140c1043c0a40320756100003c0c1403114150712003d00041c1d0245110090083c06001e01282c2c40200d010081c0d54400c650303400014183c83d0300e4880d01566031641805403444d440c00d00083c42180414090b051001c0e203030742410885414881d00703844c0e0741d101914924088040c60000b04a41b6600c0d282110021504a100544210303101d040903021060300b0700c5000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 155922895 1250 155921645 155921651
    0x8030f07021c1d0402040504090507051002032505011514040e1b010c050312330d1214040b040906061d1c1b0602070f0f03301101 57
    0x1002c0340700044950358002115511103900340d155000c6a81e02d1030801e800c0544c40b075028400843d2944481c41200c0309d25016400a110703851810050116615005208000710340007008032189682802d154503095078400c0003004a028121704102d80107024414261402c9030704a1700002d9011411040d004000900b107908015030b502c0d50146584d1a049000c42600b600607040d0407c4040d0300500c0c5800d4414000e0301507130300d4032000042d45070420f4ad0403500e05601c0c011401941d0308062444803a0010f11480102c011340410703074180012001380305d044004044108a070b040c01420343c4907920b040000403010900c2074036070b07480314081d0490350414050304564070b1403da000682c0e948201613038800380c01c00214100010008000740808500ca403c0d411050100051150f000111425480c0c0e039044194800d130100c3d142841c0c2c00900b40041c42d402051202000f6105100302c04c7c0103410f02085a500c049402d02400d0824164003418040d5a4220b0048406120b0b03900010740101103034041240b560020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 155924145 1250 155922895 155922913
    0x3090308010803040f09022503230403020303090d02060409060608090f12041e0e010902030405060109050930040e0a0b011d0402031320011205040f0b07090308030f0702 74
    0x741d500e000d5840f800c4d00d50780d40312401b005141071030340c003d000440d841050b262088410050001d903200d182c0c20114005a03034070054100c0320240d00c1301c01240e40da016102d64989459030f000255070740035a4540b503100d00340003902d4100b15905d090440707004103501101071000c1e558641c030280c050b4004903003c1036140904002800c216030089820b00344420000e07441030405007040d4000b01c80d01c0a42d81c20049015031024003040b803c1203d2041402080b00ca100540e0300c5c80c152070b0150a0241c182d00458481e82000103006603540e002c10040d09817a08003401c100e18180030720380841c0c0c2c002c40100000c480c05000901040305058541c0151182200e141c05102d003804000046030251555840b15035045051606a409460990003d5410032a5a124040410102c2d03c0d103588018a800b08402c46a82d0390801d010503580007005d4242810387e170001001a46050340f00c5020a1244240c0101045c52000000d03401074000d00d8907001440d0031800c4a074a9140800142065070070559240025104040d06 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 155925395 1250 155924145 155924159
    0x30b0a030203162102091b0c030d020a030e12040b090301021603030516020c0102060109020706290114040b0405091801020708070308181e120c01061a030f040b190c0309030801 77
    0x1110039045d0f01030840b03c4203650f440095000c01c1900105204070100030070142e40010030400281000042a0000580d03455a10601800310340c400c1382c1c1040c16402107020322245100c10b40694080355454030065030b5440000c0b00081c0203205407900c180c080018412540b0600d81d05902051141c0c05034800461080b0b4081004ea99901007103a00c03e0042e407000006104040b0141c028021040c80340760b022515583d55084038a8880e4201c1d0400100e40003590045881c0d0b80c4001504185a401c2005520746410701041c00880d20a5003c0d03a40201890404101d0810303411450492500c0908000c645800e45480c1c103841071741c050803064000440b1800803800f1243c0f00803144d0004580315000302001050b860450a0f40080c0c1c0092490502414580b2041c4051000c001c1c52028141000010f0b0305081c00a00355440780d1682d5001c00b110014010004000002041941c01c0343c3c11a9036400e166132058801008600040c640c41c5d169030401d41221505070301900610301c0d40d4403035140c4081a03031329052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 155926645 1250 155925395 155925449
    0x4030c0905180c012006070810090c02120a050405030a0b0610080f0a2f0301090c0e03030706050a06050d0f0c060f05090f0d05150a05070e0f01030b0a03020316 70
    0x512210103400c001c0f851029507025012591701e002d0700a1100c51000c851001407400c00d1030440b080d5000c035004000308030b1440e104002c030202401d103556003040303614500d4000942e03401e860343ca500d12207040041c2440c0c209003c0c1d8152402068002d08680d00e00081c2e10b09040003041c00e6441c1d80c0512090740c1e00700c29503070146215520a10048040701029a110107000020f0228031140c19448004520b150709140345020400c104403011076581e590703d51418842400302d0f9104100d06041000c2d2603100101a6804021109100e803c200c001c100d50b1a4220140c0092040e0360002d0b5116480445000c10070002c00e421181c2c03180205081d607129607a4540980703100d519040c2c400b000035803c0021140c20705d0040c9000c034500780054401031202d10309135545840c1a0355007805101c040740030f40401003206014001c20341d001d07134103203020b508011104000c038000c8402c00c03100318140b5840d4407601c41981c403080000700082d5002000c403030740f84910406818403102203005005c081e01720079540300c511108a007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 155927895 1250 155926645 155926681
    0x5070c0c050f0607110a150507030e041104150e0901060c060507141605150405010603050f0f0d050a03092a05010305040c0608061c050c09131101080a09050304030c0905 74
    0xd000d0328035001841c0d459a1000741c1001702e80341d100c084079401107086000c05030000d0103529145c51712a514080b9087c06405004211803040c8074a081400c0b450040075500d099030210366040d000d201d01c1103a01c0c0815120001c90004064004604a000041310365000c1c80343ca64140c001c4400704450f0b142c00c0700072140740e50918040351201c00d00b0000d03205900310021280401c076000d00151028400c03030f41e0504205c0310b0195815202c0384c0d11080b050092150038050440070301034502c010302d034180c2158501c3d92a04a100f0326041401030100d000d99115000341c200b0503520381d12990a205d4a410300d00010120810180442100312114001183c5940680b281c80d001d10b40001082c2c83d11441e11604980c2c256000749440d400c05442d10100c02503545811024007554444c1c0080c0115030000c4c010301110b804010f01d09410051840c01d00400b1079400c00440484c40800e00c0c00d45116540d000c404005041c0c0c052004009120001c3c1c00801e00c07442513181c000383c95900c00705020b9900e550391b03550180c0b80c5d80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 155929145 1250 155927895 155927899
    0x1909030b07180b03060f0f04090618020423040b07031803031a12190507030804080a0203010c031812020309100e0a050103060501020d1809090b1602030406020a031407050105070c0c050f 81
    0x80c07030340e900c1d45e07d05811760807911040208042400303d0b09039a1031080d6141c0951407060040c1c450700030380031803401d4002c480d00904108020340c25080c1e61168401e081d074002c0c0001d0f254618010110300800c1c400e420a101055501c2a20881e1400030b260050090407031f08013000c6440c4805640441c60301e0605201d1641904200052404282000b4094043d6150318012281c520404c2d100000040d1720030302900003056050040c1440c04040e005040c01c0d40c0010741c2c0041018035003a94038030401c0c0580381100002c0d820070010740680418a130203a145129200c85558411042a0380b080c1d810b5102d2223403804840240d9007a0f00345640d480064065075014004e030f601581117136040006140c0715001d9521011040d1520010f580c0d91901a2011214403480555807808500e080121010140403905c0c9202c81a1005515003860102d000f0b480328035104c00101085110741203800314aa201c802e4404c15500321000304003a0410803400b07001a00041400ca4011100707020004903840c092244a050101c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 155930395 1250 155929145 155929159
    0x50601091401050c03090916080c03060a120201020a060203160e0a0e0c13030c170c010c0c121106031003021809100507180305011a030a02061909030b07180b0306 71
    0x40c200645098000c4e0710321411900c02031000042c00c3e60307141e41c900d0041c40c1125101a01d05840c02005204c10b0000b00010302840c0104240140303502c800d1070b44000c45900f003030103d0f0719202d9840100e0a1002c00440500340c2800403080c00b1502e5140f0000402528681c2c546403071028403841841a8242148240c00706002c040c000500741c0c1d009076008107000100201c0c01c0050640304c1e60707006000002c0d82c000f00b820150064010903440d800700201c941c4845c1c02d003801c07003076011560f8442e00030010500800351003a040350039020801031444414246503500801d516100d10f840f04036040602c0c290320050384920f11005003007402e0302c40104114011886240584180e00440400b403010b0400500807408100c0343d00442c040c5000b2481400b000345224030004291101000381064410030004000d40c030075040070b40c10500503555441201da4800140905040c4000444000c1c1d4080034207500180ca080386843c104107919a009002100d904aa06143d0000a49514001c00580000c89100b40c00000b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 155931645 1250 155930395 155930429
    0x60209040606020a0506161e0206010e090a0c030201050c010204090e0325030905040506010e030d171501080f1003080403060903020d0c0b2a0409091e030f030e150c070605060109 78
    0x501d41060341d5003460508121140e111035118223001c000d42451001a000314006102a4000c002c00300c2d00108844c00810118040c0d8561449000c058031009042c030200040e0354004070701c290159801040c40590400900b440c5070155a26548601d520368050b04c03d1507603100d1161015000d00d03a00d0f58255856060941c18803080c84000c0c50007070912410301c40c40115004499800704038030100d210060380c0b03c503241821100314283c044e40c084e2240500c6120500f80f00d13107a03680401c805034044100d4a0300f0b10103031200c0200e200c051031a0f0308007400004000070044140f0582e5040544d0301071083d802ca8100c104441000c40e50352801c0c80d4010134a00c0320f10041422028042c200f00b0b8001030000400b00c5040c0645000b074020360041c0e11081626440e0402c8109002081412100d0184e441c40c21062644481d42c00a020561118001050541e0350100000025080141c0405182d0214080f0351604010050218640121004a4501e42002d000800da540305610070801c0352010320000341016 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 155932895 1250 155931645 155931661
    0x20406120b0f10020d0305181b04020705010e07030b0c040e0103020409060e0d0e01080c0c070b030a02090604030f11040e070b0903030c060c0301080f06010b1c0e0109060209040606020a0506 83
    0x9001000d82c010300c801d041006581e5008035030514545240c00138101031159800c0502a44ca0082c40b00c1000e80040481d0400100003241c0c10340c0360101c0c0b009032025013107008000307002406200e10240266107020880040758600003028026a0b001e05119035803650b50704c032880442d120340d00070b00c4078101307181004000506084e080705d00c1e030a00c01c08000c2042004003a03641c2c500007060b2003002c005403807100051040d58008001c139401952110403207242c43c2c009001140c4d120310620030f02d401c0d80d000100089050180f54160307240900018440d0b41c0d0b1340d54a081007403003c11548070544000291010420700c9280900c546043c450700d09001c0c06c001840c0030b40d00740151300641c80058240c0410040510604402d024171880b41c10911881c540b81c0d414903541c103180c401c0101d03011409501140040c806804c3e00d0b4180d40000c200c11000740d02c100700101c9400090908007c90669070341c00c000015003041040d8001c1c00080009031010400c0780e5440004a82c2c0e041d840001410507082000422074007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 155934145 1250 155932895 155932901
    0x605060a0c030210050c09041808090d020102030d060e0604110c07030308061207080303041106030403020c0f06190c050c04060509010e041106070506040b010f0501020d120f0906090c060302040612 86
    0x794020f0064401441440d8011420741e60101d500002030380b00022403000601c0c0a20444a0780c6019080040c25161150340b0b0351024861600824855148004403000b10ba100f00229100305400b0042842401d40e226803c0c4c0c0c1c50f04050314040d12031030500b00040781c5015000d00307440311000c01700000c115140c03454034282e0b40e5000203071103035800c241e84500c1205200c204100b5040105030ba000159942d00e002d0900b02d0101402211032480756a00b00207000100340c2c00110b0070144a0100c0d140c4000614800002d01c5500c210150740c10704c2102600c80004468000101c503141e68054420f8500301c0c0460003c000854040c0d000e03055025901c01d0040c02040b1010894503030092043c000e0200300c8203104009007a0750440c0c0c4045590b603026600b0402040309040b0380c0c0e4014800c3c250030f144500d00303240000c1d458003ca00c2100d400c20040d04841e041c1c6a0031034100003070716000c03020b0412488159041603009003c460100ba15102043c00e40011035911903c201c1d004c03520715584407003402402441c00800b03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 155935251 1106 155934145 155934167
    0x1401051c0209010e06031606020a0c32031009050607090b120601081005040501060c032601030323160605070f020d11071208030108060a0605060a 64
    0x40e00e0742c00340141591015009200b01c0d5880802003441e00a00320440d9000d407000082c0028804e03008030310f08601d1800766401c01c14207500d07459807950400401804500a8900c41c036036000385140d251031041118030040540d4407030045180c4100c05d0760002181550940c01200c04c0c40807440e042124a001001c01d140d80604100407107061544000b8000c004505000c100c0e800141d44400e079505100152000034010007055845610003446910001411804910f0030b0318080410405d1185100b0341c0300031503460b0b00f0207a00b1603401303d40349001a059010701992011072402140d6480c009080080202c140c035a040c031020341410815560041d0800e8103102144107500030140d804118008441842d0509101007011039250320b1a04100c0c2d13010b0f041010525a10404120724070000718100c401d00d0381269265160b1004400803501d03a03104540d4814403c10400022a0103031001b03170a = true := by decide +kernel

theorem cover : BRFrame.Cov 155755395 155935251 := by
  have h0 := BRFrame.cov_init 155755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 155755395 ≤ n) (h2 : n < 155935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
