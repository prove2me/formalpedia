-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3537
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:56:41.566055+00:00
-- url     : https://prove2.me/submissions/2633814c-73a0-4722-a1ed-b0c6dab23936

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 635971223 ≤ n < 636151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 635972473 1250 635971223 635971253
    0x16090203130203060114040509150a0b0d0818030105010801020f1204051615030c050901050a030f1e051503030310030314090a030303150f060903030804061b020a0b060409030e060304 80
    0x144c45440b00000700c0310070b00c07031880c2c0154805440600194a80c40b050743d40d1564004c49007010100c1c50800110381c0e0711a42d0040c00940e034024000032003181c0c0b640310031405a02c14004000c2c1d440340a82c8200950809000351380c010245070300210f1038588030444011450041241d16a0002d4030100840e00340103080280d03d5103129400503990482d907480c00c003c0e4420804140c1440840e0402005021039802001990035268060b1a098545501040d0403001030180426044a481e55540f00d5950700030450b810312000800100c4c000f5860070581c03c0c4910310000f40f012075100b607001f001000300c0030326101540403c0f42e07414200011221405a06058540204182c4c20f4004140c0b820010034141c3c990454200508940b02c4c405c0165114a0700754424400c502442011030009101000028895002182d100d030280c6000541c0310313451101c681e04114403000b22401a40071440340420300c800d18840da50401400c0314100030483c2e80360341c041c0c440340c405441e06215480110010f401d20070202c5800c042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 635973723 1250 635972473 635972479
    0x603150a0912050d0507140306060703030f110409181a150d0309140102060403200c04090b0601170112140c0a0627140d051005041101030e160902031302 67
    0x30000c8000801803c81c1c01000d0651411420240450712050080404910b1040100d12552441d55000207000b07003030703200081c11010540c0d680f00b02d4012074490b1066048001403a40415991403805909105442d81c0c00512605100c550a1000006d501d00101c40111280c203001030119a070391004008000ba211062280c00c04403108101c02007552028070071080d10414283c01050482c99001260740b01000c845c01800b0500502045091030000c1e04c141c000fa00442040b16121524407000c10705484462504442290544040c40180e41c1c002c0c401d0640645200300505132589010021555105e01003c003030503103c055802ea0701d01040c1440310314642080507040b003903c240d41e03603402071015032221451040a03c289141110041202d40490200c80c0709505803044003c0a000b000036405d08000c0850725841180c2c45c1c025005100c1c01510710840c000e0001b0b0465560302c00025040e100e84c6051038401c1e030408203080d0008070012000344203079030452900680345e95079030354036045031400c01c400654 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 635974973 1250 635973723 635973743
    0x6141306110a0611130e04050a0209060d021c110306090a020906060d020c0714010f09260d020c0f010306180515040f050103110d050a2a060e0111060603150a09 70
    0x100151a00380141113032070310a1003800c141c5d55111615002d00d542070b24010550303040a030f00d013805850a249015004400102407040c1c40d1006c0e40000c10888001c103104c0703080c00c9244014000d101030302c0307009019070708158040c044902d090340c5803a03200c66040c3c1000344039801510101d040783c4c41c1d54068810a001666045681d291109612903031400c4c41e1040181c2014031804c14074031548524a242469601e50300c91440c1c80b070408007903050a41c0100c0b9801a640c0601d1900044e0810400c81c44071b40d05110340151039200380035014042c540c1402c003030305810b040c1440002c00100091710700c3e0700c084048110340059240c0b903582e07a1400260070708841c241c1c032034105410703805804148d42c400c0381244d03c14603003040484498030a000c2c101101c45805080364000324810b40200d01000c10319266185001d1030074541c00c100700d0821490480302d82048002900f401000229940c20203140008065070200401032803501c1c1c40040c1d5620f82e8800740c816000e881c60042603120f0030310f401140301e03254000d8080c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 635976223 1250 635974973 635974991
    0x60513020120073305340605180607090b040312090b0a0314010e1303110c04050414150114130216030c0c0b0c0606010507030c02150406141306110a06 66
    0x104040305508032904d04040680c22000240c0074604440c1d11120288410403005007400c1c09505a1b044071003440c801000019a0200281c0c2c9403046a110b1480000a8284105d610401501c0e14100030810b4083c000f40e40720521411580c6820303581240d5020b40030101d029040c5a08841e10310041e0b02c4444c1241d0089800c0c110035800d072304003403040001c10561940c242e99a800d003c1e00c1c2c50041da21812156040c00d243c02c0824410451500040e42640846503440d42081c0400c0454804075416100404010843c5240c8a814800c640d4400d4910524010a5040c200301c401081103014000c0d01c1410003601e424000340741c0c0c0d01a6400d08070801000801900d05013005040b1500040045642c1561110003140d1032600f9001d41d00c005403088001e00c0c1590b144c0c2d00556240d4411340003501401124991200140da908100e41c464880c0c84044540315480d08602501a0f0481d00e043d8000607030a002a9052051004203070040340c40703c0c40c0101030b205aa031400c1e400c0010901d009030034582001551 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 635977473 1250 635976223 635976269
    0x2609010917030a14011211150403061406040b0108010e19020304080405040606020f1c05070203030a020c01030b0a03051207060608070807060e090705031512030c010906051302012007 80
    0x41c0d071040a2016051085484484c16504995001d0186070041c050805010700407a80740000da48509802601078401a001e03039003502203079000b51740111001c03519030461044046814925a410100c1910300348064459500060705444050060303100c42076003000000ea1b041200d680303265080d64070302c00c215902c0c00c06081001e10340d0b10034016180070b1070510100007100c83c400501181e10061040240030f0314400c0c080c0c0c40202c080440c44480030007905000ba800585d40900041028445a07002400b004002d9400502503c90020b1614410015081e04001084001c60a107030300f4034402210568450861815500603e41a003041c070042c40b601c100880c50f0800018403109895094903031440321b1103504100441c11008588801c0014802e1001c1900680254046503406100404082601002080700b03880c0d508542d00220071691280c810b04d09001d6148905a00034070071450460075200707141c001030068405244440c2c3e0b40307881101600e010040a202500192001084200c4141c13103031654 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 635978723 1250 635977473 635977477
    0xe09061e13020c100e0a0c03121206060302070b010b181c051e120711040506030106031b03170c0c06030c0412031e090501120209010201090803180d2609010917 70
    0xb442c0070003072800e49040d18285d400520080c505520481c216150382c02e43d601c3c1040c03a08101c0110041c403140b00f0880f1115111402880c001d002241c0d00103031164541d080159500c401a44480742e00c02c01041408500406070311507640680054404000e4440d401e01c5011115010240140035800713810074a6080321004d00c015008000080212000352404d081001c4d560300c2000c10080c0341420307400040c452414507401c0180c1c480c0008000084199072030b00c8200750489400040302184100e07100074020400c5951901d40070035083d425550424410300b4a03956901942e601e550310500010001440b40744a18040310090301a43d000f440c56a0f4181c500a17048411070181079002281030b00d01001014450b01100c001c90740142d4405034003054900059009501c145d820904654072503280310080f030200b00c01540648200c0700c2c1c5404110304d40c140035040441608106080140242d240481003011105120b060607514100294580340c94020a0041105520003842d29903c1c0040114880c16040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 635979973 1250 635978723 635978743
    0xc0c020405160914010912030c12090512030906030403050f0c100c0e0603071706150408060a060506030708010303260a0905011505060409020c0c090903040302010e09061e13020c 78
    0x40f030001e00c2d0744444205003241050390740140040c2c2c80715402c0140b41c000c604031201d00d900904103c0322011458950702081c10a8034204800310b141d09004119504050402d03d1080301400c1c061410310007420009409848040c0014040190100b0552468043c5004a80b05c0c00742100441d147c91010ba03003400c0162403582081c0c000301d43d00b49030292060a201c0e044a110784210f83e203042c80b5a5481d03c40851160000d01503582003800d822002848804040040c009032050b40010305442c50100c9001081d10119002980a0002803051110860308482928196503140c10403c0881fa5490321900400045803061515480780741c1c141701c3c1000b010b62000c91042d000b10300911181c00c6020038040000e905114594100c1c030700300003c200c000d0b070710703409005151984004c0d41c0a10f14540d0020f140b107041540c0010131604002010401c40d0b800100204407072200703850b9840d043c0b41c54000980100514103851190003451029844960385080980d200900640b104549503210319280f01d42d03c1c12022 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 635981223 1250 635979973 635979977
    0x14040e0a021c060e0a1a010324060e030d0203040803041512060e0a0509070b07110f03010501080304090c1d010f0e0406060509041805060c180d0602030403031d100c0c02040516 77
    0x800410441d031740034000e0100c00b00030b04504400758400030004500070580380108100700060350045140c50f04070070304604010081079868000c01180c0208240c00c02d000486a5815540708000410544030040300b658100c0307141c0d40070080d03004a100402c0d03928150030100240e20610700080440d1290750000568006d4003a54070801c4265240c84200d41c1d80d5a42c1d000d02c541c021028014400040d40660001030040c50250000e028400711801180c2510000c0e000a001c40c0c1011600303005404051044a601c60050714086002a0703234813413410503203c00b409195041000030f06814440e540a066013402c00c80700644200f10071a81d40b00b009241d0342000040d00c0c03085050207000340000f0f004114844000d90400042e110945500721289070950141d02d92201000d400150141203940f09000c002055001e01c1000d81e0780e182901d03005084a024490148807181605e420400098001035848041c843d81000021119500c1400b070707a162030f0642c0025805414442003210110454154080d014815 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 635982473 1250 635981223 635981249
    0x120301030311011505031c0c14060613020307080601050d1e1b0801081018050d031a041a12070902030a0902040623040f020f0703090f0614040e0a021c06 67
    0x21180c4852480951044070746c141d00c0304903101d0702010181d150f2a4a08441e08040e0347c03841c4a640c925541d801d04c90840e0107a030b000201005618188550311002c1004400d404501e5032800366005401e040000e081d4504100c00480c02c0002c00100b98030242410704100d80d129601340580a43c030028100c00d2025120440d100e0000303500b0307180103129483c1a14000c030050705180000e204640003c00c003880e200351505510b0318131680815000d000900c2da02c000e90381d000c26042940c880c01c41c00110003c08560080c1c0c502032030450014148900c86001074030840e0041a503c1102e40d405240a121fa00401e0300644000300740308c1c07011136035402550518802c1c0d60921040d82e548801c40c00e140c4240484000c480850700f8010b02501e031551188940b100b820b50014200b41ca4000c9900113500404002c8000c00c0c001841070040301c255021600c010308a61524501120441141c44864003803841181024540000840d011421030f4040e16840001032241403400303821000d42c20023900040c8154103811fa18 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 635983723 1250 635982473 635982491
    0x2160503121006031104170313081614060304060b12011a040c050306100c08121e010504021603050d110a0801030308130f1203111b1c09061112030103031101 69
    0x207809100d850210390300001d800c00749440c5c407000134a80222887c00d624007040040e00108420030707020074040e0481d6001040440e180c60200610400b082e00441c0000007801c00412040d500e08086a03403081d80003402140c058461008243d01e41410f10b00b2507800d50030300039410000403060380040d640d420201c034144038400c04403038241c5140c40b05640b0036401038691800b514017240101109000c1503c5909410714140d403031103042105410030765081c00400e582c100e64a091801c0c4030400c03070141508840841c07030610300e24200000c3c1540900c0003024400b010407500d03060b4100342d0154034280c400c84401a40d4a106800050a4000034003048000c94201408202c5824002e03148a1700c459011415050070388058682040300341c01056035004144d241d15155200d03180600150984002c20b1500340700c901c002260407400c0c00c1100c3d10400b0120f14260302040b015030b001c08440d00b19840360400c40420700f80414030a06100703842e032152039070020010001003096400b002800c01d06100c03000803c01600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 635984973 1250 635983723 635983727
    0xf091e03060f040c0306050a0504291317030103060203060306130f020d11040f0f060605130902030c070b0903070311030a0801090e101404060b06071502160503121006 73
    0x81810895096840354001408181840d042242c001380a219032078130300e03556540c035403081c1c410454000b44019280c1d0148001c100142c1102c0705090140c1c410103162495861040d401440c0c000c0c5040000307066a8000004c1c0107004c090f5800404000c02000d40d02e40c2c480c00c0820181d8803d45840c1d00a20681c40041c0c448a071400c00c1d5101c20f648824000315000e4960201314144a200c5415141c2a1020742401003a030369038890380c1c50a110100000c20350045548881c01140d019900100038480c042140000841c1c4a40d0400c0c140c2c1c00e003020050b103030f442c4e64009421502900f90000d2441c038a1500740130382118004017030300010388650b5440401241d10114181c0300d004074001007010420060060200c6241c6411080d070b01c1d0230440440722440001312401c5c0c00d40d815440045c0809081c82e0030f000500406014060906005035401c900e00240c1c1c1e40c81401488890100c0440c42e82d0118039100105604420301c03403155000401c40c2c0c1c44801440340400300384004c1d900c260440440c0807002170814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 635986223 1250 635984973 635985019
    0x3120e0603070203040905070e030d0f1404050a03170c03070b01082a0103050a0e030f070510020f040b0a05040f170f06070c20040c080f07181e03080f09 67
    0x1200543c042c500700384c504204d120103000090121020301c0050400100152010040f00703a1350901036a0710640c1015100000d00708040d004080e03003240d04200000e0103a42c54000041c400c8917400001e05010301041001c255180c040e043c12201103010010740901801051040b90781a2940302c1d058494014524041d09542d80341540641500005003080100c1c40d8002e5110b031307900c104440d0001c0340341c01c00320f000319040d03520010140c102c1e4500800d0100a1080411140d100e40b00f25000131032410b05d04007940400c3d4066807284210850700010780c0200c00703110ba0240d90042034003000544078a034840102142102c1c034030a40e50810b02c1440b0f0081030300d05000070200d00802042d281d5656800b002e80301e02c0c40300303018210614025078071804040c169490f288076010002009580d1180b00d800c02212800c04802c0281043e400c00c10010881100401d008018004403104d030106d5581c0656202c95407003080d1606d90029103040000700f00e402140e20041e0040505000888440c0d9903000ca918040c4c44007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 635987473 1250 635986223 635986231
    0x301060e12011b0c111c03030b2e0e100e130e030d290f0d03110607050c150103051002092d10080c160807080d0b1809150a0b0a03120e0603 61
    0x600440000d040408d019a1018a98140181100514040b4165107078002d07078881050844070a0390315007502c115035220421000b4078100302c408400010500800030400070b8000101c0d8800e90000150441000c4150b01c420780710007024041c0c94a0352049600f02d0010324020b00c01d40b082868400b501d082c00744203a000c0c2c04003540d00030018080c0e0243c110030b000340cad580c90751021401d000524400c080f0035182048850711404883da1540c1c1d4070903a080b2079a050840ba2140301080181d44d00c01840040e101003142c0d9140d5000800041e00c0e10519070000e00c146945d0a0309150700722460360144503140e0401d4850412a60955024036400c07992801141d200100700c83c40400b00b1018410b000c90203e040c40911040c601880480d400d00c40d032500e03884d82940c040d086004c031442e0344e60b41c1c488050502003865403c915a880c094a403a180c0000700b6030720b4220700f07001010180c1c1000700051001c41181d000800011016020007101a181d00e402c0114103100240e2030040344441c0e070740703c2041c5001d508903846 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 635988723 1250 635987473 635987509
    0x303091409010936050d0f050307081510020708010612080906090d08041401090b0a080f10170102090f0301020f07120302040e09010516050301060e12011b0c11 70
    0x11030b03203000c110764020120614000079049200800c5a0f42c2050501132048880c1c00201564840289241c072901d88240a03036081e050040c1407851100090704101902d52000d03250410119680d15100c0b002c0304188042c1c840d6030710102c6c0080c00c200d041d80c00543c1c03a080d11001d400811401d6100c6415645600940c4801400f00c3c008210f0340040781402e4001e0010720002900c000110b41c49075464a046401607041500c001c0d0462014440325a48412160010324002a100d8605505400000d05841004040030385d580900800714022100d00d40b5520028030106820704100040c000c00d46020394000c4a180c0c1c41014015540760461a040c42100c141040c442d82c0d642c03501c280c40d902e41c0d004032088840c071400d240e0709000c0054107120f8992000c0c4a0b94600e000060380e440d0503d061500d04082c10004800c003c03050006114107034029603003010108040382c0100c0f035001d102800038050418201015111581c1c0d590400c000381e0081e000c00c224501c1144d41001c0a0340200502c101400003410440d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 635989973 1250 635988723 635988739
    0xf0b070f08060303071506080303010308180406120602090a1a070303050f01120308091603080301060215061c02060d1506080702030705060604020901020f0d0918060807060e0a12030903030914 84
    0x1407000e4000b20b02e05000c0c402c1c00703d07c003070380e442c801420364000341e10a0303400800004802460204c44072b00303592980800c8408001d80750070042031124400c11000d004244c00d50000d00000c081c3d4500c46000001d11800000c0c1035079905c420300c0c0076016000894214080ba0402c00802c850104e8201228140e421054200000700c2c540e407011202d181015004420a0103a001090019005000c0d040040c600441060f581ca525200c0000d05c0d0a003440081d1601c400c84000740081a61414407035824441444883c00300060280000341851047e901e181c1441440c004217000c2250900c19001c044489035100c018890765020030980e240c0c4581c010040440d0410000a801c0e13250590107000c50b040103104650b9548c0100d03506516098040e040c48011500d850800c10900040031206e882048001406001d824581400310b0390300d0455000341c83c1400700d0401c4541054903072070703e40c200030b046580010210103034604015203010b01c68002500040ca14020101e021000fa5402d401c0300800903000d45 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 635991223 1250 635989973 635989987
    0x30c0f06020c06090904030c2a0e04020d171b0114090d123c0509010905030313030e101205060607020d0b0601050d06270c0c03030e0304030f0b070f08060303 69
    0x200703600d48020011821700c0b902d0752124000c540e2140020035902d5800320941c4c01c0e000c100112760380300c5503203900039454501007108000040e100e90026210f41c0f9400b21f900d6035503a00242c11400070380918011a001c01500b0702685140070815002101c1d03840c00c480e01030b400380c0c0f0b442d50f19944401c15034441d0004078170001d00c00d0000000d81c0d4484210131405800113070000345000198202c0c6803065440c00e00d0b00c0c454548031032090280c0e204440d00705203410000c110000e8603079546a03c9000081c50905049010000e010038103016035608640302100901070400b00001840281006c110404454034807407a00000035524180081180c18241e00240f403e010340300581d96503200c941006040e00d04100003800004044286030140001800b940d800c0e0101c0c14650040080510040b01e60700345001d8107090300320940e44d41120ba445240350b01451b001c54138100384480c0034a14400d0342d01c014043ca210100840038010300c4d0003d1390007403802d03941314551180304060841d0300745d50903918280d15030010000300e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 635992473 1250 635991223 635991229
    0xb0702010507270e09060f0c0a02150a0e070312231b0a0203101406190b0f070803040803190c081302030a0c08150106030501210318030c0f06020c0609 66
    0x803038405981c098907411961388900745000041c0d025203035003003540e005400340010320b00441080da601092134204030f420900d85c400000d40e10715901c265820f00c0c0002c2d501082215205400c0960a8017041d8215030345a1b0b40c91400040f207401a055840001c4c583c50101c01201c0103120301c00d41601c0e0249061b50a1281c03030103c03842c001c03114088144441c400c00c8401c00068400380000003840c90a000e000494015407004124103903c02001d142c46803000400300c92140060720356130001d40b541c60702210317161030348000820031504c20840090054880070042008000c96500190300c6120b05031100b00800083c81814016160700d0702c1007001090a000015800000100404462500040072181c02d244540c0b80c1412002e400e40242d60f041e0029000e440061844600c0f4074014805445e042009603d0503068804488401c01c0d020900520141e40d0014584039107000c008500e9050218486141da9141000181d5140e10441e0b8040d00700d1100003440f5030000c02c41e502d508401901d0940303000245030030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 635993723 1250 635992473 635992517
    0x6020316120e09040507090612020a151101020414010906021605061c020c01060e0c0406080103020f04020708270402040e0a050606070c1401120c020a061e0c0201090b0702010507 78
    0x141c0d0081084900e04640e5039501c00040a000f03502130405804c0c2c582c2002d5400e010b42e085600b01407a410600c4001a0058035420426002c4440c140000868488046804c80700d800801f1032101c4558008200480c0e4100d6424a100380c002d401d80724858040d80d6480181c0c1c440602d02024240303071410820800490600b03030010f200102512010b86111410305091408070f0f0400142e00700c00b60764507441400301d1204840074039048040d011850303081c00c5c0391800007458904c0c140402405240d20880d07504454482d50143c8400c9980706084039200d4500c031003c0741d0642d40d4482d00034038030304108040000c90700389071080f903041e589001c0d000a0f103940c80e030020300c0103800e020705190b410020400240021030610600200a0100003d00c450417245440005140084c01001080c006161084120f482c4fc1c0000d21540301036401400814110306100105010300110104d00c1050380c1072000001c101039040d8403811140f8801c00c3c0e4901903071074a2504a00301c0e0b000711440000f05029000d4440301c0341c200b404c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 635994973 1250 635993723 635993753
    0x1060e01180f0b0418150504051908070804030f0c0509090d18090501030f0b01080d0f0e01020f010c2c0a180e1504050c15180a030b0408040303020706020316 69
    0xc6801c106603c003080c112020b40d4410801c032a01c0c81ca0304000c00007401109284401002014005800e00f0b0300c43d0b0340c80704101409110301b815801d2460040080d04000e564030a0b0300100b00766180c0341e40e400c0c0b180d42510498012206005184c4001c10a850b10303091146c01441808001e2080f40d140c80e50550f030800040e080c40180102c03410f00003540d1310050250318040d6215440405040c240380c60203150084042e0000d003415000041c83c1351080341d20800640c1003106d2071134503009a0400d440143c2c00c000b00d2a11803440d9500f400440424031340c0011482101c1400d050501c2607140043c004140c618940070046540181d480360104841c22001d450800340513541880084d2000182060380e103800f1480004495145c1500300300300602c0000d01144800e210b0645107a000e02041000d804998419070f4004004500c00c030039071184c0c85e04c039035480308007559100b0460300d518103003420b04001c13640144c0700c100e0040c415080080340030340c804401d40d2000c0c04048034142030500c95698200c00440c0842c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 635996223 1250 635994973 635995001
    0x20d200a02042f0a05120c070605040305030711010b090705030601180f03030f020a02010804061508010501120b070f020d03110c010c090e070e010824100806010201060e0118 76
    0xc8141005a901c0d44030b50314000188840025001100c420070601c1018005240c40b0802c806101c502d1680e03401c4000c03501201d141e594045d00390b80c0e80400d1400c5500030f148014185600e01802c1000b01600f00c40194000e100c1910340b03840300401383c031005090340d0045c0c164603081402da20104102901034000355400c078505043c88c041c68175029030030400c3c10341e1551040360042c0aa010400c245070300643c80d0022020790303101400c1c102c03c480d000030780308400103032001300081e54551054200f151500d000602402880b0000e00a23540d450190703258400750b010050700c0f040321090100305035070300412140c40d00c00995005070511b07a119074420360040112040b58240c2410400038114500028422000b05524603140c1d00b13007640c10114194041d0000902030014000c406800444030703a0002c40440e80086601c00d03603030343c074071b44407502240020b001860941c12007112048005801d400401840c860942039008124207070355001080c46550b420b110720101050305440310915848544c2010407548100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 635997473 1250 635996223 635996233
    0x3070b030703090f030c3f0509030708010b0a05060304030918061a07030311090105040b090f10080f0f01122901060315050f0f09040c030f0f03030c020d20 68
    0x90f1900308456440131011400503080194201c100800b1072540034001030100902d582c550342c180988007030615000c081c24040c80c003d0300c4001820340706108480d281c4102500359940c10f942c07049294080c0442099507072244441c0a8041207505181c0140e03072069406503503209035a1320344000d50301c80040c0e038035281200715201c15000c1441400c2035074003a07010010304021a6164000e0a000b82141c00c0504a54034440c41003000800c541c0c4d110080e201511103490880d0b5807440d104000030f03031070a07101844582210702e2901c00c10160b41c1104245100d020f0034280614140c2d140d0700c1040707089c2400d000b45052900c0c01c3c100900814030041c0700c400d0182c0b410303440b007016420405481e14604400d92003500040e48034000a145460507103240030007040191030180c102641c900014844c1d90700c00401a0107282d81d01c001400744150182c0400c01180c000364800d01090b42030500414400c001202600441d04043d20305007103d00c00104003a805030203540d03c02000a04c40e503003e564603081d5a000c0782d14807031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 635998723 1250 635997473 635997491
    0x307080a030b1507050d0201051005062206020705150705070e0a020903010614040e07030f080304051002030405010c0806030c0a090c090e090105040c060207080604240212090705060903070b030703 86
    0x5425007205580204060b031074813040c0c9854000e240515101c941000c42e41401c092006401005855000b82c1c0c0d001c580003901c2d1004001d00903100c000c11002e4007000b2200c0390b4002490b9070007180c80303422391b40c00380c2c0c40c0b07800c030018000c024140c0d2040403402070640c0e0245408203c4407001e14544c43d0858140c6c040036242c00a030400007030a48140b500644110484801c031009546090f00c03903c100b030604100688421850350320f9040408070002c40190054100100007020800180041c503000322903c50219140e0606091250081c441c080307005000c205104c02245c034074500020404d00300e200c01045c4100c40c81c00d0076003240150502c10103041c2448400200411007a1041d400c80303110344144400045c0c140b4040c00c1001c00b00a040c0e000c41e0a40d0406070b818061600085191580140c2200b40d0030148043c0744044c05074010502d002405152000c031360050302060054495014170911401c45056540320000c01220b032081c200c00c41d42c55400700d00100301d15043e01003c1c50380484241000251004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 635999973 1250 635998723 635998729
    0x1124060f1818070e16050c07080601050114030108030304110310020a0c02040f0b01051801170a090c061803020d060207020a0305030c12070c030f0507090e161203020307080a030b 78
    0x3494038201c201c165120410010718010380c4404084030480b48000782506840c050500801c03030409400221309020382c500d03003c25540500d01f241c0c0201117100c00c6503403207551409826107986082c081c4030f0004e5a003d10700c1c16440e14a0059034140d602e1030300518a50748540d6201c80c03084111107101078060049054940322600c4a00c05400c2080542d00e88405070845d610400c01118501101141c80600c0c0010160241e40c1c01011b071036607101c20f684020600e101c41c60041e070b805940400c0071086103038403038200602014140c1024602074825240c07000b125464603001d60316012192000d00c0b02a448880410151414000d020071043c05400014030b00305050b00411034080c041c0d0400e440711303400000c00a8409804100c960303070072421011801c0c1059a15603480307804080c5403001034901410500b007401400001d10241c0700a15441800700702000ea01e4500913151803c000d1075100b0700a80b900000b91607c0d00c05803d4a00c01d07851f038040c1d45401e4a581d944002500940c406108055440b403002916803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 636001223 1250 635999973 635999989
    0x30906240d140f010c0210021e03090a0803010b0705060a0b03210f0408010608101427010f0509010c050c0a2a060503060a170a021003180b06011124060f 67
    0x68104001244001d17034403e0182c0742940c0c5200505030b4603c1040341c9211241c1c10012095440d000501c665940c0d00c40c0d0628034508030070144041c1070680000000100025080300400b086881303182540c034103a880008100880e1035501030b441e0180c005d2a56150954001d801c100d41c5c143c0150303920350a0100080c080c411075005504600100ea41d50001807096039803c110000d0900c0c4046c0e010b020f1131480001c004486072001d01011000b68111317920b180c0c0c03004003080c0f05648503010340c020401020800c4c0345034050201a42c11019a508c4c10260f20f004510034400c40d07507907841c84002000e080403140c3c2d40710042070f01103603100040e0004080d200e00c000e40103402400203010650b505900e0b0b00344032007004101301056000c25003880c2c4400403418a20008140d0b1021150101c52500120b1841001540508a4107203900392a1510081d40c104200950304a00d001c0e079400c2e41c41c0d4000996643e0350950790903141126135204a42040c1d002c0e01e8080c20901d1984c01034000c0c1c02c812007a0b80c070704040303003500d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 636002473 1250 636001223 636001243
    0x60902181c050f060f0906010f1503140f0414010204061d040e0a03031505010804030e0409030e1518010206220c09022d190302070204060e0705030906240d14 69
    0x350071003424840c0750000b0310341c801d4000e6800009400203525040e120710800580d4070651844402002c18458ac0358006e038041d200d1000c0c440c40300c41c41c91429034009003400508071402c03a03900300d00030f0304000c01d56014429101130b5035007a29002107580b00b416060091400c002c00083d41300351607040da0b0802d42c406100001e0b11522a84000c1a00b0b0000301c51029590900c0d00503904001c41d010070840405d900c101c280c80303071400940e0001044940c50400720b40981a0320079103500684040c1c01c0e091949038a10042003104001450b4504825618004988032002a0b4001049030491442404d000b91021a186800d6224880c10003c0650700c04444040e80c1148002803410040003043d03503500200300d060b85001c0c0c07070302102c1c42c5c0c40c001d48400030500c280e0710701000381c04059000c100001151117940c000e1026000a45101c000b9280088000f8019401242c0c030070103074000c5030081042d04c03c000d4006052400d0307540300003580f02d54000a2050000001c1320595074441090444080080140125005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 636003723 1250 636002473 636002503
    0x602090a120b010e0c030c0d060b130906050a1214030d0510061106070f1404121101091d010303050d1d0105060102070602060103080901140409020d02030a060902181c05 74
    0x1207203110b040030010554164458400440040c00f00090f0501d140101e83e48401000c07442a15201c01e24401c00007400140c0040444d0907000600c032040d0061000344000304e402980c4240315490f12030041c84958030344ca20030098030030b1446c07003030310300281c1a0001621200001411a07003861a070341425029200152102c0d03083c03501c0140d0a2012036407007146c1050030700403203000381000d0800070350041c52030262041030020081c0d00c2103200410056841114018003400c041c00d01c41c41c2640c00d285014010f020800ca01140742e12100040407554481030300e80301d803007161460296078610348081d2881d500c1241c101d1045559002d09509086e6400503505907001e40c10000038440c5804070000e441c102c0302d41c009030190f600c032500410004065278100c842c0306001b80b178040d0404482465010703550150b0340100842600100e40c0074030000e595809507100c4c0c0c0203070406020f090381e0764103010124428164040600c5ca02c0d500154030070300b400003120100b5590742c140d103001214281c40e014204100101e042c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 636004973 1250 636003723 636003749
    0x20307050303011e080307030c140f030309010e0724030902040624080603011e1104030c060810091e0915060306020d0507020706091710050a0207020102070821070602090a 75
    0xb13410700000120400f4100301d1004510741600d644001d4a00813007194024060000e01103404a0603c2c02e10104a42a10510491340c60f820020301c6580a82000c01403114584107100b0000350045802254084442c80c081c0100d80c000c81115044000c2c203150b040903604075031603440005204026615100301041c00c82c410303600d40341c0c90740c0c0c00900e8041c0203420984a603060002c0030701c014800c0003041140e201c102100049800700000950098002c4d80c0c005044500300410010f280c2c2c1e00008090b01c100c58000142e004141c888010fa011100d5051201c015581a810361030201c100542c0940b1001d401400b03a00451000c0c034404600b51103a54208550350754002c00d2400c6004074601486400c0829030024162503404c03c0700c0100102d0051040142d207490030251009009018041d0108d007110b0403006000070300e808000c10010b54031510f0101e005200340840002e1419011400c6c0d91140b045155401440a940e04410001e80003141e041c7e0b0341039420000074032196030307100e0910010056481401c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 636006223 1250 636004973 636005009
    0x406080a06050a030609051c052a15180312040b100f150905061206090a0f0c0806010e01090b0409021c09050601060801120203120d0e01060f150504080d050a02030705030301 76
    0x7c0d007044000041941e003d051503460b0714510340c0040580e04601d41c400280300b541c045c106000701241c0c5021840c2c1c031280c001d100340040c0e203504024400740b241940c12207810f4618010030b100c4c1e03074074400d8a005e009041c072020046400141044e01c0c00303400031120103041040b261210003c20303a610203540032a040c44070f212080300909401c504500003e080844599041554030350074000c900900800441c441c49405e00054012103059004c01d4144c240000e0400072005042ca000d002d082c2c05880f1a404182113032600041c41d0710561600342038a908900050074213150a4000c4040c0d04196103102c8003110030414061414050710950075010b02440c0200307103652401d040500318810680010000b480800180005602c00040d0381040000b904c1000c2c0d62001a0310141d002440e6032066601c480d4201000002d50000295001007541c0c0410307905100d0b000891404d6036584202d1203400200e4002554103c0c1c124029009019218014010f80e842c0851550381c0b581554000d81100ca08064005150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 636007473 1250 636006223 636006233
    0xd121407030c0306050f0f040e0a080705012307090303181a09040b060c030901210c21060302031b150a05130f08150a0e0304080102090319080406080a06050a030609 72
    0x2000040070b046e03c0c2c0d00c60341000e50000c00c586404202c401406036441e2140c403801c4000030082c410040e03410901c10342d15150f0f00d14199020305035202c1c1807015080c800c080055410754501c26280601031544409403041c1c5140e5058811591102c40d1000c0c52504010004941c6c07410714528403000400300c2480e0780c0310030620802c0216041407480600981c41405100c0443c40d00200301c9580c1074090804c200d040b004c4895007041e10001d407803181074441c1003481c689451a0490103502d603042023410400c401c0d003641c81c41c0804407030030ba22010750705600070200f04454040310220b600c1408400343c10032010318000302085540ea801110320100003a000030b10321075401c1510380500c005e401000f650004103440c00d070710b084d13072200c4000d11a218000a040400c40900950380201034422031702041c1c0e0381310340d655400103000790004002d4a009002d0031a602c20041442411441c1d8264040d02d054105403c000c011950028010240441d1036510074006c40e8941c0c038600000000c40c40f4510115140600e80b2308 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 636008723 1250 636007473 636007481
    0xe240319080429030114040f0e0114010905090a0f06020c0a2103060f0501030b0301150b090415080d0809010e15190510060c110d06021b0f0d121407030c03 68
    0x400d0f80d002140102d5001c4100a18045a044a0307150707580f50280440c0500107030040c16100041c5080f507281130040d01d0520f10640044d4800b1100190490a680e41d541c903a1b0295801100c1d20003e5402141402c1d001500010510280e03600481c070060901d00400c9986280844054050310011130100f1245001e803610960130f1020303215840c040c0305036480c0c0030300180f03404014021581410f80310281390700e203070724250711a401d415141403000301e110b0f554100034103180d4051300b0f00310b003d070b410900d09074140307120a00b542d01220382c42c00092400c0c100540c0215848072010704070042d15500c80c1c1c0d1000408008000620038044400302c9048a170a010140030358684582071166003207800e1000700059007001c20b8020085550a0418807030040e40e0385014001d00c500c0007080c941c0490300080c24402e02016502030302070000d56420018000c040d00300103540d1405007546040c00d540c0b02600466030300e4407a600645200100c1d04d808909190340b402a10641c060480703000d4002035032002c964500d507605000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 636009973 1250 636008723 636008759
    0xc1207030b0c03090712020d230601030b01090606050909151c0b010e0f0f191401080d0e18040f060902100f030b19051002030f04031406010e2403190804 67
    0xc4031b9400c61a07a40c04207901505044001e814021440c00102d03401d1a0710210380134962203407007520601d40e107915007209017941c207000c0d0a00c000e02d04040130461500601c121003a0220080c1000130070b90352050354040c4c00c0604500142c2040300710f207816100780030000401c5102403041c6812409076040482d00481190001c3c03105500504580030300c1004401c4540c0c0b40e420074296820f0403020703a010040c03003000e49850b00c00504080306410001800b40004610122060310640d50b0713141220780b800812240000a8001594104581c070104000400820900c0d245c50720942000c940b10100380c0009071366001e9a102c600c00708644100e034211071680341c403480c00c2941c0c00711505071480c411001d40c1c104d0001903008880c01140c1c004c1026001600070000e44040381548490300c0c0d5240c1d00c80c50b2540c000082c80207074518600ca550004608446492a124841d84d520303071100102006030240d040c50180540d01c1c481d00750150400002640d04402c10345000b150044070401d076943e140c40c8076004c05002c1c40e8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 636011223 1250 636009973 636009989
    0x2011b170a020414090a020f0408010603110102030324360a050c12040206280807020712120e03010c0509030c090606121f031a180c1207030b0c030907 66
    0x100601c41080b91180c2c0014544017a5030301070741940e4084808009108031459031f03109074804500002d0526054004074107581c1301d1181070540ca01c03180010f90b07a901003a2903552159081c2042081884580c0c03130019185440188080c2c070b0141c10804000c05881a400d00e000c1000401e030716818030890011200760070040e281070810482c03070400101c6032640206801d090203400c0c80d4010400307640c0e5003411380301c802801d000a5208440201e248100301003031640103002158982000400c1a030000c281c4c10201c034012000f6040540d0380f56074030b04640c0008461031040c01603007806407000e03840034030504580c2c50741616601d9440c0c0940040500d030031061040944034a0803581009030075150b400540d00006107001e0710349050385448040154900307020341182001e0341c1100001082c800080d400c2d00342468200c01c603a001d42c85401c2d00b03d07070082c1e0000c1014040c2c0e002141d034418900700140704144442203c0c084c3c03035500392039640385a903908096504200d04400401803012074032081c07001c00d004090007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 636012473 1250 636011223 636011227
    0x1e120908040e070e0f1c0803010906031202150612011508071701090c050108090708060a0b01030b03060f16051303080a02060c03070909020904090821130c140102011b170a02 76
    0x13034001034080303807400705841e02a00d0680c0c0c110703801c00d00612125048a5001548079100d6840300c0c9000c009020500c400e445a003079030350841182c0c4d4004152030301d106c0300900100c405540c420007400001c02200d40324005941d80c89268050703030b944030010400940108005482c00d2441d041007144401a12900f8070320503450022004c00203903c0c003030442d0450b4428208079440d82d13100084c1d1030914101d940502c405014203c100034403080d440e444650a52006d07202000030041c1101819a654002c030b4280d50700e500201d0204a00f640c3e441200c0c40491014a0442e2506c4404505503001d14003035881115441c0d03000c03844000703940c0c042c009690702c2110300f10300c9400d610b0300c103100521426446c40745800140e800588400540c440e42c000c107410f550000000741d80e440030081044081215590404040038420b0041900c10861100f503a070031581080850000d40e091451400f40c28803841c01443c1599610318100d418010021a80407030202d05446040c42009960307480b80b5100f80080c81071517150300c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 636013723 1250 636012473 636012497
    0x102120f031609030807050303010e0f0601050a030b1f020a02030d03020a090306110403060207030e0301050114030a02010e040b030a08030403030506010309030c060b010c02090a0f0f0207031e120908040e07 90
    0x348081d01d0788074001c014004a0409a0107080d00e0400352900060a801750000b28501484000401181214003201c03580d0441d036a000c0d03458568400a82c1e6207030001c3c80c200091181c007031007604107103030814005007080020a010141007645042162403480542c01040c43e440562400303204200c40401182015403412080b8800100895141e0000038021555000003450314640030007a04d0255074807403811555960107060180c43d143d48581c45070312942c00e10300003180310800205100600c52000d8014000c1030415801900c03e445500c21294107d81e580340f081407959402c1042c0c3e82814000c10303c0c20341da400c01d420014155080101020305140c20117010303038002079124034484c1034240c10550000d00c214640c40101c0e0104138006001c1d40c019030200510074580d8923540000510903a803902040f551921034102410381c06454000b5012508141d820b0005c021403182d0b4000090702c0c0e280c0902c001c1014401081141d4200c4001c0d10081c01c007003018419405c038040e009400100b82d040620345624 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 636014973 1250 636013723 636013747
    0x606030c0a06110307081602030c04060303021f02120c090102150f010501110c09090708160506040e0705040915030b070c0c030311031b010903030c0810060503270a02010212 76
    0x1055100b04403c01039641c0e840d2210203000d20580e04256400304400b9501c030310b188486030620340b10040076446402545540006454107200e000c00701da902d42c02400c0381d00c035801d031104010138a02004070002502007001c0600a082d0000140c840c401d03581c5541e8950040c100028900f48840403004034240000f400e000001c189280d0541c110764003440d0459500340c1101c1ea02c2e090011890011744c001030741300d0030b115160201013808400c1e00c1c0e0718412034220003105659070039504a40d102da644c01440400041c0401209a140150301c42c0701410020310740b503034401ba080203e40c4009080410706104c01024010890070703030303010f64014000385481904450181c54840c9164000d00c0f005003406840b4005410170403003401516519513142c0d120503030f07070350340e9a8000f07018003030200040300080d24050381e8010290040910381d010b201000409004641008410794071903101a04525800390016070318440303003051003074402c4040c450402800341950321348000384c82c1903054409442555020704c241e0840304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 636016223 1250 636014973 636014989
    0x20c060108010507180b04050907110105101e0e0a0e0106081009020a09050c1c110d060e07110712080d1127060d1a0603010602150c040513050421030603050606030c 72
    0x2384044407014050780b640f013000d0724030840504503190594248000c2014002e416050001222a403a4100b00043c00000103403c240c91140104111902c146012850b64200f562108485903008400020ce154454104514000c2c0303580d0800903080d110050b00d811810655171403001010740701e50902c040d044c0b4800382c140b1030084401d60441c0f0394500a0700d8070205041d40210500c0080340484075514043c1800c54805081c01e800307180000040100450b101520442c906501604600c1c09416200d04014a15014505c0d046090300d4404041c8401030f049441031003000c0d0b003009500b01503540d4440b2080004d07545542c002100094107500ba40d84c1d4841e480d07400882e4402c440701e200000c1c01444400c800917401c0d0310700643d2a0031800100c0081006900001d10030f22880c0a0f110303a142e1075036500c02010b111310950160982200c50400e04061034600c64000d01c1e0401d111310140000c10141001c0c0114020090031003500103030701c4590820a00c4001e210058001c5400e4020300800c1c00e015021a4000f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 636017473 1250 636016223 636016229
    0x60f030703020d141305011808091002100c0f0f081506070614040c033509010e0d05010c1d150a120c021506101d04020c060108010507180b04 62
    0x1c5600000c103804240d005502c010001000100d00c40ca1078106003401d40461a00d9540c12642c5620f030040400075000200300212000d94080446440e203503d05090100003111980b1400c2544140040a52030f0340030360189102e074006641d10005003100e031520080150740f522900e002413040d00818400c6a00c1c9841818050030300a8904076a9102c107460498010f001d0b000154000e5101c510611042140c00007810381180d00941d6088014041003540580501c0b213944900e070103642d00a199140c3d0350689024110940c01418018540f400101c0850512002c4900803601a5035a000d9004504d41000f6140c00c1004c05203c15154110f0107800b180003150200126004603e021031108a4640f0580111510f551198414001d401640c103001e941c50b10300410701c8071005880d10018006003040c8800008110702580c48052030700b411140b9119081e04480240c0d003041e000c01c01c80d1440d2208000c041e000340041400000e092401c650014071070464261100030107009a5420010f1f400da10090b0342c25 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 636018723 1250 636017473 636017477
    0x5070e041b08042018010503010506010206070c0f020d080304060e07060518060c0309120601081203060d03080402060f0403031101050c0a080f060105090a03050a2117091015060e060f0307 82
    0x400d98131400d40340c0b10607140103015035210090398001c0e04102c0001e21028100c0e6001d8009000c3c645842005988a10040b1411000224660310550100303d4510141402074000782c8810041102038403440c1c11740e40b00b281c00b0340d1b01d140c4807002d1002e400c034100f00340e00043c022450a1820241c00e43d1b0050007c0d8881691184540008105601e503c581402101c8180e080201a07034114801c4801c056200d01c42485000202d004002e1041001d21075181101d1089400038410b00c4003445594060745e07000b038054026a00040c0c20301c0a8184041121f00910185000791030704072000c200c080f01e003425150010021480075200b4401308051a401140c115008405400091240e82e50400100c905029a281840e40700301c0d10000042842000f04110f18020300401c00305000b2041e9100c620303040c2c59a1000080003a0208011190592a1109030b0b9040f500c201c0c195503046110b40300e042c041d24402045906040f0b2000010001550043c1801034410002d03a400783c100700c0188500851400000e01d80e0003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 636019973 1250 636018723 636018743
    0x19060803091509040c02100b03160509090c0910031e0807080f09030304090b010f030e1c0e03010203070822080301150302090306040605012d090b060c0105070e041b0804 74
    0x94030b00180d100303a64100002400401c04808503020003980e44a40030151004c00c0d00e800b00041107400c0206400c07005200c25911075001d0f6203400c061140303a91008000c180035000d50840321001c1d5840c1d1184078040d00398148910104e90a6041107030701e100031940c165880601504079038000424210580e108550004500341d2100b240420f1041c0300d110f203d2030039905020016000c2081c0545500000d03900d282a80c611407040314004058044070002e8150304100e910030480302803140e5480503403441d46680351402c0342c0c0161588002c00e00ba0380040c1e9040d0302103518030301042003161311950310310b00b20460390103141c0d0f8241c85030716109070620045c00354014a4000f0103440662038000d404540c006407000c0d040314a2403130305d0b0a05000501302805841544a05540c440e401c620815030b0141c060429100802105480c00d40c180e0001d00310358400b150026010310001518210a00c142d074492142501e07803c40352095041000102d0780b8418401180700b400114040d955980503010307540c07181d03000c2c02c010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 636021223 1250 636019973 636019999
    0x3060109080f1b04050709170304050d0b0103050c011430090706120c02030910141c0b01030218090a021317010e010504050318150f031906080309 64
    0x2a8580c865410404403489912440344030580000303505403040e901e80e00400c0040002a0811051300c0702904c0d0740b800144950014010151008030100ca01542002101c0c9030550308c9001c560745010030741007903c0980c0203d0040080c020103000c1020301c15824a03000742d10202d040e03286942405218020611005051030701e0f0856040c0c450144458603c4d140264807a2814401080d52030310b81c4d0007184002103103012034518418541c010744000e00d0541d00510306210103030702801800c0c07040110450400c00700c44c8848080040440040c01013028865581e11030030090640034060302e0b001e441c00382c1050f01c10401200c020100003221003201c0000c484c886c1581d25102180301c0070340112528010501c00c0c1000014940030003041c0c14404540c804e0090110b1414110000c0c201c450450b03014020b40c10400048800007507695601c0d600620080c0044203200c802d0b0f41d001140e4028140c0003500800000501c0503071100140e240d03031000d003581424080c05040602d019200d00a8290640c060401c0c81c07065 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 636022473 1250 636021223 636021227
    0x110405010f18181b05121506040908120a0c1b12030e03040609031103060412111204090b120c031c031d0327010507030c05030d0c051e07050a08030601 66
    0x195407800d50b40010a0b034030705400e05008004e201d100f140250304400c880c2000a4600340804004140b49032500a00310702001c1c00c0510303036070410040070b950f402940c0d440300200050404010303200c00e5020030a0f08400707103043c050350790481300d503482840140b2400751010400c3d400910b0300041d1031a0310000001ca1703441040b801760054141c000c40f42141e07000c04640440c01644c010780c44030440b8020755405000d030700041c0034162500410386010f000395100491004401c1c2c0281c0e000a08400c1800840c1c01c080100d9004e88001d40068000700c100b1501e50045503d2841e1504801705800c102c4006840503952a10000c0d0ba20590800b40303241d501401d0844c00405030080c0e024000480b101c141c10b26031101440403041c3c03250300820405c1d50540c2d0304052408400c0e002e902403140c0a1041e150f1501d030045549040d01c00c4280a03404070b40503c010804984407010b64080d8040b51582c9844080d101c080308016400c4040c0210840b80c5180300611000300825400540080081d401c1804541e898503a1001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 636023723 1250 636022473 636022481
    0xc050d050a060f020901020c060c06010302190305070305100c0f0923060c03031803190516081c0f0b03060408161a09060a0504210509120703110405010f18 68
    0x54036092420b001400420040c4e0014600740d03e099083e00c0c80200480208843d50090800b5065141e0203080144010304241c481c0c0307040c50f90003440020344550340f56121407030043c05800c12507407078105140840541d0300c14025502080054100385400d186c4001000b0a40002c9201e1001e100c400b00c2c414a088034203600c0c0507039800070040d00c29907032081030880031550381d4400c0d41c115a14814600603d10f02d0540407058480c1030114140c03002c000884a1710840d0700e40c200c20440c42c051800500e0100008401c00000d082c0c60074492440d018203414104011300300c43d2180d40d80702d881820402c507011700d6900807a50a5100780e1018846440d100e600d0b1440c088080700603c000c160a0741d030014101107000440d45544181d140c5d90031510300c2da17030b2011803405880301564020510418a1107014001001c888508829440c1d458040e00b4541c842c40003491003056081c110b00c407508031080c1802840110054001f03c40c0d01642c062005514002103601c09410310703c42c031420352100304030075203403920300e0b0b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 636024973 1250 636023723 636023743
    0x15050a0608030703050c100203013c03050f12040b0904090602360d020a0e0712060f05030610060e010c030306050603012d05030c060a1809020c060106020304030c050d05 74
    0x40340c0c1c50f825289400742156010101c06a518030038100a0140301a0078000c81c3c1c1a268090880c15616001d8858071400070281404942424001c88601440c0ca1200c1d05c2d01c4000e500a000401303892a1040031a41040d07020368000c01c58880400060043d044180308803092094103640000305c0c04c0041c1401802405047c0850860a120b840500207044c1035203400c2503041184109402c6841625007042404503a09070001d4001d4580ba01c10428200380001e40b0b64050000c0c240901c1e10b0344030400076400c840c2d0300d401071480428900c200344004d0500700145030348050302000c50003200742060b00143c10785484001080c1005600249001094880d4015100400e00034107116201d507198603650041c10f41da0f1904560085d90b40a440140c6801030903560304603040500071b010231110b218180042a441442c44000f4070492152a54500400d2034100c0000e2140c40401a02c402c080310360355003030000c10780c010b00c00c540c024001030010500180142d400c07100100d51b038500daa1494a821802c01d1002a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 636026223 1250 636024973 636024989
    0x3190c02211603080f07031803030b1c140f0606180711033f04080d060302090a05070e0901180207140a03090302010f05160204050c0702060d0608150415050a06 70
    0x1102e1404141d007040768a0b014603601c2407107032825910101c0403401c40361504000c19a802c2101300210100e8061780c05000c003007030080e12214080180b41d0f9800d44080070340c1401c8403140400c48145149200a104141c100c400040280c4400e06001b000070b04980b044403854000b028003c000720f8001400b82418580110182e01a40e889100c143e00420a22614585001400a0350880c00d80d6501030170411804000400012072100e031160345034511550810041c1d1000581d9500b404805640e54600a500c01d0a511802142e245004007000302503402c080e443c127015426034001400b01c079045101c1550050001d40d00141c803140c181c14446054a04003400ca184c600a0300e04010605a11800e03030740c1624000e882e115020300c41d28070102e8052003001215032104410119220051600f60061900700281c4c441080c102160f58000841079030001c580006404d580700820416050280108001114900b80c551505d00d02511592078040180804103209551640000c49102c940c0c1e000c403015091030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 636027473 1250 636026223 636026257
    0x1602040b031504050f061608180c0604030803060406140d0803070e3f032b050106080103060f0b060304060b031e01021e070c050d0807061103190c0221 66
    0x43c00e02079217400300405040464041c00c2c001903800100c0c41e0b000b400140c440c2c0e0305c06031a59298000310003c1c40310000055420b01502408207426a1500060130140d07000321400c0d60303a030601c80108001c0303820990160b0b443c81e0240d014a00556034402401200c940c009000c0380d82c1b6a190001104c03181844c0c641c1c66803007075030300040c0c0001d540c4505074000f20040385c07d42d420b2406210303190002d40e50700190311040c0c1c0e03620400030b00b075035412050140841c4114105501d0b00c0f003d820001d03501035400036084030b8001000000104140714190103042d040c56070f0340008000d40084080400d01a1000410103400c480d11078a1080031038078100f150615500d07011003004c8000c01184480c0303010758031001c80400c808290100396500040c000e001c550065910480c1350010b246410144201020051000c0d0381c074a106004d9803003c00c45600070401c10010519003d5034034901400c1c0d00c084014002c091000039803420804a42a540000d81000c0419020760b0801940b60f880b01c500806105100e1210880200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 636028723 1250 636027473 636027481
    0x9010303051206190b0703090906080c0a0e0403021504021c03020c1002010501080709090c0f03060902090a090c0b0904020d090b09061b0406030c0e0301020c0f0d051602040b0315 78
    0x40100035081e907022100040003243c03a10001c01851607807000b98030300d000d0a50501000b91603184030061194030712a040c05240c269580590071b0443c1c41980c000b01440d00701d040039428078503000c0d52210241c04904403410b000d0800340c0f80250381384d915696440e000e9241002050540d95101698021444145400b92601d280380c0340c001d440704400010140202d030045010244940103000c4c0d0b80c16142d5074001402c070145009101c0303000c1c2c05595000d4448600540000c1002c00045120b0400b450040c0307404601400b0500c1805604040100b110f62418a0581a42d0004605440a900301c4854600307145d00e035821440081c00a2186241911809250040304420030946045a6224130b50391000c0c1c400c0c0795540c1800d4940d00c2e0034050b54480b030800401081c04817074003aa200301c2202006183c5044407401d40008a4226480301486203034650200306d04000ca4a404c1181c001c484030517103085810070562140340000240b10600c0207220742d444403440300c103d4800300102d00052840100030309503824 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 636029973 1250 636028723 636028727
    0x12063102041e050606041d0a20131a070201030902130c0903060f05010b03040303020a020115061205061c110f060432130e0c03010609060f05030c10050304030e09010303 74
    0x1000b03040800c02c05040c1000076941d4a840e40c1a203044a007118075800e03040b1290a060503c00c54010861607400d41d80300d903a02d2606c110381c1100001c2014080c401956400c030007000100507001580141016130300c0720200c94481c000c08003504c0f191076080c2000301d00b8422610001d074a810001800d5a00c0c1840d00702040d225507031042c01c2c031044900460342007041c0c46c5c601703404c2d8081c0c0307109000c4e00003410340400100f00003900c694014482d4000c03c1c0300000f1008840d94001043d80c1340b9a01c2000041e014101000704100c5074402c56030040c0c800c444601820b018081024407100f8a240098508405903000300d07076588a080da400c0600c48010300080c0d4542d01ca01c288440b80201c083e10441d0580d0012442d48044101d82810010640061100c60280c01800c60040540151074007070016004031340d100c880702e031024010310015201e503200c04269241017900d50780a111040d401a03120380e000d608504265201c030b81c2e45500c52890380c0340c65552640c81d400e0581e0304142c22201c0e160040c401d5000001495 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 636031223 1250 636029973 636030011
    0x1003150e0f07180507020607120e0a06020a020f07080d0c05010608030301120b0901060e0a09081b06060f030a2312040806010905010b09030c10030f0501030b04021206310204 76
    0xf441d81c080d842050400f403c2200c045030750441d040e0b07015030300c840b000c2000c02740208900c0e44c0c80e0b02c0b5090013003003002d10640c150341040c0c1c0d01242240e11a4011403a82100c54051040107000c0446100409100380742c00c2d0704079030320b80c07a100702c0a0030700c03130082d4041c01130040a421100180400c00c00722030f41c03035a61f040300040c3c032410020140c440210140100303491003810300603030382144e13810085060280c8070650003900418030b42c80c00300c44501041081204005440d1038080d003400154010307002c0c62501e001030155030031030310100d54401d801001614000510004580c01c0618284080c070030500030030310b4001e02c1c1c0f4142203c1c0b03e19410011030700180014000400e241a5080f049041c0b0180e643c8840140d02402490a0b41d41d1603004070018050a0070b1010740303a0b100c01c40702e1070003141030000240600c04a030002e810a07070300f8142c2c0c0d00410042d0308104c421000c4c070748803071401008246040b501550309842007003d41c0a00e4140c5802624048107035811907803146800074800c020a0320316040c3c1c1081c103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 636032473 1250 636031223 636031229
    0x904050c03090106080607120f0e100b040e0c011403090109020d0813060f021507051615050705160609081905030910020a0f05030a0609020309070602060a051003150e0f07 75
    0x766007440340c0410451001b148040c0030350a00d40b07a00e108010740d040c214010300000c6019002c07055845002d01e04101041045a814285420340001c220611301d0510044d0340801c107080383d0079407010b02c0c4800c0590340141c20818068442d680c854580e145c45907081e01504803020065400b04501c0d07021018044110000c08084000b850b030720354110b644100503181e03030f4400ac400d403025070080754034032600074021061a544407860340303440d510f0402410f5016910301c07040302050f9030444403c040c1d4800c0d40603a20843c0c3e004401410002c0c2070141c40b44481e40c2141544400501554440e0714a00c10400b1140548001c0c5800e80002007500d0100e80f0014110307001141c135a000740c031400b010b120300c40380c481c42264000d003040d90350120384032150b01d01070700ca07039101034000c00d9400e0396000001100340c400e1002e140908441030150a40c9450414028580360018000000e55841e10301400201180c02d01c00e6412681d1042c0805032074540e00341c81c2401082120110495400f5249440304507040101d200c5c1c042d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 636033723 1250 636032473 636032491
    0x4030204092001030b10050d060902031602010609091e0f1a0601081f09020a02160308040e012c070c05070620030c07140a08010f0b0411070f080d020904050c03 70
    0x90b19401000450541e103403200902d0304011004c2110401c1c0b40b04800500607540078000118074156100901000c0764070407034071044030403240000e07040b5140c3c0c28020f000080001900c18000b0b80d0b095101c40c840056082d4411001080030401da004004440c0303000e4400d140c01402c80c4400f044036080350346100038201e5a103400944d40000142c0e0446119800b50344040760ba00c10300c0540f50414141c08000d50150740c90406500c44c1d00410784d02c800402240b003002d1441400015101d91400035074450811060b000204a041d40200311100380041c9002598008240c881005803900c5146096490764110745018050340100d0380082242600080e85000503840c4004030480c02091003402c640b28041d404001c0705980143c1d500704a00d0032071502007407078000000c0c0000601541c815805007120441c00f0391058658a89580702440d15041c0310300810009002c83c0140f83c80c0040d91007001650300c1c454000c01002d0041920030011180c1e0703050301c0d00c0400280c02000300342004a40120550000c44030818 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 636034973 1250 636033723 636033773
    0x1814010b162a0e04050d03200d060e1b220b03161209080306190e19060f05030c150f07030801030204150317030a14131a010b091201020403020409 64
    0x2051000301680c68412a00080071700301290000c5000c1f07020341200b8032500b1542c0210f000014150394600010710540b101d9420002d01c051414429000421004203102c290300b40d00140c0508115101c0c04581003403010301004020150743d903031058020f11a0343c1085407012004070811500a5640d00310310200c3d81603440d4441501c1409541505444807400024210101400443c4050034280111060101005a814045526010345219082d02101c00c50203000f081c0300800c80b00c040074440d0303401030180c409042c0c909500300400309942c1e800704075110b409540c4201007110925001d006886ca083c04d0101038550744e102d90f00b80100365500038041648107900d0103410100003110020150304807684440040ca4244003600202c1d00c1da00004c0221413125101c5140520490510010328429203103010003844010140c10f0041540d100a58141e09120315000103002e600940341c01d80b1b404007001c1361017101c00c80f1342d4101726019000d140e00003034100341481f44c0001023103107140d03070b454000300001c100070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 636036223 1250 636034973 636034979
    0x807270b0d050907060c151d0a060b012309030c151e09090115120906060e0f040308010b0c1c0302071a0105100305090307020a08071814010b162a 64
    0x394551301c041c443c9501003440301c0082c40000301c1050307440d060f0300340300200001c1600c5141d2440346000c407a04a00002d50f00400c0c488410000300344901e100801080c83c000301c107180e5104403003101c202c01c16034200b8000c4c000300301d502d07a40e03030b080000811050f0040c0245015650070070b00500d40b0b4001700150700141d00798031303101880300543c04103031035581c03100502501190f40382082031266814070320b202100304841601c600705072964501134201e03190701c039800010746113291100844803010090000340110522009000110380d000300e030241507888400e0103a9848070386d10141407810320b200e80800781940030384840c40d111075010f9014003c10360051003084200c4c00c01c034a1a4188030402d0181550004500c1b0b09071107500c1c8030ba441541e01540180c126440e001c8280c0005411400035401032099500408040c814481c40416580d0600c9151005006a40603074424182240050090001c08000456540000b84008003220005d0307810030100d4600c202e508101d80c0e281144500d80c03090511100c0800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 636037473 1250 636036223 636036241
    0x210020706021221040f0b010803070b0c090f1002031c0e061e131a0a06080c0a121403071b05012604030309060605030f0609150402010807270b0d05 65
    0x990310381000c07403402c20a884113028070203100c55024205855940b0703d590100300203240d240030a8060003426000316140c07003203071070800c200c65801400200c22000501c9003028588a0040700c03109404100c0f181d07101191840022440c601900034007441552141d43c505c91b1101d0280d102d444400324802c16901c4503a40d550300071401000d21840e56000ea02d601c0000780240030f000e00002111446244034030806403c03062001e8201c807040d51407030804c523541d1008120861040002140c16a02520200b0003186030901103003820700c03401d07000307851646184c1e00244851000d2080300c0080c0e030301401c2410386a550404500c607128590046601198400d004241c40b401d441002165120380c240310446981c0d6107030b8003200070f09085401140d00b103840e554045529503041c041401c02c0c0d001c010040500c2d1034800e01d0245881880300310b440d0400000014000581d03403000c2035a0f030041c20760504412826000740c0440582401040354410b0940c90724000c6801d8003903400800c004a8646400d106070f031180401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 636038723 1250 636037473 636037477
    0x112b0203010c0e130b04200315011107060e03010b060703090f05060333040e0c1806030c01111603080c060702060c041203090815012c07120902100207060212 69
    0x3035661201d0311004e0440c0c40c1d41190031603181d50307101910102d20003110903542c003085114a5103540da140ca01000f0080320602c00d03540b034500c4400910740001820b050032110307911000e05005003810031182014002843c3c4003508040008407014001c1e0766941e10500b0001c21103c001c2c000c2c00d48020340348400207581c1c80c4c4071042c0da0069030042242d050019450100d00020302c00080a242445200301c220920369aa611403500c0c100c0e406009461b1141c0700c070301000b054044440609465501400500281d920000741d80c01002d0300c03e083c0200900f0b05c0c00d81e803901d050344110070315110184100001c42004a424042c00c90151312070304944d46515408410780c4c9401d81103441c019040805c4c4000c2040e8040c126208154500a0400c0c010964848510505005910f40260030b521f141c00c00400a41001801c0d0904107207650f4000203c00d261506440f6441102806010420881a081c04080180b41c3d1001c0c0125600400c1c1091a400303207500607440302041d11603040903010715091140c000800c0d40c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 636039973 1250 636038723 636038747
    0x140d1404150e0a0905101a0a0e150301091a0609010f2105090c010207120f111c0b0709050301091a25020307050d0318112b0203010c 58
    0x841641003a007051010702840d864004080c0402044080c2c068031911a00d0003e400740012400100e00351800e00d0892104005585c400380300b0380145040521940e40e00020340c1d4200c20603281c20250035000b40b0000389111112059038000d494000000100d4030035a511054500921190600c030107142c620412800d4020b2110403400b05074803d08290b0700754402c2600484502d44940030141d0344000c6034420341102c00032140054280c0c000b20f080c5206680400c00b10004001c00c500d10071803268650798500c3c4855400a0003000044c0701c101e0307440c0994481d0300c200103506c1c8048400348041003038240005020340c1030760310401080e074841001c40d640c101800b41e40780498010003805c003007292400d00d5040d40d60004040c00500403031440881158615041a05621841a07005503240d07a42e81c1810b6042022040200003850f00c0c0c0341280311060542ca0b916002c241d0000c40143d6501f41c200042000540c120a07039542080c0ca04511040340801070a00c546018001c0e402000548014a01560004001c4c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 636041223 1250 636039973 636040007
    0x1306020d1103030f0405100603050c120307120302070c05092e060c14030405090f2e060e120d03091a090a0f03090e011203030c0f0504140a0b0403140d 66
    0x40055880041e0081300c903009407181d4202c850b181c0078103060100f1604241c00445d40303034010f0688600745241c0500104203c02030380000d90b107003280e0b5076591621040203071125018960041000300501070402124002000081d215810f00d107046000d0890700140c0c0300d18040d40b03d24120003d1b41c407486c0c0140c4201612426207504009244644458440222019600050384010400400c564446252480c0900001c860b105564245680d4041c0082407022960a80700361034504020041c240c03082400446010f42800e044602501001c10310079482007400d40c03407500c079074145d002030380c1c1e0301d68005c2c50003a010b990780310542e07000041000f42c0c082040d500f122301381d0310100481000c00c000308044c00c2d00512a06084002c6642c42c1d0480501d080309910012040c01984101024150035001e01504011285070600d200303280250043c080f4000e901440d10300721781888000d02c86d41c5039180c0c0c0c00f0181c8001407849031a640c3d42d241690040d07025500c80f0301a0702400141325034a038091038009075582802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 636042473 1250 636041223 636041227
    0x6230a0e060f070302010e2503020f0d060c021e0c060d0e0a120c0c0e06030d03020307030b0a03080c0f06010f05190b030f090c1008010902090d081306020d1103 70
    0x144011240381024003446030788030000300440b4105031981c0c0001c224441c0f00341c00218401d0807200b078090030080c00c0140740801d5210040520301000481513900d00b680e904503079994501c14207402050080324052802001a0302d04810150125000205070f07000c842107540e8002c00f0b40c5031408460b261130b00d80d100035420074400d0142c03100380071013500b1050125038210704980c3c8028854035205808518030414901050030248010203104061448a018010300201010181003200109942d4055041d080c0c0030581d020000c140d55900c41d811841001c140240701750012034590901d640f003a8000300308800e40f0320130041c0350780e030007030740880c1e01c5048501f40c003c41401d039407401c01401941201510300208950700031002045280807117000e1802620700c05020380c060b24101c42190320b0410000c0c041441990070032030f825200e0340e0003c0001d05449000d200540c40300500004100e0904040300d00500e4008003091a645919000d1b022108654140d421101c081080402c241d0f070b5a40700c2c91020b0f2480d041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 636043723 1250 636042473 636042487
    0x60e1c0f1e02163012030906020d0c09080d0201050c0a0f030b0d0b061207080d031d0607080907050904020a052814010905043c05010e010623 62
    0x4162408100c01c0e10703a00580c0d04600c0108545a100c030115006150030040d070100095800c41000c0720070403908403044000c0392055541e1a14000395482a030742004264880510781e04100e03268054418644204209100d150340d441c101905115050240903818801c50070303012400c2d403050041d40d02a060030b03c03016181128004040700c041130445500d00c18140c03902c41454268580d46500070817280541500b40207402e006040055008140380c1c00741c2075030303c540c5060040110110340d0400380790751400e0004a10880490100000040c103680858030b001e1348041040c2950003084180c454800241a03901c030b00c0c1c5403401c11001c880c040e10042d400200321002804682803080a16003c20226400d00c5400c45001d902c200760b103e5160030074007103161000c0c2c0d081041d5802030181406840f084505004040f50095450600d02d80341d540d032080501c0d1101d0080206003088e401c0403c4440750380382030000350384400a00b9170440d420312440000840030a00e562025003201c0007808134541100000307241a030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 636044973 1250 636043723 636043757
    0xf0e1903020d060e031917040201020304091a1203032502030316020312280b0f190806090312090c01021e0f030d060923060d0807060e1c0f 61
    0x103940c02c080b2003042d034800f14403140000800203040d4641c103000407101035102240c001800085c0740f88406a41c0c40001040c04010b030b80120955050710303d12640080c02010130500c543e4040f54150b503a039000710034050300d00508000840114401c3c07800320002d002444040846007220f9619401d1180180c20a201081005e1a41543c14101e2825441120300b0f10258a0313102810440603140d540c1c0000211070190a0249054001c8081c0209114204003005c1210701240e40840c02c055140e1042a401d8190045150400c606030058805a41243d19074501600318035030f40c0d4000c01840f581201002c1c00100b06d140001040d5a1015040c1d0180801c0b207440d42071002c0c11512021032800902030301461200108c01000504480001313a1004960149814462011a81010800300030b00242d04020b400c5d01c90a4840700e9005070007911400510030a50500000d1070145100040805081200140302104000384c0d001c010310700c8400c01a61450024415280c1301800150746022402c03000003150241 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 636046223 1250 636044973 636044989
    0x60807080304060e0d0b070e040507050c060402040f090b04080304050c1017090f0d05030411010905010c0818130b030606060307020a021203040e04030906090602010b010813020109150f0e190302 85
    0xb04c0900482242e800a507540d0011120843e150700001302e0b0000920460310b07181c050349030840c40d2030806a107081030314642551115030080003c1e000b82c2d01c4e000305c0300b0040c4850303005081458000500c004a8240b5240061065000345c0d0150742500c40c0180340b00700d500e8942100768400784d864132802c1420326000081600b00710002d0080f00c45000b0014400c00e54403060200c80c511182c1a904c407070352450103180054484403080c0465040102441e414811642c01052900d41c4542001300f594a038420030f00d100030a250101c0106810507203005007480d2415041d0000382c0c11400403010b4480c40e54609041c001140130460700840141d00641da44005806c1501464003802140380a5030724140e00d40108941141050300c0440002d040d10030100503551b031090b503000281c00148020310480c0c2d803000008042030300241492452042076903003181160f000301000300040003a20040c20321620307140c0001d44040d0301c2c0400701012a207410300c0c144207403401040c2118000107503c0820407441c1117401b40309860f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 636047473 1250 636046223 636046247
    0x8011103010f061719110d0c02060f012105010209030d0e040f11030c0f071b0f0e010320010e100323010e0a090203100213050109090c140a0203041d01050406080708030406 75
    0x341eaa505625880c03401b00c2d10041140502140d80071442a07a040700003440c007580100000a00c080110050103d482d00300b0b25602001209052008482481d0504500a200b221008c82d454411f00d81e07001c0c5e002d80c0024407240b0a8100f22820882c00925070075203015155142102c0d1111001040060107602d0714202034940300035007400b01030600c80310760717030710074614200d0b41d003030b0315500b640380b00c01c0045081699400b03000d001f004034859515495503031018980c2d582e000100e5200f003452003403110b0a0b482640d400c09400d500400c4100c90b500c540d00301400170480101c0d160344160841ca0209800300701e10300c134241210312441541d9040d665850001005040150f000c0380c0c0341c045c0244e480c1042d003ca0000d800030702c46040c01c0c081090318060003d80141000e912a44013142030051800b51b050300198603d400c401214205591020680707412801c5208903003250381c10034845840294803050190300681610000c4e1400c00c0f6491312207900580c2c0d003006215004003948100028480380e4400d0b13000c0004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 636048723 1250 636047473 636047521
    0x1020901140a0c0606031407080a050a021e030607080703061205100225050309130b0f090919060501090e0f06010b0901050d0e0a0b07053108011103010f0617 69
    0x1e00f0303d50303501c03081d0342e2280c0c000c7c0e40351203401e085800401f50510400d0002e0055900800a883e0566592520703000c0c40e03100130384601400c100c010010b42002c680100e0005004043c0c610b03d14140e500a4020700701901c0d81e4000900d0954042001d5a20701c20089071140c008000f0262100d46004520281d44040b422080303050040681010060300b01d5139140c19180710340d01440e00c4400d01c000b40700d080c0002d80b90040c195806d055819540e91544500a00143c0c0c09a4001c600d9944074070281c0e1411000b21807840000e40c0c9105030005000c02a40158161003240906200b0358890070b4906950302c4c00c00250900c2034124030010806085503000070b000c000410f041c158100420003481004459190011000541110010804001c0c0c10017070954085c8840c20210b0810946590500c0d0800d05030640e01d520441e002d8480c25041030411a02c0014400c40d8000d21018010800400280d0804c1c8140c0e000c1c400c850f607001ca41640513000d804d00d020594001e9903101d980c0d0182080d6158009400800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 636049973 1250 636048723 636048737
    0x42706020f0f0a0206130b060402030702150c0702010e0a084605010b0a181d03031f0911030a0209040f0c020c0a0f180504051014070f0201020901140a 66
    0x2207003440d000c0d040800c080c000c9252100c501c0c560103410310400078000c0070101c0c10240c0c84000903802002072030b082042a100140c59641d0250242c2c078001c2c440c0c0340c85904440e4081042038400d5108001c20145100f80d840400c00340d811b1043c0035007114203000f6410a901300c2d07802080d08840c114005c1c0584420551031040d074000743c050950503032446413040c5240212101c05a030510600f401420311001050b26209481c61034503040703180708078112030000d94103070f161a4130071141034907c0144011201c0c1c26003a06c0c1d407418894900a0344d000c0019810100108202c3d00007400d140901c20000303c0580d8000c094511340d1602020301c02036204201656025584500300040180d06100c2c03118003108907001070120b10900e8003000091002d5900466031080c403000b007800b41070794503107c0c140c0d8425034040c0420b00d038450b850840c0c100b600c0d460202d9852031070f040448a0340d000d041480303401080551512821a6610081203090744141c04080d40400e040000202004016030020620030080f450104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 636051223 1250 636049973 636049987
    0x71112120d0203040b180a080309030403080f0a080601021204150c140c01110c01050904050c12040f0605240904080c01020a0207080f0a050d1b06020307020f060604270602 75
    0x40a4004041c80001030794080704110810402d00e400b15000310500741003000041c465490250f890000340c00080ca4544040040342c4482010006e45e000f450340012030329110020029008180c6e007003a04a20002070410001c11283d500208d08000e0742d910324041d030703440c0a00b800c5d41146500040c03215a001c10825651150104840d80d150aa0561794800030348218110f4100050854940f0038040e0307420740089818040d11380c5c20000700e0705005000c0c2c0d400f04036a5117080c110492401014141b403c1e81e031142e07080208110301c16402085291148408200a0310340d0451032540c030712400b00340d6000502511a121203072400c1c0d4a46a0312501c500d03c0c051806842d110201d00b660401103252000d41d000741418001070710306110901c0c40d60300f500010004000c091320703419525044c0390400410700401210002c1c4000c20018054840c58012505541c0c9084c2078030300941c0e54036051503548040c092840442c1c59446d19018803003410000543c1c0c03440054401450078941c2c1c50302c140486255600704004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 636052473 1250 636051223 636051253
    0x1e030103080328140702070e07090612061d040c0b090d0f060906020408010606021207030203031909020d030503041b050603150402070f080405120105010e150d0c09060f0902071112 79
    0x1804030507110704c810440c18100204e0103803900005030001c0510140740420400080d600c018583d0445000380340418a118209040320010b101c0e44d0070147d80d200384500ca4070461110f600310356000d20302c959444840203035600d00c42d181c9401500103207648640080d80c01000710305001506402c40b1f01805000444e11443c0ea02ca41c01c9a00692150442e65128039082004c0354043c02a590140304140d1203500d407440e550740094491000504460030300c4401c500902c081540360b84419049640074040d458a00114140a4002d8108550480d21000b18034131440201d1a08000074045400140c00e150075621100300848800c0c2c610028550030a0342448241e000c241d0401e40d5a1900b40500c0241d60342d1400c18090001a003014043c0001c140c0c1800010006600003441099010302c2d603024004102018000081c0c0d10165920050080003e410003c500d2192030751198048441e018402041c441d92545107500740c2c0100b10015000f501d101820f1740f81801d05e18070106030110002d09445101d291407c2c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 636053723 1250 636052473 636052481
    0xa0e04050a05010603200a0305091e01060e07030207030e1c1a01050102060c04060905060d060308132301091403070e0103080a0e0103060e07030c050418021e030103080328 75
    0x400c802d80300c00040120326058451102c49440d800344c011400c0054400158483c82001c08400416070394800040c2c004409204646c1c43d0822503210b603092018150b8414040d011a0040c00303100050840454031f0355020b8403c41c1c01c460780c152034080b13112141c00c0412030540c1c0101d44e07040c84a01e15140000009524115803ea40450980c8000c159414a00028034124004100031182c100c104000d203c00c5130031042e40c5003141d00c04c03a8642d640f00403107900d00000d0b00f1103a00003400b400303020600c0c055040384000c07044240e4905182464500d229a540c2423035130100d14064501044900c102807000f101c004101c0c07801001e0140858001503030703d421510310075100341d00c1038411440119880707032100e03404010fa24000909207000c0c4001d6003006100041c00170060100010b0503900c416060380707240a801aa030044c827403402c55000100c81c030708615010b0b43c80b03050b003480900f446107207006a20301c42c1d90a8a050f130788c2002d607050644d921845200200e03945032880c03010411032040f10b00010606070013 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 636054973 1250 636053723 636053731
    0x10b1003060f0b12150d0605130b0f1b03090c060a18081501120c05120f0f030f0f13030203031c1503030e010e0a0806040501060f0b0307090302060a0e0405 68
    0x80d00003076080c5480c0c0072081c1d07a42d4640100030046420402d20b0341c41a49418000e801084010340040c4407088900041c040303265500005161034180410804880c0030fa164800b00c080c081e210b103254690700c40c00040d440c42d0045981044001520141caa0769030944d00c09190300c00703940d0f030880300725a11450000d007043c2c10040c005000282d01d0a104003018807000ba82d50010f10b0554020215826a541c050106440500500078544220014034007449003520300e510007010042d00c4200400000c004841d1191001e1035008098030402d09130001d822000802c0329000040052042d082c01c01d40f407001c85660b0b0004001c10f4014200960101c0903950900c0140079407840e54030003a1038400807001d00400c2c1d40b04295514003c0809400c1000400d4002030800d051070b9003440c018240e9a203402c001218070810380c2101c1e00c2845030344100001c11405510030800c1d604010326214880c0d6990a072a0507902c0222030440c006a0004001c000500380b0101600c030707001c3e20f0300348420501c209101150407600111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 636056223 1250 636054973 636054977
    0x90905010f0f12080904022a030c0f07080d05090109030b070f0f0c0308010b0d06090227150a140c0d0216050402040302060313080903031201030204050106170a0c02010b10 75
    0x40c074100030320110440800b000f8040d82403c4045003010791034035a820700407004120b005540018003010094001a41040140740c002e0703050041115110f00e903070341c030340042001c11400e00c600503000350b00380e01c0042c0000403209101c0082c214041404411106074101000c09410703c40174503000300000359440401c1c0d10680c2e6590f41c0f4031100880140003001c501c0461010390500c040450000046540005414151102d00181960700d860b16114040100126445201072502c0440c0c01c41c10a91020606004640b40b00740503c1e0404420081000c0000407000003203012808000315002903000b504000da00c82c50450b2801d040c0b002c06d840d00e81c104456145d100005030801a80301c0c51985400f06070b00042c0c40151800c5040c03070300355030104c1e0035407101518007030a5503506284035040003055404c441c1800c01c0507050301e445100040012121106c203002c2203105905120012801d1440344182d07541000d158492050151141311100c401808215403403011552100f40c07080d40d984610b03202a40031a82c0d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 636057473 1250 636056223 636056249
    0x501111c0c110d111c02210d0204080c090a0506091302060912060a0c110c060f160c17010b0108150d020901080d080a02040b1c15030602040e090a050d0c0309090501 72
    0x241107881e01701082c90400b081c400604411005145a00041e070303642c8240142d824480059000c131407040c2e41c1c050f0b00e1510715101d00018000c10519004142c02007103040998070203803180c42c0e410080007078900031100319400850800c0069030b5100d99800701255240050200b901d030814134000300f03a2540f0720300443d8201d0740c0b09806104080450384601e0150890f0b81c42e0171964141c44d24841ea441e49001a5151310407030300801e0075802c1060709812a1081704c6046515038804002c2c0ca4440944003042c800c04400c070307104c00080314124006000b400303001001691910a01d0b514050003000903440c10340751507040031120f0300540060300d42d0004a03000c1c194082c000e125101080100811411004155003072090040c4020031410101000781c0f40c115507407915911211003030615a4004180c0b03000e900c04160341d400400420700000350f0003002a100c2d1000800f1455950401c0c1a503229603c003030052483c0d102c605080394003480749000880d6984289003c8501c0c0d076642c4841020b4038000e80006d2000001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 636058723 1250 636057473 636057497
    0x509071b0b0f011e03030e060a02030d06151101020406050405011d09070315120203070302151306120522080a0c14061015051c0b0414040501111c0c110d 67
    0x54100340705059032880360300c44603d0440d5070080c510700148047d1400303008040b41101110f4000d0094030203015042030104642aa00c442e10141900c0011085000c220b0230840003030303101e40600032207084d210b07141c072050b01d440d14003001102c0c5c17801c120a03c81d0065114081c985c882e0b03962441024050382c400d50300802c10f45040c0f5030240d91040e081e4011511392032120485030040c0c0340411086c1c00c503601103503e141ea007025220009100c0c0f1824084405120306541d0104100740c100501c07001030701c19500100b001c0c0d03850102c903180320b1001c00b000c41008503231603490b480002d241200038190349500c2d280031004101e20350ba500e0f07100300e82d036510100f00390040c10400441035150800070b002020b03e210700441d60020484050903c1c4a00e80740c21a4007880300c107001d185000c1d160441d00c103d000283c400c1000b0000c20b548070610720400e4070300b00c50a50a0020300d0310071202175003d4031061904009240c8002c00d648401304000c1c03821072000418042c251480301035408090003c0f20100305280c889a4034450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 636059973 1250 636058723 636058739
    0x120c1309020c25060806091005030d020a0b0c1215010509030109060204150c1e050109120f120c09121b080604060e010203070f08070c0c15080901060509071b0b0f01 72
    0x14403c2100501c40000c80700c03c00c1030a900440d003640202094482064645405d401710300020107a40081c0c0e014405c540710096017560001d20101c1850281c0506122515104400c160b18031414101070b82e0102880c000c10060b101c003203005080d182c8141842c07460010508007007800c0d030364800d00560780d4030740c0400c0c200200d0100c0b0b4401210710000d450040c030500d64035030342e409003403902165251040c50b6418094081200952081d100345801010421400c00400001455070025419440004441d04041c000306001801000300700d01e510384641044030300302000c0d44c03030302085c140c0140c4056004011001035401c441c8440000340108030080c051030304c0e25003002010307035982d40380c0f9880aa00c1002040480c2c0c1d8085482c0300c4815145c6003011298942c120b044404214840c8080d0001e00c29a00c0012004092001c20030218007580710040e4070380d503010308a0700702c410510455400080b2180014141d6205004003034040d1000c1403044002241600c1d65400c00600302c03145410001c00c9801402941 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 636061223 1250 636059973 636060013
    0xa120513090c05270a0905060f19090f0f0912080c041d060102240105010e0d0c150203041203020102030f061e130f0504060c080705120c1309020c 64
    0x1110340402030040d800c03041001003441c4600008000000c2d001d030868070800104c18680a0502402020601c05d107440310700f2500145019203150b80f06040411000300c80b42410f081c524510784070b012a540000b8a0319a16030003030245000c00312071490b81c030f81d036241c403820943c4200c0300e03482e000d204401703c5491010006019031601509500d5004401d02007000440b4914403500654000c0600f84030264803542c00503407804c1030404000c0c40194150f800d089000084690344c5040340c209984c0e0040c5d048290050100307881c2400d10241200800f50824040040342d440d01c41008821841240e1610740e895a00f00041a48080f0480042c3d400100748503000314142c02c0990456411140000b141d41611340c1520b013081d00c40e0306680074181603003041c0106e1005611002110500120900841c0f60515062004194040c140004a10302102044910780304e030096580c0006807440ea00301c1d6454021240b03e013504030b102d1000d1710542000001c5448012400a4410b814079507000307124803c01001080100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 636062473 1250 636061223 636061229
    0x60106080108190312051e06041a19080f0d020c0405010513090303180507080724030b0607060f0e071415090411270d030e01050c0a120513 61
    0x100180103011850021076101d0f00101c0159004007080d22034038050b2070f103524151102d0f00d194070303200c10040c58400002e8000e104180c80001084540d40700740402080b201c1c100b50751006400021b00c00011030401c2c106040d6255121240240349950f81c4800500d0002404c03540002a00f11111035031140b41c0400440d00c801c1801c850a1000351306000110341072401c8403810a086580380c800041c1818005c0d40300e1084140200035842d109103003070402c541d03203c1c1a07220300015486800d038002482100c00c900440c1c81140981d40800312951010200c0180c041201c1e6558000c03003c01c0310f2000100c0303901c148200d81c80e2000b80415200d07071708000c02307040860917401041400500c1144121a0399014240b05908440401e09926401c00b540403d0083c000300c040203100b03110006918a01000c0c02c03400006100903404107295800c400d109108050900c140d0050101c1e11020742001550301034405454107102c5241100d4001032070f6101e8000340c0111000d113001040e40080c0b1000c4500c1c2507150712000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 636063723 1250 636062473 636062477
    0xc070b012102060318030a03090b0105041505061b0102071103011d030307030e0a0204020409050f07050705070e090f07032901140409020d08040b04170f0d05031e0c030702060106 78
    0x1055030018500d100c0d250702104000c0c0b2400e00080041e4400c4038190420840d14003a004407515259585405002001600800c5d00d04400c3c44000081d180b4160080303140c01040c02c00850110740c64142070026640188000200c80060201c3c0e50740c84e00c0d401d1004d803c40c01d008020800440c0c90020505007100d0112070b00d24005550002c901209850000c1120f8021a09140c00101c003524015600e00384803541600035071041c00001c00080091582e0001c038010040f4008100194503802c1094400b0702c80c409006185400c210300400100e0b10b036102541e4065504c6c1d0540b2084245592b0141c100006504101d42080301b0000c0c2d02c2c401000000d4140c1c22520b80840c0c40300179410411881640108455050700c165100d01141e400c5440300546001c49030b50001c0b000787c80301d88136080d002c42c40d0405d018014401c00f41120352038022000144c04081025410003034001320081c400111015813000b404c070f4400032a100c0240001e03650800300b4903c9032007040e260940b03d0500b02d0340242000c0301a072114003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 636064973 1250 636063723 636063749
    0x312060a05041b0530011a040f030f03092718030c12180f0801051b1c0b0604030c030b0c19050a0207182a02030d050405010f050c070b01 60
    0x7400c0c0700c44800ca0102c40701c0d1400c096031120b040180c0d0aa20344003002c40d02c002140c03c8610f505021720010103c0b41a01e60120b11040380c0103c40036050007a008a01c58038040000f0aa0100302042070028400341286c042c0c586048030300d8840704048400b50b4084030f00801e03240d0000d24106103044600c10040850854a220710420702c494400400c91852508050720344980c420441d50071728046d10b101901c03d907110b107040070780c15510094416421458400c0320f04039420301e400508905030758401d4003242c0d002c0c410214100110056443d40c90280c1d04640d903807083d82c1e0b03041d05038603580e158007410082d4412406131240078110300d004220140e025104005415092044185401e1a04665849902c091802c55241c20300c8203001c9142401c40d9004450342400304065800801090304a50100c0001102c80c40c0b101d8403005c12402c0803080c2e821a080160420702541d226500e442d0419500540140c002041c044880b10f10340048070030540701580c0c1d1303540020b40c0d4801c2002c030502c11801054801e00340a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 636066223 1250 636064973 636064991
    0x80a05011407140d0209041509051303050f22120303110903030a0c030309080a031a0108220606090e06040201120207050a230105190609050108032a0312060a0504 71
    0xe41044400b0312070f0351101e0404104211050f441d43d05440d1080c000078011f000300c01d5120140c030010301aa0042c948030f41d051000181400481a001101640e41655010715203e44404101c4190300300c81401c501c082c5d025451801c0038842400200080c000003010725480e0350840c60041e0460b0420210050805814441c051082d9404030a48411210500308820f15038100d19085000307003402c00b40246094004070741c504406515030700c500360500c031f100003402c0c010b07030380d4001035450704000c1701c0500054102c100c01c0c0060345486114030290ba03100c4d020105403d138481d0b15403030649051440f10030060f8044400c2106660b40a02d58607500180d440702181740181c3e5444694450102c0d40014004403422503011903036100800508071980c1010f4002c2055040030b0032082180110854034924a170b042410102c0c00c0034661241c00e04913100c0e03000039864080028941c003500d901c401054a00d88680c22010200d2401c28802016003031080380c40c1f840245800e40812071001001d07000396008a01d001182 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 636067473 1250 636066223 636066227
    0x18091a090105060a03270602040303110c0904140a202805210a0609060c2a0219090b0a0f0806042015090a050907170709050a080a05011407 61
    0xe81214507240f170041500e074a20000c0001e8901000c2049034117044542501d01804169800f40058900c2a51071b4224030f01e9404d9101c1c1e031180f9000072564051498001b041c0095408000f1111084202e0103035821210356448001c00310302d1000110409011161241d00245081e12007401a40100c140b20b500507100030321641c0d111001806003e0162415429900c50112262800410b80080034200c0341c2c044420b10f0a00c020300400801164420700304026648100c0c0120002644501e1000d4415440f425140c02c951071141c0384a8280c0e00214000d1040070b881c0000441400a0044020701250341c46042090001506045d400b81d100d0840206081c0030030000400c11580042d0401c2d03444504400701201c0d0141e054034103504030340c003a0f1100242400c0d038441030041d05400e171044406040302c0340e0f15014810b08110072210240001c2c52403040c1740220b02019079040d003020f42842c0081d0f1668a440108200c0d18998209500c60f80c003c024520030448240201d1101100e010403890f002e003071403000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 636068723 1250 636067473 636067477
    0x5010b03070206180a0206041203021506130207060b0a0e1501030207030f230a030b01030501080601030308010b0708070512091e1003090602070c03230712030503060118091a09010506 80
    0xc41c0101c211020309190210805c508405650003c0c6895500e50f9102c85001003241c202c0c00c2100035000f08003010203030351000c00d401481003c0142052400a184c1c5543c08029403040340220f840300c0da9149400075035114018620003170240c0200390250ba0034020500140d94a01038107460416004000c43c100296025200750710800301070400d0003a03844095030100700040c0820349024007007400300f40080b0a940c550060140c02d40c0070b0303d0030040c591301da040c80d07030711000e0134003001c0c0206041d1001001810201c100421065000f5482c090800c5815a6050b04042c0345201c02e0b154024081350300302c018540250102205040c0c2c406008070b11a20300040b0b000c080300040c200c0b092556400042082c080b03950110f9501a0740891840f01c11602c0b440d010344400340b103411903608041e82c0510010602e20020b481d80c00c0d0303101007200d0b41d079510b00c42e030b02251140c1c4018120790400c01c90729024460303400e2444103400a060000000f18003c0042c100c2d80c0e0303000b043c0c40a41d501c54400300d401008180c48040c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 636069973 1250 636068723 636068731
    0xc07030b060111010c02101109060909100e0106080601120212061c0b0a05040303060501051206040902060403061404110a05010504051e1003020910171807080a03030b0405010b03070206 81
    0x10008000d550720001a039001c4000c0a001c0c480794202034005800720f5000c13505400d4610a40b40400030401c03a48110169800b4200110750090303800c100c030a00b54034101c84000d40c4640c106001c21500390b101d9882e0820b0700da0aa110741c0c04600c48100b800015a00284481c140701d402190842c1051050503940c0a08000640800d0045444040340310700620703011181c2c407819070480e4070400c060628078030807001020210303030940001c0d1502e41b010400c1e61243c41103c41c4881000780b0141030f83c40d0402000020000c40c4400c90380090200400400119240141c070b240c0c0d05a100000e907181382609050310304070521950386100c1c0f4000141071001d6030b040825070b0140c40c0b040c1c8405014501d1560821202035500b001c05e540071860303107900c10800d07070715030014946d1001c15a10002c41c41205030060b9030003460310040c0082c400103440094036014400c80401200320400e821641203075510324005046c40c1c2c0940054000940315131408110341001c2c06150300606200320764a15515021000a450341c00c090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 636071223 1250 636069973 636069983
    0x2060f0f0a0506060c0708061b03070f1107050d060c09050402040b070b0a0207060e06011508062b020a091a060412030c0f02090c2d0405060d060e090f120c0703 70
    0x7400f00d40c1d0743d01c46005a4500d5002c40044495042c0c40c1c0d07100c107644201c200c0d00c1600c001c2d0600392803000c0d0401c0406990041d607554440a2140303101c100180c805010110f480071040c420304c1000a111b0380c802100c4000c01d0f01403000001c0311648498014418116500194001d90040004100c1403c071071007140c3c401504802050440c0c0ca030b541084004e03100d0940c01800c190704040038504c1000d00490954101d81d8000c030041d003207041c1280144c4031694222603c40d0701c07625444007100d02d50070a49564442590550900345103158642c0041c01c001f0310b5030841c040480d550302500c039200010342c09a412141d000c07035400741081d00d0141c8843c09080e4091000f02008422074029082080360321280004c2980209542a42d142c800c1c030010440d04000000c103080d000245100002e800f8200c12030846821500710589040d0800742401116445071202d122540e540d03c4002902c008400c240300d0045258002510700d0f0580101068584501c400c00c140320000d0070810a82441000a0640102d0b0703440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 636072473 1250 636071223 636071231
    0xe0d0801260a030e03010513080f0a170c04060f02060915060d1b0f0b03040b010302060f040918121d0909100504080d0c0206190b040216050a141f05060d050307030c0302060f0f0a 78
    0x302f1012541c0d9422250b046401c65000003d20800c0030b501c802900541c0c0304da6690155003911030004907a20750381550080f4450704000d404920781401213070000e0b404900074045204002070790b075034120503480307038201e0340c1203034020030014464294400c00c0d55004014042d001070941c00c1a03200d4194025061100078881c0000041ca81c0d046600c01c019140104095072042001507151440c4a69003540c40c02c0441b07171084940075550886000e01c03894030140d40c4140600300307100d23121030910802c5c85024008040a100d000c500300c41d030608500411348036602c20000386071103140025880050341c1035000440c0a40d00440c04004150001d40c0710700d100001100d0005c00e13031601d4040850020321070307418002820b084086685091003030006429204c14424219a86407690f00760b995625002504440400d40c0da25503400750258a058220903044500105004000da10300d990b054a5603020b68411808103200026840505805101155000c0d40c0007080300c1562820030800a40400000c0c05c90003450b0b41c2e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 636073723 1250 636072473 636072487
    0xc0d0f090b1911060f100b04060c060c09080a05030405030d050406020d14120c07020f01020120031f0807060315030309060f0e061c0e0d0801260a030e03010513080f 72
    0x100e04588829119a41c044d02c1141c200134414820410b0304690f0707417404466070f18000921015140c1124112105565655101c620301c3d83c9640c00782c000c1920750b03810400d6448010031003600c10300221403418030841c01107036524649803d15062024044008003400390600041200c5500071030050407001d21480c01029928110400d4001c174000c1c100e0900d0740400b54000c01509140d014010000c1c40c1c02118401304403e5054012030a03548030404204a0704007444180e81c3d552103000185403c8000c0a122000460340c480000c501d4414590001e800e0380d0162104220300c6403d80f0440019041c545100c0788003d095440190044207680304e00c2d4100b008189074004080e204040300a0401b0008091035a0b402c1004d44466002e02480080b0720024a84590b8a01c12840002e50a21300c1d40940c89400706a8a4480e51141d4445038003071901d01c01a442000070300112050101403610b9200340ca0f60301122189000b410b084071401405200030000d09414100412a0f07041603601c00a0030701031555407001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 636074973 1250 636073723 636073727
    0x30b0a090f1211070b04140a0f0b1303120e09091c0804081606023c0f0705010203100e060f01140c030903030403050f160e010603020f0f0c0d0f090b19 66
    0x654049030342050140000200d40840500d00401c00c0302d17004c10000841e840228208061882340b441a40d1619070100401c12100b031840004d00310201c4050060810240d0700d032140c0c0c401504200c0040e00280e25820459070a107425a61640c00c080104010000384102202000203800d40d0b01ca441c0522180030300080403ca85081202c1500700c145000c1100d840c55843c1a00107034003c4041200c1c454075007203042401040c0001200c1d20614210754200d00b0f0341d044c0c40c08130314542c052280441144800c005100c04924240000c5000e020b030320002488452400303150346900c0b040a00498412000c40403a000709aa00c44034030740a411041207440c0e65041d1034081140f6504c100808130f5098000404e00200744a408100718410701900001c1e10701e802803c0d001c000c01c9134668020b1003200c891010040c41030b940309074060070602058418180c60590180d000c124580c0140441c46003d60090030041d00083e030040403200304038541d04110f01c0c2c0340c0c01d00d04458100e0040010300240c040000030041741281c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 636076223 1250 636074973 636074987
    0x121312080a030b130e0d0f020111091c080f0c0c0f060a0e011b0f05060601021603060908070c090507090801050601050d0b181e130c0302010c02040b0307060504030b0a090f12 76
    0x100c1c50400c90107240305c1c070154585100e12880408511010b180342c000c1c1d8010701640e10b00c0340102d002d85143c09902d9041101920b2110003220181006410038000130324448014803550303001e5282c2c19210355080c00890325100d0a2075106000d00070a00c2c400f400c640300c403020385d408a4403d042c1080d50000820048a2490362150700c003030034840700351145090158500b446000302d8024415241d1036a5202c005995582588990b09807007440060204042a49a4001e00006110304d01c81450603020761180c1e42200c03071a40000b10742d02d0f510b0003400300b4260030140c84030040038104028000b9181c5100068064040e81070041010750302c565003401d0036a0381500c800d004400f0004a228607041c11049c580000382066000000f0348506408526800e41d214407000d405a03000810420560556004680708002094101d81090301d030071841da010741c0e0507c1924080c1c40d43e65201610b481c03650030003030805440a070032405403920300708540011079200300c1e4111049070840ca42c1c5003100d503911411200d40c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 636077473 1250 636076223 636076249
    0x181504060507140d11071401020a1410020f0c0613020109050f15180a0b2a010227010f080609040305070f0b010f06080606030907051003060503121312080a030b 70
    0x640070b900300c0d441c10340d0340000c466026030351003101b150503064903100000b4101c1d40e6000000d0160784004180e1002030649800660340559100c159201c1c2d402c1c21803818140e81124901c1c0594110101d00020100410400d160340a00880008100350600707400180459016000d00c0e802814403403550f9409071540901a1001e951110003980d030b034040301c500003404040d005100707031240c6810311001807031104220071f6030740c5268000816101003421120302c58103913840c0400f0708a155000e0081c031035036103900f807507610340e1020720114562000c4500c0001000340345013000000900455509028164a88004a50303201d60325040096803580e050030f080c450b01590290040c100b880700c1c2e00118500307040e12991800c442c2c1680351180c0541b16070041200b82e000495458485510000d410400e40c50240c044030703c1d800d0703d4180091071903119000302c1d0030144e204400b44200c0000046120b41030580601c4000202280242d0740410951941ca402c180d10400c4540320401d0f40341d010842c1c02d641d5058070078040d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 636078723 1250 636077473 636077513
    0x9042d020901051e2503170601090510080103111903020907020c150c06130f0308060f06040602010e061023060d050717100602192303181504060507 65
    0x101d04c00780d005100c1a58010401140d00c1954410300103801914860a444031941c5030311181101000c800012405100003000e580c100900c00c500020705031900c0204002a1300d041e40c50042560442c200a14058446100907010f602c2040c0820100515400001c003600e5045075103034520780b07034044228682110348404942c803e80780d01010041a00c50802000610600c0c0266402941c0b513030798414813100ca07104082d0600210301034400c0000c2c46842825440302000786044803c0003c0808a505900075030048800342c2e541d10072900c5060810003205c2d51145200d07214201090038581092000b0840000703491610003174606154465840005840d060001800108814030740780d0402031503c46414240d56820328010045603002003c15451300a0356040c0d0010301620031100d12a50307040c402e40d0001e40308070300b465030b031580c651030304070020341c6041c0602004644072050b03007400d81440380c00001c001d4421040d45001284210a1078203440c222081030800c0ca4440b841400d150301c1581102100c486 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 636079973 1250 636078723 636078757
    0xf0c01020c012405100503061002150a0e120301030f0b090304091a09390c1e100510090e010b0a0f0f0905090304030209070203040806040809042d02090105 68
    0x4107080200c0d8401e00403e1072a03031503404041d500c3c1d05010400120b030081c035001600400000b03096017800000c1d45860b0300c451045072546142e111403607010140954000898544071044106402020032800c03006c41c880d151b040c1d14551550344c0d81048806060b9004142c801c210001400e800410702c107a60040007807402c28046104e442c044000004200c6e58010b00c00d001410228000d1f03003803c2a41c158080300d001c015600c014802003110151106401868848082000200024001440b51440700c440400aa08440302101450781c14401c8410143c61103914200c20491070300100c008040495403550b50014400b45508503050250686078400c0360803101c41d800000d80c1c00c001a55001c222a180042ca051880e02c444a00b02903d0099904040ca61710500c404d10140c03a100e40300c02d400c11903d004036441d069990310001e0802c0703002c46064580304c8020a0344c0405c0d08003405070030350300084200a42c00f005400385c2d00b018103041d20034004034031a50124002d01d89900507001c0360840190500144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 636081223 1250 636079973 636079991
    0xc070f0309080d050304150b0f1302040f140103141e060d020306160201060602030a021b0f1c060b310f02120907060f0228060207050a031806050f0c01020c01 69
    0x24044d5403090700c0880f01d00200800403140503500c2e1240c080456070091031011451041303820064408901b030406c0142030780c00c10000038411001240c07100102850344843c03217403401e204005001ca524482900c004210841d00b0002000403445401d800c94048080b048020744489000c82c03e5940005802505031040805009800b0b0241c010119880a00d034001d03c40292a100100d85034094243d015000d40e00680c040c0046140340300241c0d11000b006402c1c42d964441c1080001c0c2c120f00f01c440b044158429015090301400514010b480880b54141c402c0d42005072645141e2207518a001c498a03107012801003900754003103998102a8811040f2a42907403030740317210507942c0940c030825108494140300d0384100041041c02154960134951f126006080c00e1103040e260780e1a007001000149008004003000400000c0d01840505085405100144404d0925250292017407400001306a80c2444a510801c08568403101f1039007003080c10803040b6280c0e000c2080113406401282040c0300c1c1035080007959 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 636082473 1250 636081223 636081227
    0x19020d060e1f0b0c070605090301090c06050310050d0206040303050c0f010e010e1006031119030606030305070b09060f0a0905031e0a120204050d12020f2e050c070f0309080d 76
    0x42198415010303842040b682c1e81440d9000b842920713803c00d11500701004c10800140074102518802c50007030004a140f00007aa40c0c95000d00d042d400ca08003142000c0188901c1014955070791300a0310b0242c0f0b02c80303900300325030300080d810b801340b0300c0300408006002031000c003451400c0c0101c58108004000912203c6000814203011304000300c9400c1803403007004840c2d4912550b5000c0c3c0011a40c000404041e086a89414403858601914030014800700710400040064058410f40008500941d41c40b9180c202910f400c040c2e000000d02804a0b6030700007014003600d0300e070b070900c0250480040c003400108040d05c0d180ca1400d41c0103040c03100028982c085120751000b80d0440c02084074070015640d0b01c0910303512010300c03404c80c020f6000d4140c0148900381180001110a2100d0703540c034a203801118a841075007083c241c030300948084407107400e003400c4a4030600700c2c00482070b05100895108042c845032600d400c0410036401a00005080c2000940802040c580078007140340280041c0025501005118540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 636083723 1250 636082473 636082501
    0xd0e100b0607150c091a03015003010e0d031103151003021210061e02060a02180604080604030806040e060f09010f0f060305010606020619020d060e 65
    0x495405509082030400d0500d0004111a680d5070710071203800021020201900003006100600030602c00452030100d5086e890751190807600032617000182e42e0358104805000c20640e10007400006402484000390404640c04808401440081101c40060b1168443c240c0c0c05840c00301030741c2c055103011a0010aa10040b8500e4450000c0791130030b2102c100d0058400140d0300c41100c0030b400000342c50301c1c1484c0d60300d000c400400c030f01c00242c80e0160404042d0a0f0b8001c0c080003d5500c5040000c0c40b16040003019045095514200e40040d800d0200c00c03100c40340039494010040080840a90000d440b404001555503045034520002d49100c1e1215201e22041d655102c0548095000c500c40200192007031800b8040c40c000036921102401940e12048403003040ca000c06001c00c8010b540b40e0036002d260007014400c0c0c0364100e20300074003ca0000e1542c03d28900310f030b1040e0400340031134101100b0807103020602d40c07540e400200b41410060362404c036600700000400d09500806030b140440310a2083c40d9404040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 636084973 1250 636083723 636083743
    0x1b030509030c0a03020d0f0305070606120506010504051e180105070f09121127190f0e0a1e120c0210080103170d1103090a030239060d0e 60
    0x1150b1128048104100303408070a0701c4029842001c08040c0710000e041e42c00c049160a04ca0f091041c1801c403159138403030031360300da940000c5860750036000c0321010302c00108038450050030145c3d010401818a9030440800342c005502c0b081103225000c0204111106102c443c1071a100664020032690600c24001040c0c51103101500001480454010410100c0245402d0184c0c2d8072904101c0340049040a0000810301000e05e5006560451207121400c08030040c91480f03007450710354210ba615841c220070002c80d0284124010b02d21301d4070707080b81c54481000404030201a042107403d0300c1240224000b42c0c251030b090300018990209103000e02940c40c0c01c40080b811451086500044c2052520300469400174244005001840d40108400750341c03240c1001018010042c4001003000c0390150780c0007549500c1a2203402c1241e10000c0a1000d06070b041c80800da4194188e2070205040c0e2403800034040032260089445040703000c0554618082c0d842c1030845144655001080c000642440c04541e19050a80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 636086223 1250 636084973 636084979
    0x30b060a0b040803040513020c0601080607020d1701031e060c02100e030315010302090303070c080c011710091a0904060b01020d0e0a09051e09030d1503080d05071b030509 75
    0x11004228000e000342a201501e4070f050096003014030b09001c001261110078685582182e0801c045420800701340b141a0103090741000034013503410100802407a020310740316514100b01d005001c0c1d4280f10750224941d130450740c001c5070450340c4034081994440140d072801e034002d01952030240180301180d004101c98807803034440d000422100340075405046d140c0c0300c115500b412131804506890140d40c02640601074003480038003103d0a0040715a580d184001142e08620100c2d0301c40b41c0c684100350b0740101d1846048101111050b091f081001c200b10500d0310502455038210703191203e41a1290302c10500c1901528001e00712586411b09013401c200070701020b40d2803801030003100d110507400c45c0a403c61540c00c2c28013a00300c5500515210b4102c004010160044c440d1082411034001019507061545008186d20000b031541c49407401d041c00100da0ba2000340541000001c00701b003002c41c59080a07a18488a004800b1403660744004c0115481001c1c0041c035002e0401c0c0301d005405041e4418041c0c2030841e820f07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 636087473 1250 636086223 636086239
    0x180a050606240d050405010608010908040302040605031501030f0317010b0d060b030105061b0102073009240c050f01090b0109200c0325030318050601050d05031201030b06 75
    0x4a0b00242c0d0070492a03449030088a410802c0c0c80c0c0301000c6a1120754807a0080740002006920341410700d00751030180c074094543d010041000d0007540381520400c0c00a01c000c8005008222014014036802c01c41480081d0681810701c0c0a08c003414090401c40710300728910041545c0c2c0307607102c076618403054025104102d42d407840c0c00da021075503c0540040f64142c410040c00c16003020320200d01c036425880c50760008099550280040000034140540014000405030100c0207406e40c0000c1202c86185500402401c00c80700705400c000045108030074420015102d000710000300d159000c2650341500010004100307124582c181964600c06610507101c0703e201e02400c4596076030303d40c604001c1d0f404006246082950103280d040720024050000e02c60fa05100301500c2c28128103800c2c2d844000c19488070014910300b52120041056414441e5180c000241e810001031000c0c5602c4040e5901d5050080d00d00603043c0c4260041840810015200c0c2c904ea400c0a0b51080e61312403402d504040b20a6415a00424403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 636088723 1250 636087473 636087499
    0x303040311150906040909050d11070b0f07140f0f1f0906020912100c0e0a09020307120c051201080d0804241a10171b2104020a050a05090609180a050606 67
    0x2b08030b2502151958480c01400c2c3c4609103110784502d507110401c1100110010804200020b01d044a440d1a812840004d00390000304261802d052813000d800714010358214250409010101412492054082410001d080c00c00c501d0050028464801c1c02030f0710824100701080d0b98100050100070800c1502428042c1e010500350688503841c1c040c0526600c007508400a1110720259806190300044601c1c0c00c19a0000c0001514111521060001c00040d40050310226110424140c0d5004000f808000d00c6010b2124100400080e40030b40020240400344ca09519050102040d01c2c0050303802c48001c008903840e00d24007052000803441d4685c040c141d0a50080700d840d0103000d0382854010b00c0308210019564584052199001140020014100500a0701c1b0140400361642c20000a01040f815203810540100503035003450780d000b24480c02500d6010311aa84980307104a400400079540c058442e2280c0c00c04040d280010050068984a921a120144240010650f00800701030b102e1f80f2240342 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 636089973 1250 636088723 636088727
    0x61006110d090b030c040e0117011b020309041d03160606050901060c062a020f1605010f05090604170706110604080301170703060c0207140303040311150906040909050d 74
    0x29420a20202040e070700a41003000030305a03c01542c0c0b025880c802d503864603858003841d81400f1b03000c0c1c00404912054000542610200744902004540044c02c2c2d000141840d60b40250f8a1184076205406240c5070134001c4002d00102a092403000b040405a946441e1002e41044508a113810b0036110141441c02c000b610303003000010241640c2d400e0b0741c1c56400880c01c0d11514003400c15a50406503004c412410700b200003a005000c40d02c031508650107800150100e00104d454004103132607190f5403841081c002c0016a8101c02c01e15070541440c10140e80703e000e41c0c000a441c40c0039030b44c0310710034554894110000070305001c201c3c40c094031420784038240000b0707480786541e588000464000f00f6180d0104018071160080f110050303020b0300003d00700c0d0241c60302d0365180e0066a251481103809644a103d0038045550901c1d041503004109a00460506241d40c9030241c01208102940e80200c29401c00e80c0000240c100c116521903101500c0c1c40d6446542c0d0074040b0040800c5101031390103014214070102c00078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 636091223 1250 636089973 636089983
    0xb030c0705070b070c0e04050c06030f06040b0306060102100c14130e1f0306020c0f16140108090d03200a08060a051c12030b130b1203040f0905070c0506100611 70
    0x141d0005c020180180c02d00840c0c00640501800c241c0d43c46c41152024400344d640c400095201d00340b202201003440c1040340c04c0c0710030359285000c0188280c002008020250743d0015807030f80d84c040100e1011503076034040c00d001c0e00c110003c064003030540c19000070309114410b00b00038201d0848070980c00c0340134182e640c00c0d03580040e818440600c0205920072403040021560540203803102212200688650016003450245404900c000b05031425280c02c0c0108a5a00c2641c64005840400e081100d4645880080613868210008254080c1903569212000d13244001100c420b4a07900c141159544146549015120840440b1114404e0501f0b0201240e0390801c24652001c0c5a00c0d10052a49060f09036186051101c1c203c91250805a94506410550b0303030b032280b1000d05110403000010707441c5011003030001c00f10300c001c1d44103aa64010841005a24142a000c00480e441c140d0006100d468408048401340e88110340030b07049100303a41c00e01c60722401410004044482d90742b2404404808059101d0325a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 636092473 1250 636091223 636091237
    0x206100e041b05040507090905180312130506041b1512050c0d0908070c0b0f0a080403050d0509060f150d02010c0f02120a1505060f0f0a0b030c0705070b 67
    0x11004a022900003110740b505220484802500c84080a44a00101c3c0071244201c030f8100c0042c0460340c04120600180c80342c95007000083c01420354852103c002203a49209010070945440100000594a0031442c1d412000f010f40c06820380b4102d040030305180200400010f02c4100c104000131000400325206041885080c00035200c0d00314511100a44800030301c03000304445440c0408110003d85800d0620034030038101d05c2442c2d443d442343c0c15800c291026400e55003200c500c006040115010b5030603a4005d5802494191074000080d984074503084a05018801103106030390b0410041c8495500080f5445108030b4241c0e125032000e82d0340c04000507908050500080c0c00031078400c030020255128040c0200614050140000ca180d00d90740400c50440d200c11110080b9000409503200f084440c8a0041d805e02c0412014025400e10200040110848031041882220400080307032150301e620000800030001c0c0c1608948074500305c5a514902d50107804122214003482c903000c06e41c0d07043d4500b07032540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 636093723 1250 636092473 636092489
    0x20f1203071a36010e0303070903060e0d050702100306090c030e19030f0e120304030c0609060c11121f06060e04021804020a0221040e0a0e0a061503020a0f0303020610 73
    0x203000d50100343c0c03901a442d00d0081c0d5001e9500e0b0284405c5070038007000298015501a03660b40651869410a8002c40382c108040004540100760081559903008043c1c1d002550126642014005510010340042240382d2005010070300f4402042d0001c5c2d0903501000b801d10b60401a504501e40d40c189031090204425402000705100b07a480f4840c0e03a01c1203541100300341c0040d00c0e6101e55004044043d285070860b9008075a00200d0807011300002c0c3d40300419100500040c24056000004e542d40c8001c5404400c07017503401112a10000d4400d0b00042001c04550750096004c15101c3e021942c140014100c180a0100810600702d40a406400d15100310340d59003071644100280b460596042001031740c05464907404501c10780c481c00345a41960842c00140b146500013241d915403520544054060340184141d03020380c07a201e030071078144001140001d4140c1c1c0c018000214450010554a00d5602c1030304013940003101003a01141d8000c80705980e2080d00d002c0d8089a40c01d5585003c0ba03404688a400b460310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 636094973 1250 636093723 636093781
    0x30306090c160c0312021501030c150c0602191112031b0909010b0d06090614010f21091109060a0303080702070b030f0402010e011b020f1203071a 64
    0x4010071100003074100c0d044410042078211400b0b40316000c8a90f40c582007914a00c034070420021585030108802013085880e41005007440d8590744400c2030140c598410452031906541c1e6821240d841652008010b660040782191507290802c401104101e0262007030740410035103c0d0304180d0100014490044c0f03c00080c0c00c61650340e03614000382c44e03800e00c0d0340714810300300702444418542d99600c65028082c114210300541c682d00c100072624151011903000040c0c051030840d05006000034031219200d03a00d420301301a049405120070840d00d91186041c412540c00484400103800c04c1960018031100b4081c050102da242c03144420000c01c0701c4155901c030351100c4a8101040000c0c010b07801281e204801e4016a461155184901800f5038811500c480007450031008102c1150303000020707140c0307400b401c0c0b0380602003407010013048880180552000c3e2280c00780d5042c43c80c040c0c1c2c541e440146a1210349064a4440082d441c1c00c3c3c240d0040e442c25000c99580c17040006600d01c0c607662191403410360103c9403c4c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 636096223 1250 636094973 636094981
    0x1020409061e0920071406090a05190b150d061802030105100506030621010504030c0510140a02070602070204060605031009021305040218030615010908060f042a090b1203030609 78
    0x5001940603031030486d864a813218642200c12014010f1901c542e141d400074015030301381440c1c440e00700240c844001c10a100005800000300343c0070101e40c2c0e030014075551a4142d00d8421800104102c5100320010802400c2c607035124041d4052561444542d84258000e000c144c8401805902c0722009000d26170304480280b0001d08646442e15880780c071851020300b035800201050203502d0940e02d00701c9059000c100c042c10310350304221042200c01c1010705010000c11031908036012014000390003800744500e260b000b0074220103001407a41260700595006004200c91681d0f0072015010383c100302d441c600d00e0200080001500b600500031141d120100f510040c044501300320401c0000d4000d40800d00700140b6080b04c503d0300303441c200a181d009404141c2d450400341c1e10400010710a41c40ca401c03512960304900c0c2804030300b2045c4a031a9820a038010100b8504640340e0321803600088600c0d81d80101003494980005462040360b00030000414107a031116a441c0c001c82006a0785d20046e1041070700501c0800c001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 636097473 1250 636096223 636096281
    0x10b10080712110403030f051201170f0304080c010906020307030c0204020d0e1b04050901020a0926030d050403020c0a0303080f182d0105040b04030c0501020409061e09 74
    0x115403101c01802d1621000100c480d121044aa00c0000d400720294000b03803d006158100703400345400c000c2403508070300d02510881d01d440d94600c184140a02060840d80d07081c0c101c00c3c1032041d014800045e8048a80b0307980d8804089030b07964034048000e404201050408a0300c1807020046a14854040d224000000d45035070a0000079401880c5ca8000295500001010a0401e0141e8003e0407440f0303150080b2007542404120071034101070407a0400d41e1040080024060f0060b484108850176241000355039814450b00100141c030212441129000c00075404666051660015002d9402982100d500749856003c0c00711111035400090301040d90b0500007059012080f0029a1000b541c00f507603001964601c0d281403030500080490500c1c030810408150b042c01c103483c1c21100389581e0720300a100b541000c2d200c5101c19100a040034007008030618410041c000250100d078020007803003100f0007125582d0b08805081c4500c00c1c4070044114110440041c40707030400c0c06201824103c2000540c080b500c0b0030b60b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 636098723 1250 636097473 636097487
    0x192306030106121d0f070929040207020603070819060b0316090807060c140118080a050405030a0c0302130507051903090c1d01170318030c030a06021b010b10 69
    0x29004009444000149400b502020716803070562038440101580c541050185080c00d08541000c3d0410786090014072001140104080300030403601302d1008c2040700b071008100a489076500c082d402020000c14090844d0744211224443c403406005000325400000c080d4054580038403680401d404c060020514034280c004200d4000407603801c00d8003005a55240003414000b0301e5001c1000704101c2c0c00c5003014020242e001000c20345540f4001c0001407400c0700309407140640c88501909000c00403480301c800300c0c05001150302418006048984500081c40c1c85070400b446070108900661150074200c654442c24001c0d24003446490322a1400c1c00145912010418001c0d42c00304101611211400c01141482c1440070150030100340e2200800450030500ca04804107a001001c0b4001d900700c0e0075416000071050b5074070200400442d000b48825200081d02d4580e00c2a0065818015600850100301d216801000f4081020700c1d200c1406140750421802c8070a03503030386980c01c0308030030110440d13252080d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 636099973 1250 636098723 636098747
    0x9020702011e26060a0501110613020d150504030e04020702012a083f0703020906040b0d0b0901080106030b0126030406030902091506120a0b192306030106 68
    0xa40001c0400a2007480c2d00307680f810340280c960040070354060207802e0806080440c080c06003800c3c0314200600e449411a0b442400501000901c0d0105518004554501d01000fa420b500304820864218981c074000e00103000c180c0b001c8001c180c290140080707508080c02039031201034050311000445c1076006100d4540c45001c18184c0092010307800601c00140a000141072400000c2c451410300e006542c18903820f1034813110712245081c4482629a11801c10700101d02e87c0042c291901603100d000703e04c0032800394000c5401c4000b0551005c54010081021607100786410382c07040325640d5180c3d0342c1c0d10206003298854000580020603003070040c403204212000c40d100d072500304207005c20f4a0110038051415604107070003100009803200d508200394a42807005980081d2012040050889102c000404600ca01180d1504880c4140005100c861895001c0c811803000540100403444038070f030302c9110030103d50040410710081086060240380310651684461100640400d144d030b42810001c2da15003504035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 636101223 1250 636099973 636099977
    0x2a2e090b09010806131404150608121c02071a010b0913050c2505010e16090c0c080a0c051b0105070f051f02030a0e0c0f0d0f0204090b010302030709020702011e 70
    0x904e030364040d400030703200340300002e1152611b40550b41010300d00702c41800c01c06200c0d101c00a08115040c006900e0108521110a607107030b808075a56182e12003405201000100c503a20114808a054014070071580300310f0103201220b008025841c5e88800350480c203070140c007100d503421441030110f0088640c503d500c40707500012030101c0141014a10000c00480d005c1c0210900301d01e0307401c043e201081001c2400340021458080c009404175500404002840e0441e5214042050340c0703503640c0304078842c00780c8418a011900440840e82e6141e100801401c8400d03d100d08683c5c5214210300c4031200f0700429420745403080705039942450b000f12606d0360703003400c2c0e4130310415a0070b4011101400000a01e90712070050b00042008056101d1030321040e4101101c10f030b40d40c00c54150304541d100c18040e548060814115070030480b40d80c0300c104405e081503216100042c5000b900075150030810420311203410348240c1260301c00c8003100c500540b06c40c800001d81c00750043c0280410201c0d0f65007510181441100c8010240314 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 636102473 1250 636101223 636101239
    0xc04020a0e13020c0f030412030f030e06071805031b150c0a060507031a0a05061e031e1e040807030e09040605060f0609032a2e090b09010806 62
    0xc800070b4a840145a02000e440b54001481e9032003c400b80710103d240703000310015605051030400d07041c28180e2880c0c002410840c150fa0701e24400c2e4066031244490800c1032003181d0051500d428041c01c555801e24030300c05015030222000802c0d2800041c00d041c00122181440400780416007884110b00c6046210700b8425400c0c0f0101c0000c1004102d001c01c085d000d14808211030400840240485900d00c9040081210403080d80c0c0b406d80703030f4025041c126442558a181c1e25105070100d202e203403a03070031840703221204004144419201e58000740400c41704500d071000b5090b22008200b01e01c000c0d004855481e0f15013500c002801050902c400382c5003081c041e08208213182080c20001f20b18600c02c90f0101c030b209590f1800c0c818581400ca400c0d645860007981c403145419810400a40d032034450308509210380a40702161404840102444061154090402070398049606144000c144203440e0340d007240d005a0201c1c500061080210604442c44046d499184c942498011a04100018a05a001401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 636103723 1250 636102473 636102497
    0xe090c090f040b0606030103020105030402010e040f180b010b1303060e16060c05060603010e0a0f06110703020601060305090304030309090f0915060f140a061d031f0f0e0c04020a 78
    0x1161100e0384980c1401d403003500740d0b24140c500301c0049000070705010700a4205200600042c0d03004400c481e0000c0d02400e2069080c1c18140c0010083e103039000411140350f0520442c3d00a02420f45102d2884070320505078410b60340c0c0c80d07001d0340c2080d000781072104442003000081000072442c0380d40190a070004d0101543c4456840000c0070f190440a80e0020380000c0403800c8500520038188000d58000f48110003e100c8030014a0381c1a9030754244100c0600306e2001280500d04221290388000d4414203a25445a1a01004c0c1406502c1e07100074401c83c0080f0341400005241c0b2400441280d05490381500d4a661940c1021302540080010000c1200b58540d10040078000ca15002282d000c0303a540280042019418114a85050fa00903440300c1c81d6090b400740e83d8542991070800707000581d04540342101540d01c0040b4006141103068203265090701070503c5603810040585050481c401c52400280903082420009004542405200300c1141c0c0014820401c1807415800504121145103040400902 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 636104973 1250 636103723 636103729
    0x32104020a1a0d0c1d09190b04021603050304051501030c0e071704080a140f07110102030f0309010c1b03120203070e1e0a06110309040c1403090a2a0e090c 68
    0x180205143e01048681c0c08aa000c1c401000c11981141d1007504c0c4c540b428244494501c00c01d0003d42d0001e0460780c8c86200442180e103da505885000f01c0702c0364900041c040743c0c100506240d10980e0140d903079020740c411580031118030342d03050340c101c0c2d0780090f081c645030f4a400e8200155007000b078602000c2012040302640c0f034101c2d00c40541c0c0914041c50b80070341c0d264040710003d403801600700c0b19010101d0040c08000101019031050711a02608000c4071f0308280b510b01c004030b0a604c0b400140131180342011062082d1301005500140c840d803241c1d19030329189160a040c410961252100040020302c40c035142c100c8101482d0061600605a403d113040c0220202c0009002c1c250201455926000f00803030594040c50003501c0c01c001401c0d61304080312180b413a12003081d22842400c2034140a1350300c846403107804520800c1d03154010610081029101c0c00c00742d00c800d443c1da036508001d803030001108481400308003c230034811500c1a150b64845925074502005c0d09200d940c010305004a5010f010f400c003280361 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 636106223 1250 636104973 636104981
    0x8070e030d180f06021011042711040e04020d050f03072109120602070f02060f09030d030c200a081908010b0405130203060a03080408032104020a1a0d 66
    0x820b51a4140e411648070802c409a04865002c140c4418010008222890f00410400d540884c50300b004108180d60043d99800d40c407981d03010515040c3ca0040f042115295009100840341003140e00380809880c6080100c0381d80194000c0040104401c0045401458180514240303d8414400c0e50b00c2d4030002c0d00c5090964100c088181d0750011003c0340460f0710340092840c1c01e17481c5407030304003a2641418802c041030005110750006008030b900040b41414031039284488041164002c04007903988070342c1d4092117100d4001c541407034020310600380441c0c2494000d000710b07202a82c1660758030380a5a40e86000741d0740091760071150300d01d44c06184e40c01004100900000e080c0e580040050103001204280c0083c0985016440751200c01c205010603c86591090940d11029000420168694550790009403a00c051940014940c8800250002e0341440110181801c80c54030800b03881508030021603824103c00484000f9070103144014140040c3c1c010740f10880d400342011008600f000040402e142c11030f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 636107473 1250 636106223 636106243
    0x30605010545030f160b31060305090a030503060d030c02060a020a03111f1a030703050706230906030903190305040c0518060405070c0f08040311030d08040308070e03 73
    0x40c4000c00b038403040c581803c20420102020020061044010711810f59402000e9405101c0c5000c170300003581c0c49004802e01f50141d14500d45e03440742074080714031a945100c8005a1251101081c2450700250310b14078041011a0203680580b6201e18580c5c5800c1000164140184d04505001c0b0407100740001d80c4604004e0030303501c81250000d11042c001030801030221240483c0340d510f207500c46844055500029030301c0d5600d42c02c000030b0108406e0414108108805500800f5580500c9240800818004001280c80443d0916103503207108851702c0070921245910207480309100c200c204544040d034108030300116071241c42070301524100a802c4108412182c821500400000d0315201030000b8070411454403001000200d514183c240014840300d581480300031315440c41541c0d10800149036500800ca01c903c001d50011100700e61440301d28003c1c0e080c0d00240000c4c0c805500305c0b0040780043c100040d4a00c1d407249503840344403c0740d44541d400c40720000e000300301008005038101c05105980f0108000c0c000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 636108723 1250 636107473 636107587
    0x90a120f02040b0a1809030918060f08010e0c0f0102210901020106060e0907030c050405030109050115090b01020a0f08090a03060507021213180e120a0e010306050105 73
    0x3450340c0c0303004120aa480520f00203105a50341d604c01c0044000b41e505401103c000f250f40032a03000f5403410b060b24250496400030410403400100d0751406600d80d40404250b4280c54200c0076800e840d004014222042142e000c05581e100d090014900d15142e080c403c040d03081441140c45080c902059100040c8000040d42440c0da0046416800ca42e028011600904410b00c1e24400c1c0d1a0004002021090f010300320310107255441c070051030300e640b00313a00301d0b009008060020702a0340300c2450103500816a080004a070701a5128011403400303110f01400c1c040e020164000e041d0385105484811099001d0175049410700e404025148054545d508600010341c0120b40000e42854040d05c003034200450000e4a4084240412400300001c44074180390702540c8014001d07035651160b00d600e1780f0040480a0b10112144103031846982110004401007240c501e00f1350301c90486451482c010f50a541071809028045401848140302c1c02c155038000300103c202c1060602001450359103000012403030903078000b074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 636109973 1250 636108723 636108743
    0x1080c0f0918011d0607020604030504090b03010603080c030c120f04060f020102130e061e0a0b18040504141207050705040203130f0305090f06030f13050a1709040c0e09070302090a12 80
    0x4c2c0005050101c10340c00300550000d0101d41c81d081c1e800038458411801003101040c0c0e03601c500ca00c1c1e82c4003540998003450303100c003000e45c0e07400c031400728184c0d25005082074151034450b820031a1a015030071800c1d2040110001c502a0916040c0b60342502e9203400c500501003107642c02c3c4101041c12401046103c02002c0340050b040e882d092640600c0003409011000c0c0c68082c404007a0b68141e80c4884040c1c030126014000030f2a1070300f803002c075084a030190750680150302c181080244024054040d800b1800102a50102c400200402c500106135005082018149410503c0104803070f0801e500216441403004000240d01c0302d0300c0e5210311412031400720a400150700031803480b4080c281b043ca10609250121007080c1180b5180790b603881c140c48001c0c00c550300c1d0855401c5c15070030003000b0042e05910551000c0c0e03102c0318078071400d42d0000d160041d80c10203110314203041080d05c4041c0603401040818101511881c955500c0704800e42c080c0d407107090604d400c8003003c2b10020715030b0003084c0891281c0d8452102c040b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 636111223 1250 636109973 636110021
    0x4020d0b0403031b0206040c090b0105090a031505070804031e05071b050109290d110a170610080f06211c09120b090c04020a0804060501080c0f091801 66
    0xc5104d40d180402c14150f600000910001c031f40300045442c1211a120804038034101c3c4100100c807540144c1c030001c1c0d08661045804820001c018015142001540000b00310319a10f01c0011510000191805004504d40112403000b91000c44050000b01006040407413074007c00741d50b0b00b08041c60010b00303c801001280c10a02040d030b071081e60800202041000000110521f48044215400c1c6801c680303088840040d070a8817114076608501d1140b841507043c140c9600d00c20300041c080c0c0200a41404840c100b502c000f40080c5402c080d542c03000c1e00f56548a469964400025032002c99010f00100e80c40b4121241c42d05000200030b5109102200800160111084a618189000c002c0300354050920011040520481843c40c114108480e000292086c1a0720ba488089081001e04e2204542050000400c0540b150308840320074040c40c454242013065a0340c5200c1513441d01c000809481e80f0440c0d54817280400e280c140c008541140c023038000102e034810f0a00c5400d08451410050b18020a0609111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 636112473 1250 636111223 636111251
    0x201020114070212131a070314030c071e2a0f0b0306100516080909090a0203030a05091207080a03090911030a2721020c090c0304020d0b040303 63
    0x51902a40a01c011212034105034101a490300c1505008184032070012600d03809003201ca800150040c08501840e4444000000407050036070712120082c0c01050b19020284080d2441c60100c5e8418401c180f462410000140e9445e581a001c5442d048a074910583d1950041412030840305a8000903e803410384c13203841603c030a030019010b644240c11100502808028241c40081140c1d4040e9040fa00090602c40e1060207481502800840005600d4001c204504000800c00100f0b04a4000c4071a12510360300c400340c031696018001c90003900341c0c0003802001d010b94003407130107026240001098120072030035003004640390451a61111480340d00010140040c140c114a202000e00b030080001c1c8078640d14003101081030310002d048000d846540354402c02c2817070580f01e00d800c1e0781c80b10359560700b8000a060038144002c41130f1144410101045181c1c601006000080918200002506a212590720115120026040144240d80042d00400789800003445412079034881c903c00e84000400303400303425078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 636113723 1250 636112473 636112481
    0x706030b01020c060415140310051323060f0d06051501081005060a20060a0e0f07030803130c0e1e0f1618140411040b1b070506030c0702010201 63
    0x50300381550444074410031962034071022541540c241c0584280007100580302103401103142c1481e59035803c0040103108000f601035162500702d801c101c5003000c2514040c004502250b070000150b003110341c0550005081c4040c48080d0552100380144080303e20050480881c214141c0200200c07030043e501d4040207480c10048a10712400c1e03900386007004d41c074503001e10b00c840c4d40e22040c080e40d48900c4010411107419841000446283c080c2c2c602101e007513200810915981c2c04080e0f5282c841541009281040318078000307104030b04801b500f401030409918544400c8986d40c00501141c3d0b0040c0303e11080000300389103100441c02080181c444019503e002a496090b0f2030003c10f032028030110100070b0081c1b0302d46620403960800d0380703240b485005018010003500d048041195620016050003030003e803100020f10603130b030918802d0310148515100210724100c68800c0d0300584c10110320500200080e1841c81c0c0390b0300c01d4840c0c500200c0392090740700c8000a4254008481d0115801c5000802034110350b42802 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 636114973 1250 636113723 636113741
    0x160201180302062e060305090109150506030c0303030903090603180d050a1106010e0613090606170f030307050a0f05090a0e25021002090a033c020d03110a02040e070603 74
    0x2001c041501c07058513054082829442900700301600c450108101500039841029042e5103ca08000c0000c80f000741035001e400202c901c0d41c4240944e640da40443c1c00e000c411a40310f034164001440c038000c00c5004201003070f00080e2504041c007813038100901042030204211161040317192030f136685605020100401c885d10040c800034254204400400203420f905130204c0d000a400c0b01c0041d100c0c03801c034850078000d003500340d00900110308120000034038248407085240b0308a84201941d030580b0081d80381d1a40c0344803e45111000039030810102c0075407481083c207030710400b0b000c0c50444d103452060380000c1d000003e07a0f048403454600e0030003480b01d85486250400c01780c1214500c146090111078001a4071402e81a00d884482c68000900900c550b403007a502c030300074641c45003c071101c45840d580642c681e621004010358200303c20b0100800460900001103107016030041c01400c0403c01582c2c115951b4000c0303080d4070642d110380800300004ae922406031006598001004002c01458400004c0942c2c24100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 636116223 1250 636114973 636115021
    0xa0311100b090604020a2d0f03090b070f11030c01290109211703090f0601122402070302150a02070b060d05070503030703020f0616050316020118030206 67
    0x4080d030015a10b5495125074000b40880c0c0058890208880590701001ea80d04410104440351700402e686003010f0002c0600380001e03a940d8081c45905940c1074040701d0703003c40040d00300c403071150000c0d80300c030b104c0c02010040e2062072400c01101500003821a14580080c40300c0c48099454807010a071003a04030085110000f99055040616514000060510140c40c05403900c1c021080c1408102406000707850203030260311440381902c1c0c4203291039102c000d420645d001d0415005613200d040c03d01000041990503220000366220240c9001d603224909a00075840e000c102c4120502079142201755032002e45007090082c0c02502c00d056428141c0c3e03081c00002080e03600c04c0c601c1070100c4030100e0001442c0c80d034420b00035032ba0400c00720a20b040007464140c00e540150313454400090b03480101a470110710030110301d030000700302d400b99180c64051103a80340088440000046d0140300040d6080307040c10660000234020b00002440400c000020610f50b801100d05401681c0407005111495102941182c4011518 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 636117473 1250 636116223 636116231
    0x13c140a0e0708040c23090112020109060509031006330c02060c010204080a081905120a1a0a151206050117040510050f0f0f0405030d15080a031110 65
    0x8a0444122a075016101c64100441d0300700042c01c10580d411414040c040590240300321191014850700c0c040c0758520040d02685c1c0c158000201e88a00010b088521913050715156111414104112900e030462080300d68140300340701c541110909140710304e002070806101ca1884800b1003100350803410404044181c2030800b402c540001042d440b6510000a6034110b4284c1d039504010b880e4140039001d04d400c0500280200c0d0004402c002154004100e0316004c0c200043c640703403892a003030369107024201c1003503900c907a00000181080580c1e0300c030750b40d5810b060203800010052400800c1404445d6006079128070441d5070044010340e0040407a603c5d05140d06414800942004002012000c1c803884071341c0e0180b031400110f4100705040c4200412402d114104200c68500008411003154042c2d402a44c07045007a004030300984461081700384a139800c07500440c13402d806400d411004090a180204400e00b240c0c47c0841c15072428400c61341e00c54025640c080d100301c40c540125080402c1046800039651034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 636118723 1250 636117473 636117479
    0x200d061a0702010201152601090b0a0b0a060c0b0c09180f07030b041104030f150e10050105010219230a050a0b0906070f08070912060f0b011403013c140a 67
    0x1100502d803000701404644900411070341051f182c050580e040004010740254020890454100c0d4000d1701000c0c0c1c21160f59034900c0e610023007a180c1000d1010b0250901e5841c0c00066101214140207040081014080035102030f040c0302440c003e48015a005103016070701e1424002266450302901d111003500b250300308400d148400c0c0079410761149210003490102655100c0003070000041c071408002c80718031414081740711444d03000d9407541d507103c402c40000c074a42000802c0c01d52000512100c0e10004c442e0f0f01100551907140d01741d01c06019121020b4510080a240010032000d03c0400300041c840c07801482407007558500303500712700c17070060041020b40d20080400290540c043c80001000c0f01d0307428820b510340c591100c111042078454020840d0f84000d891076030300f000f005903c6201c0d0042524810030906442ca00119034004008003a441300344c2c410720050005041402c1000307056800b410484507010303000400343c8850701c142001d82200c0c42d0402d04c1007110348484011049045802c8a01350742044c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 636119973 1250 636118723 636118739
    0x110a020a061a03061f06030c0f0c05030915090f030d050708090a0b190e03030a02030a180306060b0c0709140103030309030c0501020c010209040e01200d061a070201020115 75
    0xc480d0000703402261901c900010241c9603600416801e81c001d419103045280100c02c0300c40c00400300780d04441c00c240300c000021b5564407030310941c3d1500324166a06203000d00e40440885d000241c4040a40b40d60004010b80d92440eaa10420b0f03c4018140400d41c0e500c5454a0b000c01142002000190f402504821216010940d11004407040c10b40e20500c030507100e01d0480c01003854018590002c41c82c801001030341c502d05802520005004074101d40d9622082e030b0650302031580328022038003004007690003480f54100180c021070b000b42103030194100f0303000b4555482e1155000d55505600241c82a04006880b00c4188014030483c001380030b102000303100315165401e10000250051201804140d075074201c010816200d04d50100c900e81e04000203549445103410980c0c002d40c032070f900c1c1a100d2840e00d0004440d030702c018050313229a8844005440d02c00400d040f40700d640c0303134885003019480ca03554100c04502c0c0d0205107140099203503141e24198881896100182c00c44040d030340580051905c040003009055 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 636121223 1250 636119973 636119983
    0x3060b030114060318060408030919020a09020d020d0903031b020a0b060f0105070b070504050f09040c06030209010c0c0303030f0f0203060a051e0a035c12010f110a02 73
    0xc15580c83c1d40d2035580101d946454141e4800c102c5c1140200002d0000340041d82021b50300a41e140030130b680b50200c094201050702068401d0094000c1d07201d140030018442d699003d42410f4420180140c07070910046e84030011102849409c4011a50b82c1c1411040f0100307a40c9941072598841c002010300c000d95840e05490001c00034541c1e071054940500813075150348120300f0f594806502c00e01340011030401d60400303041c6030080e00030103018980c0742d040302c5002d04e803000402d4022501301d14452171540c10050b04402035403100c501581070001e230b00b030003070300080035041e5a2004500a50b40003a101d0708000038241640d00800915002c10b00500920140b50344580f10f24040f2581150100701d09146031501a0b0400728860b01c8680c0240380c0d01000003407100105203410680040300f0103603030042030204195081c1200081500d40d0480480e0f000c180300d919041042c1c11030084e4004032444a03c013000040c050540310405c9009a519210b403044581c3d0303503000d410081d040d5041030508052115500a50320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 636122473 1250 636121223 636121259
    0xc070e180f0f010608120915070219050420030f18030c01090506071e030f06050d06061502010207080711010e0904060c0f050c0c061b010504050f250e0613150603060b0301 75
    0xa06000b110200b0082c8c1014100e40c0901c1d800741607811112000d200b072045070030942c403600303024505042c5010515400c61080050b0941840c0c0700608603201c604807280d08090003000d482da0003100d03401041039448100054884042e0007000841c0b00803880c0745c2141890b10141c500300600c0125075502d60500f040c100280044407840c5000074251a926280c2c3f4094003603644003030742260710002001c06014568204d10306940844c00303010031701c445480c4124202e06c50000c003e40b4a4100f40a4000003541104c10083c54400502d4007184196100f00040c0b120b00c800d032411a8a00e44d241030300700d84146c0203000c0c203100c01e0700c40c1061810704c0a001902c40d01c0d03a10b114510b034810480014228000c01214014515200103c4001c02c0390f0f20b080c1ca071055560480301e41a100b60310034800360103000500f40807281109103c10508400c254545503d107028440e014200350f074000409031001c1c0c800c210724407078004a80e80e03444551004034641100503084552036000305d00e00300d82c204010700150f000d40401d02d03a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 636123723 1250 636122473 636122479
    0x3030304081306031a0d03031d010c081614031902030a050105100e03071e091a1507050307030309020d02031b0109050904050c011b08120f0c0c070e180f0f0106081209 73
    0x15501b0203140403002040840340c4400304004410707255000b2101540400700b801d21a40f2256419110700000d001d0360303c05442d480c40041d000400c801d883d464514083c503000a0301d5146a6110b24803034000c61300b6a0411542c96008540d940e00402039458441400000c7c1225801c08400017050400070a40300c0c6100e0146a02003490041d0041e0b41d01860340c0200014900d02c01c0401001a403020300407180009214058850200204001205058001100d000c035038440003d501e802030559003a8081e2510400680c0c5c0155020701520158800303200c5c8021588118a050904422040004d0941815900000d000344026400c03c00020030004400003991000d09002c244100c2500c606910b410080340000d000c0c0901003005001001000c180c280940309405041b00b080d5503440311911907010b00380d98a070665020003420009002070b004016009084a1460410007640c507045c03601c0c0c22052900ca007095403109898101d0741078207119860150082c040901200302c034244a0310380d140107060140788 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 636124973 1250 636123723 636123739
    0x50c03040b04081303020d05160f06020c040b060904050a0c030f153303020a03050109020a08041101110111030f0a140115171513060807030b041103030304081306031a 73
    0xc1506135410340c1d000295401409041400000c0c81c019031100700030a00304d046604201c03030110303608561003028401e9a020ba402040305100320030811000e0244081d40c1a00410100a90b50140d100c0d80561846000700b035a000c1030141c1b03242c0c4001c0803510181d403c2c0000e1031401441c13040c0b0030303480d41c0d04004980204281e541c0e0798220500501400d4049001180501c0c44522020a141d170190040c0a441c034041d10f081010380e9941c02c00340103a115101c400343c001003d1000080c0010411880208115010303d4424810207116001c40c0c210b601030070406049036030220800c00c8200d1464490390740314035903560502980c202244903000c044d1040c0100300360715120910b01c2d51554428102c0d902d0a0380b040b01111500d040100b0207030040d0f20709100243c0100710f812400c010b1020b0714002d010407960080c0003002c00510f941c0b81c0450155010f04115554500d0010b07151480e42c0401c0550b004501a0002c0c1c0e5803800d001c1c0701c2e400150243e5228a040c541001070500c44000200e03080b110043c400e0b1341034a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 636126223 1250 636124973 636124987
    0x1080c12041502030415270b0a0605120f0c180f04050f0a03030606230a030c0302040518061806011b1e1202070b0c0d14070f15050c03040b0408 63
    0x400b2265038401980c8820310100400003401029400914206030520007007000c0104029a69020102d040c4060014011710121000085624554540c0554100740004046407168001690340c0c03e01c400510040d03004a81c01403111605101005202c48100e03001c072005088041007125012009007081c0441c50502c0c0040d0511105001b00880c2084d140180c0d80c84d280540b902800405480c0107040026000c802d0b40641004035101840b81160030040b440d080990510b021800703441503514010405400744000a106d03210341c40140a8100d40700b028001030714100c42480303003090420041200c400328020900c11140d0f040440c4c80c080038059540c0c80300c00c0c074182c10054901c1c5440f482c800801c103c18208803040c00751080068501920b50303800e0758909581e85a11441a0244100010040d004024440060740c000c0704080c4194040b060202d09004950f15179600c0e01c610520b05860b4405005940303915000d980c41000da00c0004c8414050450a05469680500000070002008410006445 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 636127473 1250 636126223 636126233
    0xc1e040f060c0201020316210305041a1f2303070f0323030a08060f0105073512041a13030309060f111b0c010203160c0f080312010501080c1204 63
    0x9420309120f5040409003007d103071924000c1d802c107076038000401c10004103944c20301a1190286078002e9070803460f455000152114500d040180151914100888242504202c41074480041008000e07103012140305501290f0051031044c0c40056140c031940000d40c042c00346200110f021400e480d003156504588211000e106000c0f44c26a0f032800c100c5200120300c03010782d00d902030f00b501c1c89614103640c45100040c0d403100568140c000c41400030404030307040c0004241625088214003c00e40054549184a0803101c43c190843d402040c50021401001080101307010003420510300d160240030b1a00d21f5460010552801103144601c001c2c02c25444030300f900140000b9070000604500c811100b0000c82d1210101c5001d10f91002e00d4240f481c0d51080310181c94902d0103d0171450020341a0080c61410740c00300820704130400e130341004994160380448086081d482c0e0316096401741c45104010343c0da45020a481d00f80744031059002504120140040042081820b0300752082501140700d4a89592500e01d48 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 636128723 1250 636127473 636127477
    0x10e090406240905190204122d03020d020601080a0b06060702030f010c03020a1b030203041a1207090e09120d1e0f1b0906020c0918060c1e040f060c02010203 69
    0x1e8422004550b011030084900d03030105000c0c0b040c903a44084424000c4c0000d0742680598480c1d59030300b00500d990800071074010b0031b4500b0f0b4845064480f9480c203400341d074040565500d501040d00180d002c660807000054040103018007400c40391006000d00b18440e5242c80500c60700403c0302d80038002c08107005003151001c02c00002c1d1048240c00a101d46488440010001d41059400030f0009400c11807220840390420880c00c0c846030194051482c0c1814800e1942e6031804101d0001d01910080117003c86800820940d9800348040e80ea48200305c1e8981030360b15145442c0a41004655004401d9680d18481d1045c11a40300b03480c1441e010502c1200b064403000c60070010400030006905100003640e00138a291711030070071003005c903041c00025000f800301111a036905020368000b5a02909442c00c291401d00900c6030701035900620700d50b007603120342e02c802c0c10410207840f00885640003042206401d40359048001c0441d103400021410300c3e2500c6600d4141400034400c5005203c80c3c51070340025a4800c0c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 636129973 1250 636128723 636128771
    0xc0f1e020405092d19170705030a0f02030309151f0f03060c09060503130c0b0c06070219080304020d051501030c050301050708010302210705040e100b010e090406 71
    0xc10003032803030001c41050f11540d030b00000c130010080241e240f80e03103012000f1005000000b094024100103102462101142511110680d6591006170303503d4061700c40c140082030b00303c3c4a24050340d1102482d100240c68180b000648405640040c070804c818031a0000d00b001610202c074401d175003181c80d00a080440000d010f000cbc551045503035480891914035001c800b5044902c640000c2200840900044881c0c0185004003000075a042003c5484032104030846241140941011130a16a4541e006101d80d07004112094440d0405030421070040d80600c4070b9011051401d07086940c550a03951543c01e140310042000b481151280000400d1000412030901e2070b28200b480d40c0e000d0758682c100301c5403507030641c460b452007582450300080d4264030030410941265409000403000e000901c036500b02c12000c05030745500d54401c541c000219170790341d4010500e51080c040054030350349a02c8c0c01c03a8010340342d100d00b80f1414000850b48007082c40c0c0390642c08a60003904140005902e12400c1070150304449080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 636131223 1250 636129973 636129979
    0x6060d11090307090b0a0e10060305070210050f071805030a031b0b070215010605250f0b131e02010e09090a0f14010516230702041103160c0f1e02 64
    0x40c001054135800d580c09944002d90440701071803010383c1d4252060600c801101d1080f04034402c0d0320100012806034110030b40140840c0140c0301c100700f100c00c0300703011210121542182c0d04500801e10038665080401c0502421080400c00004c508010100b5590754016100508204030362040c0c2c1060150b4030000d880349940007035414a5410448002541d80345c9802c0d0462007004208000100030b802501220520700c204079045e40001c411035a40010f130801160281c820284206032003001441481c400c41c070400c51a0804102c094050030407403260118021088040d40d56050b4440160ba08607a0103884104100ca41045559641c0e0419042c8400d16100a040701c0040c0c03040d808028203c0a4180c40380b120200820150703543d060074039000004152640041000130501018030b21481806400205120400d2880c0078165404241114854030f01e0580c1104040140302e071822885460410807c141e03c0c0c140010300300398030789007080021804010141c07204046643c24003144c001c054000f40b9001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 636132473 1250 636131223 636131233
    0x2180403051b0a0506010302060702130501180f0519021b0d021c021c080702070512010219050a051c0605120a03180f14010201110403240506060d110903 67
    0x15260140c05a00090b090108407200200b992034020000640410b11941000c01809030341d107541c090290541c8045c200781c0c1c00021505a81001540c1402000e0003000c51002c802800c04510300094200d070f0f100d0f1640c40005041c103042c8007400c200305508440e200c109410040e96202c42c9540da4116520708150304180c0d0040783c1041070001d8004c101d400340109840c0003c0880c50480a01300e17100c41c06d004c405008000881d42203074035030b8828240c1b603900060a004983c12603407140d0001d00101d2005407022000c0e900000e428081c203041d10003c9500e42c110f03040090a141d18000090a903000d9054a0004440022800d84180f01c903504100010b02014184404800a00302c10a407111301070141500450401c0401c13903d048620301c41c00003103070b03d80c008060205007040700040c4031195080c1514115034813040e0341d0000041e000001c1000714404c10309a211842106e859110f10300711900320340c0d0000d1410041000d0340e102e0700126034046032913027800a402032115100103182d00403070b8807107505485a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 636133723 1250 636132473 636132481
    0x10204051504031b0333140109110901080726040311071a0a05160506070903050c040501120f0320010e0106090203060a060f120920101b0218 62
    0x41c510041003920302441c041d45114040c40c0301d18000d500700c1e1000814521001e022080001c3c3c081311950079501c00c0400c034405444003070302e450007039071450664a248401b1715001006011594401c02d1a914144000f481c28031072000000381c1f2610006025000703100f0301d5a0214040d0f82c1c140c1e480e10525054650b100d60b075003082c0c00c2c024181800d00074220707054821124041101d894103054843c40040c81c1c07038a00c0c40c100031b41038101c85c2d5402000c111105010341d06a100001042841214800c2c4a15500c0715842407640c18040d2806c2e0350090003502503403504005111850040b40c10340400c6410900c9219800080c0c907040380d0082140c0107505003407003141c902c0c02c80c02506422500e50f601c6400000e00c0302e540c880c8401805c80c80161102d5034840c802c41004c01003607000340d500d4020a0700034105900c408a26946540580f2069003085850f41040c400030100307600b000595001d03040058605003112a40000080c00480b8419000380051141e110300c04210340c0d403e441d141401000405103801814 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 636134973 1250 636133723 636133759
    0x806030a05061b12130210090302030c04020705280b010906030b2806150f1407020907090e0403051e070f112b0c050d0c260102031303020d050a081801020405 69
    0x324504100c1c8247c2621001510315072050036140296130300203028140b0b441d4000300f04402540030f80d4085685004005c43c0d0220100a40c8800140b070700207076141c8410041324600101c044805030042c0b014985082021b0010070301c12421a58046441c10000350300103c00313401c2ca423040301811401203070a07003084008100d160013840c40401031121511440404145032405403494010800200c143e60810b0103a0409071600000c01508a0600d003002c0030820380f02d0003820030190040380c042d004585e00203203003245040965528000b00c0d01035403640c0e04100440d070311000e500d800c888000d045140440d2850345603a654400c5a00d060168030340080e00407000c20002229114038000964054042030b40c0003426060a00b4001851a40245280140c40c10442ea9400071072515100c4044608200911014100c0900c021806100c103814440301082c402d1034002d00d44201d90070f12508004050100f20b040981000340b03203800c01030342503e0342c000d20a500005802400b443c2d1116602440681188243c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 636136223 1250 636134973 636135001
    0x5040c060807020102091c061107030305090d0903120e15070506040b0c0a0504061b02040f05191104051e042901021b0607020a0510020309010806030a05061b12 70
    0x2660648075415941c0c0da40d0801c1c0d08034018040140e41011080c014510300405030702030720385601c2c4203041c0000c00580b150f4510580e90800c810850101e43e84006100300f2040801001e4070012086c5000d801c800e0a5030350b2541403c20b56188142480030301b0340c040000f91340300100419038407209081c0f2501ca1a1500f082996010203803025200b00c006840480c003008a82012201e00b090542c545918152070702c0b078105d558061203000311400000030202c12005030345a01507100007108c000b1000c10b0782c1c14600351801170482c215400d001841c0c03038140c00704141a0100180c2e0101e410403103042000d03652003580c0c0c0b0315940803d620254003614201255414440c41d00003404490f80c3d003044004da801c1c010005990b41c100c000c03072400c0f042d9489482c88046290004c02006d5052018000c00c0105a454010aa20360300c02c240c00d9025800204030845d965900100c0242e000314220f006101071140c0ba29800e4440c0005094031103582a50150100c440500008440c06400c1c500301005441c41c005032090046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 636137473 1250 636136223 636136229
    0xd210c0c051c0b1e04080405090f0f1605040b0c030c280b06040902120303011802041d09032701170f01091d0601030f0b18100b1305040c 60
    0x12500d40042601c2c14440304104040d060100640580203040d19642d82011000341002008108800c41c900981e2404440034050351050310340a40721400c0c10300304607606030300514001d02c22110074100280c00307502c0a026604082510303016003a1031894070b41100e03184a1904449115400001c0c81d004400c0000010800310a80c5010b0303560401c40000c503440e400321124080040e8665140c030840c045114019000c0c1c010703034003e10005104100f980401c92042e02040203c5d0780d90004001084130300b0109580303000c000ca044504601c1c190800c5030f100d26801c02e18424104c910f44040008000c0c40e410170840b03035418220310391240310702c42000d0081c490851804d0391a000502e2049051030107140041081c4c02040d00360a0165a40c1c04c14000000404191180290b140070810700b40c0b6410805210785400781d4014a54696960118201880310100c00b600440c901fa0540310252641180410f107412024010301001c2640c0d29810001001d40d59408c1044074400c0c904000e003c00c100800e0001012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 636138723 1250 636137473 636137483
    0x120708181804060f0e0d0206090606040b060f0a050f0f071104050f0f100914062103041e0b0c0c13060503071e24020705030c0105090d210c 61
    0x112590310000d110400c100050554000c0d00d4500c00300d000601c003604004002d41c007800c0e002a0090f00350a0084c80e011149a182000d80c000106100721302109212141d0300c641d040d00e00303202c07060081012413a24030480e00458000140415082c80c0c1740d120310200c0d42e504001040d031a4640c0c8000880c1c089a40c007020b02201c6084907044003100505080c05528400d2044c0d030082e21460b0340341c05042031042c1307000340041d030400681d1001203108891803250101e2107c0d1039240700075518040781482188183e17015111030b6a056445502c81e282030000481b070580c0d03c82c481d076621410b807040b11015029416042040c15035400300c4d0030320390714000003a8009543c1d0101d40100509400c0b2a5000c12a501402295015045200140034907051401c3c0d80c81824103850415504941e41c500009600920143c00500200d1040c6810a140d6040250202820307040b00176281c1c10b545a000038126200343c1494500800003100030500340003000020300306e641804400244549007504005241000c00001114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 636139973 1250 636138723 636138757
    0x9011503050708040b04110307051c020a0530010204081002031f1511150a0501030c08031801030e0102070f1b0e0f040b0408190e090705180103020c120708 68
    0x2e9291180041c0d074091904030604611540700c0c1e031503818251310342060161301841031a6000540ea1160792091440d11031030b802d1901c155006104110b001d030400d60080d8030840e00410f140c42c404502c0000d59280515850f4503034910003909440501900869010320760901400f4104c820f198007503002580305075100c040c081e00200c0c00c0f0741c001d00411a03038000c12192075499483c1c4114540684802d030038800c0400110380b00c078050300e504245462801c441a0b84e8141e1140010030030410300f00d01d480042d140800246060030320070440d500249100c2807029040640340d445400c8044029412164401d8210400c06011201810206a034445040300c40300c4030310440200085540300c104200f400b0360456900e402c1580c0790b6031604248804003810586000070f04101d41d260742c050322003c100d01c4045940350464844801400c202d4510002898501400800c22001a18890004035000e0243c024200144c84d0403003402103d151400000f103860442c000000c0349002d118040c07000c1c0030302c0a80e5200c1d000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 636141223 1250 636139973 636139981
    0x80705060a0606031b0f0314010b040e01060c050309041a031c1b20012f0d0e03210c0111071e050706030b063109150308070c050901150305 61
    0xb03048075100c1102524225184078200c681030706c1171030011580c03030007450040384800380a000e03c40410001ea20000c060f50001404101002003c0e01b03079070051030242019002d1031802e40344c0d41e880c0e00c41e901c003091040b030342c80485280c081000c0a4004240e4001781c1100c140155500700003040000c40c0710032074007050188039202d09880c0000c0301e100303145030f10410031010160a0002d11004a111a42160600140180e55981c22511555454030048661a854284000d40c107125040105040a00d02045008102d815a503200040d1386a4401403501c0038410950056100070003900640103580076a5090101c40d0f0315116401d4007a109942c050078007480075001c216207004d800c40c0a014001d24540050b04100000c0b402640810245000074107141e00d40a548100414142da40240204070181d1039119852031010810194010749104807042121124904071241d14075905d01c03008040d400300140010401441e42621402040054039800544d40c540750201c42410304075919100082c9020001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 636142473 1250 636141223 636141227
    0x120f06090f0106020307080d0f230a0204030f12120e07141e12010e060f1e01080c040e0a020a03080a08330103180305190e060306100c080705060a0606 66
    0x910b04a9038260021032911070aa0399400d0f02e82c00144148000659a81c03035450900b500d80030b8060b5000080c1d107041e501900390440803400c0720340544070b4004940b041c402840003600b4040c00c01001034000c00c01e800000001d98080720540301d880e4000c4a0241071110140c1d54281c001a41019202d0422243c5046082c1809105015030009402000a00d14529411184c24807440c81c4e8500c01101e800400c00c1440501c640d03141c114151560340038203000340c0800c10300440003040110302c05045000c40d91594074084a003952181c09000030340c400d80e0707114140004644204140002194080c08108001c0e503071f805c0c20361344c0790812114100400c2d034403c0010303c02042c240c47c42034011012501a80040380071074034a00c4032110305a446041c103a0300c030707003065406144500040300075110b40ea51540e1200c1c001c12104030444071180d06001d0042d80c103410420307507482d01c003640c0d4026070549800c509100841012100f0503c0ba8001501503640082d1000511601141c11849800404024082c00f5070790702003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 636143723 1250 636142473 636142501
    0x31308010e1e0715092403060b090a03030f0504030b0f090c0102060106092601050a0b0a0b0c0c04050a0b0d050c0109120f020411040f180b0402070b150105120f0609 72
    0x80b031032690300070b10340a00078800508880303140d0303040614004200030348900a2880045060484007541011100e20040381c0380c0c14018140a40340c456040c0c0d00b000c040350040b45480001e80001818401140c0504141c0e91150060381c00568000358442c4403401d040c1407580304000306555128560156000d0001701c2d500000b00039040790b2241d5601545546080750061001902d1170502121100c118910050401c0c2405403038020964100c0004464209004000d0314481e40d50200000d020b06001c1d0314280d000225a01242145c00d0782c02145550f02c160340e1341e00901c0303100fa00c00c0e40301d8072108044d0280304c00000d01c0d4500c20001c0c0c9582c2c1d596034641d207680b0100d040d07100c1c00500d04002550301c0d4005013007641240c7da0101441c0d205a051a45610190100012075000a50700a40703c1d082ca076215400d60140c1020201c0070b80301189018580e0701e940c40100401040f0030403040072082480000d922070700456401098070b003034a030081d007484110031030391400540b8240c0c440d003003200100d2200f0f849015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 636144973 1250 636143723 636143773
    0x10302090f22060b0f030706090506071b030b1e06090c0a0c0c080d080a0b09010b0f041e1404110d0b0a05060721020105010311060c031308010e 63
    0x41080666a404550010800020107102250760384100c000080b20300c03410700c01d016a01c100c00c0490301550480a20010384d1241c00168842d90001c0c41c10006503400a00a0080d120140d40035955004203007007000d24000c2e0b480300000c40c800f04071000005c2c0100440e41a0151043d102e420601a05022001a600c58103660095001e019500401c080e00c8004000f0700c0940040e0074404030489868075000d00524441d07025081e60f40104845108190340320350000c0d8030070580d400402c00741c4059004103142c00014081d440c10074a000415070101c90780d4809560041c42c0e020320503103030300140000400c07001165205d500c40483c9014210703121417801d03000d5a10708000070042d031030038844100c0072940501801c4003c0c9810074008900800d50f81c4941005050682c00303400d1214030001504200c400041c1444841021a45884010700000c0c1c0700600149c80100101c83c12900e071041c1d005c00a0031485420443c0450240d00c503070018010b00d06421044002000006642c88100503601c4220341724060700b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 636146223 1250 636144973 636144979
    0x2010203061c030906080622060512030c0d140d0c0201091716080d0906090f0b0105090108030a080403030605040213050a06090b0706020a03060e0c030603060c1911011116110603010302 81
    0x71300501c061441001d10950003c001004943c0c082c80f01c00d04042c513252901000354035141c07940403c1c0100d081c0714419000c14903065004500e450760a09a0584645143c20300004008004485401030102c02d010fa035944c0300b014104100c52041d041003e4001c2c4111601141d41c440b200b550b49006004c054181c840c1d440c550001e941c003243e51555030880e01c1c2e000c1c003200d820503a0344203801004070758540702d6200c00700c1c42442d0f02107084980307040c03001c90024140c2c400c2d407064000d40018802500080151544009103003081046a02c1d07502d03060300581800e8010382c0e0003e10200d41031918128821106040b203c043d40d88036005a02d0b60011603421495000d198120241002008000307401980241038240f041c1c43c00040352900c49910f100c54031000d59140ca90844c0100920040340b0b03003448925004111942405e01c1d00d1880400c8140c2200d000c1c410384240900c140a6040011080d0008040c000034000800e03070383c0308032284c0e29095540002d802c1e200c0c106003c501c1c0766a4180001100c4c10b9a07002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 636147473 1250 636146223 636146237
    0x907110d0302070b270d03020403112b21020a021503070207060e03010f092001030b011e021509010f0b0604081207030210020f0405010e0405060f010c03020c1002010203061c03 77
    0x184c9000103240b4200040c00141180d041111005c0380203000c2c500d0481980e40c3d0250f44d44d861424801804514510301e94402d04504440f4007028502864003401d030510400882c0741c1030700ca420300210b103444049048060000c2c07503a561105030382c08140301190301c0c4200e40c0b002148a070000f0141c0c480c0001c640707104c0035910186042c00800e024040b1880b68000050010908192045244c02550341c203990450b424a84d0504940400c410166440b0b44240207190400000c00300e00002032407115a1088080d5403003d03c15900c074910300c240b210f01543c0405030300c44003160034041e010900810240c503030104160b00d00651449a0728001080700c00b10f40c070f03c00081020340b4280360462941da20207442101544261003086014000d1400500340c100001d14209441303d00d0500050301c2161a038404174402c600c1e0004001071941c44603140c10394514207103010032140680f450b041c1d01d880700c007460066002149842c44030403d50305400541c85103205542ca002002c20700c1200340e80082440e00000d0202c1d0103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 636148723 1250 636147473 636147481
    0x1090308060609030123060a061403040b0c12010806070210050105060f0c28060e01180b1302030a08030105120f07270f061a07020a090e0c0907110d0302070b 69
    0xc0a05443e020040000172080902c6840942e101030340841c40500d01452401c001841c50451003900051046003401c900313040070a68503658034480200024400c00081c00441d0711500e010055603030ee101e02200c4841d0701d503180d03c4e0550b6242800c0703540c080103114402d416078402906e8054035040720300140482d030509000e074440c140c55401181c00e1245510800d030500f00c030224190303440d41e603129510b8610315a8800c01d04190702541d010014844040e070428200540103010300c20f14082c0d054200030300d100b40f034440c40341c00c2890b80e01c1800040d41c18801c40d111881800070100095040320740484a20f00c5c101e501000c0305448485e042e014901c1c0340c2014000708660303503000f158143d2503210b0100001e400e0a2444040003141d400c20044001a5130f681424800031030400c2480d070303011001c0010241000791940c0003031220111405101c1101e5166803102c1e400c035000300044840103000070300280051500300300c010101a401c240f014141d10074240c480b0800d5001e4404c1380c3e2002e4226a00d0520380d030b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 636149973 1250 636148723 636148729
    0x111c06050702010207020a030309030b0f0c09010c020f0d0614060a030b0f0901060b030a020703030c020f07031b1a131a090405040312060617162c06040905070f020109030806 76
    0x103001800641595000c01c0380b80011381c0c407184184c000e9446510b4210881d41141044401a14020707d8000229506070900c030b0f82010040c00d40381e100a003440c00c0080d0105a00c0410340e8a6401502c107034102d03502c664803000f00000c2da004142e08000d003400341c0740c0130341c3c60030100820f000d0382e0700c006004001880c004c10a42c038070121815a00010440c00401c012340d90328129902a401200d001410355030108403a010580d040c02013600001c958030060000c0094891400d480c1c030214800240010352414005030004255100340f4010071a04c01882e00c41231051a1004240d840700020b40060310382c04034040361f04011009890a20001e0400c903e0514102e503041c04007c140c00341c0140c0030f02130103611761a500c90711401030702d02403c148da5030f2a080341002c130480c04150354041c01d00703032104144000010115030f1010880201004580ea202c4040454404104030356110203203072a0400c500180218959816400072405142c2e107903101a0024161282242210000034004000445100124607030785 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 636151079 1106 636149973 636149981
    0x503030d0b1e060a0c11030609030901170c0409270c1a030415050726040b0f0402030a030e0118081b06030907061209051603111c06 58
    0x40a074000a802d50003692204810811805c1065090058400608a5501014058501e6410003d502c95103c2e800003503003074007103003900c0030560f0300c0c445e0259402d10901b4001c4105042c0b50070924008094500141c0070b0031000302d118000005c8039020543d800c0c01c64811061401c42c0361402d400100c51000d04422000201e81c240108404550340d103042828071030160b1000640c50f0b0751448103071101c88800c0d0180c40c603030190072403811901610411131790040c0d00803010b901d020f07602c04050070560003040780c000f5010b8000c0341680c1e0000740076400540308008141044189103410102080c0c40d81e1855000d8005544943c90845a10300800006070203040240e8803e1715520b0084211030341c074185441403004003d18525143c404204d0343c0c0c45640e05a50080503603800741c8680300b605e8913825640c0001c0da1200b600344803800380c0f480c0004108000304190300340940c011590f87c46500040c = true := by decide +kernel

theorem cover : BRFrame.Cov 635971223 636151079 := by
  have h0 := BRFrame.cov_init 635971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 635971223 ≤ n) (h2 : n < 636151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
