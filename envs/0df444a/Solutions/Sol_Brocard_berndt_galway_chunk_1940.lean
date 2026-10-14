-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1940
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:14:03.218988+00:00
-- url     : https://prove2.me/submissions/d09b51a6-fea2-4e15-b182-1a4e50fe9825

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 348741007 ≤ n < 348920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 348742257 1250 348741007 348741013
    0x7060f050913140702100506040902090c071b150207060e130905010608030703020f0d080f07053717090307061d0d0c030e0402030c1206120f071805010302030703020111 74
    0x201c0fa511003284880c1c0c440c1a49401400c2c0d1148448051829900014801c5d0b1180c5c1c60602c50750010303560700d084a03411040d00c43da166280c0a140c58144480004010410020345031054001003003510091945060601035080e246941d5607004192084c5500d09603542c0c4c4810a001c4403900c650b0164044203070203016500108070039985207001411540208003e070b0060f00310030400416924104202140000e0070720f0311721071610b03000504210700500581801d08003c0c001504230104100f54a07030054910001007114000180390b201401801e440c0503002010a20005484503c0b280d00920a8403c120010145240110642c0d60000030f000c0508440f81281400ca031484941c00c0c20081d0900c000043c0e01d079038101105d5401e01800c030344140044148294010000c01400e040c03e2010b9805104030f8082c1464940c446030002400825042003410b1240b0074040148120440065203c00312510303000d841c8454090000c4440564909000194040d030080c81c0400055103d003c03030f0743c07c402001e02030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 348743507 1250 348742257 348742271
    0x1a100b04050f0f2209051501030503030412180f060810050112020c01060e04080a1421060102150c031503010605030c101709010b040b100e0f040207050609060907060f050913 76
    0x10880f14240706151901405c2d503a200700c4040107002c0003124600901142d900841c0e6240d565a595284001800106050100b160540c0c0403401200c1748400301d034805040d04441038513100012080c05040c8612400100c2c402d011a0940c01c0c0940e0070015a00b043e9602c1d0000c01c21055104080e42c010200150690f50300c400c002072003420301090318001c520800403641e40d95062000208070643e001000c5513546d808010350782c1d00855509403100900d42030404286140d440300d00613800c1c0050000d1440074904001d04001501c042e810045125000c1000035480154001c81414200c42d070074043c075a01a848100f00e1030581c40c000e4402004d0341064a043e01505101c0407403008071050907902651580c5d120b1036a0217080c074160107400205c0505842c000c40b18001201c006180841e03800313085014011842e000c0301c160f10355404488006070088110303180c40c00c050f450565203040460301201e2502441d000450308038440c0441d603003400690b81c0c845050910030f0007001104170005840442440d92449 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 348744757 1250 348743507 348743539
    0x12020c03030c0d02070e3921090c0105030c0f040302101106010902030c030609040302101410060903080a0807030204090c0c062403080c03071a100b04050f0f 69
    0x2d0102d00000d4010b4400403640324406403512403941c2103890b180b2024020842448039030100070081900742101d101021003020005090701014030065100e11400040c0f00c0c00e401100100c000c4416589458030582da60f070040016118400802c0090015008001042c20340107542c018000800b0054203d0346001c0d965400140e4030b02d24510040046444202080e40c0703e00c090050303500404001005502c0c500e03100d0000c0205100080915100c0c4e004d0f58042810b040c801c03c2800781100c0e0441d002c2000a4000005440e10072007216441015981480040b920034801c0400c03100712a4801d421314100654a802540c40c890001c050754101f5600340710000d00c984d101c0c0140c041c1d292680d11440e401c83c9843c200082034030003102000c40050a08685040e080014180c2e1f0011a0f4028180545800140340d4a0b070a6106200d000b4080300d407480c00030b204d101807103c0c5060095030f00a010f020041e41e5428045454012481040d60003044911303020841c0c200340703d54440c01c220080031075060301e907040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 348746007 1250 348744757 348744763
    0x1121a07021b040e03030415050c040f0e04030e06031311060a09050d0f05030307030c02010f0b03070909140a030e100f02060415090c090c03060506090a0303030e030f03160f11070312020c03 83
    0xe1b000d0b00c2006c0e503100c0345804040184110ac0e04201d1035a842890316040001d410a00304492023000d502d200348000003400c0c94401c0003106d8100c58010b00b01540d03410038600308980d504207900240d40305400c1d290003443e1440e00790101d074031090003902c403842403514150400105e0b034403640d02520381040c3d070b0f10340c0d10004000340b009521a2105403000103980b1803108000b421035214020703d58525150407001c60196400003100b50031101c107480042040c0a4038648401c0d04c501d0700c482d4200764400c041c1c858040507044003d000e0200b405542d1100c0e4078203e9601102c5110845040c0b00168003d80045400720f142c0300c500d802100c10001001c145460155a405082c102ca50300171607609948a10114020f44c0c54080c00e0014041201c0103420000001c3c00902042ca061000405060750342d40300c458500d0307081c0151120800ba031050181c5a1030711a1718005502c82c0d048070240043c01c00c54541003014010400d8003000c1c461f502c000c000749804c40ea104c031989888184440258032800d00380b01c14980d0f0030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 348747257 1250 348746007 348746011
    0x71d0415020a02010f06050d0b010e31050d051305041d06310302030f0304060b0a030b071407031d04020c010c05120901050c1c0902040501121a07021b040e0303 70
    0x43d030300002e03094500c00003900803030751a13401c22403143d2351003907411011450b00a81d0905440310071043c030209480b03003410000c40706c1888006220034090f50b2901e070042062402e03031190040c0140b0580303500031084c0d501103a45110f514003080940c0c200710410301c018140350f4011402100620802c9080b03500d0441950320b4640304559890340d82c44480922a00040c0451840c0802028660915800c0031259000303034030307400b44007285003540360301000107414031400381c00c01d64810b640a84852181600c0b814821000c0350304a0301030000ca81240c000c0c0c440c8425203c122081d04c3d80554941891100403c0c1281040c40120072050740a81c0901015012100030320400b08007441e541c880380c1d03942c08121494800d40400400d80002e81e4034000401010761030100c102c6810304141551200521494001c8400030400d2141c042e400c10300d40000414142c0260790341115590080d40803d00d084025136010036144402c840300c80058000c40c402c0000c0c1182c0443c05502040b00071310100d07503002048007040c034640003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 348748507 1250 348747257 348747277
    0x271106040e090a11010216120c0b0703020303070801080c0d03030f0905010e0706030b2707030615080403032004140d050102030a02070b070c020d080d14070e030708071d041502 77
    0x4035003414010498201030b01c15130b0b40700a0001c0c00c0c66503400203448507540f070b05104104940c105c07600824104000301e0003180103041c4000180e038507001e01d410b0095807500f0445200000c10031250000c141c81d44009040075030040010454000d4825540d411405484108a4210b201e038a0303081c0341000440078000c0354015481c100040c81e01c18a003810003019201e80c5c203007040c090501c070120b040e01044540501c24103e5801c410b000c10075120039100314010700056000c805620000e0850300300a543c0000e000b405075000750750500044400500c0d081440c0c5882c28200c03580c1c00c08110070030411240b00a050b10300c210042400c403e44d90151507140c2a42e204450003249a98005030342c204024611086641100e202c0c58000c104040f65804914081071941000d070520704c0101e50311101c0d45668110303101003500220390180b142030515001d4070020300849014030a005600c8042190351001923040201c030b084024640701c990505607590016070f8050f009460200a4041041c11071368940000e2610f122 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 348749757 1250 348748507 348748513
    0x2010b1011010b01050c06131502030a140a02120f06011b0b040201080907061d0609031605041b021f0902090708010e010e070215180a06060306271106040e09 69
    0x3894009900b102e00c3d1088150602c030081c4071918900e04c00083c65984401e8241200405054a0810100e8551552912024980004200040007105820070800c80300c00b00070f8000140ca9130040e0700145e014a103130b00540403e00c60000341daa0007505126681003030044c10069504410f064004030300c2034282400b80c030000c2a40041c0710031564046121940014a4000380803001e041484c02024080d02136803022240303020700c9e8048155540c40d400c980d01e91a0080c210354014070601c00c1115141101c0c8503c610a500d4495062240704080c52031242e4004103078050603a0406803405500c44c0c86080b800824180d40d43d420000c01601c40b100202d01445030750700c0b42141c941c9000f51007110600b050700300417442258035060000d4203400254941880300317071f10f01c041800c0e6070710600c2216a040041e40e40c0e100e88a120425820722405600417401d4034018201800800d20410780c0412401080200c800071182d50320303441e00450541030080c10000c40040c8082e280507070342c0c945104000030580302825650 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 348751007 1250 348749757 348749777
    0x80906040915050303070f08030a1b020109060f05070e0603090111041806080715052b020705010b090c040501050d0f0911030c010207060818030705030a0f091403060705090102010b10 80
    0x42d420261400060400300c00551801c101c1c1d58612204903405207008180020104c041003541d0f0242c1c00c80b00800314038000703020050305c05007c000c1c082e043c0300e1810b490180c500041082400c15600030b20f4130820144d203d010700300e6030003000e01009500c02410700c0400d560b60171210500310300c401c0040000301a5801c3e11a181d030703000402c001c01c6070b403568440503082c1c0c0b00400800c1030b40449242c4606413a01409d060307031039200740b2070b800480c1c85c0000000c00e0141c0c42205030315814442a40500421070044000b009040c40382c81c02c2c807400c98000d03207817000e400b9800c2c00200300b079600c03a000900090070b4441020414100820000d42911000141200c034281541041a15401c007041040c0714050244014144030b0b261000c05001114040e00041c1410003021964110032010400c480240d40c0c040c044a40d00c500000c8c00400d5072031004103090028040d15800101083c40b40d2011b418144000c0c003a04560721000001c1e18150700c00100315065540340c1e108ae04c50703a900c034104401207000c0340d240d10703c240b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 348752257 1250 348751007 348751031
    0x30905120a122c06070e010f0c02030f071701020f031308041a0703081e161b11090f1905040c0302031603031407110411090a0306140c03160c0809060409 67
    0x141c00c0a103d41e00d11984260100242c165001c0301c410043d00c0203090000c0c288600043c211105448008040e4052080d0480724201d10030008106003140c8500700115454800c600c025420303442603002201503000c060011803040d856003400d40c0036151103800e0461429607104c446603030710303102c0d070440440543e07020036488180f68014008984c048012800c40b80c4d840b1600b400210844c10241c00310210301c005480c81200c050140d403071070340c0c00251034000d0f10280d40c992401c903841c091191002c6011302c12070800700351402102c1ca0030340e003c0c2d44607000041c401d00d0b81100101c020080104155036100d101031000025031001d0000049011840c21640b80540c114140504010844500840307840b00420840c00840c0e54504000d003a001304403000301c0e201c0c48001c40103680e4050f00748019817091481c50000104502d40e07016900980e01c0911540f12640c8211841e4544e000803500506800714801a00c1009445024010350030b505c1641d505051007010f00201741d5603001600080d4205903101e01468035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 348753507 1250 348752257 348752321
    0x20306060108040209040f05010e0102040e01050a14090a0f09020406061835012703030c09061407021305160e030a0203120a02030f190807030905120a12 67
    0x3101000303007000c0c07445050039404030f00d44000003480940030f4141c0c949103004200c0290405d46100701010020364035140c0710001840011000e104c4c0d41e110f0411800d00045020340c031020089031100040c4243d0850f80c603a400c00300500aa0322103895025518039400006a0780d03445001c0c00f42c12290784082441810038482440c01110b0b40210306112201400c41e9004103200c5070791800c90f0760b4100381e45204802889500c1c0504643ca50309003805000044005480c0525170320646554040da80c02e01c200e0000c5501520300c8203013030140600103a102003180c00030891010041c079165102030440250341100d401c03917108440e016280d0740340c01210041e0102125501044500e46104224054016444d0320b50003e9500d2044258901c2c12100100308920b1640c0207109480e5248244c0c0c1d0704582d140340076850703481c080d4001098680480d1116000c28082c911030b100303c2c06540e511070f000304070401000034400c0190700243c1d058010030990458425551103180540f415600b0304005205a155156440c1d080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 348754757 1250 348753507 348753511
    0x90f0604051005130209180c030601080c0406021b03030c060408180603361903120207030c080313061d01050c030f010509061c1209140f1009031b03020306 68
    0xd4003450b00704144029514a03803418250703d800000180d40303c48140200d54420360b00000240840000e40800607003640d2880114460b40c002d0b81c0724100c0307076600c11a081d42405540113420042c1e10582c40c00b10780c40c00e820510400c08100400301c80c10418003428083c40c01c10700b110115030a58002ca6840400e40c02e030081406a80002c03a05a401c5d03140001260080042050416403090700c1182103010340327400d04454078181180c800982c0d6000816500c2d0001c680701906044000500000603049584000e1080e07419081e0b15594106401090340c65001803608003400310041e95107031031a01d4000441c24440d00c2541c4801141c4240200d001707114480c21144000c00c4030000800420800c100010040521415107104984c06140ca40307640d4045015a6061000c0c0420300030b242e001c2c0402d0217a135141075080e9854070f5880c040100d41342d848500c0314240000c01250800000030710400740d85044000207075000817901d4041070080e546c0d1181040103003020380c10b2007a50075210090040d03090030b122090b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 348756007 1250 348754757 348754771
    0x190606030c050f0f0c0708030310050a030308130c0504020412050d090e0f1b030405010f0606110318041104031a060a05130203090a080406170615031303030902090f060405 75
    0x70410040d0054414440c60350800103080d800142c1e02d007110000030a1716002c80b0040120742030340303407900f0320307141d4075441924500d40700c01040c03c1c001014902843c0e09016a07905540d40d00d0180c8030501a0010686511000c0311551074071743c07020032591118400703040280f075041d507803480c001443d0600702c0c20803e040c980801005010350342808424001060150480c03110032250f4a1542d9494042e4200c020460f40740c01d101c54008140400c0c000e05404c00512000c40c0354080054590300c0c0380c2030315800d0360003030f22100942044c800b80c0150341d0350301044002e115000c0c0020a0000c2d9100203041190710540084404001c40d201c0503132090742e50480701d940941c0603206000c04509050028010f8801aa40e40b0880c54001000a16050041c002201059480414651240d07250740300540312014240b41c0405555031a00003c00d586000c10b00150541d150208692660711a403103052007070708442c68107909050f01c4040e03890060700c0307030180ba46c0301c0c0321100400c40950a0213000c100594030040c040e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 348757257 1250 348756007 348756011
    0x309150a020303011512020d1407080105031f0e0d26040203100b0112051515131205150a0b0901050103021c020a09050301060b19020f120a110619060603 67
    0x300c20541d00082120305450304c1c114504540c100d8983c044500002c40c0089500b09800420500d05c0130b803154000d6001840085228541682d40607801c403500d040902c00c590f456030001c2e94881c00c0c1e948040e10902c0c3c7d01d124810210715945480c1c106890f10350004072060000e00e40307039100b201207001500800703d1684001c0b06036a6608003500025a03907108503090070f110f00d07990762149985a015940c404084441884103018602d00034965180080820030094000c0c511005084103841c032841c11640d55800c07450f00382a02c1410b02c24141360040001c60202e402d4482d8080307440b40c1c020b40d005000e1103406005004a51150b0706c1003442040101a4000b0381030500600c4100d0300014160601c010180e0440d10040c3c43e003803188004c54060219038017045d0154a42040407402012700307401000252503030b0700c2400110b00302d40000c0ba0366511040b0141c5681e00010342c044c0402d00100020000c482c400e00e401e00c181c01503c411a400e0400a466010108464044d9003151440b04d014880c002c0843d0b00b82 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 348758507 1250 348757257 348757267
    0x10804030804031206080a0c03110105130308090111030c0105150904030c171308010905281709120c0a0501050a271a04060e0d0201140715050702030915 67
    0x54580711000d0401410320414401954441a8580c0680000d2140004840030500e02e41015500c100ca00d000503101080360100882465002d44111460000159404c01059156440e400440e8001003561410882101040400e004042000d401c20701c0491000041c541071180c01c80107201c003c001d107280540d00110030000804e03040880d990005801c1035040e002201c250310801060b106410400c580c05003824008144864154840680184a8806c450045c1d600078900ea03402210700c0e411326021022000344200060958003181108501032144508000103800012201d40f081100080f00da4040c0055100ca4a0240c24050045c5000e0034214500001910300411f9140120401d55407101d551101620b500301c03840080e401070461881e0346d80003151052100c107481d80544620400101c540c41da4103402d103020907415843c0d690503114204141c01c002002c001d103810452003500c0191800441c082f11130000c0c020907200d0102b503406140c0c1e9007100000c000c00b1404620074005800313001c2c80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 348759757 1250 348758507 348758513
    0xf081309051b030a060312090305160506090d06090204061d1311101101111b070501050901030f1d010203060102010e0114010e0c041a0711030d0f08090726010b010804 73
    0x10000e00c22035030078425a41d682e0300c014008014040c5d651009081d0b03d03001c0c9201c04101d5000f48004162031207030b03041e02c5088500107010f41000440c2c1c01640e5001c80304000c100c045140450003040c3d0648240c1c0701140c88035081d0000350484400344c0c03107560701e05a550020401d994118542a5202c404149103850604c2d081d2960502e810724070745468061903036621400522406408040c0045600000070f0044801d11080c84803e6007003c000c66002203100d0801605c800b80c0820048103035441a513486041656900045001c0e1840b56480c0600d5a80d80300d04004109440040d0305071146404000360f45c2e0704011000a08580d802481281c06902d4448480601e89080c144981160f0940403810840e484a1003030114501c680d038003e02c4220074200034030750600409006406418080d0800240b91003400c0249502c42e41d10b809050001522000e0862082d40695003040e00203502c0e00031600c605d40c860898200884601d1700c1800e40b01e1600d03040001341c410034000c000151000f0b04c4c000e031880c102a5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 348761007 1250 348759757 348759781
    0x4090506100e040b0f15040623071113020703020609070f0302030309060903010e100e060f07080703090c1a120a02130605031e041a100605090f0d0f08130905 69
    0x10030103d20540d264180c41c9842d907030f110365070810050010003040c03d1006607910b1140c2c6034014441c5002059001c1c98001180002c02041390008070a480e403285000380700da4404088500480d44180d10802c06206081030441c10320140007402d21a4000341982e003841c03001c06181c00ba0a90008031000c007484414801030301c0c040191052801c0c141d40c00c07901d498000002034054014881c0c0580d06205104500e04980c20a40100c1d5040100d1410340300580c81d610040804d07203008603624400b0614200c041f50481e84a5403095551030700a994403080c00f81c0380c80300d5000c0d00316401c05c0c24000c1140412514014840303011102e8001040074411450141549000b2208007003610880f010305c140030000800c0003c2ea02c022030f0b00840e03400c6c0c003035040c2e2807d40b6000e00d2b40c800c080c079403031002200c0100280300c64140d6121003090f50a9910784ca030034022000100031000b070001c0301c03244d0844e4911760014002240b05904401e090302c1611a07a4032142d200083c090001d81d241d000c02030180c2071500707104000d83c0744 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 348762257 1250 348761007 348761027
    0x7061a0114180603090604110d030509010c0c080709020a02070807120209040804050d0f061d120a1205090604052104060e120d02030918010305070521010e01020409050610 75
    0x1400106864100b00000002d00070345010201c2c1d0025000400c014400340c001c9845071080c1d00c01e0350343c100081d10b10380901c042c00c000c501d0003d011400411024503190302502920110501c41d54290a00741c1e142d01c400c90038820b00d948040289a00421541115078042c01803002500e20400149850341c90131822540910141301c1c041c0c01100141f01040c18004040c0481f40541000752621028450624000000c040010f07003d03148549410b106501c8441812040402644450010a00a046001e0040141e40301307a41020074000a16922580c90026004181c810300c1c2170780140401740340505210341008032207101c807803250428500705103003040345400365000d55420703280540310100b0620200d180340c400c1d084c0340d104500c80c104484851a90000042c849400141c41004040c00398070591082003d00307000003840f54010010600490802c035a07141501c1e2145030080150b003484c00100340c219440b4804001590750006811b00881c0407e02620b0f42024082da22083c0a02036248c00414850003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 348763507 1250 348762257 348762287
    0x4030b06060f0f0915090a17010f0504050705100807120f02072001140f0717040e10090515100c031e03061406040b070b2203020307061a01 61
    0x2000c1a9107403111010b5414114110b510280e42d50141414409543c010b050607510521002c0311640003a40c084043d5142404003402c5130040c10f0078a11401c2100008494440c0d5541d610041c0c8031202c0d40701c1c001d850003180a0f102800d5a0340c2024188500392804448450601c808501400716069200d40d04109404100c00002030881c5900819006449001000340180c80006400ea100f80500d0b40000c0302107900362070341556501010031540b024051207007582d01d080810b1200c60046500300f041e1044030080b400b4000d2803e903d8603c421035841c4144d9010884a2818200703022411182c0b040caa040000b82c218402014202000200540207400801041081c0c03c01c00c80105801018035100400e155802d124a001d00c103070000300100518402d030b6409900846d8101d40c242864070880b8140c52580c440d89181507104c0c0c43c1c01000c0c0d10f01602905161200f0b41200800050369103003c04414440d5001e541d45040d581000b0054a810301d8039030f80f401106101c0304840faa001042a440d03020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 348764757 1250 348763507 348763523
    0x504060315090e060a0b030f0709090606050414040303111206060d062303160e01030b040f020306010b2206020705151905091002070608150d060e030c0d140403 70
    0x282035641445501030030b074400c003601410a41e60034146803021507003901c240b641c07880400107091810308159a030b400e002c0182000d0b8210910501c4030740f81c1c50700091055030180001140706681c46011900700c1ea43c0e041c20004c0101804240820103038540a10303500c01030924401e60a001c180a0b4000d040100582214850b00001485542c0d070b90740d40e00010b0080803101c03c405520840d07030304880d00b12007801d544d00d807103405091124403200143c4031f82c1400f61001e9407201107051b0709607911202140c0f40903100f500c1c00d0250705280ca0043e602080f205002e81142101c0d903032a04250410841e84000443c4200c078441d6106801b030004507400240344044401c110f50341e01c0100d000c10402081e038801c02e00c1210b203100a40c110407138582d40040081507a03000c1a1204a00071618a400700d072948154041e00c4000360a240205149513640d0308101149a4010811004822581c0d24581244c03000f454000342c0da08081f424002c901000d001e403244050741814980c1024180b0807080c406441103000060902c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 348766007 1250 348764757 348764771
    0xd02070e10080c04090204091202010e070e0c1b03071e03030e01021903020307030e060f04020108071d1003060b03150f060a0c080c0a0f05060916032402090a0b0301141005040603 78
    0x2540b01c8d000200180d4105041000d94104081c1c002e0280805607400d541500c200c160001c1c42030700381ca081920481d42c8007002d030705102404040010b1b442180c40d809002e03120904c08040428003061b070750300f0800c00c10340384600c0241d8145405400d0b1000c090040920781d106014501b59005d841c40048044401460b0050380d9035200300b0700313900804414996000c18403400341013003090200c1e02d20250055000340c071000916556607004550380c80304000726080c204441c2c01619154106880d80b01c2003501c05050200e01d094441c0091000f6030005c0f146c400e107500c04514080b0700c505002d00001c11401041d15001d103040c0607440d000e02075542e1158002c4c61902d0002d50b61319046001c1c08640c00040c1d02060040c0d2044c01418070301e64a0303600380ca12100350b001d10700d001d82c80d810a404d014411681d11001c1c16071100c461025400c6e147ca0a00005100070f6000c20074102d6540d11500d40101614468007083d4495042c099200f814036120340f080f41c0aa658036602804598220050728222011450081500c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 348767257 1250 348766007 348766009
    0x33090705100f020a032d1d27070302190f0e0604080705061e040b07030e03011406040f0b04020301090204170d230d141816150905030d02070e10080c040902 68
    0x700d006d204401a0000c1420b4904280c66404420030042501c040c0301c3c14241030341036040140300141c00071009013100400e40c50300305201c40d42c0e005940c40b0303a66003001428514180005461100b8410540001503c040b00c4244000e40000148807503000c141e403590304040c200b520103503070740884d800f41504c211000300703001c6d03e01c400450300325165080b06100c2036141d40d522105a0160380040c4030440208004040244040c20144910001c0001390194100a0f40300c0400388401001c0c40c0e102c603406152031b0b5050140c5d94035580001c50091a003401c0050755645880c0710260800e0340400d011039290000152501c00c5c9501501e04100c02c03110020408041d10341132940010745c0f1030031a81c820910705103440400340f941c1054a040c42146001c1395000719064000c15291102803141071104040b83c5280180101c0e400c0c1140c450005206041001c2c010f40c4034000640781200c506a8000140d00018050215a10305086d154000c10703d40740b814080c504000e40c65450781501c8000c5405641c0d6042042c0039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 348768507 1250 348767257 348767297
    0x110a030f020d02070b0f011e0303050a301109030309040e0a060f06030c05012606030a0507091a0307121b0306050a200a0233090705100f020a03 63
    0x2d0b0b441202e030119030398101850720300c2842600700c41350301d5219848800050543c2c1d601031807141d080110510100c2d503500b91740c1c003600d45410001a05c0c04004654245152a030004811070001c034010303042ca0094070126400d0b002c196080269455040304c03061141c41030b903803000819070f006e241044502151540b040b4145a141807081d11000c1c0c009401e190f20005441d10769032000c800d4078000d03132803030f120780e03072201c0c01507544040c1d803169400703038249040d0494402155070080c2901301354002c0603124900e14a4035402c2c5006401e42100844690ba50040c0368125018006240c10b20030507400b80c041d162a102c03820300b00f015842005801d00300c0c0f81d02c2c2105030303e844d01c0000c006554084000c115030b0401a450400429480050410300800d161840b000c50311507005803000403040e6070050202c00f2240c0001c03540d000341ca0041c1c0f001c852030f8058440c084008400075078440c6000c2002070090750320300400c010320802501010780074410300c020300e20320711607000c030b06491100e0b05407c16240780901c00350150a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 348769757 1250 348768507 348768517
    0xa020102150a1b050307020c090115030902040b0409110405060f01140a0314011502010f0b0607080706060302030322050d020a060f110304060909320c19031e110a030f02 74
    0x2041c0d12450f8140241640c120020f503000e1071443d421103102141c210207208014000b8058250703100d0142c943d14180ca4806e070845445a48054404280381c0f0104000c681078821042080f200e04180e080e07400928101441425070044040f0f800344012100e400028042025680c140bc414440005050030102d0081d00080d092000200000c1c2d9039696074180800300441e0414200011f50902d05010300c10314550050303000b01540204002d00d08601075503084804e502003a01200c0c8951210300000150390140050a015464842080d8517a207142c510310903400c5041e08154490b400c8010140c02686480c0107400660713405007000c1c2183c5c900d408082c2c4048200301c010355180e00c40014089413541d8420b801341d040310a6440c05101c4048207804c0c80a001500b401c40743c107942403c403038035001840c00240e01d03508080d41424051a11442ea48012102d685500b41c0c1c00100e0740f00e4405038210810341d00300344484220410200004d090b411443c0b110380c071403203030420b04041c1c80d14194002c0904682c1115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 348771007 1250 348769757 348769781
    0x90b13020906160305090a030b061201050114010e0a030c0e0402100c0b04020616230c010507110919110306100f0e0f03030c060f16021c120b0405070915020a020102150a 74
    0xd92401e9072303403800842c24901203446500030040b0201140d5001d005014180c140d5070240b403a022031100c0d04e40115a080500c00344c2640c400000c400c00408100c003009045c000d00014290000c40385018014020244250410b01080211090308030011844110416810580c1110b04942d2010ba0b02c03450030b031035a40c81201600c1c48190001e510090f521030041e400f204462030701a82e41c0d11107003c0c01568240aa85005455142c403a6212500340c0f411a0a02e584402444000c0c5400010002500115500c1c0b04010503028000014403407289810844103460f02e40038a0080e19040000c1401000881c1600c40d11340034050950000400380d9080c001c4d61101e05440048900902d481111948a050155400100143c2c0000345801e810300c082100c80c3c0b80c1d0b40c8041c0000c00341101c20011210700c80304c00c480301c49142d0355601c0803085956a01030a4080d401c25910328100300d052840c0520355610084002c0d0566110b105a0310050760041004030780c0880100540303c882da11a8401005851151000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 348772257 1250 348771007 348771019
    0x2070506070f02060a060506041802040b0c070e0c0a051e09100201090204050c03011a03060a0b0403061407110a030806030313080d180b03060f01031401090b1302090616030509 77
    0x88682c0a0311050118039258221411500d94040502c00c45506000b902d400c42e1040106001036000105445105000c1403001407400707a0f9004410429008800105241e07005410f0422615154402940c3c10189104520b440e01d000d10002130520f124007580d030454901c1d0707611101d550b03958400c103030f40e285500901440300508049400a00a0a030b6003c200e119619120108690f103651405483c10780f041402c2d02c1c46440e03907842d81011640c00c020100c9521110b00c01010a51964500c0600000d501c0f0350004105698107400c44c2c0c0034500d00030107040400c164604400f28412002076810401c940500f0505400d4445070042804c610075078640d00c0312003824410010710030000141d801c7d10168a56102e00802c0507540899040f13210510804101c01800d2010407500e240004110040a10504000418101403036146040403000d82c08118260313580e8000700e2107800d00510b802c03619020103404516000d500d50020f1601e00604d0f44801a4100003102c010425006808031f4600034001400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 348773507 1250 348772257 348772261
    0x190606081812210f060d140106030f140613020a12050c06180117090a061116241e020708040e010308070311010504050a0311010f061e0e070f030b0402070506 69
    0x410f803011144880411860b040c0c01c000501c01101c40e002c1035000f0b8800429542c110190741d10f80d0108080a01d04044039951384800000010354140703002e549161107a0b16200d07450a43d422070b1810310794010002804848504950300042c0e40700040381080e210741c040d48108a044508203d0b24041d00a825523400c40c20028200003120104500801800004d07a03400031203e050145603030040c60152001d41d5130b0380c0903c410302c0006543d504110003405060183c941011243c800002200040e4a400d59440f1a20340520404100d01c8000400c1c00381e50304428402204005580d0148612244208084540c08a1405c0800c45000100d400501034802c02410550f141d0600c00d5190380024011000700b0340c00700d281c0811580c18050584a140c200c0007030312102e0083d8500380c2d0b10400c15030814071075541c0c0d030301d1101040240b40300302e0f400303032202c921030010041c000c800440d141c600603004110003604038000c106146078829500da905076500c1c90701149200301d280c01304000e8011048018024018030003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 348774757 1250 348773507 348773527
    0x11d06030a14010f030b040f06020909040b010501180303140306010e06041707090b030a02040b04110a020a050d09080304060c030905060304151407121d010e06190606081812 76
    0x104020b4000c0d00d44000031907903600c2d080320016030b496103c014004201c0f0700001380403030383c88500181141d0064501514242c86074001070703144402100c08a4030526a030b00103000329640200000070b03d10100850060300c90441d100a0401c031050402d6903d24100000010302c0f03a48101c0c81c000d6807500143c0356544031502c84101c4078201c804865007011500c030b0401c00141e00e80b02030290710301a42000c0c2c05040110f20903001c1c0400303422251000c0d500140c0740e150f071040c0708006900a00e0380c5126a400341441864500d041418080030792503010800c07122281c01c2c07124440100440c0d04441c502c2c200034484608a14061380c542025601070b6038003520201c1040181303d109604031144012440341004144505079505484075816510200082d61558400e00c115555600c159001c08944140307540e040f00e240e00d21800e483d0306103000002c032341008044c0100d044600c6040c4c100792448003402c0c0100e50070044003c0032004d00819450340c14035824642000d502c424030941085020b081d000f541ea482c001d807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 348776007 1250 348774757 348774761
    0x40e0c06030c0a03181e02030a0209090109030905030a02060a23040f18110a030207020d02150a020f240402040f1b11010b060703080c0f0403110a05120a02011d06030a 73
    0x283d0b01c000841e09140380740400215409100600300c0d13108486c200300c49038198603141c2422488104982512a450040c00540d5034403a0300341c402c6040e83c0002c281c64485140044c04400c05a2115009074031800d13482006030340d60700a4540d024001d10740040b55000649011944c0c0054120b181151030307000402260072a071000114007501d0030703940403684104098021000f00d8007402210701445000303104040c800b912035002000407038001016100207208039000243c00d01403400313800c00e021100061100f600c540510801c418080f031040a40040064840d400b84217800c0803400611840301800020308540d190f9020064890160400304140c0c002d00b03125803544419083d40340c001c243e030340380602c049102c140a850a40701c1e024011300c0c100b09007580d095400343c501828405042e2000d22007128018444406000158010090151115440700030301003ca0794942056004408410084074400e50010750201007a81c2840c00032800e00c854600032807042060241294054000000c2c401211001d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 348777257 1250 348776007 348776017
    0xb03010515400b03071202180307080f0127030f0c15050414030c0312040201021e07030b010e01080303040f050304120b010305121204172109010c0509010e040e0c06030c 74
    0x100e1007071036200761100f101c02160b01007200c1040000741c171010680c4c609203580e000f0300030f880f51040c030f80c03490108800c0000782007010b02d4001142c00e5200307500c1001c1c880780034001e4902100700d207042100301c1c0820203580c04142454031409020710540842441e0100c0c49410150440d98004a081000034021324445002c8d28060b9025a124209100c14410304100801180c948000c92001507240c050704402001040c1c2d00203000386d0540c09407287c5101091541083c5010010180e8041e141c50b60551400002010068010429100f442c1005000500c800411642c12641041000c2004111840c0c260303d14412a080703a419181150030b25030402149042c841d068900c10700a40b42e40000c41c4240880c1c9028410803800000a9135002c580403901074a1100e8108034045c0c0722a24001c0001a03140c0701b24140140da295181d44c1008001000b80300384111100b040851408a2600c00f280000a0602e4003428055200755070f65200080451010000121108e4019005035280c3c03404994504543c2c101d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 348778507 1250 348777257 348777367
    0x110702090a0510031b050607150f0b0f010e041d0d020f0610060f091a031806010305120d020403060c050a180501050a0305071709070503070b03010515 66
    0x11400825140354032800341c0b41c0f24505002103d1442440c64552a829402410007a00c0c003ca0314400400c0a44130a0014000f46000b404c6000d40120000207640480d811034944544030f83c644201203c3c1540d45d0701c2d200c00080b60918010b4a1b06840c040000d00411441102c01d80c1100c142d044041d01103404141d0f002503c40c5c5400b40c0318040f201d14401a03c03244101c45050070303001603000c01d1106502a44000c0d4802080f0315107a207620340c4902007140040340d80c409034291805c000c0300300b2400000700b01c0d008001201c0d4078090142135242d035031080d030355046408144010071070114007185181031550669000350380103001441400131004000d01aa40485000000107600d200c410301080c2c103400e0404103c85042c0c0d203682c9403540135001100144000f0b02082d08020030140c10784c01140e80407001e0b90162080d4030151800c1840c0c04201450402154001c0030300003010700040149a8507050b02c44002901ba042c040e98802d901d01280d52080b01030301110104624011749580f01416502d00704103079000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 348779757 1250 348778507 348778519
    0x109060c0f03051603090318080c100f090e060301020d050c0d29040b060c1c180b090d050708060106030501030b0a0b030316110a0b12070f120c020709110702 69
    0x750454228203070740088601c42d0f4601e80034101442581e110744c2c0120364070350281c506241c002e160541150441e1706558881210b036484840700d031000d444d02c0300e03612b09504070504164204020b00301c0b001e08100701c0ca200d01144842e00e1000241240c40031340440d43c10700c072420b00400803842c0903900720318560401d02c404038000c0d140800f1111420525001c4900c1c2c01c502c9000d80b811400d44034200130150404c01034298002400303100c2c5440303440301005440c18004000e000d203101504201d00042c9255030441607038030a000c00007820016428120304960a940042e9003c3c1c200f000103007001c0d464a441d0703600c55082481100700000e05241d0607400703a4180c03803040c5496030071500c0710715180058035031029030035074590400c001c0005802030350303c0c0d400041441100040380c820a900700113402070f8802e0707024821302540025a01c40c0541c0d5901402d610042c54140844c0e0707a25180380041218804070700320f54000703695440c000c006500800c401d400904072010180f150075004c080d2030b074154102d4131089019176 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 348781007 1250 348779757 348779777
    0x4090e0601080c010302210a060302040f0f0507020601051c0c150206040309080105010b0a1d09070507030201200306060304110a031101031401051f090e10170d1d030f0109060c 77
    0x145c842d000b19440300c080c01c80740f8594030101900f05a80400058040c5c540e40f5505c020000c016111405001d00000f140c082c00104008904400e0b420b9a800408a0702190006801405183d41700b03c4a00d07a44c1e1880c140c041c0300c801092522100d404001d41000905000907020a03040d203a00160044c071a92090b903a007071406a5500f041800d82f04207011b42d5610a806214050005220780d50044c44d28410940b0801022000b60119041910a68103180003c5e4002484014983c090040410045843d00c45820013545200d08203040d00001d8200c070310904000001c102070041d0801080c0030428002c06c0800710039270300e15280c0005072800c0c58113804a030800c03a01c54201c00683d00064101c440c0641402000c2108119001800c043e09615030b09000c0300c8407001c42d0150680421134410b21b070354142c134000c060070000071518100080401e41641d9028440c1c05094503440a203d080c3c1c00c8441c0d03c10448aa01c160009042000c0f101c0d20007010b42ca020260000d001c00b44d04008810030450310340401c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 348782257 1250 348781007 348781009
    0x1a040c090903050f0904020d050a0b010e22090c0911041d090d030b060c030d0b181b07060b030a060c030b060a05180402040e130215030f13050304090e0601080c 70
    0x40c891010740500421418403000700c03c041c46000610f8200d030020801864040c28150142c22035000350307011086d01c0d680b05013052441d60000f140d4216010304880020340c41c550040c4c81208920706418824203203485003400000c1080300b015940103010010401d0190b4040811565500e0b0040c0c816283c0840103002a42400c86041f44058040c40400b0090710700c00c080c03a04180c0282c4250140140c11950400881510010030700182c21980000d4201042100d2a0301c200b0113080100008022000324000a208100140f0b003000b0100b0b019181002d40c48006c14100f8100404007001480e806d409403a80300000c100ac60391040980840544081014404100c02e11007207011301d95000001c203000b0005c40303261000e4481070114088004002505c1c09440e071240c480200700a0342c02119085049030800214500a807000002d13400a501c6241036240043c0300c0e1208041c05481554204582d415000030b103d024001c5601402109005000d1003c5525940d03a5900c400d1207540c020740125202d004403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 348783507 1250 348782257 348782261
    0x4050a020102190f0b040c08120c0d32190503070f081501031a0a23032103060d1209050a120b04120e041a090714030c090303071a040c09 60
    0x10064000080c0710b003c1c0b00698a130b24003800301520a480025a0087c00036444200704039000c08030207101c0650340c81c1c000000c6068900381c1a2441306040c0180301c00c0013030211445605400044000c255500d5280c000c0e00c07444480341c415501550048449000d558030f40c55040300042d401200195078560f2801c000c10412508010300359032021055240c038003151090742c40717500301020112100c1e5030041d00540810000d12255141da0024280a003400300302c0070204400d900405c0c200800341d0103848900107549007210350034890660a000c903103012001c00c02030b0300c80710755800074161f00020f1a2004a01840081c009074000d00c103e602c580514200402c1c1e504110001c69a00c0e94050451444e40d226a581d0b40a1441c00b01c4034581044502600c2d20303610b03581d9005042c0d03078029580d0408608006041482000c810080202c001d000d080311038161601e490360226584555503401c0c403a1508803400001e0304500c918107000d44483c94600301041040080b512040c02144107592000081c5d0391030341c82c001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 348784757 1250 348783507 348783553
    0x3030405120a0e060703050a20121c05010303170a06150507050f0106030c0911160602073003060905100302040c030618060f0501140306040b0a030506070f091d1f0b0304050a020102 79
    0x401d40020200b0003001d2b4880001e800303001c15480c14807043d40035041c540c600700d5100b40d10a40000701da000c0c080c01920740d02028070f070f0081900601130001e58101100003d12078800d11200f002c00c200012100140700c01800194600342101c8001e0045580d00d040c00311100302d843c000e000c1075a00e001069002c00d00a101122040740600c00880f14040c00e5440b040000e40015200b0307510404040482d06403071010124081005c1070f501031030040042c0031311009044070740c1904010740d1185070506100241c0c0210a401e02102e9044801150502d082e020440103842c803548100351000040b6508140c40c40280c100400343c9407040c01455143c1e42d5100119813072201c4201092007228100007150160419030410b001003280070300f0800c0c0d40ca80da85e540d50301e03000c4211a00c40024800d035140000c481d0307000e13611000601c040440300050488041c4904c1c172520b030290002c2c030221029a84616a0f203061b200f1500188400040300703450745031a08020740c80f0350080004900500600c0b52020000070700480c441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 348786007 1250 348784757 348784817
    0x51b1917070b0a02070816061401050f01020c09220f020f0103060b04030b0615030a0207050c0a080304090b12070602100f05010f03140a0c060e030f03030405120a0e060703050a 77
    0x612243c450040e248025030017482c0039590307060100030680300301c100441e074506100e11031400051601106403c440500c00181c0026100f40f2031100726003d660790004650003036090031100c0308541d8403101c002b0307082401107080c0d8100285481104005114681c4480400d141c02558091016140c500044040324802e001c0d4054181c1c0c180301c02d00204160003080740c1e01c5200a0b1561080070600c0d000ad01d0190011100034001d6500051a071041001c1407140c1c048a840503182c04480c5405c0c441465103900903801086041c659903603150015583e00603640f01d1002c000010703942ea4a881d140001d451f440c503100701c2d9500b2820110080c95020103441401d0480f4091802101c2d198119540c4400d042c112700c0c0381115620804007c50081400c4104070002800c3c145c694051080e810717800d060034030380305210b0001680c0041c4200800300e07a02054000300c070709050190039030b06c1100742d07000c1e107072910b50010041e00b00c0c0c2c0c04640d000070940c00c2402481d442007185c131088d5240610b10707101008242840e08074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 348787257 1250 348786007 348786023
    0x20f01020f041511030324030c060313030905061909060207080c041a12010b010f08060d02012a120306050d11150403060e01020405040c020a0c06051b191707 69
    0x400c0240c603030312900c00e00080307180f0b0240002034135458001d00d982c00a559082e001e140c104050050030341c404841141c6481b00368003910894004400140c0180030082585e10b0114250094108052240011a001c0c02009112644907a01043c0b0755900128807000580440c08000000c54420b000244240445010b1001001040004014840644024115141c1c0c0c440310400c004500d940e20311443c1c8c074a040344000080c1c07030321000c00014200740145841c10140220102845034a46503014100b440940a0034196071404000c001c1c200b803500030803a0000c0441c0e494140d101084001c00042034a00d00c26a03041c00a05d84510030460f14001007403004014800301c01348816a07082500c9824031904242c4411402d0980c2c1e6281c0400f541c440f40d41c04292650300103000d000a207401d114049c0604210b1008144980040d61004500d0f211406890140200890749003a503201c0da0300c1ca03854078078401099601101c001a4500040c10303070b41c02c088442001050039940b0100b008401d0380d030926041420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 348788507 1250 348787257 348787259
    0x5030a080702040c17181902060301051c080703020a060c05042303010f1509061d0703020d0209040c0305100803030c04060e0607060509070611010212010323010c0c03020f01020f04 79
    0xc0100600c1c01d40303d000244120340d0350390b40203903460105d0140f0038401c2e481082848884012101e041c1200c4106d9080d40395881001c0c400036803200c0042c0d03419150250346611006090814816070168221030081c000500001c422042550200f58079444610036034042c40702c000b8140c0281c82078000c50041000e20701406d00d18200b200809440c1c030300c52a0000d8000112209012030713403030584907034001c581c5201c81102c00800270122503104210040400f560040c030714403800000348401c400c020780b04030b00701b607000702e040003d6070b403d5412a01c00c0c2c0d0004208000c80304001c0c0c030143c0940030840c0c3c00c54808521420006031401d000c402c0724480d000d0300c0300780c50ae003504011043d510802e22011003034012009102480015190b07106280c090b401600040054a26041c00104000301010b0003a0050340140802441d16102407050b50640341d0051031005000c0096105c007000707080344036000b01c1c950700301140904502c2d00028a001954080e03400d03140001c4124a07114280c1c03040c1002e10030312040c1048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 348789757 1250 348788507 348788509
    0x80c06100303171510021e030310231c020915012316080324010903020d030c02131e02090a050607050715082203171b03010902030f0105030a080702 65
    0x903001c4d40300c20002c1200c800d580801002ca01d82c0d285600e0700030096841621000c0d541e0b080406442001a00c00009500d103180080c201800002e982c4070700c0400020301e416116101141c0b00981c0186400584800414420320312548402010204103900074402d803400300e11040011001420315500607100c8207152402c0072100320306488907840c8401e4122003441a40440300000a0000030381e400f03980e0303840d00c078101640328999106050b200b80110109840d542e80050342c000d4204170807290110782c105620034407801c0655189102e43d00c000e611000e06c01003015030f41c0e1a913000340ba1001d8201182d048003001d03544070740120711503407860796444100d000b000c120500c0c28a00909516200c0c00135104801c0d5142c03941c0754560302e01800301c80414241c00c100003003201000d1106803528810b114002c002102520003404941c051040602c80780c03070700000a03e131070700c3c40306403498640007a4580c00d552b0360750351017540c0080d001510f000700034200310000000d0500d00043d200001c503802041d02e9150104941c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 348791007 1250 348789757 348789797
    0xb0717060907111902120f071503020408030a080a050a0905060c03090c0a1203020c010807050a08040c08250510020d050d0f0c0c0204050a021608071e080c06100303 72
    0x40c000b40c100f1070300440d8600c100d0801d00c0040e0040380c0c61200c80d0007207841c51040000040c403982d10100c003a804150000c1c88800d0020f800c07000c698141030003c850521054040700070340b20f00c2d04882c40714071002171600c4120f81d200d503a1620400610071308010719140d625080c8155094001d02500a42c4400c004c0348100421708001d5030040e6070034084500705883c2c04003149030760095a0003c050302d00c00101c094149038050000b500c01100900c0c00d08050314040700c0190650141003c00002c00c00b0b04400a4204070149501e000545010021603212165100c00303403450b8000700c03c0b2510700c02050305001805051805160a008900790040c02c5d95407500e210440d010b030040c1800c43c1045e0303100d0000241d91074051040311518010340e6103200650b0720b0390052006850000c0d15540080b803040000310f0442c400c50564a2140b6070140740316990301c5007410000020b010380c50740d24800d08181c01406003004007410003460100c41000c243d85043d50740e010948291846407002070f010445200d84060108211 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 348792257 1250 348791007 348791011
    0x601021203130b040f0c1203080a090f170406020c030304051507110d03110c030a030e10050c070f060f140f07080c1f1404080405041d0313030b07170609 67
    0x304155060035550f0300c0344280000284d40c19030320810200c0161090190440d02000a824002c940403400c0c0440e42c0c0041ca9000c00904c441d111a564003051020082039141e880300c02e0350132600b94480c513104801d01e4103281d0b101d81b00d074070301503c28107140b040b140c00c020050742e080300da000304000c0000c00c50320440c175501d43c000402100d0303d00c0790716006040ca64911407030034010ba0003956a240d1441100720028503115428014a202e54044034034280040d503c25078280d103402d02030791031041c0e4901444c03090f500c070300841070030340203d00a001012500950101e00303d001c0716400e50b2241d0f409403c01c001580c000105002c0d11075910300810540c0410700040d40281040b6100d51030032890401303000c40c400e003881030308040c00003402280c42003921041c5a9000e100460254410b9541103410140e4070007400e4071841c880c45009a854110020280e107424007249003c000308070949907541715420202c0c030302c4481800300721004162000800c40c058442c0c000902400c815148148550310f4800400407100d02c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 348793507 1250 348792257 348792271
    0x211e010f0b0c190602030402130203090d0302160b0906090c01090305030405091015021f0612230a030507020112110307030b0604051e04061401080c070203150403050c150601021203 79
    0x70b60300000e64400c0e03030390400090f05401003000580702c1c280f41c8104a841400f41c5101100c044c01441071105696010949400c044001e080041e0b5402c1800003074000c1460a0801a01c0049417000f040101d1401007500b0b07210384404000e0711a0468181c00554140c196404007810b1680140010711143c20040a095007200340c1089066900b581c03070b01d0000c3c06d02d280c4c20500b0b0040c0c100c61400c18000c8184c2900510814100109200d0a0300341180f10b0b241c0c61070000302400d495040c01c2c2c6043c552501c0002080303000c182c1016543c0468841c20080c1c540e600c8140d04a00040c8455407112290120348184030382a42c00400c21403540d100c054084000d03280303140655901000c108800125030b03840d03940c0c0c9a0f050442c84507588651100c0b100300411503915901851027990340c0350001080c0c1e03a0083c041030380500c4e0710140c01e40340c08050001c01c0c0380070094010320014044000a1209040d0001c0c050125440008129007414440b50f04c030b0300741003005070b03030083c096071100e5034108082140740003560740610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 348794757 1250 348793507 348793513
    0xf080609061602070902031801060f1206021804050115140a09180e0316020315150111010b040609140a0608032a03030106030617070e04080a05211e010f0b0c 69
    0x1407175211210881e40f05075100100034500401540d003041084c01218010000d11191214071850900266010030303149000030071403540004c00347c0d1058004a001480840094010003056860700c01c18040c144442d01108086a05a241d00d02000306040441d0031044281d9541034886e403070000045083c00c0b00314070060341c01e83c03245001e24882a080010b0602000182c0f101d10748503010b40141401c06440c1c0010414498003a820000401c0c441034858441e180c0a01c0c00040050740d00c0d100034010030750031a1130703603000341007800000b6916103c0d00841b003410a981003c9401d901c481540b10100c0c0c10520400280303070020301101c10075140b4004c440528415413540382c469846280307404d80c2140d000340c200c0000b00390b85007403c0c00600d81d844909503810304010014465141008120782d0421402000207281c04400100d0301c040c07600c200b003030703071004140c030350140b11141c84c50901c01a81d454204c8030201c000d05007554096041a213402c01d541200c20981c40211140d00789101c0c10000e0780484a076500602c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 348796007 1250 348794757 348794759
    0x230903090d0f02180117070308091c060f05190c090b0a09030209040b07090f08030d020f191205060a06050d05060324010905011202010f0f021f060f08060906160207 72
    0x7032903001c042c0c158011061302c49503d80d8145008040e00446429a01519034441c1c030f42031002880500807503000e1403084684003030f00780940120103141c0084280003002c40d030800744248a28246500403601030f035900c1c40d140d003044080c0c400001c104c4203901540d80000340812804c102825512009054107a11407030b00c0d420180d21307500440c00b100810ba6040b500c800d1400704106400f9801016100513111080b004584c49148c00d40d026902c2c0291015045902c3e4009008001c000c4201c080318840c0724100d00910000c1780c0c968000e0207840c2c00c40c0c054400b1509110000b00280f5281840f03506440b480d480b003e00305096502488000e00e0024807594040c0306860065000501110132410041c8031155510010340c108070b100c80540354180e11684d48241803041c5100140c1c0c0060201800c140e0a1418a084c2c80d503581c004c9143c52181507081c20030b4684a001070350b800049401c4901540c25401501201d5a504d0003101e5550030100c5890201d40c01001c00f107540c41c03004a01c8482e103120144103d449031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 348797257 1250 348796007 348796009
    0x40e06271b04080601090f0c141317010c090b0c0a1403280e01090f030308150a080a060b06040302060f0a03110a03060e07020a05060a0b0d060906230903090d0f02 71
    0x282d44503812120b6150b1119004014034440c070b000f0380502242c4000c044c4500c0703002d01f001030702000508541032451040428001c0041c0ca104941c08000c2c03a2021410b0072070380d408440b5070f0003040c1c3d40c075211000441e19840400e1400342c040c125170030205003400400c0803003561303101c21601c1e00700e402440210380420401640c4074035264044c60381c00e002c00035002e0008440000047e1120044006640c14803044080821041c042c15012608032a014200f084140c1e03550076507540e1803040d001110b0350000040d08041403c0c42c0008114038000d1250808002e1120900d00b0844075004505c00254805401c1200703820f64650000985040501c030704002c030b4018140c00c03194100c2c2d0400c0300c0260009a8034201040740d0786d1404045130f00000da600141c40066000e07166103455450007409913003519110810401107440e50744071004074540046081203a240a0b1a00201a00c0a01c0741c1561030b8007903940f503020310b54070408028012407464000b1890411b0030401e2000d01d109078001580c40c200c0355003264001d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 348798507 1250 348797257 348797311
    0x703021005030f09010c051e0c120301050301060b0306060702061605010603032c010c1b171509030307020309090c0d020d0b01030c020d021e0f0a03020102040e0627 72
    0x405880d912119181d207000f03680c1100140000b460001a43c0c10019540141c80d0072200315001d0810800d0f49600000c01800c035901644200c0340c010748644031b03c801d10030020003250080c5050716004c074020b00001d5034039007031141d0501080e202a5070000c000c014007401490300c0f070020001219031001201d075205517130302c480e42143d1240d40180c02003040844140469142e00c1001038002c1c0e070f00d40b103404c500550400000c0c8800c100450041514802c0d00e010403001c1e40e410102030051512000f81162180c81c4a20a511408074096000042c00070001040b21184044192486a805580154202520f6000300304590b20301520415004004004060140003980002d15441048510104035101070a0004040316070b00c911000454022070b00c0c900907203038003098698454000e45142c000394400d42000500700a20000220300610500849000305601074016104441c03200031a014541d94900601140d03c0500030222050410002d1902c90b00111070040f43c0c01c88400c60801d41c52440d00842612 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 348799757 1250 348798507 348798529
    0x301270f0b09060901060f060e010e13020f22050904030503100e04032118020f0411161103071505031008030a0203040e0c07050309090a0e01021204110d0302031605070302 75
    0xd0580001c0108401301c070003402200010b01d581400854202c1c0380ca04010600010503c0d07450400892900a001e103940d0005140c070300c071041180456030f41035050308100f0075502c0403101c80041181030207010808920110001c04850014142010b6551941d030201c40a500041050080400305007010890569541c01948034520944030b1084264440720f49169466141600400c054200740d1400d000300c1c50b41d0034407010a030f0706880b00c0700b41c1c0b456280024050701c0341641e1489808008920288110404850380122174002e180d03101ca4105440700707054841c1d5060054505c100c00c24100c49078924401c2005540c0054199008006207403203112442c1141c0c1308450220041e80301090510540d0826141d145e04a18003005181c60324070a41d03601c035101e004420b5094840c1c541400054100001030b00034920340d10089000b1980d40d6142a2107120240c001d0758180c2c0e28070354400d15a101401d00451984d007103034054001718240307061400070000c40802c02c8011100f40c002e01c100000181ca07600721813a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 348801007 1250 348799757 348799771
    0xa1202071a031e071b02030f01020a0c0c0b070f0308061f180807080a0206070317090d080f040209041106300c0406050304060b0406080604050c030c0301270f0b 70
    0x90b0b480c2002200c031200c2001480701904644114021300003040c0e0408800f584405140001c0c900860b501e00000342405086a42a91554000291190303040d501030032910f4858456003c6103101c0b03856001e840c01602a034000180210361643c03015012034003540c0020741c8010004c14800070710341c0c402c240102e191484180f4402080204562544c0614a429000b024005040045c69464a4140001e580384040741020340224000601c1c0d406241c403400d403c00400102c1046941c090030030f140002d6942d030f4200c2041d0001090703140440c51140c51a89450302a6800030000c0c50309840b00d840c0c0188060307809214650005c0c0c10003420a181c5190706800007080c0305248140d80c0d04148022044100d04000c10074550544100001d00015412500350ba811079000030300000c02032843c0c0b0224004000310b0b0480205803052108000802c1800555041148000d42c103850b100c5083c0360070706003a90401018007d00c61307814003000a01d8010010b44030020350290503400d45404044d251010342e44e0080d2205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 348802257 1250 348801007 348801059
    0x70b0c1b0604140a02030a060c1812061503020609090a0b19150512070e010c0213091205090a060c230d170709050402030405160b0a031505030a120207 66
    0x2c244a8104801151001e111002d0000c221155000907102c0009840080140e9942e041000a40e44500022202c01d514500c4281d60703261102240c00c030390b4140d50003c442c058100200d15601401050342401101d074041d1055081440c0c007020004412001007050440c5135488040518a50b55110030b00003480c10301c0402c484050501404080c800141c40f692014014100700d5008008488202c0c0c40d03105580b49013254452180c0760040380c3c00c2c21200c1c07003e9448020048000c081d81051381c0702c00582c81c803400713003404007502841058400d03000d090308860303000c003030b50208008250003028a1900c8a2007a01c0405100310818400c400c0203042040d85012a4411800503940a400180c502d804501d02e18404000d40750600004203080c0040c0910f034002e070b030084003190401030100b220245104802e182820407981711900192980c10085d98100041e0030041c03810b0002582c607038001c003903070009009401d80d603030103465601d50441e802c941c600071841019800103d11405010303071466484107a500d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 348803507 1250 348802257 348802261
    0xf0d0c060e1213050915091305070305030d020d180210140d060915090e0a020d031701030813050409051009020a030506090a030e1f0f0203040306060e1f0b070b0c1b06 73
    0x9111030b4031801044082c01c14500035180310243d1f036194055511418000000c0c040c14454604181007150341e6200402d1884017007487c1000401c1e6030040d0450713040d081401c010f00d000081c0201c0c181081c2407000b82d00100c131680e8506034144a4007103c4400410340c0b84144c0381083c103000030b03400c464055100300c14071a0b641c1000b089001e45610031800078041440140901301c1075a6201d600d0f5021808024401c540060b20748003054064115900302c1d419202914185603903030704169040713074848100c001842020301c0011400385007510a03110200e8102c40142800f1014000600061038182e009a80c4050b00440000004070704210403071241008802510b03003c0440e00d8043d19912100e040780b8800c2c43e40424480c8071152042103c2000c01e80d5107090304880c0c1543c07005a00718481d540000c1c28850812401050450761108154002d1000381d0810b11404460003820000c0081d5004a03030a840007008000d02049142c08401d41006e08115003900d051801030a00d10003e800c440844080d4000e80f003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 348804757 1250 348803507 348803509
    0x8071b06150501050a270e04050601030203010509030429130b07020906060f090f040e01020c0c0907080903040b0306010504090603060c080603011109010525080c0f0d0c060e121305 79
    0x11070324010002070802a00306541030001030038110210740c20b03031906030390005003001e40040404403000034000d09480d40794900700f40c1005510351100740400e074000e41c00d09010800e542c100101303c800300c4030a40000400c00481007c22403503e01110400b00115400740141c4600020501494000b0042441d94035544c10740c034814020050801000ca0707106110503c007960012103450101c80700d4400884400c2d1100b039003070000074001e1903186422400e540c40840d81c40301008002411480c903403411204d0001e0b580d201401201d0300070046032444801d070414030003000200c08600107160400c0d414106103081036100c5902c082114010390096400f40c0c0c859920340081500b10048a41180d4140c0c02802400054146076141d0300c1140c0741641008030000c4c980c0200784501c914000c2020320081c00c1240d1006600f03045c10943c00802e4141020302905550620340e040000b2080d1251400d80c5824103505810f407216002041485038041245c01005291070385808400005c21141075840f001015580c2400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 348806007 1250 348804757 348804791
    0xa050f091e011d220f030212040927020d170d05190b040e0705010e12010906090210081e06040212090708010c020304050607060e07080307050c040c0305100608071b06 73
    0x1512507800300313035840d100000c610015140320076155005074044004030241e2034100d240c143c240300c2d03e0f0380b03002000c980440c0e844481c0c2c0081090502c00105a00030b0310b41452407913003c005412000798441c0c8443d95041c005202d011017059100b2078104800e051003e412028004d0701e0b02103407080404222920b00907010100ca110380188600181d408000c00c0c000882c40c1c948e03a080314010710707041c0081d890080c40c0554a0000e100f54400e0b0040c02408800d07100d14000c00a45000d0000324440e22580500f06200c0c0d10900003d440303145803038140030340074004141526a0385806050070340c11079000c03c070000000701d0300450b550150701003100408070310703241400d41400c44507006c900000710b41040004200d01c1d912842610003158004000050b10400011580d00e0000a9407141c410750102003000d206200002c60202c1403d0400d48050140c038002d018114211001110f50440481c4814014014548547c0740540d00c410b03541421158020685200b00c585a00100c0840303219454900204c4d040440c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 348807257 1250 348806007 348806011
    0x12031b0304050a1401020a0303050a090f060b18040c0302060304030e030604050a0c0b04030c050f01230a200a0f030e120a02041d0303010b071104060b180a050f091e011d 74
    0x100b84130402c60320480000079140c20300588082c00f00741e25400480c803018240d5008030b06440d44130760b6611401c41c007890901e02401c1543c0071075201d04544480c400300f900d11004104d201c1d0754000d181c030b00141e0031a400c1040076000640140c1c10460158036910880e00c0801c1490302540c040d000401e01030644d40f400d1401a80e1680150b1000349017072100b0000107401d408003106440007103510381c070b04082600040b03411542500744050040414080c50880840b01c900410804c0a96607414420066a442101c5210006071203500d05900001d030f0840400c07030308002c0c413541c0d505c2450805500e0302d000001075114521188409034030740028045030f045103014407034a003c00502d40d100ca043c82c52454806a00ea000511500c103000c0000100441001076098104003842c3e0024002c000d10b64461200c901150403030b0341c040c00c941c141d1038006a80c07490660b9044044075401044604c030511654203102c0040c802902c3c164034054a080034101c0324111051560282094425a0031441540007072403200c4200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 348808507 1250 348807257 348807269
    0xe0c040209060d110f040e0a060b07080d0b0a0f06031d07050a03020d0314030f010513270203010e0a050a030207060804080d022d09030d03180212031b0304050a 70
    0x204108152858480e5070036104008250180010144d00342d9904600a205289040741d030380c400000e000c90000401240e1078010b10303482002300400383d01c1d02c8003540207200f0701c0000b4102c29018010400404a2500700030584070300900b18022040c0e84443c05413010340c080d04950082521403d0300e1206680248801d00e0000c14807005000309440e20002c12880d403070501002e401524203044401c1454007a50700b060803000d2544107999640307840d49006404205c20300030144180307650960820100d100c0c1c0a410000300611810210020055803801e1010120365003c07a0155201c8407003030310041d0148800400180203070060301c0e1600c031074a0000e0070414160052401d1104500c180400b02c1c2a040c2500d40c1d140e41c041c00180d1b01c0707040d449281140c03005c41c1d0741c00d0401c2c03c0d0007402551000c000b90160071107140a07070849505060120060742601c01030507a200101c02e40100b18800741c6404c1d03001c0c0b2110304c680815a8a01a00348402d40440b02010604107801d900000702040346051a1203c8002000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 348809757 1250 348808507 348808511
    0x406020d090510051b030304050d0f11060a020c0a050f060708011203080105061b1c02060106030b030c0d030e031b1c050604030806121603060c030234150e0c04 70
    0x802e00c0000380400c825004004104400032501c0f0410017600c41064800c0b20445007220384910741450803d69400c4940f91103400544412300110105024441100600880340060b0540d40c0d1740002d9032000b9086198000110f2245041600200d8401c0c02400440291030024282d030780741400d00034080000603482448420716590803900400e500404032815500100e030104c0d41c0d1134400340c0c120b0410402c00c582081501401d00040f940440c070401100c800300030380e000d81c0d0030342e80da03450190201c44480c6a81c503090340105c03402110a00e00203141100c400d100b404c040e80101d5904020a1404070700c1c801200320f94001e01c0008100e0b1034a004004a201140040c446036100709640348c4d910364801520050911410b28045001c5580d000703202c4010480100c211400c202d2064555a8600b00340d1000b50344051170140e2541c8130134464003c42c0c0e5181b403c04c9a0100421f1000c0320600f40b4000d00000442d944007050641001643d1900001d0380140c0120021940d00f5443c034146080002c0c0100e45881a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 348811007 1250 348809757 348809759
    0x1b030504090c050a09090f0605060301060f081005030c060c030408070f03030905040504030f08060f060a0e0906040509120f13060e18010620010b13230105030a0602030621030406020d09 81
    0x40c0e002c0108420b6406442000c1fa012003030107420b0000d0000d581242e81c2c0310b5808070021400c030307603c5440300c816480c040c0e40d0210203450320f2401412a174420301805401d60080000121a130400320010020003803400d0072a40390541e0b4048990414800742c1113518500c44120040060541c03021417000540401c960400c0b060800ba078001d0000b22071506c0410901c591080054a155140511540103160180c10390b0740d20034808400411508603050304610542015020842078103047c800c0350702c91400c00004041b2855800f61240300c0da00b10800140e800142000304016000c8580ca14070002d003950346510210300064020030091294201441600e5480c2e900100700c40f42d4803800c400744001d5140880c1031085000c04e501c41c09000846c1915410982542444218103910380c04620420001100d0000c04040d00c00840e031104070a11425600d07a01010543c00414929401160040350007400c60b40010440300300081280040e84031160035420106040082540501881c0300406039842c0070301c042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 348812257 1250 348811007 348811027
    0x90d02030a0813140606120a08160c09230705190509010e2805010f0807030b1c06062120060f0c0c1c0503191b030504090c05 55
    0x1d0007140c01080030414414040b40003240b444000004894111041600302c8210086035642d038401540c07414000d903031000c04450111004641842101d500510301c518101101240f82d02580317643c801034444120700c0d40c0c0025410514803c1c0c44461000ca0311400010401c05140c500907140180a9010b002f402c10088001c600c12090700745645959040c001e458109100c0101d440355030001d610354000c46005100c00001802c0c0d0741008000301c00012409140391100011a005003c040300300021440d000c01040c010f50280e0080c5a0946000d440c0c10603400403941042300c030305203030700041d82c01650340c960901c00306c5021440240c4d640c0c004008a031580c030440d620000c120966020351292017142110720916552000120380104101c03040c101e4940292001d840d8513010319107800d42c0304040c601c0c0c0710110b03114242d10303814071680c1240185062803400d10b01c10742c180150741d81078000c100328511080c80c8110041e0300c04441a00a85c1d600344c031582004400750031034490700072040512400741321007000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 348813507 1250 348812257 348812263
    0x60702120405420403120936020f03090601050108090c21011e05010806040c0b0c12030709140a08030301170c130b0301140412050f09090a14090d02 65
    0x41d58400601d100781c002550200c02d00310546084941d100300100800004403510f80d40a08140e9004105174804600700d400140c99402c041d1007084d98040071809149450800107820740855900f00940030030480308a1144000c03a4040c0348000c84c0044044103100400004110250141900b800d26000604095000c1c80d52201907040d01d40c800d520002440c010810200342c000e5100411100070b0286100801c1d100707018070741410581d911949040000240d80100090700d07405250083c10103200b05090082031002c6038402015656039205100100c01c1d0510000011407003040709581e5441140c4c2440340040107002200b08031440b8411140e02030112240220882c0e04640c0503000560320b00401d4200c5074145400041c02a40c0302181105500b034818450f0844003403000f0841c000c1010239030380c0400c0d400070041a600684011042c0b0684007084e4003407001001002c250340e000600b0005100d0010388880c10803a03000840f184c83e062a49040d692803281580c22401e254094404141c034104000d60f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 348814757 1250 348813507 348813529
    0x1e09030b062d030703020a0b0406020d080609150d020901090516020a0503030711070810150e09100b010302040314150708131101050d09060509160605070206070204060f0305060702120405 82
    0xc2c1c1c54105102490b140c0c0e0030480c9000465001c2c0c41103c2050b03803401c0880345500184610009401a81e0505c100d0078414043c091103a00024080c150070f031516112040460f1a0a150790b030410186410200503949071200b60b0300820542c42c1c08038881ca02030302041030701000008000255844844800d00044002c000c1d00c3c1d01c001c10703261070340b1008205640b40c0d25040d02580554641e0140d102102c5459140303400080b0714484510000200d15602c0349074282d0310104840c00012a00400001146e0701a1138202000e4000305141c00750425032240c9442034000c00b251640744940d84491402e081031010306245550100711400e00161603e060b40525200b011000001480d04000a9201030b55070702510903210030034014001002010b00c03c0c60b04c00c00806003980c0c03050032031064840419034100b01c280d42c00162500c942c2c13054240039555080c811146c00c4880200c3e84145c4404d00410b02c1280505808000d5001e08001d0506040c01c82c3c010f801e206041c80c3c420007149080005001d240c98540c4045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 348816007 1250 348814757 348814819
    0x910020f090415030b01030807030206070e09180f10090b07080c0403060b04090b04230715050c01020d2918070e0111010e010c0e06040608010b0a1e09030b06 69
    0x403d4059101044003000d041c59007008105124800002c014040700d8809041628441c0c0c00321f0700b150b21030540544200c00c3d03958580384d10641000c0000d04a41480ea004210b603d00e2800f120820f43d1003401007400c3c220398401c11360307186030360311200743c00d03c1170a14403107410200e1401d00702d500d414482542c3d0f80ca44154040a480e69445070110b84458445a03c4031548a400034090841824a4940101c00c030b140215403400e0344503c1c40f00e070600710030041007500c215071103000c0d0f0ba00802d101107020740f000e801c088400c54641d542440701c440d2842c2c0ba40100b0718001ea01d0309022100760024004003082d2049049424000c2000c800d01c504805d01080300c480e00952541080303c00c00c1002401240c400f0040749003001d481d400e25038440b141c2c4505400c800d00c0303a40c06031222940c408441c02400300c2800f40e40f09038000200c44000402c0300468410080000c00d4a5240c00c0c240c004000c0c40c0135040091000c0c40d0400078420f18410010300003101031141c8c02010895034410740e001214807a0704020a00c0c9405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 348817257 1250 348816007 348816011
    0x41401050f011b0f031d0a05060d09030309050a08031602010e070506220b04050f04021207031d240109150302040b22020703020c010f020d0c0c0b0c060910020f0904 72
    0x107000e010704441040d20806130300c040001c1c0003c40d035141c01060500c04840a042d03001d00902840761a29040c03001d039054542c06051a41440c1c001d0440102401482c0c0003603052641d20080c04c00400d005110f6100c00c24040c00c10144e907420200c822500c0c0426543d150001c692501600780c02c03a490100d0740e41c0c21514111044d40e10359600070403809001c061580311081013a141c0e03800046a1807020007420031a030003114030000c8031003402c041c04164403070a181100300c4860780780010300f620300030f9000b60340511101c01001d0000c00d001c001030b450000440241141c489201c80e64098410840c41c1d02400b51102c0e4005011480035160101307040030301d41c08000e106640b1104490610b494000c806450828100000c0707055902e5066464000e40c40620280c0060080411024240d405114a2581041a0341c02405002c0499904a406044040d412070f0108078814002514030502c001a11441d120b58000e040d05013403100c1c182e0305c1c0c548a5110316a5880c010300500d00d100c04100140c4501300340503600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 348818507 1250 348817257 348817277
    0x1c020c251815090f0605030c03070e0609070c05060f0121020d200d0b1b0915030c1204050105070915050f03060307030209090a06060e06220b041109041401050f01 71
    0x848901c083d04000a40340c0741c0885815050229044001110800d9090b1445003814030141516100b0b54010f0714440c410b000c0100f01c160500c003901c0355106a042c9040d45280040d603540328200b5800391070350400c0c0c00c5880300500c542011300d085a9445101119211604512580440c1c5445c85038000509551914800d14410540038031005103c10b000030000030f102030091401880c4800199440392041c0d120f806421144042c0360101c5007400402020341c1100c0140c03c03400d40c01b80e4001000d96072070000078801c60b401d88458028241c01103100c1c100200d8545000b520081407000180d00200c0e020b400344d840921903035000300c200e8030858448600140d80b6562040800d20344901d07640001d4000c202c8408011410502040484c490792081c1002d02603a946c40098483c0d10105031021503101051900e520f42040003410070160740740744128086200a002d1001070216000c1c02c503185d191000015a0b040180307080d11803214405404000700c1c80f154182004038003040b00088880b4144100416 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 348819757 1250 348818507 348818531
    0x1a090a0903020f0607171027060b13030b091c18050a080c0102060c0a02190f020d030801140405040c030f2103290d02061c020c2518 58
    0x11040300241d0380842d01e15081080000f03150560051200c00e00310701e090040341d2204000b01c7d8903c11600b51407403900003510144458518040041e148280c52580c9480010702c2100c2c42c0050701103245105405000c42d03146041c640e122407001005184581c01c4400f800c210740001d03910014a0080ba440c110780c00c2c0f0382685100f00705507143c0e00310075400540110700140d902d60002d002c0b60030760303001e0f42a03a0841d22003071220000c6005115a49026820a804180000004070f840010440c01101c0c1226000016000303e258009460f00943c0000c007164010f201801c00100000e140b20420346e410805d501d42034407480c180c103406010007880001c141180d0020301040c0103a10000e031480c0f468050b90b2071503580c8060700501260041c45000540c841e0341c05000b070000b080c41641c44002410b94010345000350308005a6901c005101007500c81c000d4200080280d95202030701010042c080108a0040a90001d44201e01c3c115070600a05840c10386c1403001c4082ca008060003c40001030100d00711154107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 348821007 1250 348819757 348819763
    0xf0b03070c06050c071703060a0e010e040b0a0f09060509160503060c030c120a0603031e1b031125090903120c0e0409110a0602070f0302010c1104110c011a090a090302 73
    0x31030280c08128071050041e081b0441d0002540607110450312002c0e240d0b42c0303280707d90007103500b485580c0da0b590f120707000a80410303d501c14455201261070400204454141041821113942190035a035456484041190b298010400c1140780b40b0b0046000e20700c0787c070303140c0000d54586000380036181204000c03010810189200d0b050342d8010044502095181c942048a440141080d2100350700081e5600021800c001c0340754051052070b20941c0c1c0d6020640650b40f4030880212400a0440801c407039008006585030003885142c48203203a44040c0141161004001a030b24800c94110801c8507250450a03030009400c12140030743c1c503002d500c000c40c0501510209490b290845010180c00504100c2001c0c100b203074071010b040ca119030446030449080e8490204a1351080c0f240555050a00d100c030782800558020382c3c014420a210340e08a000040c02c1201080640c1c050769842214103070040b0b0320001c0300c1001e00501072b154540f021004030000400000407803403c000361190100b0766942e030050050510038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 348822257 1250 348821007 348821017
    0x71707050f0315040b0f0a05161803080a0f1e020312040305070203061003060513030f0507052a1f0210180b090c100e0303031807120c0f0b03070c06050c 67
    0x202c520f0940c2c41c43c06003418820703040112207800070403030b00c1c40024400455921807503004012104800e010000241010b84a00c1901e20558085140d810f03800400038034040020011500141d4420190002c0308502422207000c0d0b0748808041c200c1c241d00d12402c80e6000095651400c005408a001d5488500f01a601c5110b8204041d4040c0910010001c4080440d8542c50447e442034808100f40d64031b41280100c48400404000d0008480c42c0c11280400c1c41600541092070056064030001100501910303400f0314514180d0101c00300c408002132041c078000d08100754025100e28540300801044a00940b034040426034481220380d100c1800600c2000d40322120782550740250810710728140f0070110345c1d466907103040c0584104403c400c41d16200f0b1181800101184000c0d00460442e00d4005100340d000c2c6100810b04034034415001c00040b812102686900380501800c12811280c1c01d050001140302d01540042541c4036040043c00485036000324003020300c03a0407010000d01901d40c04044e030064070070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 348823507 1250 348822257 348822283
    0x60d1205070c080105011a030405071703161a0f09190809030f0a06110906070602031e130203011a130903050f04090203060307060f02151e0108030c071707050f03 71
    0x9280004a03c8010542c030880c180c910341d01c0040c071488138945002c4620300c004c49004105400a10003000000c0740b1000700d904e010001e5060381c0c105140c801591243d02d090480550350a02d01121911003c260012005d421120845403803d06140c4056040d66403041104032480c2d0400440242c5e0a000c01207065800c4000002c003503c0d4054041c0c0501d80e82c07a000c10720240c80c00c83c90004d50020f1420a04100c4856902c068040c13070501d0315a031201e00c02900010a41c5d150402c8400c082254040c049510b01d1080459025400c03030005030380103040c04c440e4520038000403001d07030150110080d0748140310703a1a101c080010100b401e0019203030403500d034001c840c550790804502040221701000c041c0c01031441000282c0444042e603a807590100ca02040445080740980c00060400d4944024034014552185400c10050b4201041002c4d600c1440c000340d0154003250004070b510300c2a42d4041c00210f004281d511a03205041020405081c1c8901c150700c00d041c45070140f030780002501e44040c0085a150741c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 348824757 1250 348823507 348823523
    0xf041403010c0f140f1c051005100e0f040603030906021b1c02040e19030210050403091a040305030a0807030e0703020a050d031403040c060f05040320010c061a011106060d120507 78
    0x1241078000010040014654038825060800141d00702405201e4003080302c070000c1c81e01042b0a6610020b60b1000d4010000c2c9030007144040c1e001c0c40c0380e29180a0003000f94829904e200c0e507186840300090406000c01401e0402071400d00c0b4500807a5100b007400e4948907a80301c1c011420074030074400207006201e6103d42480308d0003108640c1c5521254044880d60050113034007610751006901d02c400041706d40490f0010003099090038140141200c0c040224140405081024900f9880b0740b0361500e1070304221300b00c0b4002070800d07003000481c0307516000d40201c10303161500400045065038001299100d450043e14007624400b01d1050034940305a99100c00881c8101e601070b41c908060074042800c043e40c0c0a40004607040c5814035828500c2031049030126034000386101c820407035031402c0c0703200c0c2c0364101c0710281048000c10a030000303d0568416a4050064298900e90300740c0001c0004d8160404500645480e401100821130320341c9401c00c2c10408161300c8023184a07007102d13500c000c0d5461f0141c0400a84110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 348826007 1250 348824757 348824767
    0xa030b0306270304150309021507080301031109060d110a09060b07022b02010f090305060703094b080307021501120305090907140f041403010c0f140f 66
    0x841c00758074254003a04400c0030350001d800030000890f6684203a22480c03017800c1c500e414034160326200b42c1c4070700e0070148018229024080024220070094001d03040c00e8500c91300c0040104208142c0e844000c450320002d8800c1049440c0090016529104011000e403040c49400103443e0700d5660b250140c0054804510200061034840d58160340c0d5404c20750703089001d04000300074507000e20003d0420a02c07030346160301c00344076440666004490540346600040e061080e030401c040001801400300c14030803502541c000901500704e0510401c0031500c440303d5155007080042460314070745a03406190300c0446d05d0940f03020000c0b00740c2d50100000d4003960701900c1c41e0400701c14400d84a0f40440d09440c64144900e81030202e0343c0b24440b0b40522000400020081038041019a20038207040c048164000340345d080000564001030702c1048580e1105209041c07640f00010107000254100d4403a00300850701768000c10014100d2703400600a140110f00d400180000f40f51401401c0e59104120b510000c07000344016120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 348827257 1250 348826007 348826021
    0xc06020f070503041403030702100c02150c0d14030c120c040305121201050405060604091509050c0705060a05012d0b1303050c09160e130c050c12040f0306020a030b0306 74
    0xd030098021030143c42d5900d07516817610b190010581d441507800800c07128819950203016600d01c1e6181c0e00072a00702581c4a40d19200208850140c0318105c01c0740040d0007001000d08000f0a50702c020f44104482c96003e00501400c1022041074800540481500c6003030b03074884030710000b10743c0243d51008001c0d01c190302d03c81807550743d01806003500c8510b00701144e9060340c88004000c25075004480369034111800b44420004210f954000b0704074840302c0a001003c4a031108549010f542040b20600341c051030000c3c1304000c01070200100c035440741e110f0000b008994189103500b07400e0040440d40405400503060800700303c4001c80030300402854031b103044643d504909928142940010b100580f0b460281c5481005603040c0903001c24400d08602407111580c118018042d50201c0034524001e820450890314100d02001a214000f88100f154031101c2e169400010424544003d1550300c100303c001c1404100206d40810149c074050302e505c0b090142c0c6a00d03440a00720002c10009110300d42c98843c1005100311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 348828507 1250 348827257 348827263
    0x1207090204170d0206310b090d030209060706090804080318100f0c0206131d0f010807030c09020711130911270702150103030914010f0f0c06020f0705 66
    0x300c509040b90b00c581d020100c1685600c2c0d416604043e40940c100da8001145c0b0000301000c00c201d0b048100042580200c0c0c811085441440c5035011200000f228041c0309000740c0801c4451007441035403405600c1e00502d9008154070f070084c0c200c000d1613070341c43d80c10880800188605880142100404880d00e4015050200520900526040e8003c40322040440f000c144100400c001c40f0503e901e52505c01151942801015840040701c2c0940f80d80e501070100b0014540d0400f5806d03032021103a0100e0a04100842d0701c41c810040c1c3c40741296900c0201c082001555120500040707079203501c0c00680701d0b41241401054521003941d07955024400440340076500710542e1203400c0079805048100154455001440004440c240c0780c02d40c14000341c030444181c1c11080c2200c6074071403414030540e003258148441c09680c43c074082e08210081380e20004203010340303111030355414900312003481c02d1481074030400c401030941c1413a1103010041140408502050101c1501148c1020b000c01caa41e51762080181032a5403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 348829757 1250 348828507 348828509
    0x100e0f011a0f01090308032e05240405060f0903010608061033120f020a120b03030c0d02060403080705070308040b1f0b0a030b09041e050a08040e01060e0111100b1207090204 76
    0x1d2084100800e4040b282008c00700302d800d84002801014105080e010b9000d031078413416040c0d040341f00080201007036a0b158403003c0c5c0300c00e080c4894601c0e1100002000c05084d2250f03504030b10b00a41c040300400c28421000e171841b100b10340d80817681c410b165041e1000914442c14519085550500d010040f0903200d1740014020100c40c0c50250400814035500f80f0300003a4450b600140d000240e9400001040311429402684403000c0102264503018401c40c50720f007850300140d2402c0c0541c219200300020305401c0602541c3c444071529100d4a0184640c0c0e000c0d080204c0580003500c0e1195400000b034000215103100382c1c5800c00c0c060040c056550b41c030004043c59104c0300b00c04c0c000a041040542050404010181c0507603481807004084002c40030000e2040c1d0340154050702c4500c00c0342418008504084020030240c114810400c100d0f6040000240c9400154907446040260034032103100d0841c400b00f1659092141e99070081a1055601c00007005103022128044040c00f40f50400500e00c0c409a00400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 348831007 1250 348829757 348829801
    0x80c0d050c04061206050102031b0a0f08040317070803190b032b08090c2407080301032d20040213050f030304080a03050912100e0f011a0f0109030803 66
    0x40c11a40c20500c00c0e0140e030451b219090160f80b06000186801c10300c0c4130010300c1c01154004640c0080c50640b5000425130045005035084440000e040c028001420306000c0c00c00200c51010f450710121740c0c0e07a04d0140c4001408030546061251460800944c1c0e50040b040c2d40030001c0c11203a040e544000c58031003030031400f40c2e81c890b00c203e03c03980110214005c484aa00c07500d020f00141c04412114001c1c0854103540c0320140e201d5004410122600b221040042c20400e03000710326880c3c41c0c0d81580350203002c1c40e40002d00d41011004c4044c8500500402c034000300c40702c80e44002c16003041610a01c1e405910180004203da2182c0040b4150344041d50540c448401c41d40300700d42d84654000c981086c142c0ba40b2840c001c0960a0f04544150f00100c0d0080000300b041d0100940a000400c07506042c60f42800745139020040040e46640d080b0f440382c5420420004d49900c00002000740384074ac1e02e0300550b401450398042d40215403102e40701c00107038041d9049800458004213895660f141c030743c100c11102503043e980740f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 348832257 1250 348831007 348831017
    0x4020c06060a063608030309030a020601091e0e070506210601050705070e070507060908030f010b090a03030e1906081605030f24060c0c0a090c02060106080c0d050c0406 74
    0x8000b4495540d00f800090004810540181d80301d0750140d246a0b038100000c504d000b005400a603405040009603c24109000075649546000380001d060640c107902002c409800d110645a424560008502c1030241800e0009281d1803817402035824445541d101f1a4003a001041042c0b00701d40c41c0002621429020b070347c0ca520307a85c1e42d400648050003000b00143c52540840418490701240305c400980060586c00c0140c10310045656160544140d240c1c11200307102c0110034070200034400c0e4589800f504025855604010f21500407a4410400d840f010301080348943d514041500c44004100c036698915030301c0303100350b0744400c4040e0000e542507400307081e4034010355000605107124406680c0900c05410305802d581d100d0f0319039100f8510702e101c82c03598501000313070062078640d852100410f401a60ba0001d84003400e28a020003502886070351045490b903042030740440c50143e001c00e00905640d401c1c10460340d01e80350125000c40d940164426851200e00d02400c5c42944a0594040c3c4115105030f43d0b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 348833507 1250 348832257 348832259
    0x203010e06091c02070308070312150305190221030301030519050a020f030c100f0201181203020a0504091103060f0105070f080a02152406031317040504020c06060a 72
    0x1d030380c1c0d4401c540458494102403c1d456103000361801c0c012920920348100e580d0342e600d0751504011a8029241103010509402e00404001e010380507070207030302002c10100b1403094615203030f1548030060303030322114250400c580f0a84110760b50085510112858036025044203c001b00e0115940e42c402c5c002501c1c2849904241261140909844080154400b010b0a0700c800181c3c02d00c00b11400e000d8015605014001000340307180c031401d00745820680c195032a40448000b0306000713401c459041c0103414285103011070344400300d00028043d040c520007628006030b50300c6400004542c540110703004070700940d003060b041041c0a560540914000c5104a070355142e581c1c840001914640b142c00070080880e08002200000b0480c950302401c4003124138010742e525040140a445041c0804880d210b803608011065465803d00d0101e540c0c58542081d5100b52640c10300a202d04451401680c005211802c20b9090040f0344c02c900b8103031001004c0c080c2c020340d2510444041551110743c1160000e0213885041c0b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 348834757 1250 348833507 348833531
    0xf0906062709020d020f191e1e03110c03030403030b040e0a0f060f060816050406061d03150a050a051012080c0106170307140606100f11060a0603020301 67
    0x6100072441001c0200c0303106052a104800340650042c00d1503080082e42070040400ca01440d40c0202103807911003403408180d00342d2003000740003040b020b0030b120b005c07071040220311807550b801910752810f8008802d880f800341400c80354101d015050090400c1102d00703020660005010002020b035005612a4a0034415030445500b4082201c844080014169000c0c40c20035007c600d1103400104002e0041c800071560020030b4581005503074850340910074541c0441400b00346a114044800007a00044a0900106141141c001c0c01c01d2800c51741004040c11019403180341d0b44d01004102c20982407001c410002e0b1a00080d00d00040508480703070b100e140c0c20b0000050a00d28041700050641d03102e00300c403043d0300d0000e46525110340c020003038501480d90388100108d1440d140210080010900030000d43d511891442c120f40b101c1c80350b03150b2036000c1d0f0140d0140009542e900d0845c00141a40d490709446450000004880340c03804030851880301c0c0034182c1804014416900140d065034000e500034420014016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 348836007 1250 348834757 348834797
    0x415050d050f1507090608060301060b19030e0a03021e15270c10030911030a06020405151207111509101503050c22051e070806030616090f090606 64
    0x4e49160026180c810180080da020b03041d50760308824060000600316480d008203041e140d00294015205070b062085503048994140901c911030b541d200c0203041444603668029545841010303065000303450b2039480c1100c0010405c4215000039166802d611b09040003c6078080c0456044454880c008641a91842e04d51000400019402000e0401e143c2501408802c40040c403c98000304d80c070301c146052034122070340c0c2000f940211502908c4016503842c41c00c0200003640c580358000000f40c0d03c0c02d000088600b41445c000340d0784080036040c004410f464414a00c1d0810b000300460308004005041408bd9200000606550303600701e0f07a10420000300e40c10008036161390984070041c460381c016046100c0070700340321030b80b039404440c00d01001201800c40c010b6201509c00c05c0716200b040e91580c9024420402c0440d103400d40114150500d2015400c101020035100c1d0b500400904101c3e40075001030140b24030842c05480103054154103444890b450784103850140005100c1e800006000b9032245060031069 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 348837257 1250 348836007 348836011
    0xb0a020601030b0c07081305010206011d0a0218060a0315290d020408060a09020f1c0b070519020a05100213170c04020d020c0609010e03090415050d050f15 68
    0x1a00240340981c61543c60030720100d00201036454984040c424240000c55038000380400c020341c1510b4000003070600000a01c0d040050b4849411406400c800300d079982004442107400805549025a95501403041d0b002c5030703c0b100c2e204503001100028414103842d49603002d2651000510241c00c2003695860203c90a8a104440d03190136180004080211807210001407108440036007025051079525a030507810300408070351b4074901d65100c1c0102021450030a90341c0072580021201c04000c0111100e00902658803610000c10820307110b00443d85443c003980a99050703110050816001c140c2840c0025110104a1000c4813180309a0381c00d205684214001c0d034001092500c090105079180c000b9051002c581000d00e107107035005004022440c1e403214001001d411503000c1c005683c40180c00c90f400d1400c1c074000d24112143e450b2001c1252404004412181d82c0d010407907000c1001640c102e45243c2200c07899000a42c072420701100c01e4104a00030a94a1940704224142c8154615041c03407441c00d1081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 348838507 1250 348837257 348837277
    0xa02150a170606252307050105071a04060f02031003021e010f050a050d050109061401030e0606150c1504050607020610090c030e0a0318080304140906010c080a090905010b 75
    0x206114000104134448000014102c4180001c96004019110b2500408601c01c81600c07254900002c01c80740b44080090380e00600f400c1c40e2082ca4086240c84801d18110410400151646007a0110301485100c0d0002281e480720003000310341d2800d10202c203600c00c0c4060310080f8002c1e11a030001c0c0642c01040c46219800700c0040c1c481004081241c68200d0385a40982692414032070184120003900700c003449a14064a00490000b4200d0308040b03055400c02a06120581003504111004100507804034140340c200f281581c00c003148100f1120303021561300800f8010030b07480c4030f104144000e81d034103205214000ea000700d09507001c540303400e00103d8641a0031260700b110002661020442e440a50b4440031800105150003d54030100c84d2409003059a0381031f040c2c1c000b42102011540d140445602d200c014000c1d00e0045161902d040f040346066034282c280640308841910015541364040d00ba03803040e40d0750040750150703502c4507944094503142807402191301807481c100c0046046001d1000710380c65580 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 348839757 1250 348838507 348838519
    0x7021e0c091f08060402010e0d11010e03010f020309030a0e030a0507180f0e153603130e0103110111030909090111040b0d0f090f0b0402030a02150a1706 67
    0x350301000e1006030840549103a00440c0e071075044551400707190103103001801e4500094041c03810240001850b4a078070403040b074456244400f4642c0002c24114102545070800c2c00c08001d807000c00c40000e0b00400308500501e403003d00010070400c800c0000b1004104404003034031110f419030031500a2540e2401c00301c1c03008103a43e004410906c0302030301c10031000c0c0394140448400301c0d2480c240000007050b1200c0401071a490b500202d1300954155030811003541c85000700fa030150258a07151112a4071105d4440107174443c501000c502040c415091046a81d100c8800c400c4001407641c2d15040d4020050910040e01e92141da940343ca08a58411b4881440c0303903d00710019420700010400704042994041e183c2c4025660710700d174410400d40190080c00040a1340351429840b040c0c3c0ea1407400507034000c42404040c05241048450006100160b8401401c3e08140207100590362403000c686080d00460f0065484550086800c40d031040030700080201d00304659410510900822082c0d0720034a00380c1d0300583c451 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 348841007 1250 348839757 348839773
    0x10022818140a03080a030c030c110a2a060906030e010216060203060f3703020105040b07030e030610031e020f130914010203011d010605030705090301090204110307021e 74
    0x2100010701000003001460b0301e0090343d03640e40345a62580a610118086501c0d4103001a800d80c1512440c0401d00ca83d04107804002c4d803440425803291801e81000b40308003003031141c8004d40e00b840b814100c4c0c0440701c3c039012044562203040c00740586549115a0001074102603002e1884001070082e214619000920019480c01e40e80d540d41c041d4100804158000c003154604007960354520010b20b0700e0303000e825905280b0440c44216290b8082c1d41598100940050200420060364050700302d130b00301c0d8029203116498102e07038582240c010044609460749440b4550074460321a200001c0401164425100e264046000c86200c01040b06104006540030002c0360341185141412950400014910040010782080c25510340d11755000321400100941e50200050000e07a03c1c410310b0503001034401c440e4001542c58003100500d140b0000342a034003040b0000c0b480018035102500032020040e802041808000c1c00407156589513081228400c005101c7e00100000c2d2041c01900984130303a90305001b505000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 348842257 1250 348841007 348841019
    0x20906070309180218090a090b1f1a0d0203060604030c06020c1003050610050d0923060106080c0a0f0c02030604060f11090d020f0315190b0103020f1b10022818 70
    0x440c1b0010715104d01c0365194250100003410180d1030030302c030304c8e00700201e0b001031070001000600c1c0d039409412000550060f4410800c1c9c030042d140550301c00050725034015a890380c55002080c414021340d4802001a41010400304100307401040c840071400c010764800004d01503004003141514415500c00707401c4015001c0c40c60146209400800d4064500b0301c01280d00e4502d6030726501104481c80340c2004292000382a03203100782007406400e0040405240c43d000900342600554000c0c402c1454031003d000f020004204c4242c0642c48407591a5002000c0e1281c602c0c140c10100060407044042070000d6207022500c2c2240d042040c25207041c40e5010b0030800201581e0350a112400229035101503140c441d400c42400d034541d218500074400c80c0c003005016800d40d07418441c11f0a881c1001c00d15814180140111085202040c0034ac410540b0804690040c0d280c4c0701002d5810901002c56184401d4000203500c449020403643e11056107880c203541104010402d8000c941c4041c400300d100c0e9954000203420498 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 348843507 1250 348842257 348842269
    0x19050f0f01090f0902130506030903040b0c0a06050a09020117010f0504090510060609090b0a060c0209180d0e010206010e0f0103081804181e0b130303020906070309180218 75
    0x800c0d0604040321001d4503070301c041400700000d03402000d005030001100710042901212035001001c054400b20700711b0905110702c640f6400f41d80101c24040c2400710314904c101c441001154045500304204102c0f40c20b01601d0040900b0489100b6404034031003003082c8240000c40c038071044c1207907205c1044e0480315003000c040102401005505465910414810b010040c40501c03910008000d540c0329400082c1c6403440c2482501c4112078a02d03c191890042004800e420111405c022a41250720328416541c884081400c00c28008030504944070f86400c41055640045103001c650601b60200d99107603a031001c4059040c801101c8800301c8820710001040081c0980000e032812070001549802400480c5000c502210a40180c4190f180c8000801209000b100d00c91403a22074000b0501c40100c41003038440d009019400b40c05c41e4011100074006a0a25100b41d05403070807940010505941d61401d03080017071000c0c00d0360088140c421200720b040328441103036108031041000c1510b0b0f0190070610034410884 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 348844757 1250 348843507 348843529
    0x302271e040b03061807080304081b06130f0807052d0a0e130308070c02030c09151302030403080106020a0c030f17121b12061e1201090219050f 63
    0x240050b210300d000c080c240c2e82800010300c6684064925104040c05800061a220540d805086281c104000605c480c01c0049007403044000130107009012082040e010424620806640c40c04000c02801e011075408c1c0c00c0c490140464a0b6a0115601241c6804c1080102e034200740c003544482c2d10085205440e164100c90105250500a14201c24169107110003c040f2000311640340ca41441012008209a08100d4030740c0c100c0d0440c58110350606a40c0e000c80c0d03503540542103d6124958100004460300b9940d281c0100150015011480070003000503054003a401c2520110003041d9070100203c1c403d4030020304500d80c01d80001034000514555200d034454040d07015010360700383e0b1030000800318000c02c01005010007032400100c500c02d4903101e87d80d080c00741c100c00c01d4010004400c0200c800e0902c1d9090381940c0024007141c00544e5002080911300e403038200c50240381e0b0000b0100115030100001035002d04005402a00c0c0b510050a0301c0c8641109030003070780a5580e000c0042070a0402c10300780b03441240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 348846007 1250 348844757 348844759
    0x90e07080628180e0a0303051608040201020c220e0307141f0b0a150503100803041a1b0a0503040306050705040b1207030e01020c1605062d04150302271e 67
    0x1401c0350701e1020309814032a0060059012239106c00c18407244980b07019030b01c02038849070301e00000305003041d80c0002c2d151a0700e04119403050450b003c0b134000c901c05030025006e986032580b40820562072404181d5842c0d4201000640b0071100c1c4100590080202084102002451035810b81410b284585c01070010301405240c80d81024a00001240c40c2e8441d60340c1080c0f80006441c0c185c0c4030300d4081d03d00e241c02d80702d41e04000c8094000380010040c003460840541d441540d0101800d0311020371248034803541889490000d00d9105412168081c418040001c0c410780307006000620096450701c00694a900c11482007459102080180804d01d4008141c0e20342c0245180c41d020507542032030808c02d0700303a8100034203100d007642007415070020f004801e201440041409030780b19400d000ba80f4128075100081030200c01118840088130810825800c0115805481d9500410080c0108070000400a410245000340100c400c80c1d8207568154080e28941650700313005054a240f1844210882504a1142209 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 348847257 1250 348846007 348846011
    0xa18020c0109140613022b0203150709090908040e0c120109021b06090607030506060d050708070e220b010306030c0b0702090f0103050d0f090e0708062818 68
    0x2040210000c0c003460b40d0700b50140c52120280d0010700d0415080000140c035450034483c10003103260061b1140f1540302c07601035204a40e0b0a014071540d22008002246550003540750107001c0c6030140250360000203501644c09a5150f08266484105040483d04011000b03040090180010840ca94142d1103045d4009010040725060804103030702101410403c0e0810031050307401242460b9664108018425542c0c2100000c060740e00380809455107603100031b0300c10010162590000303030f01915500700b12007a20011351020422407600d907074028540941a68a40c0004da03400c4640f5400d450030030004d101a81c29203103250204003030999280c00805035406101e05140d210300c00000403c010301d0286005205070384c83c96036104128030411000c110300800c00c038012040c42c4010b00100b44002070042c12003456051032a14403a803241c003070720080000e070311440099012108200c400c992002d001401000280c03585880802420740ba100c3c2000215410342038180714040c100b0032415040e5080e05401811000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 348848507 1250 348847257 348847267
    0x30c031b0801020a02100e0102040612090203071d09010b15180432011a0a0c0516090c0f02120f070f020306240402041206051906060f08150a1802 64
    0x1d803420381c0c02202d1000090b070449215111a80c0c140c2c0110f920140780c8000071032525003002c4016000b0044a4240580240d031001d1650440d20200042070203800120030071203086905c045028003006048411422950800d858030015041032404001211901c003440c0f8100310082089030f0b080d07002403081650143d2122451260740c2c2d003001d82e915966042060070100311020910711420b030401a07008004110030a028911303584940015950510010319101c00030001504085d0b203042c1c90800c0105086180d02c20001d10544a90b0142e11074200540710040100f035804826a124058000021144442041494011051040145a403034812840600e407031b40e4580110340750090456400849642144441d080c10b000106100400c04084505603d0241003000c0e08090b10102000181125250f10204540f02c110410203204100390220030044d841e030760304004010f00500c2c2c0311030021644c0705020410001003140500c034424805030100c0703c1d491600005032800c580140c11200b2003642402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 348849757 1250 348848507 348848519
    0xf080702040b0901061d0901060905090411060d05010503010f05070503061c050303090114010b0c100f0207061506030c05030105030601050d290a141911040b070b040309050a030c031b 80
    0x210007130183c40c003a641c4640036007412001441c1c0c2e40c461040e07244221180c40040080383e03800180c3c4000d840701503e10b0981d0b5145c80c074104100c2c0d40d403c2d02c603a0384440e01040c61845072100b40d02590480d01c0c118024401c00c08000c1e0700c101150001c0d56904009030007000022310b14146104d0b007070800c81c40c400310303201d03404010b80398241540c101343c0d1860344607511599907982030700a010145000d401e580302210703e00491b100c1042c0e070f5031954408803d10140c44035071050003075015a069030303082c2c0c0c0c0150b0107020048540244444d500607600407400030034135003251891094414400d80c0c1c103a581c054000c02c0181d0038030003000401403000c41c0848070031441000e03090785d0041d440209030315401e50b510f640002d0f040c4001c51002ba111260b00404e04089a94104411489107804503245041030502c00120040b14440b001168030582c1c0000100c00c80c0010a541005002c42c1a02e114074041e9442081060300c40003001182d10480c07001500300030030a0800d00c04203040a8001e03c8055010f8045409155110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 348851007 1250 348849757 348849769
    0x915050d090b0103060506100c12030b030f0c0108011a0418020c070f03050c09072313030c05090c130303050d021b1501140d140307050304030f11030a0f080702040b 72
    0x420465202d0940c0004108100907070117000d0b0025000c845444040e070307141000500c241c480010142100480040a000a50183e40642d0301100042d041d602e4142601c000d042c2e0311401c10039003900007240c4c0400010f40c407688000583c0c1c1c2821070f848440c50300b441c00f481104407504c60b80303500701225400c101030703080c40c0c1c0c003004060000c0403a03c1075400e1041c03035414214206001208000d013310001c1040040c0c1d194402c20441c0e51040c80754140803141140074030f041c1d060051103c5410501c9451001100784024550004215001110a03800390361342d0300000000c50081803448160307a9811101400024040c1002d00b00101a0348001418040010f02501120000f00409001900081c9030300009280b030464080c0902440c1040c0c10342030034040081010424031035000740c2100d40c030342c1c0d4509003d001801250700c5d154000341220b403650b8480c100481c1c9500e46080888656500503500e040c0c5080204003400b101d500560544800c11940d251401e060340903500c1282c0c410364a841e0561070359104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 348852257 1250 348851007 348851021
    0x906211003060b010507031b2a08160e07080a020f031e0a0b0a0b070606030b0108010b0a0e0609010608270f0706110606061c110d0b100915050d 63
    0x16203444189981403440031160500049410040c00300700340e001181d000146407842952001180b43d9080690034240320804146a500c2c1e10a18854030b0364940110940701d1200b0b84406000340c500d0b0758440e003801c4146482e94402c1c020030200c04000908a18050401554403100b800e401516002c40010120400d074400c45241c580300340c52240148001242102c90b507400216903d042207501d4090000600d6410184180741086500041000030041950001c000a540c004404961035071100722081c0070708000c80d4038500480300d0010001d40d0000c0380114502410700074007403a400b64244070707088441d04030040501d10940e20308107000c40c034a4050040126071540c0070010b000011047da0380300d81011a254081400c2060558101000100115906030094021500140d032001e45a120042c2c2071540700c83c0465a6150a81c040580020540180038165103110100401c40d10082008504681c2030302050008545800602030f02d03442911440191070700742000c600b810035080e841d000365404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 348853507 1250 348852257 348852271
    0xb0a0c080a0302340602031509090a050d09060f08040201090803360f0d0c080a080901140a0c020f010e04020403060b130b10030c090b0a020f0c040b06090621 69
    0x300045550350400c034480c2c4414548844c800c4030b40d41215811200444070341c1824040c00c2607500101140e00792280050036084000d0250128089245c520305480d01c5111200c0e040d1414010940d0000c060b45c410000e0401741e0301b40c1d403104040a90303030000c00c03202920018003c9051044030304020414038410070180c035000000321039403040094903000090841448900072100952071010b03200d1340d5074030107203c1080d0f102c0c15145c029102c00d0900b04078048039074513445106c0901032482c4900521002c8c80c001c00e50746401f80c036481080710300030003a940c0601c222180d100008041d89066001403800c02402e40041070305241c039810440e05c01d0002000c03130b48158030441c2c1065030355034010080c1c2840000260a041034502c100300d074000e850085210144803090350340030555151401d1b64894002c1d031003100039042d20445240c0b15110804003940e100428003100f601c510078081340c0202442e05020383c41d2044000740080b81018001030503c07080d5002164041030011a400c40040c24000c3c420078244908070f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 348854757 1250 348853507 348853511
    0x1080a150b040306021b0f100209041103072d0e01050c250302030f01090b0609040c030c12060b0405070203040b0a0923010f0c0b01030b0405030d09030504090c02160b0a0c080a03 78
    0x3151400c01b0000142811502c54541c0040803220b030b25080104007050606080d00c4050b031740300d01c00c02c0010014450010b190741d203e2000f0040c040d003d0741c400c1c903962a00318641c0796000c8480c070b800503900305900c00c0d407224070019500080001c420351084002c0c1c040d007032524044452410505404000c907548804001012404d118800c20552908000c008003500716031008200003140c50301c80c2009003034010052030007242c525000c5030170803000c0180d800066803c40c40c0360065503110031200c3e80c542110304080d210039040c0b8031030b401c680c0742910070742c0d0140304981c00a61038540360020080064004240e0b00092005180c0000f07084484203084402d034a0000d0781403c81c0b00001c80016002e02011500c0600b048a1444044000341c141c84015056941051040140da511b5203044c40c55441103090180d9500d040c500520304041d00200540180c402c04c50081c0026807807442e040341d4500404402c409410781e26482041994800c0b4010000d03030f126407400f44001c13007507926850b01c0f681c01500c000340007175 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 348856007 1250 348854757 348854767
    0x12051b0d211116051f0204060806031f150306140a05160903030c060204032012011e0f090203060c19050405060703080916030f02090105010302030601080a150b04030602 74
    0x540d40c01c416503079840050020071803000300c1e0403032030301c0790042d051404a0b0300b603009903000c10f2210800c0f00c60900c81403000b8032003a190344409a4006504144918800304080c2c00202e0b04914002c500c641400c0e400c10200c90300950803a404501500c00c000200708900c101540c0400800e0260044900070140901c203291030b401c21074101401c44000401d20441d0082c01c4201e5800a80c1c0990120101c0b0381510b400140c42c0d4003410f00718003c0c402c55200800e24540e0b19801d101c0d0205d42091a47c018400300c50410444103c14a598262202004088038242035150b00c3c60010081e85c1c0458200b40b42ca0b400082c0440b11580880d15004050311541d0b0400004111080301e4504c0703144140c3ca00c811440c0440c20103103000081541409402001000c0c07082039000200540001c00007600c0540c00384500c00c00c50380d90b0741011401308084034030907402425000c0000c16994082e0003180d018502c107035101600f6540b105642d000910503e5000e58000001c01070009a0980c1580500041c41c011400103a0350 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 348857257 1250 348856007 348856037
    0x9040606090908070b060f09070809100501060804021002061e0910020714010b1009270c030204080708030906042105030d0b04050906041709010504050607051f0912051b0d 75
    0x707517030014640e510070710301982800c8407520f41104041c1c0000403810310240300d469840b0310a0610344903070102c042992030800006841075100301c040c1d00a50080d1000149a460010107e8841100301d502100088603041501c42c50100404090b900c200800c1c142c9549148031076120080e43d11190042d940d812072000302c050a41001c0c0300742450f092040390a0792808010350300262040b009403103400c3c030030030b8080340260702c04101c00d00b0000d00c4801c0510401454158113000360082d00180038007091407191020124804034000211075103000000d145a040c103280c4100903250390028100100703c8440c9207254800030388100058076003444180c40c0071840d40907020900040715401414080700307601c0302091102148404441d0300c3c800d400040003540ea40440c1c001604c591041754015900300364005040800e01c500820207080003140521084281c0a10b0501101595031000000c0c024408102000500c240503030700512041d0303842a1103029506c9a00c01003810107851180c280701080166200b280c0c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 348858507 1250 348857257 348857273
    0x41b08010e090a030f03020c01090b010b0a170c1b070f09020415080618091f09030e0d080904092a0305010605010c0c030204090302150106110c0f0d020904060609090807 74
    0x44215801d008001c00625620010117002d44000814145640014a260804401c1d0840d60001d40c104001e005c895a55080c160201c0e40122081e0f80015642a0384000b4051825000c90282030700030b141a0030304144151a18090ba0102180d1000e44280c0b0342c0010100900410710004040e40e1600588442c54211540d0075044008401802c2000340c01c2000025a10820400da81080451a0700b242c2e03514018021320300b4014084107084070904000a2460500c030380c00884200d803103903803442c0429200c0f4040c407101400001c801800380000b40303e6400281809d500045049005174034021011480052080c0000384000443c05806030000061090020034000c0800401d802e00c2c00309500034094a66881d4030700c1c107000081c45241c0350100402414070802004541d08145502440d2a5035941d80160460f00c607071124040074004d40c2458001480d1441c3c41000c0c0580161030008131b0407003503081003003503400200101d82441e078030580420305101e42e119050b9003500c1454100d80d14449030400d609 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 348859757 1250 348858507 348858511
    0x905060114040e1f090e1c021c0c05150a0b0a0f060509150f0f04030b090303060a03140109140a06050609010f0b16050303070c0b18120702041b08010e 66
    0x1401c0e081000304200180f941c45034668014240038195034850400e021000103500300d5807000c2d590300e040490740450300d02c2c0451035045e910116100d0021428894170b05070b0315480c0c4c01d0720031202070340d02440004005000300c0020ba0b180344140203407414038115411029580d84c090780c00c95821655000340a00c2810842c60034001760841085514076075141c100000c1c440d2240120300d5000c3d950341080c2c00390550040f001d440c002d0f005444640c0d00c0390080306030f882880c0c01a20042e541104a400814203402c0088100ca0046101504200702c01e41180c440c00f04503107040c044071055642c0d42004901241d0400803494032480c0e004003034082d488050902106890300a4002c5218982800041040311590040300040b1141d04421036101d0284100d1110352040c000b402511501000042002d45544902c18820b200d00c40e10640080d5140c01c1c21090008140041050481d40003030103050515501c1800303412003070310091011885c0d81e8400d0308848200c40d800600380100d52050300500c00401b101100c41d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 348861007 1250 348859757 348859787
    0x80301030b180c04020702060403020d06020310090b1f11070306051e0108070e0c07241109100e0f03070305060a05010b0a0512041e03020a02030f0f060f070c05060109050601 76
    0x528551034140b0645500f1842c0250f841140c0c0010504c046440742c1c03059034000c54006203c080d01d08600d0a240010b540308440c0d0210b001046800401c28034110320a0645000c8007401441e564081e00d903006040c1c0f1041a101f40510000300300c04030b07034a01c040110034061442030b140824103082c2258000310702000812000c144110350801032045040020f55501280d0b00c00458442c25181c100c04290140b040340d01c09401c4206100c5044180d00450540400c0408019400c10884d01003d803178001c140624015994045540c90007c03a0007031040d200340d07140a00c02002c0d500ba4810f00c9001900c0d081459008907002d0304440200b240c110124411a07004051a00c0901e10b8200a40c0d40100f035481180100100d55003401d0204091248201c11203070341620450070280c4d800d900d0300b00a503581008400481c400d00ca5280110708403100841c0200302282c00318018140c640300d14188281340301000b0240010811004401008164208421130003847e01c00c10019840c1000d0000400050342c802442d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 348862257 1250 348861007 348861031
    0x90a0b09180307080a0504171506011b0b07030b030a03080103020f03070f06050a140720011110110c030316020c040203070f080a1b17100b03040f031209080301030b 72
    0x148410100c00c440c250750f0300c100180e40d80e0200340350070380340c4d40100c0e00000c07400401003262007000038001a0030072700540d11169551103a5a5a00115501614000f00005010100442e43c00107a007054690380c01082c1828042421910400841d1401041460503000181d04034010415410200c08400b1580c002341c000e081403a0401e100e41342000424801c0300100440050960300c1584038030b55011040074821178095071994142084040c1400300e500700880c401d40d04c2d0b4444003560040480000e5000c0400c06444c06102210b41c000040c0102504070702d00f04402c00c8104044003040c0700840c800c184a0708842000d41d080e80d4024a44401e001c0396a000700e01c10010306c03070615040042280f818002d0314081d607035a901c0002640151000329920518082d244c8150000c868000b00d107a02070f098010701000d45940c40d0890001d03020994403402d40c55210400101d008205500d4417040c506000e820030000143c04011034400700c0d184140159003010300800107208000103914910b401000c0c000007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 348863507 1250 348862257 348862291
    0x121116020915060a0302030412080907170a0804120309060806030a0b040203030705060a0b0f0a030c0303030c051909230901060e0d05010218010201150308070204050a0b090a0b09 78
    0x140108016264902901c03954100c0e000400d079100c0004084003281c0c01814054950ba800f0320050701940013510110fa12803110b020003c240703071017854558071a40301e54005001443c41d00e078002e0700c3c1424168040c0307954084c0702c1801d004038040b00c0c0100f006007d111100f4a61003000e0400030a2a14190070142c100407100701800210340c0c0006a54024a410180502058a407880080e1440c4102030b4000c000d409040200725000409030300c2031084680c141d81403211900207070300f00300d07025000d400001d1020115180500100e4443e0740171109003c118208140ba00f00e0100120701c3d10341c020018000000c00c50442031002403440700b40306047c24815056102a550a440042c03c1c107041401901d040015071000c090940da5103011003100107400100841d03803000f8000300c0650100311403410501560030000c0b4422039000c40c121400c11640c008004c1400d18006030f08000c0a0305010700780d403c1c02526240c00d80c07041c0d41c5a01d2090f009882c0000300240c440450340500c030360703c1c0000380085941d035092030b5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 348864757 1250 348863507 348863527
    0x120c14010c030c080310030b0406050103030f0f08010b0c03160f03120b03030703121d0c09180d12060306020d0504020a1401020d0e0a170601060809010c09050d0609060c1211 76
    0x3c400550750352001a0b192a40d030b5603031207418411850b0f80b001e0104d4040d83c0c140400c0c80f03c01d5000a061324000e41d00c412aa800d50300040d83d000b031103410080300052a030b4004120004141e0046d19a014440c02540d01e0042c451800440c41d1a0b03148003550b00441c040c20440406801070141c035800c0d48208000d02c0444800c0000a4480c001c0f0600071b800c1c00f1041a8100c034001d5030b5445025660001303103c01105001649115503940d0a4010031781c0100c007030a000c07032810800c1d12400d004840602000700414908400e0443c0c444405812080d0341d2a2520f40200004c0e5260010381001070180c80c0c0003445190900412040c416554040d00d40d1040072916183c040c1d0380861060200e516500f0101c40100000000c0b9070030701e1300c1d94130007d0b500c04030031154011502c02080481c1280c0855907400302548407001d03980d00b00c1d16490003200225517002010082c41c00c01c03032100c903d600d01440001a9100007910b9a100b9074003005104000500c82880e41504101244502c08116105251003414400114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 348866007 1250 348864757 348864767
    0x3060114060a0905040204090c022104150c020a06080f2a07020d0213060302010f0207080715110d0905030d080105181911030f0901180b10120c14010c03 67
    0x50310038025000010540d000b01d01504030302d001850040c000710740c1c5a64034860103005000302d0080d030006025850b002d00c0c0e0170300700e01840420008200c1c0a02d00d001d183c1200d850a605182c0514820300551090803005039498100d0031000b041d083d03d40f4030082c60107210014002070024410700f204040d51742c80745140034560b4100c3d8025600c6540107a65041c80d8000140c5031003150030000c0d4003112282c584004001c4941009088134400e80300d111003207119010680e200e2041d03000315512580000c130200041100340f200420700c0d440070b09110032040f02c907260140c02d2101407151603010400b01d110401c80c5082c1002414550700c41841e090009506040019103805001481c2e042e82d0b81c410004104114000000c0100e01070a0a13070400c4554562034a01c80c40e6007040711001c510385180400220002d00600458004150048810310192660b58464a500e200606541c042e9108140003142c9038041841c003520481c065242d0b081c007103180c0003282035200c015640441c10042d4181035800007030307000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 348867257 1250 348866007 348866039
    0x3070b0103080c0a0213020703030506060708031311040c031a030a0302061b090909060a060504050c070210021e07180c021009020f0907081801050705091c0b04051506030601 76
    0xc8071100d07940f500d455050074a800102c070030295000388280442e54054203190300808603540310307031020700050350f03003104103c172a0145c0741000d800c0041c10000242d04000000076810142e1080c02c05103002e15038040807030112240c40d07400c080420360300c5028201a0f80342c410141d25160b802c0703000303010300000e41d40d0003511004050301c1100c0034555090004071010004055500a4002404240079172a0680c0101c0c1c2e11441580d410308524038088000c0340b203080074019144203481c0d8801c85031410303071541d00b0b00030780010b0f00e00c400086010b1511500c00c0100300140ca000d505c512039004003511420080c0c00380d03400a0010320000c4441c501021190703419000b1076880c1c0641e40c0300030000788415903400030074200c0481700b00241d8403034000c1d0104a041ca03005041c0600810040803411204c48060795000c1c00c03103a050711003001150041c00088150314240c05c204400b025400c50052400c7c0c02541c0300b211034941581c084565801c080d0705004803254801d0016404801240109815450141940000125 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 348868507 1250 348867257 348867263
    0x6010206160f20160e010f0f060509120d02101805070302010503100902030c190903170c030408100e0f07142e050903010b012307031106071e0203070b0103 68
    0x2150080f00d90340404000d8204820740c1c4000d54900d0040940390030b400404500034002104207010020450880840c07a42c8141c560041c07207502c82509050301590580c0103000b90551208400341d000e0540d000c14414000307034514640040c0034011a04480780292641005207100001544c00c5504c045039000501c28102e070380a0030b00698940ba07001ca003c48001c2250023850406000005000d00385040d0001408075a100038164040302103d00d03000c8510310b00900c4050860444407500c1c2c1008501c000062000070341510480e49019900c0301280d007000035541c81600080d40e2007007815100117050210000e44c1000c400601884c60600c05008408180c00c0c4805024500c81c2c803440300c9801503004502d00b50b0410b08000ca141c4810309000400310707400800700c180694244284440654010303542d0725082d0b40380504205a11410006080309900a0581a0f0400440e6042501c581c04d0601515000d446141d480c41c1501c52802d00d06401008a00c0d000011940100264000302c0e00f058001070540c0d42c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 348869757 1250 348868507 348868517
    0x10512040b0603100e060403090b0315040218030a050706141207030b04090b04140d0f0c0204240f030203010b060f16020a1d160206010521030f03010e06010206160f 72
    0x2103a0700400d24009544e04051101403420885500900c80007030b84505c07aa110342e4402d211a9103c1468000311300090b15161092028802d01c20030501d066006405101c4070703400503022034a080310003e40750500110056515410016080c890307a0b038814420040c064803c4912450711114145410002000908507010150742c1e23000626181e45603040b600302039030880c402c020035090a0034421144103043c000c11a01d48104040000d505006440c80000c44210b600c6249505000340c0030700c40a0440716440b01154845100002000b4100000b030002500030304504088007070650ac1458216810ba0442a210b11400d1107080c551414101c01c841e104030380c0340541c03c0c2c40a000d00c0812080a0390b40c000303204180070717221101c002c94642500c045c454190101000940d00f1002c4050380c8554080c00b4158201e0b015003522031508186090030f40c184c0410f04203c03494503038401c80da00c0c1d242e00b083c0c0104080c0729000007800542d40c0d04000c03554009803406803c030b40c05046548040c1c8218100791174242401f03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 348871007 1250 348869757 348869761
    0x50c071203030b040f02120703150611071a130e0f010506130803161104090b0f04110607080711041a0d020a1814090a150209040f0e0f0c010512040b 65
    0x54400d0f0405050403101400c02c0c0728000030074080c0006074000000c50110b8000c8000010ba07014885e001c3e03906c0d00d0400d012412401420008211202d11a4603007400303103441099400a5818190060b81c2d01043c0e0482410380c458848180c1103250700702c1603000c00c0b2005400800c3c0110701c0c000403140c0e411070381c044481d260303140c0c80440e00000384e8130180d01201143c00086a14281000640d803a02c5a161040206000009040d000c0004403281c071032010700801a0b40c0001307481e070303614070b4100e0b034005008074030314000c1050f0540081c82c2a440044221076007000450410308000d903403000c0b045410821502400f5a00b00021030981a0250100d4184079521907065074040d500c65103031800c042c01024802c03080c082d1203442d0103000703000300c5049594101001d80004504c4200030991000303d40d4003400e0301d00030799000046003000c0d4014506142d40150b0304d15000813080458440c600070f05014102510750b0082d40c0b007815042141241985040c04070401c000b0b401d03a440c4aa1080d805580111141c58503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 348872257 1250 348871007 348871013
    0x9190b060f031501030b101e0504091b0311040608010c020c100509031e33040221010f061e0308030c130306060509060d021c05030d0903030b040b01050c0712 69
    0x40602860050941c103000d43c004410b02c40c0748103003240701c0e200e000b08041000e40d0b03a1413020040e00d0101c040300d103030b100400003d10142c42c141d081400c400c1c0c00307400340901a5545452025811045038000c40d007000c0b02038110b03007160505000300d40003007881c0c900130001c64502400103500c0385c480300426882074290030078020f1414050b00c01d42d86104d00290031a45810240241e02e84028580c944620701449411740c400c45039000031507421100d103008180b1001c2908008111806800e0241c4101c2c0d00c1007070040c21030b00003010b5210802048070704400206445001c4803d450071a132140e00300d00d003a44030f504581e050700011000e00c07004403a40544000c2d40ca035594007004400c1e01912000d4100501460b8001003800b40c0c1d43c1104041c1e400840d2100c0301c1e41c41e1f0720100086210b8240c40203402140b440c0da0150340d61302c114034828485001d00d095901d0a50300510749812150840c200b10b0120350303106032040a0341054883e0f80b8101d4003e0800515001410710f40d9a0740c2d102502c601844000b40101403410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 348873507 1250 348872257 348872263
    0xa060506010903121116121109060303040306050415050915011a070308041403070f0b06040c08010b09010201060b0c010f0b0306040201021510080a0c090f110a0e0102030c0307060509190b060f03 85
    0xc0c4c007000c4c21b414803040352540e01480c003410000200340d82021020107004000d2801107882030040c403000b03000b5403a00d40740d40d40d01406000d0007001030301c0410f010382660440d10154007c081c42050000702501c8900026000d500c201c00c0c040c1c1219401000510300d048030304043e0b90446990540600b00b403000359807a40341141040007150020451404041100c40c200280c1d550601d0a4908c6a40d00c1074290f40c0d85814001160400042c0c10001441080104007203135040005048500040c0b001140d26511540400b013907910810780a403081c0c1d5113115600c0382e0207003482504c43c5900e0440c0a0121030900383c000035a04c2c8402d203030201f40d00c220000407030300128030607503290018505a000d0700c0c2010310b02d040c07001c003d0210b0311620f403402d4200b0000c1301c81c00300d062203071080160302100c20a08001c1301d06411280301d000000c060b030551000b0860210010800c00151004602c5448003241610300940b11504000202103420025201411680009034686008551100041d502040c00b02980000246 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 348874757 1250 348873507 348873523
    0x30f02131a151e0720060406030207051005010e01080d0e0609010f0c0c06020a030306060809281b050312070507051005070f0b2a030a0f0b060c0a0605060109031211 72
    0x1802800c000d445a40b82000c000139281030350040b01000c6007035448409152a200300070340e025500030020031081c0503490103540039041d001d0041045406036104104079204583c0d080c0c1081d500c1c8219240100910301c010010610000c11134a0100000c01640300402c0301802001c07556814040741140340ca8006124006050145810554500e805592590041d407200c0c5904810b41c0002e0402c400030401d503025170005402081c442d402071030f45684940d400c1041e0844c00320504040d01c1c0116808020545004e0070100c250b105007c2c81410500d00002c0503d0603070400000d1051041c20301c611404a03e0100d0710700120f4000343c42401c0c542c000c4500480c1d04c0c0c45881c000a0410700c1c41c0042500b84800c481056114554012503002c203071180c1161803800d00003142c511500820304000044900c0d14a03084a9001400c0b61000b182c030b0054a4005411900100c803040754a40c44109464140542c0380541c640110b42030802465090540d12034100c6210552800014000c003006140444d840400c2100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 348876007 1250 348874757 348874777
    0x203040b1b03030a090209070c0b0403082e05030c0a180e0106120503031e16030b030705040606020f0c041802012708010e0c0604080c090705070b01030f02131a15 71
    0x240e40b131900800550003052076110031b900400b021030014410318060f4540860700d5800c00c000c58032685d16a0303422100958001c0801c03c8081000140000d105000390900b00c000081d05844000c00341000145803510b1894424603200708008081006250110341c81d01018900c64000071030116441c403441405041c150740036000305a4440305040a00001201942c02a60a540840380c0014041d103500c1e150082603800d85240c03050070030300508a0b8004c0c4c0c03060704044000f03420303a10810760311400a4100c410a5112b800560000c950b0120040e2003030100890079901120100507059045402c060010035004000307040c80035009034003101203080d84092064200a002c101081e0340c45030356582c080c014078a024141031280c9454000d0601d0144160703030540d4000801002000842801c101c4450b1002d03040c1002e0201c02c00800c00803031042440c1601039030285103c5a24004d80e441404135032258050300e05146841c208100710207001400c051040d00c40d00b10348192480c045071002d140c041c49060001c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 348877257 1250 348876007 348876013
    0x90503030f0a150602060a0f1b05030412080903250f0c050109060c051b0a0308030a06180213090209120a0609030305090307170d020c0105070810080309010203040b1b 73
    0xc07050503603069029114038040942884540265407040c9000a01401101c01580103c800550400c0c2990300000b940d00040801248200452602802003110b01c01c401d40050000420001445603285040d0522211440e200e415440e20b0b2254546a004091103032001200d04541038141d010544144015640c000501c070300c0c80c1c24075181070a0350b03103440e104060102e00030400004625008188040526401401034100a682e400284849400d4100c0156114031900c101101295100014501c40d01d81040002031081c2045985840100700c1002e00c0c007441d00411500070410706048001c012a54544009600c0f022000006014940d0180344d20b0001e01c1003003041c4061003016000910700900944040145490340ea404d181c0324414024040c02006608000c0020010314800a00380455a82c9005060800703204595080d24020b480710303800610954140300100203c101170310300520011009514024003540040d440740500c4c8103842031120042810013989051245149411200e8401d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 348878507 1250 348877257 348877261
    0x6030c030e030a031e06050108160201110c07091512170903011112070801080a0b1504050901140601030c09140a080313230a12151803021b0d02060d09050303 69
    0x42c010302600c5180345c0d2039103060020138100c0382e10784251811b030f81c01a550080195290120440d480c000441c01004542d65101001c00c408070a2000c1c1500360342c00e5014000d001e26003203003441503900041e0028100d090190b02005020400060301000316404000c00c00510403050004500303006600c101601035081502843c01c14991800400d81c8a0383c01100c54141c1d15052000c8504d14824041c01d503242d40007050b2140403034a010241030b4014644102d9140d41d6160700c0c045800d80b0000d450031011a91148070340b80b41d00c000480d403650701c100b081c60100086111703904024a000681e100b140c0c0c0c2078011146030312484d11200441c4002d00010011a96102d114500c1003c1040072440b480d40d60585643c0c800300740401c0c4001a4681c0f0364024549460b09040800c04a601c1005810403a00c180303607000d0350340c3d404002d8012601c45004040d14803202c05c3c2c46042c01f03070916020124508071100004032181055843c0c402c1c10002c141c05664054071003080850308001481d541d80090801d10000c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 348879757 1250 348878507 348878527
    0x20c09010f03031e090501080c090406090e0c01020c011d010509090114120c09060105030c07050a03020c030c0909070e060112060b180913060f180807030f020a0b0106030c030e03 78
    0x407450007140d10030b42e541d02c04410300c034040b0680100403034046400240001e030100410b61041400c2d68200300c1e103480c0989405600780004040710b00c0780d4845058551070b509115003800c0140401c0c50b80c17080a00241a1102c550000207240d200004800d480c0c0c04515103120040d81d1050054445416024210030b1a5503100d4100600180007104624494140e02c8076402140d480841c8000300d822000e4014191503d6007001583c46420040003540000303c18041c000105008000c1c1c45c00c5d10340a038004d4007a81c5a40018941000540c807941070040000c41e050001c201c0c00082c84404480c07a004100c40030703071100e0b00102c90003a4621140142e20b4113000010034038051036801440044401156645010340e14000c0c0114802c00f1a483e00c10340080a03070040204100340c02c03000c3c00360419000000c03103400d00e056112240c0040304050f190240042094001c041d00000f05245104d901d000900c0302c102a503031030004480050003010101030f1251032403c020380c06a084160b0461400003900d4032803420782c1f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 348881007 1250 348879757 348879779
    0x60b0711040e030408010e03030103170a1202033c0a060e0402042004170c0109030515192301050a03021c02240705011d030f0711090708092b030903020c0901 69
    0xc00103560500f11207180c0ccc140551040206c5045200c1602c502000c28124142c1100a410080850554421403000c0300e4001d603a0421062050810310f20b514100c605a202140da610002000f07031140910f4450300344168a405950341d0f40c8039a0465020502e48080d1082d0300029600758125110920045030100b2038a80b5000d155200f2230b1039904451890000308011903026403e1710014055402c645a614240c080000c0d01da80d1190760f5001c4440d06a4000032002d00711032000e446550740b05200707814003422045036a85140108003c40d07600da0b01c81c0c1180c000428601502e0441921450003842440441d1218081e000c0803000649402840701d14801c07040701c0d0350340107960851326540381010503288810b14000c0301080c202820000d40c100300008600084035400b2101c15942c48500105000c41603494401e45803262005946985660610100d490320305a4070700b203182100d0040031901c6c001d044800d012a09011360038500410340407003030304007a41004034090712603401000150000c246200d82d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 348882257 1250 348881007 348881009
    0x2160b0f15040903080412021e03090306060409020a060503130206040303120c110613050102120901020a021c0c021e090a0c020c030712060c090b0a0c0204060b0711040e030408010e030301 82
    0x1060380509041c4566040104542c3c46080c0100420404070115001c650303002d00c100d581029a00448400a185014040f504802c5c0c07074466099510024440115007428007002c1e810000648060082043c03c0c0e0024855050070700aa00400a0200000b4040800c166002100e0307600608810f64840e240e0800601c0d4900c805201c11116050103c2c02e2207141c800c4151141503810703a005894030388c980541502601c4103034201030341c40b99002c0c4281d0034058203a103502d0707014000ca6000160381c3c05844101900b0035161600300040707807600614130a40c00350082d83c2c041c01c595044030039260081c000202900139100700740344580c000d0074a0701040f1a508280c1d0000b1a500740980844040816220416030fa0760080e010f01b0740146501071460b00001e2a036080203400c07222504113492101e45400ea40040e07500600b13000b100040c0e0003240c040950625100c1c10700541b4961042c00d103131101d5522400040540c240b1250700490f40d40b048510400402d00980e40900003440c02801342071b0100414603666042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 348883507 1250 348882257 348882271
    0x90f14041107020f0f06250b01150918020d0203150f0604081504031704030c031d010e0112150608010504050106020708120702030a120203030a0b011d0402160b0f 71
    0x940750900d00740360146010b030780485500a1400d8000c0140109100b843c1c015400110b412110034094440c469190540d4841250291011448a2001c50514011400041e4010005000b4803114032003400e62203030420003961240704200101d0b40100c843c1c0c500901c140810350b00c00070b2001c41404902d40c2020150703520814119242000c0654000030001c051203140b144a00301c0c4d0000e0f8400c618000e4203800558058028100458140d400c02403180f62408210b070f0803000109010440c008054200c10340310780302c1c60b02100c5040c80031140000a0705010001665a0600010305071072070b1040305a82183e41d0215419070460360055403000060b0044a081c060140701d0f6080000110f1304c1840060340344c044442c1c0c0002842194000c40454041d03038000c60b41603030140200c0001c0740c0425001d00076a12040c4180c1e004542e20b1901c6d41c1200100d54265009c80d0404c42d410001155142c03694807001800481158010780d1412004580d071510380b60858000c0c245031101040083c2c46403c6c100280c443c42c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 348884757 1250 348883507 348883511
    0xd0602190e0f0112060503031b060705041a1c0204080706030b0f0a05130e120c15250302090904030509010f02193509041109061801090f1404 62
    0x600020555000000c01078040e005580c0844421041d0b21401e4a808400b503040340000f4102d0f01d800104c0c0c01c40e40408511514040d100900030441c1000700684ca80c0641d103850300600b881d040001c241140311800c06890000341000c00c2030744560320400090b010f13805019000719912507071001c103203868032114829280401d161440c10415801c1c110b5130403880ca0001010354002a090508002c280311010326a440119030f5600518440081001444880600212119112a01180031a01d0004600001650f009000c01400681e039902403400041d071415004002c040e6142141c00c500a0007009030059201a0110511050541003802880e1812081e80c3d400040b8032404800c0c0d0f0340b9101301c003002c500c11110b01c18640c04035002550301c0041c0d42c003088048c0c001066140003030008a00340624000720100025240185141a200340b030314500350584420b0600c584c503400118640280090000710000c24001250305030300c0350900d40c4c007900310150003080d0545c541c0e850308800c2d14215042030040e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 348886007 1250 348884757 348884797
    0x60f03070b040b221211060711040f0e070f1508090303010605070807060f0501320904110904060c080a020403120c06060f0e06041803050d0b0f0d0602 66
    0x4100494480107680300000307054a0503151404070401540700d110080d20244040742e0a00301c001210700160010000d039a072003a4100f1440c20715014454020100c24450300c030400c60b40000403103070000c0240651040328005868034903510294007034200c20005008500405902040340e01141c050300d0181d40d40c240034618080f10040d429200840151485982c0d5401031004111040c403820003440058452940b480c107100c400d40d01e0300155100326005143e040d40316001030051440e0248181b0400c0070744007089901c201210031640c00d5041e42d04c502800341115400242c240030b1701c00041c099405000d4207408080c138140c10a0300080141a00302e20000d802d800106a02c3c04c02d600036201540e030060540c19200d81c003004291618194200d08440584e1a802c0008111800c924484000c007401100050b036032030b048081108860803840c0c801d884594600c803010200354424140d81041c3d11400c4000303007014441e8009001900c2d0244155400350541c1003510812440f500038008000810024490903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 348887257 1250 348886007 348886009
    0x21c0e0c040e07030f0807300806060703030906020705060f180c0f06030a06050907030e1207170309030c1006090b030d050307030c140a0201060503190b0103030e01050c060708060f 79
    0x25400401c00e652141d0301403038050010800f941d26144181344140c881038503140b966912901ca403200903030062028400c148c0c49420240d4080021160b1f038103140340888251030f142000601e01e020f40300001c0d0805545141010401c08031364112070b1566001300442e050b901c0d007681c0c100b400c0641100c0c10b60f4101c0004000d5400c60500180074206d205008140c0d581500500e4140031003608002d0002c0f05131515140002641d44807406501d01500007a680803812004200700c2519104140030303421140c001c2001150f000c240550010303290b0202696040e55251180303c2858a14016041000042e0040310181030380c0082c190300020445615000c1031021040f07801c10103071102c1c413449003000452000c000282076540b01e50300840007405142070410320b00100746a0840541c00050012015030354461060189107003c00c5030105590500e68407004080391559085860b0206100040500585114045840c0c0c007400c180d0340500c0c00d80e0704a6809151281c1d0007420716206448142c050611040082c4c21 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 348888507 1250 348887257 348887261
    0xb03011418010608060c0a0c0210180b0316032012040b060409020d060b0109030c08031e0403050a0609020103020403061b0f0c030207050909031207030510051f03050604021c0e0c04 79
    0x8840e00c10300a00100da03101ba0349640107a200e201084100704240c1c08802c01a690038440b24440b101b1543c45000c142c2044a09440107401e941100180107024403c001d07200206580d40320001a00e0300d00480c800740c43c0f88600c42558140080c0410b4a0f00c0440c206030120101c84025116038040c004a1429460320820701c000c07038165003000794200c920b0f002d006002c507100d034200810500c0103240099410b0f6598407003100136500c1d0b4003d41129040001c0281d01745202103001940c5040145c070403450640740d650b030159101c2501200502440e02d800c21402968000d44c142e900031a00440140684100316440760366030030750503014102280b030050045110750b1089050400032075140c1c0040003000e060070100030020380c1c0207040c0c0400748070411003404285441000c66000e661f1030f13100440e007810417424a090318185508400d001d00d0350740f40e102c1c84c0607500800110300000f003401c0000d42900c0c2c5030b011038080c2c450311a501510910600b07094802030b11030b502c42d85c0a0303000e800a0312134a0400ca020841 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 348889757 1250 348888507 348888509
    0x60c0215040e07030518011d0616090e25020c030f0309010c0b10090207030504150e01170603010f0e03120a05060916030e0706030506131506050d0b030114180106 71
    0x20103814080020f481d85029034401d581040030b10b05400300044c58010040e00751940d01414035152251079410707110a010411010341c101311403c000216a003039001d030042c44020188910100414401e000c110617001c2990303a480060340203401c18001d14190030f406507460381081500e600a201d80c800750011224080256042418141c0d1500181220f0381c44030f41c58800c01801d808601190f000000420412a1006001c11071290300c0c0c164540703182c4880942005c441d1081c03041407003800e0080040796a4040c001c948006107070040c24800d1380703440010038010300764100021b9010703240c06810240160004058103e03a00c000001d0700c0c03030740c1d01c429001c0309a1740c0c281c070201c0e0001c00711800310b0b04255280c580022000401d140003d0f40000311840c4502d0540141e00200200750744400f8080182840340608110b0400207009000c20003018081900d1001c8034815501081408290140341d2080c68100900311800203009008007102e03032a5104050b40e0a0340d002811403417620241c81c400106010b400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 348891007 1250 348889757 348889769
    0x305010b03011202031c0c120302040501080412030b0d03020708120c0d0507051510050a090902031c05160c08010c020706080c07060f0e0f060907141302040f060c021504 74
    0x241143d20f40030032540c180e401c40c401260715004040154074403003c004a030356079a03002075403118411005800c000400340781100114080500400c024400784e40c0228040740c1055016140e4041075800500c01c50091512f0389240354099140d041c510103040d40001c0c20000e071404242621655100c4c0100d640386881128400340403500700d1701e00030580500038000f400c0528045c03000da500030314002040030003604086417241851039070f102c0c061000b802e01c008071001410000350200301a122640000c0d42c0d916142d281d40803008495a440c3c50402d120b41d051311034a10300c008100b05809014035040390b0022903801428801e40c078024130303840c2e81880003440c882150301c99244d04056071a002420032140c0c0c0440010f94105032039020607440e4070700c03a01c9895403070011003018000c0150b16501e690f00b0146e024024140c5544039503800d102640714030754980d0450700c00300c0307030a0312146010311a0006402107600000081d0f03518200051015080014546040d100b25400d040d01912030417040d0103801039010794 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 348892257 1250 348891007 348891029
    0x40f021f021608120706060509190c1b06050c0f0a08041a04120302030a091709010e010509030c0d0f020a121106040f0603180803071d0a0b07031d031e0607030501 71
    0x145044020440003005c406006043c0480c05580700d41c00b2400b03440b0305541c910541118003000203900340c1a442090380c06409854030104030305256080c04000d0680e1172010b0701d0741d0b5642011a81c800c503203200f181d2280c19489075503900e4480010000d010024200d45c240d40c00080e440c0000307885541d019606125981c400c1e402c1107000d209640480c029000180110000b65581c40e0420100b802c0c60060031840c0420071580d0760b01c03290b241c0010802d9064082c2070f0f041c08018400700441d60b4011030782642004081c0c5040310000304c0b0742170001b0900090741c400394112128440104808003c01507444289015036071104072400c9441c00d00005104922a2003451021900d0601c15180310b40c000400c113179504048040e48240d035841d0704c003441c0c0c0103aa482010444120350280c0038204a01c9641041e20201c56084841d40303040b240a410f403081c0000181001754140c98010014a00d22110344815009402c45a00c425540013214100e2022180c0d1200d44c07041200103a100351003400f646060b21502d680d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 348893507 1250 348892257 348892273
    0x91a030a0308071803020d0f11090c092b050604120c02090f0606130b0a020d0e06071101050408030a0807110606010903030e0d0501180c1502060c03040f021f021608 72
    0x4201d410718004c4004080901c01c1d00000000f6941da074203c01e0582d4041d0b485000e83d0b40300c610704a580900c00401140c0a0f9050354108041c1c0c0003000e054515506060368169648049c11282c0c5040040e420f840000030040c04030a1030601134001fa04034469446050072541028164100f036030460540c0703100950225241000078907450040a0783c50304000003a240d10300b808481581003d140174036410500c07040d20701042c03400c400c0f0343c10800d00500404900f0300055600c1172030b0104000b445030000191928900c1415241c2c141d00c01c408480081c8154801ea94680f90001d1004200c0c1006a070080000703605004000400000803980e035004800503121194024070307580d015502c0308800034420781c8c41b616403400c000c00b0400a002c1c4502210301c2c0c0007015140c060368540350700820070b2500100c5140e0f04048100034030366000038207540c100609442650f04d0b50765a01d405c40e5550682c8d00029002000c03c1c082180b60001c00408a500900d15006d540300c2c60b4010b030f854400f02c04640310310b48907035101c000c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 348894757 1250 348893507 348893521
    0x20d0c1404030f0f021e030607050702180603030c070b0a03061d1b0f070b0108070b130e0a061505070605010519090506030708060f0103050d08161b0c091a030a0308 72
    0x10840d408030310031364440b03050340c44603000a40d000500251481c81d22800e03425402d003901e170900070540d01103403030b00305103052001640100d0611030750465414000180301010070344503135080058400100f0120115140356440b603d041c0010307081028004d02090411070b01240c10000c041054850080007400306411342c0d1081c03c0c601740728a01480708c842c60a4100009a10a000b100c001e185842c09115403000e19490a6003881c80d245d05640410843c080c03d21680f0680d0103421030340412549284a444010b80391040b40300014081e0343e2180b4201070581c02e01544454104c0003400611340141300820980e82d0341e82c10700100e10480c5500c60710300b0840b1f50041c002205164400c80e08240c01400300c40629803240742c0e051401400b0365050040c040c00c10010010000200302041e00d002c5140313003841003820081c84262200807800104018000340c0919244824141c80d00c00900707a8202414400181c1d0750319418000307100c41d5100000103902e004e99540c0c00d0030700064494006906589032041555010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 348896007 1250 348894757 348894773
    0x10f2003040614090c0a090e0d0815090115110c010909021303060501081f1a0d141c0f0207030f030302090a0906030602090111010b0a090c05120a020d0c140403 70
    0x3070040722030581d00c002d90340360320841d618030510502001c4002c0154100303020800414409079449442824145003090266030004951895001c417a4100300c035003503d41c0c000c0100c902c040c0c40c2040d50040c806d0400010405549620509110006d403910780d041084800c085448404a04865000c1098040100804202039000b040e01c03513588840814420b4480e0f07150002e9074400e174465009640f1000000c900c0303030286c0b1090480020302d50b808111803d6015220042c1c0000994603a21990300001c40d8410302c0100391204800040ca241510210307590b10481901c43c421f0984103200180715240300e502482e00009111060320b0700300f00c0e941c1c041c3d049580c003103010b580100c0155411452407000010524881c2c01400c02451043c8005a101c02540c00014098442104c0b0058643e0401200c40700c00c0e190b0b2500c0400b6280c14480100c0c4100005000351250310a402c082e840010002003003094101865000e800c1180c84100140708040110724222403c103c0901d0480d1400010030040001440388 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 348897257 1250 348896007 348896011
    0xa060503070c0f05010501080c180604050c0d09050a050c01110c190f09140c040311090402190f2306032802070f1b1203030e070503120c010f2003 64
    0x3482c020310700944554610007032400d4024200d4060703450b02c0042c492030a06106140010780140c64111107802c00c41d1401404040251265018079583c00108804030071804c1121010302039014140103001c0d0138a0328540e103000c02c000582c3c060180c8401c0c0d000c41e40c4a100c0c0000c145003904000e021525405042101c0200551340101003030200c044002070001100c0700f10001080c1a0100056102840002400b08140102104c1840004000900c000b40312020740c030466036030076542e110440c0e60381e2000c912454030300e404942207040c003100c000901d981501c8683e030564241800d0940f0010044000b004400b0034000b116500c4002840064204240c0401c000d02100380f40f0032030382488101046e90012643020361002d984902c6c1d1610703c07005010006c07440e41710344501030352403403031007490200e555207070200e804401010141c40e100c25440046041189001901d4000d041c0d800742d40030900008030302e41c00044c905481e5400c15095010030040c5208010720129101510001d09586030343c003850580c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 348898507 1250 348897257 348897271
    0x17130b131e0801060816080a021804031709010e10020c070302010c170d230106050a030e0109150c121a0103050c0c07090e011103100e060a08030307121a0a060503 71
    0x14480015079070700c00340240c00044c030660001d0401c0f100b070090100c6c2c5101c0503422690b0340f1307030249048100585984100e50f07041d84803032001d40555121490b04590002da0103132250120f0900c403003030043d02c2006601050804e140c1000b03c0311051540402c034000c2e809030b01409051500b00303200400c0554007039600d204400e8400c900502029907012408044c0f034205100301c9590030740d2000c840e4603032540c3c5910f05030401c421040d420019850000c0040c003520504c41d54908164654034050401c0b10250000500e499019a502c0385a04800c0002c00c02421050702220000d02001d450341d01064982c072810200b20420100c051121303220000650203440050881c00f044c81d000c010402c03004c1401c0c00000701034020300c4004030b0000581c00641d030a40304110201c00d680c860400c184500100c2c55516102100da0f211907595541e522040054be18600d03640c001d140c0ca0000208104849520200c10b840307040c8441d40400402d0304002411440041c0c02c04165001084100c0502809004101450780100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 348899757 1250 348898507 348898559
    0xf0e03060a0e0f0303040f170c0d0f0509030105010b2101030c230306090f0706030b0603061c050303190f110a0c140d1d040903120203040302070317130b13 68
    0x1010444880c619170080340d06807140b1a91102d50010408480c107928541c0019282c0d540c140031420b05941d0b100da07403410020062000000091701103d0040d002e0360f81c0010014000c20180d0b03900d032603407003050f405413503482850904000042414200000300302e050700d4000078030034101c03400d20000d102a2042c0411540c407450724030844009d159006c01c8103503c41c3e100c14025000020a0006003480c105543e04a8030525041907030040c000d46507041907980c40002142e030004000700c82c40034062007064120019040380000020800b0928908103581c007100c1740d51404100c48800e200c20b4804540300b15451040d02a01049024503c51258800b484880c0c000c000342d60130b00002103403103441d00809503200000b18030300808004c0000668500c1e2030b0800700680e014030005000d5a0001c145e04c00c04112608029400300204003454820410340300550340c0031500200900c0b85072401099030300060002c0400440001010400c0e440210644400204215406500c141064072a40034204503054402d4903003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 348901007 1250 348899757 348899773
    0x90105190315151805070224040204020d110c071e06030506120712050106080d0503070507150c03060924090e1c1701060519030c0507061103070f0e03060a0e 69
    0xd8070b0300803103900401e104c40540d441c028100b140101610b00040c02c0c0070554024400e038410741c2d0031112180d401c2c1c040008112a60f030340d491000800074000d9038291022a49061080140040714030000c0c003113482c450703040b607000c0342d902c0301d010164101c4a0300111440c2143c03801040f007035010b6004150031000041906503a42c0a4801351840e040103540001445500c010b061010f000082c801c40d00580400006800000300d000c402404521014040d10204500000c11009014040c01d0340ca1032200b03160000d00000e001e024008016001d44c0c080e9107030591034032040300c0c041002c0c0c0c96501c1851070b030451a00c030114907203000c0c0d00040000f809040042d000e0fa1451035502801c01c013400011064503103c03010030481d0401d2a10009405070000c0083c04010001800e60f840c11204640c82540c003407030045021004a02c00312818058080d0091103d820801c440c1c25145009020f0351003050b040d5652080e90b01e50760411070708510b1440b01160160040ca004c102c522080e500b010741c581d410b15017180c640d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 348902257 1250 348901007 348901031
    0x90402030c07150f0e030403080f09131103040606090c020a02040b0a0b0310080d02030c060a050402041b020a0b070e06040308090103060b030108010e1e030a0f09050d060605090105190315 82
    0x216a450b1251403c0ca954a503c001946450711078110420340560040d400c0c241076540d035040e0341c8921800068910170101d1441100d6540c90700c04015008011018060345020428031306013504151b50860f940c5061030000700794491184500a40011942d000703103440a1160240801003040280d42d030b8120b00310360400314004101000030b50045e1707091801444100d00e0000b04501b4a005500703640b0840d0820400741c00584400100d90360042c08041c07001030503884610025008080d0303c01407000780c2c0c0095111400c520303000300d014010240507803403d10301c41e920311074110349003510845803a50201090200344040380002000c1c00c0c9100c0306040002d015900e1b10390b0003400350002d0703010640eaa9152950301a40c1c040c2400421081d20006045d07010100000c40180e0312409450101070400a860300d01d1500790b84a400300200a02004e81156503454207400c0c1580504942d00545001e021001e00000706030503d000f400e0500d440000d58544034a0469a94099200840044191064460f00c02c460f103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 348903507 1250 348902257 348902273
    0xc020c0f060c0d180504090206030c090402071a0603070f0807121a1f0806010605030f1506031906050306070c17041a040602010b012102210f07020712030203090402030c07 75
    0x81040c3c40d00c0d070010f0103441c0102400d004070a900814011420310050f140142c5038281940c0d0008501100103860f01013120200f0000d006000e8064498020000710040d01440400740502821082d001d41c1c94850311862451421821403060035031302d5120300c3d410082d003c1407017a4002d040e440381c40d4221910740303950001a1403d2041c0c6000d03c1041040e00101e00000311848114001d1282d40c000c1c0903558589035003e010b601000300305070882826007000480e4030310320400982200350003c00d00f0f5100c0c24840f500c8224804016460744501c1d25240000c15107150002c3c00511035981a91003000b946c400c1c0d541d400001640c5500300200610900c00810010210707900d100c883c03125a0055502c440c43d082c0001d09588203180903906114400180c1100c0d1000401208803404c00581c0c050780e55080141400c0e2108003100e00d9000462040c1e062017198048800c01a00920030b80c0d0845240d903880d10701c08201b180440c10010050790040242c44d2090a141d009154880002941c031410400280c03180f440d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 348904757 1250 348903507 348903523
    0x13140a09031209120f09050109140118030c0503070509041203020c120c03030f0c03042001090b27060c030703030518160602010510030b061905120601050907030c020c0f060c 76
    0x42d8100100300300b001a2035201002000c090700a14190085a147c0f10010b000d0044500545c40910074a10720001c20781d00480c3c14580400c030181503c842d0f260750b400d107a00003000174045c041c400e00500c1000556440d10002c0c890086403c54a2811203405c1d04800782c00a50091018040f05d000702c10a89040b0680310b005001c1144001d4003860341c901c1d0510004004000003440080300e804180140000304980e425600c80006040300040400e100d9000160703061141036101700d031009000074040049203207507025510032040c2c0f41c0402c2510b4030084100401c502400003192130591060100340702107403094002980102d003000d140c2003440d200c20b03201403d100300100841c0540796100307000c0103201d5091081641c4002c0326035036002e0040c11540c41e1452070310007030031492107819190042c220f00702e0044c0d0448001c000040080102c0b120280950307032583c10074132070b441c40f8900160000c1c00003030003405200010000740d40a410240801010071503140c8500881e590022018817201d00b007494100700c160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 348906007 1250 348904757 348904763
    0x30f10151206050d03020a03030c09090e0c0907020c01120207030e2806020c060a1101021b06043003020a0c02061b120f04260a0c0513140a09031209 65
    0x24401d514404a100549515a11a40c09958a01d0340140440e81c0400c2464560b5811310700480c000d4980c81007107a450241e0f0f005044403614043d400081d180000504844180f4192020005580d80e0b0701b044e40ca981d1580805400300300341e800b07908185580d0f03074010300b0303007c1c40f904010b00f203090b40c00c001c00e040c6414141410342910145e07102084291a804e02940103104520040c401d945091000c10640d0003140201000e00c01e02c001b028941b2602901036503184011500500740506941c040b41c1e03681c1c03500752002d550385020305600401e0003903c503818103000e40c41206540c0c0c4280045400b00d0007540205401d00404c40c810742c3d99001603440f9002884014115020225581804c0c043e60f030405292580102c0c0000080102900c4510502c064504584081100c1040d5105c0442200e0384092080404e124a00420100c2c600300710207002d20b1800c0d02c4095a20100d1001861512404c840030700d0031201d190b9042000140035007159400c10980180710345048024007200a8000c0280c0700c2d800412 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 348907257 1250 348906007 348906017
    0xd090c051c03050913110a020328090512010b0d08180105130603180506070f2c10090f090c03050708130f0812090c190308030f1015 58
    0x20841071800a6880440c030307200109a180c1500c81e0303076026043d0721460342401d005582d084245451419160321611044410319106691000401c178000d40760f5002e81c5d003080d80400421a4109649035200722011020065203c44507428103010400940d848032580c040d50b40d40d00d4038000c078401d8440c0d1049d07800312445840e440d511245c00e05011251005004405070400074280420092a003085c0e90100803140d650a0015614203203c00c503005204034100060000c2c454442400700c0b695001c0281024400181c0d2500c0c54105400008586031045a036010003010350803885001a1400499440107120340d800c004202641d11b0a00044080542d44400b0036281d4910084420b0b54040c0a00c40d80940e45180c03019152500c081d00a12848103103030003400c01c0c0c542002c507004000300b1008070b5070f0803080401011541d14041c3c80780f42c0c4e00d1800d095114021380b041c134208110810040d56a02c240c81d400a20303e41075641e50428191140c0713001781364043c0981c1001d00054a12406142001210440d07134403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 348908507 1250 348907257 348907259
    0xd140112231c230412020d05030316080124030e0102040810020d1103090601230901150207080601180203040503070606080d1806050306060702030c030d020d0809061b0705030d090c 79
    0x1001c0d01954031801044803881c0d444a0078400000c1080480302645c2d03001d54907104100c007038004985004260b4100802c070303205c00018056540b00302d80070001401d10b00d6440910716a01c40051409a00b1041410041e01b8414090050304501a402208014103084001800c00b59a4683d03145032500c0303207500c0000305600240034115000d0301e01a40600c0031030f02840034078500f000d4000656070901489181041d42052100f070040d05401c002c241c0c03d4010041c501c1407156100c41100e00d00444107000c00c80035104041300014a2580171441c01e0480e003814881c42c4044400b6182c02000c1d510060044540780001c002081c009060380c850000071305214801000700441c800c0000d0800c03010360805a100c3e0714040030400a290744201105c0d40514180d54550722012984086880c011000a0442e0f060080c404410841d80d0700041d005004505544c0b4010941c43d0105000d03192007050b6451210400d075007a4001c0340300107010041008a00c610112807602e0320310a00304e01200c1b5100e00881c0e138107444c004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348909757 1250 348908507 348908563
    0x18060306180209030d12060b030f180f1908040e0405060601090f180c11010c02032a0a030c05030705060906040c05090f0f09010908040b0d14011223 65
    0xa81c016008a91050031031030007548500083e9a41d5204c0860020002c100c40042036405041d00110300504c9a07551031622410458048801c1c0301c412280c2d104800b14500d00e103225100c0000741f444030100d402d406040b6110b410320118400c0c02d40c20b042502c1c411010040003c1c40c0581c902420310443c0034001415982c00c04d0400140001e1081d0b0210507050481181806648807007001404250704248000a05030038060b8161400c1620f04900d0301c0399441c0081100b00c07181c0100003041c4412150030440d00000b0380c0c00d02041c17929a200c5541c241580007400307910000340101111456a4000d40482e800d2002c650707034041c5009811200c280c015044442808100048950364201500c4c0072180c240340c0d03141114000c1c5602c1002032189480c04021004125080d00c2984009450380d00302c03a8440c2e4890703c4488003501640000c09500b105860401c00407036414403089a58140c5038004010841301c01c10751104d01880c0c1c1054003000700d0340e000f01d46510804004011040a82001c84890741504007066 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 348911007 1250 348909757 348909779
    0xd05010b0108130c090b1314040b011a1b1509010605240a0c02121005010e0a1112190c0e040f1503030c0516170613080d0c18060306 58
    0x2401c0f0035003240300718240e00001001c254800c0d040d228140c00004561983c80c0c0000e00245807083d40301c03100c0345495074580c0c092004440742d500c140e000305070076144c0740d982c3c404185411810141c14070310390409000c82074450f1191a2551a1070541c0c000721190322140c01c10700c8000b100d080c0c82c0007036669500c0400300300741c2c03c0004046080b03840c07109560100b03204611284d04c2c035124004d40c020402464144d01c104655071400f05040070006a021102130300e0169441c003004140038040d4142c001d110000081030101c842c0a210003035501c4528583c20152420720740c1054030b6000e0702c0c51b84506d000907820320f89000b5500c5070400c0300400355508840d4030b411509000841e4202a5031074405401c00148080c140d440c190107400305d80c0d0614280c54140c1140c10041e00b031481c085090700740b5014a007400075112035245c3d16800c3c1c01c410007083e1106c5854124186038403600c4041c00030700c038030030510222820300000d6104482c041c101d410480b00780303030584803820f1059003541c0001d00803a507603140c1407103004004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 348912257 1250 348911007 348911011
    0x10b04050c030103230d0f0e0d050c01051b0303040605061e01021c09170c0102070f08070e040501020702040c030507170408030f22060204170d0c0b10050d05010b0108 73
    0x262020003050400001c40203592005020107021955001c80140c4000581c0741c2519034011040195948910841e200030600482480e0354070000e8110000e06640740380944119461a40c000010620044004010750300307030700711000c08902d0417058071550700340000c1800114030840c41050001442e2811004010800c2c2c0b900791520341802e4084051401640c00094207075040e18211444080450290390440f100720040c0c0007103100d41d0859000c0e010780700c0001001d0100c1d640076000c0d10031240c0c580c41c00360301c109054401d102081d444280700b0071a01d560450303c590414052000945820340715008a810b0b684011103000001e981d680401ca00d059101ca00103010042c400000000c034105a16018014000500140c2c2c90b06031641c0450310441c503680111800c42441041c0262003481307402d09a00035082849100940c1903034003494811401c02041c4605002c0194850300c200c0e81d069101c4201d4900014518041040f45040204050382d5010720703c01140d204000200c0c4401c46100010209040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 348913507 1250 348912257 348912259
    0xf1a070527060c07030606080f061b030a060305150a060b0a0c020405060319050718050613090303020c0102040e090706030207050a0f0f150e06090303061008091e0a0302010b 76
    0x401d100c04204900e04180c00c0ea0841039101500d12628000e00004425100c0c41c440e4502074401c001c00082000b000340c020008035101c1c0410341d146007598402d503545860b42110311400e071070a49020882401d101c4030186401503507102d0001100c58030307a5151403803d41c9240f90000e030007402500308115100c8600500d0003604440e00c996045c039281d41400781040b01c0d0008002d1142e45c503000003034016101004090b082d80700b00c895250031080981401f40d1144003034001ca6038000d070b10561014103110640501400b484000c0e180d5510404100c0c2d01500038980c55400310704040d002c200390f002d00074090001d013010740503840c004407142c109000164a80a5030780d00483c10b160050208201185021540b611142c1c0c106400040d01a0716141001e44100d003100001c0400306002c071b451036142c1450340300551581c015012035025484200156541c1d00089606d80d9002d070401500202030b612901174280c210041c0c00c212060b048004003402d0400100004019007035105c00300720000d141c0e090040c0048404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 348914757 1250 348913507 348913517
    0x708180a120806091f05040218180a0506030703020f0904020a090608280f080c190803090f070e0c0a14030103111003021804020307052811190b060a030f1a07 69
    0x405c0d41c40314910360f40714807401707118035400709401420802a007242a0b0040b8000c1019800c0812a072410003000c00c1601c5c05800245068006076180c140082c459003500c4d0010700d141e10b040010070400800410003801280c03c41801e00c170000340c0e0040c40c020f14003d0078050000d0002030f101380c40c0c803012400b52a5101a554082c030a040d5021490840e003060010707810004081e0361740500c0030310a141c0070003da0b0354005949002c01e004c0a0100c24030165000368403183c140c034002c0700c0c81d40c446a0744184a002e1130449801e2040800d0400c2200303002040040d1081c10241e1180d0001c842014494000364420380300d2041c1030001c80711a1915100201000e6814107086081541c43c001c4c0320040100170000e6802113900001040450303016605548801c10303018a800d08041200300c03030300ea02c80110400b81007c690300c40c03241c1ca4481008620308007a0194005400c110006546807a03006c0d0402038006900001407020100104a5545078181218010b800c5003d881404552811004070b0040070081044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 348916007 1250 348914757 348914791
    0x4230702011a031203070804020d0b1501110c0a060305060103090212070911280c12031401050105090d020f04110d060f06050403030e040506031009060b0909060708180a12080609 78
    0x202144c01540c0c0c01080e1880e01156a90345d80c404030b09458061a0050030701102c0b6000c01c254131145454104400e4407ea890000d00800c01c0d40d06070355002d108403407680c403400c01082071003441c0c80b85d8800c680c064014036010903135005a80200c1e000c410312210400340350700070410600080d021405450041c2c0807034a034030351030b0800500a01e41264803250408600d030280480f40c140d858401c01540380840d03000399080d1221a030200000d801014509981c0b001c10140c0381c000540c660217401911010780b400343c034500502000d03608002e007107903528a28075800b503079490615041c2c92011015103003640001c0c0380007428900344018030850f16000e41c010000c001c410403080c400a5400086070342200d00648010441d1b84402002a04081c02c1c40b013841d00040c07401c050001440069000308004c21019101c04005448a1380c125803107213001c0b560071001c24201004a602c04c660004040a140200c0c800d1b40c04100450341d0740c0c0201d280d170020000000e1441c105004880c948034cc5295080110520300f6480c407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 348917257 1250 348916007 348916033
    0xe0c12060f04120207091404030f0504060c15060906060507052a0d050709151d1315061e05090601020a050d0513031e030909060b03010504230702011a03 67
    0x441c1c03000380300401c00808403440000560080000c24094100003a051007500c0d1115484c0701540c00403541507000078890042d1404c00340c042c00071070f8180c0c0c00554602d564452030761590030321003800011598003156510340014000c0118800c001c0905403c3e602c8031b41c1c4583c0d60034460310344020564104105900c0b41b0203883c2600c100700039010b2a08054850b007034a00150f08041d03007007000603400a51054103102810805255042100007660241801c00542c0d040710003c00d240140222800c6000b00b0060b40f028010030030080c0340807034540456001140d590745401d0382075900a8800c02040509220300803e122a1a00b010640d50007030081c8021704042c0700984441e075036280c00b03282c6d82c400d10600080711001ea018400c03445c000f964010b44440003848400b107050b0300d480078007903054000800640300491101c0c09030185000312581001320341e003140d0078142084020300c00040b890090040c0710800b2000d0540c003481051140e00141c00009890380c001806800c0c010219413554440e40080010b0028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 348918507 1250 348917257 348917281
    0xb0a0b0a030201080901090203120c0d091203030b030a061e0507031a0603060415080601090509070b070b060d0b040606060f02010903050415020c0901030804080d17060d11040e0c1206 80
    0x210780d024a05030078281c9804c01c5031401004c0c03060b00030b1b405005105060f0303000320160006002c84044682103030b00f100d403001c6084a02503a54000d10540300008203840700402c0c86600904580680101a9403280140d55a40c01c12101140c01c81000485941c0d0207910210162181c0c81c0e1210590030280845480b0841300000c401520110340d105190220100711760307448940c03003004038650180f03c5105c0309449200640d65010700340700e4492083d040c5400540c11410208014049400c42c804003810005690703a031007104d0000420780c64000854038059408941407410103809603015903000200241003010003485d00050043c032a00b560704040d09140080e030300c0b00440e001c640c1c5c801018150300c801d41d4401ca0401252070341c001e6004480380e0010040c415414002c00488420100300e071541b010340781e020344d100041c40d0300d000f008561040000d45141009100800901d220369101d4a01842e1000040e040302d45155200c40c032548035039180e05450a201000c031285000003401484685800300329280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 348919757 1250 348918507 348918509
    0x2010606030f0b0d20040f14061f030e100c0507050d020c0a17071d0708010e0f04060f0902061603021005010b19030e0109061b0815060a0c02120601030b0a0b0a 70
    0x100d15401400400c4c1142050f0f41d481d4280000207000b0300c48446030042e1200540506003c02c090802403c01049c064640f1540241140500340071410080910b600190300030980d41c2c842d42440e000382c0c140e4a4414119100300080300c52680c03103054444281e07040c054a490b0b003210058056510100384140300d5512011001d080b105040888084007010301201403d04001d0751005031b4410240501c8450801c0000e8002c1c070400c40c5689201d00c42e03a8031110103120210036a0084050b20b0f1080c00314004c501190059400803940c0c030004a9002d807180d0120342c03a94060340c0d4075001c2e019680c140c2010554184070341142e2040c1d80318184000e504004d95646a44540440d04500840503000c030301846000780c0000a107142410700802006484d41480c1024003401c00d401e41b940460b00d426540307564041c9401d40d0042c501c00c81d050300000860b5040c4142940b0804c429028040000c0f60b02c1c2c0181d407103080e41000c09442801604041d403451810601e420320140c11052803900b06600c401d031545502c2d172501c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 348920863 1106 348919757 348919763
    0x130545160203041a2d0304080c19060f0e0106030512070201210203070e030a0b07110a0b01150206100b030a0b0a0803070c050f040e07050d1a010602010606030f0b0d 72
    0x4040340490202000d15000d0007c81d0200e040080a0001c103a908812504002c0300b25051040c1301000d000101c0b07040303440d440010040302c0c2600032210081c0b40c0e440280309039401c595070300b620340c40d4040c440710b1ba89c100454030300250782c4030324000c07101c01030b0254844481c80f0b5031101000c00b0f94800c80300003020131048040b24029040009075031881d00d030010104103158039082c030201d40b6051000792000051280e120f6000105400c0310b501402004000041da01060200101909084004102c00340c0b04e01f01d82c10401c0000c44440c00c582d440080034000060404121002403082e240c0c98210340d0395032201286070380170840c03030400000075214211000500034118030f0401054a10b905131011003078010a80c10041801e18403001501d19205e1401034000c0d130560240c0d0640032200342c0c0240c0c0140e44850007003210315090710400c0d112100002042c81102190301c08105401c568400003 = true := by decide +kernel

theorem cover : BRFrame.Cov 348741007 348920863 := by
  have h0 := BRFrame.cov_init 348741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 348741007 ≤ n) (h2 : n < 348920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
