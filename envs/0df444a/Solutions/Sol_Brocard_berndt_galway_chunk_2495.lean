-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2495
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:02.550994+00:00
-- url     : https://prove2.me/submissions/716516c4-72da-44a5-9f1a-984de2e8cf55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 448561151 ≤ n < 448741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 448562401 1250 448561151 448561159
    0x10020901110a080403200f10121b0f08070806010804020402040e0a090605092b0203040f03030c020a150c0b091f05060f0312030a0510050a1205060c0903070303080402 73
    0x4a44640307120350810102140403250080041424420300549440c0000702d1810401038903038600803100001c4016a02500c0d15100b500d600600c0412a4410b0045409040318004140000c0081d1b90303103070220a05040301e817000502c0d0101c8044800740b0030180c8600886040d2901d84d0b03140c4501004603001200104141e800c00d03001c0000046051118100b5442406414800100e0440c42d142c844140e48018080b400b03954010035061040c0c40d0202e8801000703424500b82c1000d0315802d4075069086000f1035000d224070081c1c0c00d0f0f0002c00e141c1c0005000010718400c43d80003046030344620b004680604001d219000241d503081d42400000e02d01300701190000110300c01c40740351624400e0480745c5111200d20008000351130307a0501019043c0124140340e144001c401170400c20302c400011000d54000184a03042441d2603a0210305402c0c4640040d901a00303006c0d00c1122520788450701b180f0300760324038801107400380304001c0040c1044003080e090b203081d18002409058007600d1514202c80849003e0300c2a42c0c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 448563651 1250 448562401 448562417
    0x60801170114090c1e01091701090b0403090f0b12010b130f1706090604020102060f0703060b04170606040621060b04051303021504080307032703050408070b04030510020901 76
    0x224055405000d4800c4080000406004800c141170003440c03400c0805411540c0d540f541402c0440c4e80042040095074425546c240900c400a80f150780902543d2102800000b00d18040c0020b140c0e01038008001c0d40c1c643c90448a555556a400d00d840d44650280315840f130355090018010030410780f0003002d00181000301d160541c1d0300d0381400c026041c22a800b110320500e070030042401e548030500c4029032002003440a40b0071440c26800103034941d04001c010510001f0507500185a8030301a50203136000d40307403200c940342c2c89640b40c00d1804a04140440003000905c0354200140c010700c1c1078047c0d0030550344100c0c03002c0790711040002c500c08111068482115030580791038140d021a2654420184118074040d03608201c0440e505000e81003010068000440500324810080810980030441b90030462500d40019281e00030507104004581c91524010f494601c0568a000d15610a01400686100206854040d50380300c1b40103115100b2407100909903006248032209690055015211000040c1480c04d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 448564901 1250 448563651 448563671
    0x120714190504090c0c05100902120d0507140604030e2b0809090105101d0a090c020f010b06040812030c0c0f0d0e0f060304020f0f06072a0608011701 65
    0x2203109403a210100001d80049003c2003242c1850040640600207401c1403541034441c0c1d203905444c0c05080b8484100700d85c0300c001510440d15405598000c007121071051300d4001c0c40404004005601c4030000340e6200040e0340c40d402c11044041006406035a0644604208910b14002c0c80200110b00c2144404814041500300003031885009010105204030483d66850684000b04201c102c0107030412800340710074070b1080d10b45c25001100c4000d40111124518508039803003000a1050081d60030001503141424000e134000b58000400343c4098032030300000d0041c2e0340103400b1f004950007284100001503000341e0852841c803000348001c541008140000d1071403e4846d03441d113480c080d1040381042c6141e0107002c01310080d5520040c000c8009000b260079003010034070341001500070b003c0070380040d110390080301e2080c40340d80d83c240c0d8503111444003400700da40310030b454242002c003405841002c00901a50f044501004c0c002e0458100c01d40e0860388448055900f4140c01540122102101c100159a03c3c06c140c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 448566151 1250 448564901 448564927
    0x180a06080d11010501140d030309111c020f2407050f071203080903071109060a09050903040513020304020306011e0b030c0d0c030b030712080708030106020a03080c120714 75
    0x100c48000d09840b2007000e8400300040301d084900c140d0041080c02c03204071000b1104d942d01e01c40701001c15090702e8042142d03806c6080604020b440b12242030340c0305010282e80940e09483c81c0001e0345241c022a01141e0030740d01e080074003001042521900100800090000c0301c0818141c01400f441409a01110341c28668a401a488c08419810420f02ca10003035440d00200741d442940070383d00c0140400594241351070341e603c42c00d064912038103442c0b10f144606c0014800d40c0f0b848149200400040e00180642c3c100a07035160784a0b4054040c0f9405451651003c1a030f0303070228003c0f00d0080c2d501400030011030b8641601a000c1c480303511403014182445110000340401c3c4403001e14010070861040345c1d5a0921495281c0031119110301c404140740c2840d481c45466030303000c01ca02c401c80b030501d40a80c040c42141d19002e17119209801d0700400b913090203c0041070040d40001c0c496042c910030344807403070203859201c0140c4441c0030342d0300d400d840800a2000a803074184a42038002924183c001928141208aa840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 448567401 1250 448566151 448566163
    0x2070c0b070302150114060f25140f060408030a1e0e060105040c0f0c0809061e040501140c0d0e0f09041103060a020703020303151807031a0609180a0608 67
    0xd40069002ca500b50812a04d030001c880c1c01080c0024044042d9040d800203d14903006801c0c041c288040041210140f030b20884010040344c000001c0301e10080c0ba140d2034001c1900c5100f041c003104502c203400f04460764082c0003984501480c0c100034102c4c103603a1414071480152050a0300c0303030018003010082c206201c03000e0068011920f803000c0030b810f0b590b0601d4288001c403081c0152580030400e0560407500001c0e001240000e4080e00000010365602c06940410b00078460740440d152a512141306d28110500d1a02c054020343d4070907a5008680e0345403154100d403902400040813150303000034640700052800340101c2001c02c14040c0c03505c002c10740c481c800940b5409040307900b07032000c50448a40310103628040c00410b9201d0040c0408500f030841988009580c2d000082002c8101036401000007996a21b407081014404480318400c98039207030045000740075148445080b846403046410032010352800300280d91407030303401a00d01040b2844600401c29132450181c12500c01c29903614020444020030f001c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 448568651 1250 448567401 448567403
    0x20306010f05040b01030b01270b070b16032a0e060f1b1605041a03060108070e13150506010e03010204060203070b06030a050a0b0c0c0118120e01050d02070c0b07 71
    0x800a8140b07400d06010590f01e01c00e01a604051070544280c0700c40ea0025107448990969205510000c0c008920f00e6401c1650794000c0c44009801281940410402481540c4110b4021440c008405050f82050341a20b400100c2410402803204800882c400e04a64510755100071b442c043c215501c03d580404c0300381d84125484581c483c000038503034161701c1300241089025560340c4010000c18108440201510030140035041c440d03500c880800001008007070aa002540004098a00c6941d54441066440e135540c400c0604130801c050020740c1903222118102c1481e900404c0c1d46030002a216020801070000511144c1841406031545445440902c040c00180180743c00865984c041d9051001d01c02900420851013136210440b890000760700483d031400099407201604c8200d03240c06064124601a00c51140c00a6103450740c02d040103001450b5100c50103001d079095500390040f02d081110b00000540e0001d010030303020001581180d0385580100441c2d130007203513003003a842d0b2a2010b2015640c04214 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 448569901 1250 448568651 448568669
    0x2150c130320030c0604050d050f0f061b0a0f050307050d0f020a0905040e100905030c01020d150e150f0102010908070b060114070f02010302161e1506081b030a02030601 74
    0x4458451002d4030008080c049904034001d2000c210031100084041c441d90054502803c080583c403010803404003d069003022a4505440f60b69200c1500700f0390303036501240c40b180d403000200e002c4280100c2100807502d50f180d0036aa10512400214000d41d4203500150145007044004c1040d17001c030410714852003400c80040c05015a68005218004080c12100d4220398803591038a00e0b6412403240c0020980140d6820450200b011040c0b41072031800c50040c111a43c4e41c550000403040700d81c0416500c8901c042c5809080b041c911034699404460b5060b0448162060100e10385204045261034402d014100700c0500c000300f80c443c0c080d07491012a400002084580117400c00034400d182d0703004403840e85c00c812101d0750385041c40801d0316420401c90040c80003a040c11b5000800c1c50350380c00348808401d15150000b808640d5840041030801c001300302c00030b003940c102c0c8104c2000b00305010342d030003560219a4900b00400607290040e041040300042c01a900b681032150180050058800740700560081403004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 448571151 1250 448569901 448569923
    0x901082203111002040501020703021e0d0b0615190806060415030501170c011209031206030308040233091201060e1b0906121305030c0c040e0109020102150c1303 71
    0x203103490f40740002e80b00c0b0b10101680184070034404d99038001190021603030111200700780000d50310002001160811410b540000e085400341c0d041c030074201121030007500c0c25200f1043d4a0b08c504c601007518040c16807108201d51440790b000340b1316031040500340d8000344003c4c0310524041d03448040207002ea1550310514007194072200100000d000c4900d05049541061000d8440b0310301420000f00801c0c0407801b504001903440000500781440f694601c4070350b00b02c1c00d00c108040c640302d082c05401e00c1c0040742d080384210040d41e440740d48254400f0b902c1c2000850304015070380050034507d4400701c40d002007020760f8204889000c608541c402c24010390004004490305c480e40c50804944c4806003a0420300c10050500e000c2158040c02c1c5c6852040710700c03828042601c0c0200740c580c0c00c204080194400005071071480086841001e0800114180f0559042103d00b0806501c29002003408e071052003030040e000d44c1283c00350844d40c0c80d41d10f4000394420080b1003564900405424103400140041c1c00c1aa5109005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 448572401 1250 448571151 448571177
    0x907060e030304060c032724031a0618040219270b2208241501210c02370201030e0a15020c01060501080108030901082203 54
    0x400445040c6015030145103804d00708640505455181200202081980148207074040468110300c0b040e86998101d11400640c2c801c9420514914212084040e000404d1100136680c003910903060324500c1d54003d502003c1c1c403542084126081000f6000c102000d42c4a4180300b652544020a00030084071032032414080380c440004c00c58007600030880d030030f480301c0303005070303003d0380c7c1440c0300000316002c0051141d517a400490600c0945c0ca03011040800c1c0c0000c911012600010209064a56a1185c02103800c40300d454a801c00d2a21000d442d4500c0c010700c0b001c3c0202480d480f800b24150b2400000994420041001784820209c8151224880042c2c012151900d0060750229494a84a0b81e52402000541c690003900c1211820010022305142d40d031ba484101c0aa41400210040b940003140300907950fa4510405010354403116a0072059445e24070041115806401e180b41279540020003141080381040064442c2003014143c01544100090071404003a941c00700690300506c603a0760004000c1d01c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 448573651 1250 448572401 448572407
    0x90f012f0f060912030a0903090815011415031b040819021807021f1e020702040b09010605030c0c03090909030a0f0305190504061d0d1101090b13060b09090706 70
    0xb01409400c60390304403161006002c0824001e03079400c00414100018503070030342c0c80d0959003aa85a4800740c464080c1381c3c240c5031712000c0f0b8460b05040303c4803007806030200e407a0790040102011850503482c581d503c051000c00d003034142030703c2a03641804605070442d10b42034444030414034290b018150ba13464040c59808200840c01d091b075075070390342c1c3c80402081c40c4030f8188604080d40b90112a44204055400c0d004039100c9403840b0703084903000000190420284900e29101c2001039404840140c0c0114109425039006003850780d1114102c80c20366070790301e045440b08400401c0355848444164900d00c014800310009035a40021035001e84c007184021980c90b0210b282c060080301c40741c0b641800345842c1034100300c1c9240c8130000b100c01e00342150300001039595583c6050700007030010740c0e47d04107070700c004109400c2000c800003182d40c5440141d88686110500c2d00303890500341c40341d11a000707003004003001c0031945803034440c1d504a0445105400210f4820340c06004030f089503070220758036081548004010886250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 448574901 1250 448573651 448573663
    0xc09061c0b0a120303020c0a020405010603060314061e0c120112020415030503180301150e060307210204020a030b03011416050306100807111606030501060203090f012f0f 75
    0x29036144140c0c2c0d18200c0e010700c034036945190103401d054002071141002c6400f403060540655000f0130400665841b01c0d0002c0041101c2e00044400c00b20044656015400000341c55100710111110100310b05910002d103a480140500ba05800800901101c404c8500400c4090f01a029148240070030700380b0360040205458810b915100c40406035101071001c510080103c42c0c000d0020342a0b40460800e010100b070042100500c4441202204d0f4000306035032099000c031900690086044031022074446004c0c1c0c52200c1c0e10341c40c6281c0d8076880d01c411401800c1ca60041c090700306803410300054062040b00801e09540d03185007420884072050040100c41c41c0c3c020702c8688400450b2074140d0552612101084e103d05044070300d4800d2000c1c4000203040180f10340c1d00c400118050b03006485800581c074480d0b0a600300789000700343c0401d081c2400813803098400026140300f4540104511802c0c84054015958192035180800b6a403d88003540e9407071201090600142e50740c1c40008002810600c454541406 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 448576151 1250 448574901 448574921
    0x1050c010c080f07031806020f160501060501030c090609120c0810091202030a05030129070602070c05040b22061e030605060d0317070c0b0408070204051b040e0c09061c 74
    0x51500342c0c00c4c42600b00c51506e00c8011070f0300c540010303130f03c03612400025074030b005240c01c00740240300c0d41c6d40d03c3c020003106410400850341c00b0f0300e050245100d001819241d000d00f6004c2c00c070001c1d0452108001c00d664455411240301d0240d40c900415a44510038281030608480080421039103552824041100c41ca8211806030503070306c0514100143c061000700381e48010300c41c1100703500740f1170000328620540100702034110501d1500b85030341d80450300d040360294000b8002690402c0c030301c510014080c100785c080c4403c41500105000c0444041c401044c05205a80e000006002d0391038001044c0b500100540250078034801003070f00401c510f0340c5049000d946004055a00600000c407940000a0b0012403884000c2009070340b2851a580d0380400b110800000040642152078a1040c402805503c80050444038025a4140850782e29a0482e00d10039000515a52a54604000400c054012840025085502c00301030030728040310b2400143c00f58000d078101d0b00c0040542806250b01841d9032107180080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 448577401 1250 448576151 448576157
    0x207110901150504050f0f0301020301061d0411090904063309060605031617040c080d02010e06060d05011d0d170702030913021b061503010e190201050c010c080f07 72
    0x2070b101100c03008206015030700c01d40b405079030b41010f10001303591002d0403440c030305102030001c646039039580340001c011200902d100800800406804400340c2000d000304200c000c1e03e041e9081c90b00c81034000340501100300502c251a02540c1c0d014000302e0301d903000382c03456500c50649440300015140e01c039102c80c03034851680103a80302840c0000410046401006a83d403040d110074440c1c080241c40401902d07407d0103565026041040807040004000090102c58142c07040300c5c00300c80c0e00c6481580c01340e00300d03a001c40f042c0702541d001c01c000032100c1c44c244144480c5540300d0400800d8000f92404086454000c0e000d0b4a2400c1e0801c030b1124000310f03444841800f4006604460350300e00d041c045c2010b5100d00c984c1440701d000c0c0e0300613005480e14a1640e01142d02000c03030b2a0b041000144d1030300c01207494420680d054081501d03500d80301402890140100144030a0707100241c2036101d0490690120b40e00d149404074184034090203900c030011002e03c59a12030758000d03112078402d46400c0b90341e40c0d1000c00040c000014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 448578651 1250 448577401 448577429
    0xb0402040e0c0f0c0706020313050616140c090a0b030607080403050a05030a3b0d09090203060307120f0b0610081501051b0f070902040e0f070c02040207110901 70
    0xc00101e011505801000c1c00042039550301840c80c0100480c4642c80078070180e803203070640004005600200401e540070074685081c000c1604c2e407041008a211381400e5507900407020b403401d80424040c9003800100700e064021110340c0315001011a0105204455903040c1c543e903141d0301d45d103500301400031a038020303403c2c81c2c025891720706550080c10600459241d0300030880c0102c00252004a1a40040c0c001c0b11a607580140160b2642c05140c1440506d039007030f110720881112040200c0d07000054004641c1c1079526094205070806542c00001d4000515403503141c4200300c40018218000d031440354816001c2c0c0c0300c84000f900d86040002c402c46000d0540c0b8000c60780380c900000180d5004d00450380000001c16142c001480300c00049450b4014018a965510010700b1110342031840003805082c02c0c600007040d10901d40c5e071038204200b24060780c420b0030308182c04040018000800d140345244d2015050824040543c841d4002c10105d80003100100d41031013008076101042d142080ba03041c010460310080c1c0030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 448579901 1250 448578651 448578659
    0xf0b120a030809010b120609010e0624150301061808070506030406020702010c0227060603100315060306050c18030105060a051e1905100c05070b0d0f060e0106030b040204 75
    0x603590030500d0000c1c04014030240460b00c401402e400070407240b4802440308404141141000da200e0308140c1e23201d80251b1a211070030080c0503020500c944900c0c040e140c1c1044460090b150003500399481d1680a07403280e18903142482861030a0059800b9110903540ca902c941c0704007000b003200701d141c0d07001040d181d1304c81c0d00c00b004940d43d05012607910070350010000d600c40c9100e20041c0d40610349100c00a6000f210007489200f07120039140f0881c03c0b45885d0003a600d0940700c680c01d10081d07110079107040d450001c0355403090010442010450300085102c8200045d503507980d44135039044450640703440319040b41c00a0035994884180220800c40380301200200214140a4005521400f1520402d40a50381c00702420001400c009540511150090540c02e10b031000a1514240758170903001e0030384034014051a1790806403042d04850360299100000340481400c0030540c55154201d5002000c3d07050300c4200340080040035010f142c0080c02c00000c20061541420809020b0b1041114441c0c000d91060100300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 448581151 1250 448579901 448579903
    0xf030503090f03010b090712060608041101110f0307050c15121f05041848051f0e0414181204030b010e0112081c020408010c02010f0b12 60
    0x10980344003210a20b007940706440200e4058146420910b520070070401c20011902d40104542c9a21502c010f003c00104c0c2d00e90100f1790b2490010385d07028186500394001c0a215501844510058585580c1292100848000c1c8585103078800c000441e520f07089100340b80d20504050003852030f6030304440201c900302206d0b0b01c03042e10a9140109034152001c1a02c1d10300c80c40fa01203d9501c405024090320a11441085540c000c2540703003a07e100f2900d000700f9032841c0c460050302e0002000c4d182040000c034004040101712415a0500e14801884014082030ac0000c2c0c554405050503409120700100d901034040c81d98011f041c1c40110700d0301600030390400b0046914642105202d550058507403542008041c3c66030a0b561401c4c10f07404041d121410006800b009000e42c900d5554102c0d08018100c00c020303a02c0b440940c0c41010019401080c50b40244a400d4000141c0c01c9641401000680010700b41036440d05d401d425200c00d035607500c02503590f6401e91011704a0324080c080c09030b202136503c080c2c0601580041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 448582401 1250 448581151 448581157
    0x2a03012901120e0304030f020306061f050307030612062c0709180209010e01080607020c06030f04050a0b0c0a110d270b0316020d020106140d0f120504030c0f030503 72
    0x5a030400040a509480382d00d05a44070120b2021050b080f281c9490301d0b4500403400c4c04a0042c180d200b880f0340070000b0313028074100f0000c80306604a40b205800149940f082507400381c001034420400e060b22404042041c81d100140f00c01001d020307540105551105407003088036000c00710080341d451b0b503100010006c0c49400168460486050210000b11600c5400d003d4040450418000350b104a00c4800020302001800510f41a00d12000c250b4000e501e9004050341d4032020030403400d422240500008102d1100139144a074481c3c000c04c180c0d1841a40750f0b48621009004566401c1007200202e0b18444d20b82d8041a20742e40c4003040d500401804007002c00203070040d075a0f91140045401102c0d10303000024910b1a0f070b4002003031400c030025140e0601002c80c1d099800001a1000184101d81d050702110b4814003540007120403a0115801401e0848240300a070b510b004800c1d14001280301e076150010f5007005041a142d0400e551742c544407811440c001150019603405240300600c2400248003003500070080b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 448583651 1250 448582401 448582481
    0x60901050a051b0d02150105090115020a020d12020706090f03120915020307021810030b070c0f11090c131e0b0a120e0106061209052a0301 61
    0x45541c851140c12070885041c030503000c0909050088801c0c1030510303a800504071403c10101c0d02952031101003249089581e450901c5510341c0410032000400002014200c40e0200000c54410346440310f06c650046400e00c0a00c0da0101c50010601c00b03030113001903050101401400312843e18100b0320b0310b000f29810822290307004c0075003501034101e01109050b000b2a00d5100400761f04080440703005800c0f0001c0d441c0e4101041c01d07801071080282c801402440c0c0d1251600c520061008644a10308549591410340c400900c2c85040c0b210321021607020400003110341500c10712031545001e001d40500c0500500480203488452640800c0c006a4401404a05060160303000700c2800e00e604200c104e65100c8515050317100c420781600000384070090329844410442c60007044602400b00d059a2542d03517088402c10310401d00003403207000070203107070441d0303500480007847c00f0b01e007201e80d003850104401051210401c620040161104c000d0101d07070030f081c02944450000d540145c20041e81e51412085503840030701c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 448584901 1250 448583651 448583657
    0x36040612080c0a02030706020a061401030812040213020c0f011a1c02031006030809040621020f040906110304060e0d0e01050310030506011202030c030106120b0910020f03040b07020606060901 84
    0x70885803260b0300304660044650002c04980006684003800383d1516030824080c0c42d42d509105240240011f44400541203d81c0702401a1078504400c0d056580c0c2c0001a0040380d00c0803042091621b800c081c1e0010344080d820308000340ca02d81c500120600d00319440c460b003c101003035489a0507510355459941c1520b00c00c1640701e01136105110b074400203003402c049032202561145040340c04824840d40002510004500761070800c49241c40b048108440c0d0812440040d440c0c0354810890018181004140396181015101080b00d0240340c2c0d888040d50f103218080d01c603c841c007104200c1442014081c60380c440001c42c1c082c2c01191303c051002412035010304000d0341070200020104000320032900400700203541203401c0d502156100c00301c0b00326415400c442a442440350f00d805960916041c440d42c4200c4070508201300c0c00146540d507801d010400145100a14000c15145c0100c40301d0300c0c001001d22021404182c0d0303882c42c040c5080d000c03d69010f0850011540070504100322274032264221034034240300342 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 448586151 1250 448584901 448584907
    0x12110708030c041809032d230c060f01120c0603050402010e04060806060a051504140a08060f010513050915100512211305010e063604061208 62
    0x103114520700740f140358007800030407030004105404054907078070440780d051103540d03010480c4006210b20b207010504400610f800c441c101401c80e4480c0c0c028445010520400156903426854130f840f92905500300c48840902d0350850300800c80b816400d007502d42d0141a041c011040b142c00c090300c3d40700d0300038054001d40307080c0b507503880100d030075680942008000042c0080c01840901c2d2134010b1b4540b64103080d107140717000e0b401e0b020010810b0b01d0032140911201c42500c0020f42802d103082010b00c1c203544980c1030607400860f00c80001ca0807010034802c3c2482028440040c81881d490001440034489588004182107494281031295201c00828108120159222554103d880303136602c03d6640700303541d0f000940c40023100c0c030b002e280c6000204410117542d00c0d4441c4010a5003500303040c415a445084c00111a01044580500041d802004026426030010b021507013003c8490050341d10503526884400c200c0720580c1100e400d141041a9100c030101825101441010b140a60380d00200c20510b8009094403c08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 448587401 1250 448586151 448586161
    0x30a02120a0c02060c0c0f040b03100903091703040e060a0e24030f06060306060402160f0507150e03010f0606021504110916021009020108040210020f03030a020a1211070803 76
    0x1861400403464000704420b9585c9014002c10360354800c40884280282201555044585000d119003800392401402030000354610720048001450801c2040303081c032000450100700c150b207140f862140c5429240055640d1390030301c25100c0c6c010600514191080c00440f2041c000d0441aa40c030f907030440c07541400000d100444100482092040500f656010310900b220390302d404d03400290703460207100150281d0ba0251600b2081c0426881801c0100072020484251203001882003c0d100e1109800b82c01940c040640755092102194200c00d40d4100280103140031158500d4203100345140036800140411001b0718041000c1c0d140c10f00d8003281c0b2000c5082c840042c0600c60706605141c1941001400c400b410314042d011031100080c9200b2020041c410303003c0f54102c1d81c5940c800e120b1943c0d016100d00c2d81c5079565a080000d00f821000c480303800c5004000b02c840403980c08001031802468104005a01d62040395001442c002c050500482c6850600010051450800c0c0c01c550305282c000300d901743c1e01c2d034030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 448588651 1250 448587401 448587407
    0x141f030e071502010204030b0a061a030403020312040309030510090b070f03060b0d0203190c14090409020d050d030c050f180109080d230c060a022101030b0103060608030a02120a 78
    0x200b60300924680c0800b481402e04a54198003c10a980c0310701040b14040e20303055012001c4900e28000c2d401112010252507040089410245510501c44d02c1101c0c90a03900641446030682c00b50b8003180800c0140d1410b00c01c005c824852001c600c0d80d07401041241c012607480b450802071000c0c00c01030a21070050079403801548203810540c06003c07094142c5980d4001d4682c608000c6d4011902d4040014400f985580007100c0c0c0d00032500d49014070341c3d402d50303c134424000d0280e990380034210999102d41d407480204010b840b180340c00f4410a01500c080c1c40c443c1c1e00f401002d415291180802c00030003500300803035500b0030284800d485c403200309402000b02c035400c07503401600c2d411116005420184150105d00540d2a071103412070715080550100c05d01c0b0b843d1040700111080c0100502c00000d40c003c4000a41c111000da4083e0440655a00e144050301c7d45440300e29918400030b0300196a150200740062091040c10300800004000203001149010b00070340e8000c2d00c078000542c0d1500c4000b00081c1440f41644 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 448589901 1250 448588651 448588663
    0x901051003020114130f0603060b181314070206060103240e09030c030313031b02010c14120406030b2407030f172701060b0904050c071a01141f030e 65
    0x85e10007075400c0d407192040d8200ca00548102e40011b0f05040c40418240000c000380c420540c2c11000b03104941480c80200482c22015000802d046a503c1c4054141c09400c10845406503010341c0240099007040c0000405550702c2c0c80c0c840140105410a1882c804c000c0496070040b510000d40341c00c0140c03121010035040d4400d03482021030900c804401d003e1900c030103d171700300707043c7d4481d40f50078001181c50084003800c1c8a000750040d01003401661030070b02045c44e004220010034080001d403914196050390f41d07030246d001608414002540c840c1103800608012514902001804826039154a4072440c6840c02d0300c14448000c04102c1c00c001050f540070302411300d00c1c0d90075800c1c0c0310040c0c05103400403440f0003007030000f00c49140c1180c029141e0104807106200d82816951040c0d85985008040310902010701405441032034030505c108094400325169044040c41d11652810b021120351500342c040c0c2c0c2090706050340612031300a07241001a2413184408403400f400b607900300414144c001e8036030942484 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 448591151 1250 448589901 448589917
    0xb0c010e060907060e0d08030604050a06052d090112150f0c120f0c0206130c050607110a080318121c09080d03180b1b0705070306050901051003020114 66
    0x100c40c1da418040c480c54007080382001d0720130f284d4811482c0e50030700d01040b455041804004c3d020b50800c00200e211400c041c0c00055000d9a100d0002c180e0a55030b0740440d078801d1440d8450303031041c18491070030080326030200ba1540b0040d00c212a0214154180344410700c407100c81000040c82441c104096aa454980ea0041111003010b48030070080b90414010142010381401e11580200345055415003907000140314100a0300311541c000c0906a40d50030b94044400110070017170703e0402a0a40000c2c4664503c8010300c400c612415001c0c0192048038188140c40a0b1070b0014480c2e50000e01200180e849a080200d0348107808a40ea042580c2d085002c0340c0c14420b4040781c501403410300c1cac001440003c0c0c00c0200c480444400b20308480d00307441501801c5048603014140320703401c0c002000480001c24800c00700d4541000c0885d0706072880080d14014200c25070300201c0f00f211a0f4201060800c280300c007a210b440d41c03010301302000b071159141c51b15241d90500c000c1e010081c14000501c00920b104c800f0002510005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 448592401 1250 448591151 448591153
    0x21302030a021b03210720010902030f0d0f03180f0609020306070306080a020d0c15020106060216260c12010e0c01050a0c0b070e04021903110f040b0c010e 68
    0x2800c0c031100c072401a61000310248414003409240d8240803000004954a0340e4015080000156520490141108000d0202810405000d0700410500b000e01034a0314090806400000c03000c040f44149401c001d4203641d55101c40d00800120000160402d01440d007000c00d0b450001590308051042c81806801007002800346d2244d421400c1c10401c05038042d0400c94001c178100c802d99a80c1c0b50049080c1c80030340c0201c55150700800580001170070518584000e0700e2096461202d150345402c600190030f4600d075030200040c1e440f80c02c10441d064040c4120300c0343d001c5d485400195a410039050f803480c1440000d03c0c0c40c0769480304e503c043ca03840c024041d40e001c17150000c210001c0052902c650703134003800c084500300300b45001c0c0c1e40b0740008660040c03080328a0040581c88903403d986442e02d500d4650003004003420103001e500c00c403c024650b190710043c0000700640783c1d00d0241503403607803004048070500700b107075103818204200d60181013285006407001c4079a031160b000d42e212884e6200c40e016003016034904100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 448593651 1250 448592401 448592407
    0xc1e07030c060309060b0405270106051027050d02010c021201020a09030c0e01060206160e06040e01180504170a05070c090507111c030b01021614010210090803060607021302 76
    0x199038550094604580107174000d12011855008010449800707841603582203404084080341a1201150310343c11885000001404a5803800401c0c22010009180000510410074400c21400d541c00581034011030032000d440c5140c1024041051010b4901002e410b00c501c40700014215903443c4649000c11072210002d41d200c16a41401030700c3c000700350104489000304140041000050b41d08807034100c440907401002e542c0c4990f2071507140514529035202c10891007030f4400c0c20300d0320713410000c0004200100c24048990300d4041d01010400142004100c03d5042c10180404035042c500030000210303981c05102c0d92050041c8040e20a8032445d00b0003001c03130f000b900c03000560206a030b022510030545502c400072081c51611003d616000c5000040780d483c52155140e03824203202e41d11151000e581030045400e030300104114850684030320381c031412071240b402c1034824155a06111740c21100302005411700006440d50b48990303140c0001000c80340034200c0400d030401075507114002441000004407046603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 448594901 1250 448593651 448593659
    0x20c0d0306050307050f1005070c031e12110d050f0409110a030501120804180605061c0b151c0621120908030a0309111e090603030c1e07030c 62
    0x5401c07903202d224864051800006440d013085105001025070040040e1703400b5908040940315604500000d0701c0c0e9031701e008030100005015100d207200301542054944100f03400c07403070003240c00742c6c0b0b0310555020894110b204c00454100059088102001e90030070703d0f1940d042c20725aa4513405542d111249090a1171213282d607c2446400810b101e00c4207907401d20180e0788079841c02c0c050500c280001040c0c82c8040000700300030403010544002c100d02d00304004c0390960381d840000310103800c00d91201340018607110000358200880d210701c4540103801d81d49400c0410302e084000e096800b554156803152241c5034a2840074003240c2e0f0200e0043d001140811544d0a0052802100140e900030100ea01d24100614003012a0240c44084111948074004520b8485a0181140900f01c240c1d41110342286050b032155407a40c50245442c1240308440c1003120082d002800c108500101030501806901b080120411004000c200f81c08803240d009105001808001e814615041c2c00d07510103070510700b1503a8085 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 448596151 1250 448594901 448594907
    0x3040f1b12021005031b09150417010c360807080d0f1b03030c0207030204110c011a01081611030d0c0324052b080910020a0b0118020c0d 60
    0x91007500a0b01c0c40004003107481015142840700342c1e104c4d001c4d502c2580d0315010300751032200200710640001d043c082d046010265030b030005400580101102c0c0909030352036012180b09120b6141d11074420714204000340c0f00c01d9291010500462a25070300c41821204041c1c1c468450000980180b00042c01c80744079a0b82c0f0710640751141d5011011200040708801c1a1840389d1190301030803450100c40404260200c810b5800360020181c040b00c1000758014283c0c0040580d44a114503d04402454000c44d6629410b88038076084482c1e00d001d01401d01c0030307050307042c0c91a42d101d640958001e025101058507500c00c43d105403038280100d84000084e02c000140c4401807041500080f41c0c1d40115201406451320740d1840000001210400908018400b981001940744ca030000b45400b8a40074241c0c11201000c0d440038072281441c000c02e85502c24005840b40e100e0810340000c4003400002d20140000704601d6441e80301060043c441d01482c4580805000801e01c09030b411251101c282d901100d510036000c800107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 448597401 1250 448596151 448596179
    0xf0102070209090c0a09020c16090b0406060c0f0f0816120f0c0510050a020f040b03070e0924120f0c090a091115190305010f0f060503040f1b 62
    0x40b800703814400086407030140c0c0058441e04c08031000380410045410000310500030741000a10140c54441c41e58812a6010008085009405c0070758000c15503e100c130040c030003914440cac1d01450030030486100860104420003c03800113903500c186128240070041c03c0008a6001b00743c0d07d4003050710050411810407620025003181400b43c2e8030f03a18550700708030b86e055808000082c00035046800410545016000e51781c40382e41d020450202c010308100501200602a03003094100c00b088020003c140406607030441c2c0780b940304200407100d0028600e090f80f001c000f80f40c0c480568401010381c501407165a80da90b24410950394801004441c41404410000c40c2e6a088e42c0d002a0700070443d20700420301800050050042c01604941791128040c00d034014003074401c0c48018a04007141092048881a420111800c0c600302056034000c10254100750111030001c800750701c800c2643e01c458078204006a0080292940310344c000c4034114003118030b0b05003407001034442d0101500302425510007281c030b02000442 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 448598651 1250 448597401 448597403
    0x20f030106050a060c1106030103440309010f02040302010906050a03060902030c03040309081209151b0303010f060302130b0706110415200c0904140d0c02030d08100501120e0f010207 80
    0x140700d621000400d2000c08c0c03000b0300020b001c8140c1d40d030050701b400c1000f2540340c011500c04d4042e0f40482800055560140c111428440c4040d80b0000900c41754038402d0044594020701c0d8101146802e16687c0040c0010000e88141c009018000c5541c2035468040e6200340001d107002c20080d9503904c2e000496041540c02102c5c21400303e6a42c1c8808a520200024055610b40c0d000140ea80760480c100200081400c40c0c0c088055070003000c0108000074000c1140b814030b8030348903000640d00c1b075042c000c03801c180c8001a040001014414405604c1500010304a00c044840b01d506a44e903845007424400003030701c103001c2040440200003c000403110600500c0340d84d0012660f448905400c000e0050014104020f1070184956200080c51152882c003c03c0c40b81e0407510175404810004d80c1c4508180c1040300c108120070218000c2443c960540c14103100080a66940e840c105080349004d1040007800c140c14000c3e903041141c00300d00d80c0030235581c0350302426200c0c0481040b20b0520002c120010301030350180034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 448599901 1250 448598651 448598663
    0xc0a14010606090e1504020a1224090218180403020d0e030706080c0912030c0d050405090a0e0a0b07080f06040e100b011202030103081315020a1704050409110915090103020f030106050a060c 83
    0x801d54800d030ac400c070780c01034a1130100c0642a0390500c1c07c603126001c1c0d00904040c00521940d140d001344035a4a081d480024810405a000d07014942810041d09050454511405102c0101c00c2c08440d56801b154030300580300300742040c030096215000e541d41036005040c3d140d50012602c080d621074014001001c1d04094205400300c89444050500889690141c0c0c8035960700010b001d0040f070071800254020800d413010413802c85031030301c404bc0c0760340c1d1840105590600108040b0818010403c5884825590240e0140c5050010150740d8003445e07070394082003000707900f02a0743c4c0311420401da1007040000051000540c00395101c1d44c580c01c08984e1640803400407655202c5e0070800144118400050701c100d481142c0240c403003880603895560300710b0b08203d8484038000007004007240701c0c0d49621454881d01c0c01541c481c14102444818072131030550240c02034041601203844004250380341070841e41545e9050303601d0309028507950701003800b6003400d4100310303480001120040380d0345500501d1102c015020300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 448601151 1250 448599901 448599911
    0x230a0906060503010b060904050703090c1805010e09060a0509030405030703030306091a03030409021c060b030f0703061505070602371d120a0501020c0a14010606090e1504020a12 78
    0x200425089525520310b40d40c001b60b0902200000e890b066103c4c030f50050041c1000300e142c5902d65a041000e81c025080201d11a510010304240e0851074498140907010700c0c0800c40481c1040c00006030345840c0244103901c49500c400001d421480c0520070340b001404040c0456102d15100c0c078000c0d015104900550404519180c403d021503842a0180904c00e5406000303141ba003401c051228020394002608007120f9546c034003100140001d140b00308c600400070790400548034180007080050101d00605020205800d190b014000f20031410a440f50240f81b5091041d581c0c070007490220081d00940c0905688542c142c1ca9080280e24040e01d079049a03c4041e0303070f941c2c02e2041c000e4103a9800c0601a00341144030302d8110203281074240b9844d00041e1038080012146006616541c183c2686d0008031107a056401c032080e12410848034680c004600030141000340300c25401d000c4002e094a18610902d001d07446850302250300c1d0109084004c14418010300290750b07668410301c004d8030004000003491040c80c42c2c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 448602401 1250 448601151 448601159
    0x213080f03030c0a0528080a0b18060609010e09090601051c052e060803040501110304030203060c0702011704080a08070302090d11150d0501030506090718230a090606 73
    0x30080b60700ca19030a0a40a0800b942c103030302120a5007120328040c0140c120035407000e000012000b81428000c9040e601c445643c944041d682081e142074205d5140200f074200e89090114040c6001c00ba0310406c141c40c0f10b5203805402d8012500307008680d4186401100036014000e1161020807200c0c141e803c251741501c01d0701a4042e206c840300c8103023440034010360460344042c00b00c0c0c0030440c4041e110f01c80900c81c5140b441c03000c0240c80d08071400b5501400850381b000400300f003d07581205014070542d4109001e581480d2454000c03c1e202c41c4000c19001500794000f9291046a0160400503000c1d080341130440400d14041c600401c42d0340c024031201010880360300014151034031030b000300e40c40700501402584055500b95502900101d204201961010000c7d8150408402d00005040414800c643c0842e43e540765040443c10b040c000707007034503c8a41008005000c2128000308403042c01c1300203540090008814103280280841902c50507502964101c180189100641c000b00404c80c0511420440b969072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 448603651 1250 448602401 448602403
    0xe03070305030a1109100f030f020c060105090717090d03050a06030f02010c05030d0e03130518150415030305090a080d0c08031009090318051c06091103010213080f 72
    0x10840010300048040001030211400e0340c01010444d200c450121307082c40744120000e0b0001c1582103800b00015842e41584015a42c10700401036680384150702107140c20074050415444043c140142402001085c0201e140184a03070b91580d4004503070003d011090030851440340d01c4000d400d07082d8001906180c04114130724814480e0300210380d400b280c2540c21074001d500540310184034002c20f40301d42c041408a01002e250900805428029030406580e43d84046d00041c0008407040d00050300620b070320341712001034542c40d004098200c040900d14849242505c00058060b02c0605000303408070404440000400d03402c14007030403520308200c0380341d400182c40ba01c1c1310782d80c2c000c0b614500000446900140012441c1134009640000e56202da0708402902d404d026001d80304401c0c412000540c41008407001514100081c070301034001154040318014440341046124040100702506080e0b54038000420851030f4805403a1040001d0300954607002e54500350035a15103141301c2c224150113040510a18824 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 448604901 1250 448603651 448603657
    0xc09030b070e0d1202010e1c120504080f070f0204110703080a0c0206070e03070e01080a050d050307050f0901021c0e03070501050906071b182a020a060c02011404050708010e03 77
    0x41c007519280f080d00c180d480e4801d69402d2940d0040955680c1e900d1844440004d00100b40c4c41107810311645455000b91100a041c440344080043c0d03d146404140400100c421007142c00220b40d0364000b42d25940a8102007450200200c8025401403505d00001c4945080b080a05581c0303000c4d0700c44c24442c0d50b80d1149642034647c000c00420058026500042c0902d00541102240c00c101408468150351252000c0d0103281c030a8100280030350050401c0720810a0400c12420054100c0c9009030031403d00c0f810141c00c0c0e00544803a840c268030081459a0030b80d200700015640e03030459102c0d441d0410703e07030032029000f8100744240901a009148010941d54002d1341142c40440c4045c2559180041c80e4451070480c0c0041e240b000c0404104200000d03403a41801c02403030140c1c4059100040f61a111100c4002101048101a0b591242c0301100f5000d5074010410700001c1307420440108080c00c4139203040303004040261140302124810410301080c4040041c8460a0780c5184000b0400800300e0404259640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 448606151 1250 448604901 448604927
    0xe0a090905061906050a03050309040c020312040312090b0f0a0605030d0e090c0705060c03060406151b0312061706060405190209040603020d0f03031505210a060c09030b07 75
    0x50302c9400418001c00150010003072420702c901d00003402646850004541d03217140d600c156010b500208030480c252a0a1251410902080c00194500310348480000303001070004201074144081c0307500758908000e0541160700700b40d0340550924403501c1c02e0720340c061103c201a50030942c0d080c50448046075900f00040d000240d4001502c0d141880041c0d030041102c420001041301490400602810000030000c02000c0e000e000f280ca01240c481c60f00302e007800101c0d2803a40c890800b011703404a502d910181c1091140c010440401c568040c481d5450405440003064100e05001162804100080c02e40c0240e6040c90b003202c00c00c098441ea5108c140c10001562000e035035246120b06240c1006070701b10900c0d401048030080252000c281c103952500005d000d20b09500c000d9915901040702070080591501c40c1c5207820070001d0b0580052420080810598803041000000a01e01116100c6240408000b190101944400e090290b02c1540740014584045844200d0b160b105c00004200860f0007100c0f095815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 448607401 1250 448606151 448606153
    0x100518060121091a191a040903052206050706090303150f0515181e04090305090346020a090e0616050d050720031c0908040303030902150a0e0a090905 66
    0x5c0c01c010700c400c40141240302d40207005811100c00c0f40d0468450707005481100c0e0198480c40d8842d2100d958000c0541035503d001c15030000d50810502125070040286e401868100e00300003142002403405600408c612040f4500d041091580056850452105002520420b5407980c19160b981e0340c0941c0302e80071380782c12100154090080c0a06509000348a0100380207030426100e01c003e0424049400c176000f18909400007500011800382070308003040344d07099420401e40e403006144100c646a414407028540640050110504500301800c030340c81c11000842d070002c00115019588032405401081c071552004080d000b00d0340090016034110400f50510450b9803586450004405142c40080400600310002d005034403228a07012400c20b0310f110380700d0740000c00859a0310160300341c08803105541104403112500300440c01c400034581e0016a02101d0385800c2c0032480300700910000b500d941c202144070529504c04200e504405620540076880140e00741c43d2041820b403140001410b0f00d40c04e00e80038020b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 448608651 1250 448607401 448607431
    0x60306030604020d1514010f05030c210304090e100506240a17071107080102090a15022401061d0306071202040b040303030207050105100518060121091a 67
    0x25040c0090409804c901c01d540d145600c1031083c40d44130032610164402c018400c00e0743c00521500810055090181600310000c100ca04202000511008254090700c3d290040d0300513801e4401d9010400e40e000351045440c1072007140212803510b581c910700c024020f030a960030400801d20034104000706138131609000345000c40006160116500b2a8010b062000800a0002607260319600201e40e481c01003490795180904ca611140c0c0c1030346051482c1e00031102c0740e48100302c849995960b04001c24221103006c08ae16039810884038061f81407417450f90310301501d068444442c100c161038124449050f00c88544841d11507e00c000d40c0c04000e1146444003540550065002c149258011803c010300081c0082c0050b140a44400198440e50890760088010a402088038004c00001b8054070342e100d02800135158032580742100107010300714040d00011107000900302140a0781d2044420607412480e0400f0b40075400b40c41c2840c0c03402014840802c0d0703141c1c00011030030b80040b0b40b00ba001c907008001c1c90703409a103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 448609901 1250 448608651 448608653
    0x1e020a17070e0c031f0b1e09032b0302070f030e240c06090d050f07081315030b0405090601091e060e1918030f0309020d150b060306030604 61
    0x20504003815144146214141c00060346024000c40380c2d205100032002c0c1522030400b140000b100c07100b420446500c91003c0c40f420310640740650b0035213510b0700c5042c2040745045024914000301c1d206805203986c06000e00d03905501010600d01d2a2001900718079080c00180b5100352084003240640303507000b0001100018513401103889180421340e8010018181030f5050403a45c00c0801020207080144040400468801d900c40024460b084d4401080ba000d400c2071207400500900038800c195a0141900d0003207001c1c001d10206106913142c01d41d1034414049040c1c0c032242d03241084d1090700721100c0081d0408044c11000e090900513140180b034074030010004d40c2d0a180d1350b0000791090b062041d8030300c003010301a00004582d9010700001800215901d14003804c2c81140e921903803c80c154524a003900388255201401e200f02800d80303e03182c26240628411003511012809005101c801a6020900e41c0c2c01b802030000c8081041d21480400c1410006044144144041c500007129aa503140c0c1100300024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 448611151 1250 448609901 448609919
    0x507050a080402130c0f170124020f1002040e0a0c0c082b02040306051308040e0601260f0a18060902031f0501030506011703030622090f1e020a 63
    0x203a00030b0310090070b4804501c0070550103012203002d007a0341742c0000c249000100724980c00500307032404240c03a045250207560410094001041d0403107890040940e0700440000c4107031003030000c80f1086450323a0964584103c1c41502c8000394101c0c1c01040004203000011841809440c4a45950f8070301070f0702c800710903500940710280c1d140c00c905041381c80400c180d00c0c03085103880c0d80f101c0313580603080c601401a121070a50a09008585004150030b80e01484240401c0202d410602614220381c40281411a581c4d20400100c4086060301000b002c00c0210702401c2c1c0240c008100c0c4140300f4040070602500a980b408284000e50b801455400700401c9070b08070460201e150382c5c00405030640050201c07401c02d09004810344c481403104160a1400e641d520051081080a01030540102003440450094078948038502e0740301c2c4405042d061003520040c80362010b08295075a90300c40002000c1c001c102d08041c0381042030742e40c1102d0340200c035040f00c0e0808886482c50100c4082940d141c0160000c501c4c141402051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 448612401 1250 448611151 448611167
    0x1060e01171302191a070b060a0608150a0f0e090c04021c0b18041a06010206060901050d03180810051602060403120b0306070c030f11060622020f0a02100507050a 71
    0x10703200218012a022584800a42841111811306003944d503546c0c500d418500d08071403020b010240b254000000030000b46d503005410607000751901e80c1d0190b50782c410b4800a21078a0440c0c2c410800311030380340c4002904c00340d2a82030501c6105550196081801600c007000204d11800030f407905604a92814040039020307540c05810500c0c0c001d80724480e440305449800143d07110440d01294104928159000d580282e00c60b42504030000380010b140301c0c00c2042c00281d030381005000f52401010130342070240906100380280300b082548481446d00c10303600e0b140c200d600d40c40d00c50300d00300386c1c0d87c00c0001055171a0b00d00f600201c40b0100301c0d40500165200c41e0f5080310224032246001460a4503113204115a07641408a40d0148a4030f48502e1068880b5160252071101521501030a014042411158402c40132a13815403001d006c0b1040b54449103281180745840c00f081468416552003c500154096107510082c14400303420380840c1d20b445041030521301960f00c02ca901c00009101846918041e80c003403808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 448613651 1250 448612401 448612429
    0x9060f0c170106200105180f010b0105030406230a0e0c0a0305070311032509051509151201020c011d030726091c0c090b0603130804050901060e01171302 67
    0x1139843c8000712052850709540064500c2091145200c0c0712950b02c41003000010325440b04103000740300c08049440042c10078000204040c18003178942c0c50200710400501c01511a407600324041d8250b5061401a02c4010710781c2030902c100d588901c080c40c5c0c40914112051500701c035444402043d01c6400d6a48050b03005070b40907500e5030107105100000c1040310550b1042c550b09464000706804251504944000b0303a203003d80130000b00c10703850844c240e8980b00c0000140d40401c01281400c00d4074040000b00d1150354441d82070359281d500c0030548109010064000c0110050103a60800e0f0a00d00c0e078202e81d44a200307540c002054100e09950780c11400080c0a150b40044441c19140d03400d000c000d0b0302250002a41c426080b9074680508540005c007d980b40880d8007821442e982040101c9200010400c24031000c2c0c045001c159220091400700114801140d025140281c43d01d505941c1d107990260014108044050100d40e00008206a51300c5100c0582d1107203460004480f020304d40da40a220407510203c030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 448614901 1250 448613651 448613687
    0x5010b070b2a040b0309061501020c0f03031c0e0106061713020303120403020606040e0106050a1202060f0c0307031202070b0619080105180f01150605180409060f0c170106 75
    0x1024044014500a0300080020500070384e5a46408000c11f070a15000920a4030040c507402c01001e50750f640055051581c100986214414524010029103940a00304400108400515401428280b00c1e042050310200010003442896140c281c1558805400341481840e440d610300040d06502100110728952400542070701c0c642041014811845001244d040c0e0160303000800740a124242840b841c2880600b0300003c2107003c5c1058002070b415801d52107616101803a8491007420766131540c00b00c1c0c034454070380d22000ba0b0b6a83c0305000d098407900b11450036070104648030300c4024500d1042c021103041c80d44c041880301080d07407030f5000c001c0703180725004c1141c40c912500000410300030800d20919000303940101c503501440d840c2c0d580e03040c5002c060365900801a410540541c00790b10700103004d081520034030b090141c2c0f121070101c24000480710303803040e095016040001c6070050081543c0320a41d0031201c1d8609006040c4410700a6501a035a40b00c20031440c030707480b401000207034440d0000000d5194442 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 448616151 1250 448614901 448614961
    0x4032a06050408040e0609090d030b0a051306031208040503030402040e161e0f030804060806030f0109120e180109021b0123070801060f1407050d1205010b070b 70
    0x40c0303628003207450495080b01c114400080c1404070f40d03425000c081d8800000c88040706030f032900c500d1068840400c40c10800070f0545600351441e841e521100b500c001341001400c0e110a01c07511442c400060803040c0f00640d1503001c5880000b400d281b10345a02441303107070030400541c40c6031580e60034000207003480c02000310383d0f0180b105189441c000c8c40f082040204100030740301c0407903108158900d0b0586d48580c021404c010350724a0401c0020480c00545048900074200425581d03240c3c0c000c24107088000d414920a5441d000030300c000c10400341c5158189040c140e5030140e81307002810921181d80c03180402031a0b601c02100040042000307a0f001072610071181128245241c0742407460b079094800010030b030414103040c2d405984841980c0380c041d642c00205813414002c03d51401d48045c1103001600c02c4001000010440c0c1c01c204143c94013110b00107503004080384c0b168000c000700103254140304820b44201724200400014806601c1c41594403d9400c0099104140c44400611000c0420076807402c1c190b014070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 448617401 1250 448616151 448616153
    0x19081e031519030f0b040209060102152a0a050a0e010c051005060f03150402090604050103020d14120f03060a060203030606040605030a1b170603061e1005040204080c03070b0304032a 80
    0x300c2060603c8511910011105d814144104070a14000078541d9046502c00100140b90154552103070741c1010341e4100103126107940b440d00c0b01030902c80310400050f010780040c099025590003002010341d45103541d601e81c81d5070b4031000115899040018040c0141c0c0c0084500050340038158130846e0020701c010b1407907214099200209040038551442c1200d842440f00803c13040d8101200101d5100104031000c1095605642c00110f0b4001590409003840f900c211101000200c10814800110f0050f44d81d913440d801212800e543d10361085405501070503110900055035400001601e0044000605090505013809000c4a842c0c00040000001c0c58a4100d665544480c14205441044080d580d44c0c40c2c0d5004840c00f618003460140070140254010003c00c5403401c0c2c035a001c254103003c502e51130f5a4507100c0540c00c01c0b54400c60341189510501c0000c001405400c0041c01a1140d0001d60507900000c2e0340360003501c040d00003102c01501041060703254254410844011850036000119003007038003840c1e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 448618651 1250 448617401 448617413
    0x9050d030305071e030b01090b030c03130f02130501140d0507092f0306090c0a120c0c14071d0114210102040308031b0a0210050919081e03151903 64
    0x4e0b03450f400000c240c3d03602a03c5081e503400b0810001906807081210702c0c40c1451070070b0010300d202c02408486403580144101d0b007000b500750b06079080b494004101d2901d40101c0c1841000420003841543c1c1c10b00803146056000341000c000c1c0040a13600700f400362040c02c1c1703800c09110280001c1da400308110b196040c0085840a003001c5c2020464081040498403480c1240501c0a1040041d20100d0703041c1c1c2c1070140c0300815910864800502d40e00e10f00200d102c0070162002d81d825402c900005000c40d4180501a4019000045060456800c0d030301c100c2d840c2501d502c0e00000f40c0c000307004c0c04010f49400c580e400c0351400c00c40c000426880510061a01c042c40a5108600f241c0042d00200c814980010900662980102c005180010400e1610703113051440c0300041d50b60a6090691f50200380c9035400168400003d0112500102e40050406049000c42c6800b0700c1c0c650000c01e15080403540c40000710098024901038a21542d11810240c1c03410340f904041058044000000000c600c020b41804000949 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 448619901 1250 448618651 448618697
    0x190c0c06020d0b01030b031507050d060308280c1a09030c120d0f0b0f0d0507080d0201090c061806030e071a0a02010b01020615040504050a0203030f0c0d09050d03030507 74
    0x6200d4000064529040f00010152490300380f001d8465403150440a080b88004d840c6190803ca2909210b5521038104150201402c220790016000001c0414100d90050341103800020318801d101e28403802060103003056400c0c1243c410b020300480000300e8818540344550300c1c040d41103552001260306200d4a2510580b4000021007a03805004020500c505045028001c4440150380c640050100c0c000e0200840c40d00d040001d0818412410b2420000502006000d40c0300941240400d4035000350407040d029000e00048a000c40d8541f01c108000a5290f03c10301c0700020030003110003569100f518080086000d450340301c0040e0031318000d0003c00a9040b00f804c101469019400c0304054a401808a0107030031110046005810741d00314038200000e1031800c0d0080711058008640000d0191590b040c01460004a004001d415200000348100c40c03c19031b0014110844265089402a86140d08100d034481d14520540e034010300c0140038480024000e0300080d0b8880924640700c20804000a00040244 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 448621151 1250 448619901 448619917
    0x7060503190914071211090f150d020a0603021305040b03070303050c1c08091b0a180902030d030905071406030705030601030b09010b130e1314070f09020d0f05190c0c0602 75
    0x2ca00e4002d1002c00510721400203451b8802c030340303e040c42e1a244243c000c2c1d03114003d003003100d10b0084821400d2240c1c1d581032042c00482e00501180702803031316010060000d5010f2200b08a01e15020f2a000607649414040c0001201014000c2c00b2a5840c50703805a4064000000030103240c0282c21158006409072000911035541d84d07680c0154030304100010364284040c0680460490000e9850003a41c0e0312081ca900f4111140c02c200c242111548008610003440401e600940c940a092006981d096041d00440b1285020b8800c3c0c8607116039030004422001d410310126500040c092000403c002d0003480130b9a4400e0040c180410500c030200d000a41401d000d130452100e41d8404620040e454000403141c0002e00000414101d050500c8107248400303c4410382c00401703a00c0b010245c42c2c502d41061101e2001004a003500b2514981c83e50a800003941240112104161030540310b1030b1505090f0040900076114010703142c0a808441c800800648600c020b146d00384542ca20740c480002c0d17980d2000305102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 448622401 1250 448621151 448621169
    0xa03050a03051b010507021f1d0109060c0f0912020f03010c0c0506070306031104020304030306080f07060e0105180904030e030a060f060518010b0c0c150702030706050319091407 78
    0x1400604111010f1000710207200c3c21280c0c90107040082003500050441c9241603000000d82d071041404400700302a010421400d840305200785291101c0c078005400407040b49109813020303c4207140d02241100d2070140d601940002070740c0b5120410440d2100c1c2000e00b04507001a006a40c41d4003c00003107401c0d02d513100aa40c00244040303070f22205210090001740e07040032491a042c00f800385980ca520050010074410140f043d030340040417070105402580090001c21400c2c5c140c440c0c0901009019465005511442c030229240c80c1c80b031002988200102c2c1c104140700c26042044c4c9101c00148a506030008008600b4080840d1410b88555810050b015007144150300200340d068032600317142e06868040d40410b0007605001801072000741030b0002641555001250140c41d0040e0505407480c00d0168407015070020f550480c0031f000208054000c00b1540d00960407134102c1c5554610480f00740c40f00311119001500e00c070311000c0d028200d07504100513041c090280014401d22420003035041003080d0b4070004507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 448623651 1250 448622401 448622407
    0x3090c03030513050f01050f0d060305060f1803030705030c0a020106030816020a05040e4204030807020705011e0207051f08010602010c09031118150a0801290a03050a0305 75
    0x52000c1d00700f4402420b01070781c9801080c2c0d50940042c2060040c1041c0d21203400c004140c50741080c0e501c0c2c0c0103d0080d03410000f03c9405050424005018240a44200d201c14000c00c41111401700000116070042c0c415030748692555581c4200d007242c64010070080c4c0115520790701300002041160018186803e003400b0514988040340c810080e420049034800c0d0300841c246000c1d0780c07a0140100f070348480444504096421070181c0c40c60400800912411120003c030f074105450302c10702e00d1204103441544203403205020b540b54000261380d280e4152041d240020f04d1841c0c071010a0b594208084501d151500480305055200c0d0300282d01400c01c8050071481ca44082544000560301c025024010201c0c1e000070401c6158003580146400d485000c090902150921002140d03140c02c0558080c243d01e0221543ca6414410ba5800007203090441041c82111850360108818106102d500e010060186840b06041d107041c0c2e046412003041c40010380e00c8204200300002180080c8408411144a50f440c980d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 448624901 1250 448623651 448623667
    0x30221060112091208040f0f03020c0414040b01091109090c12011203050f0307090b0d0b033903070512060f0106110a0209061f1e0c0b130303090c030305 67
    0x482c407528031103000c12940c00c2a0f86070010824107440d0404112052401c0c400307a65031400c1c002c0340494500c1c070040026860b100c00000b45540801c100d444051304070303401c1c0310714007030000c00c940000007e55015180716156401041660003550040c91881d8480641505102060001401e050310440760780303002c408001044600715001ba1403040c0580300d094040e0480d104d668500a01c103015001020b0311030507000000c22006070168150750000c2101e998620382c1c8840c080c20480103054071141c01402845405001c180b0000d107469900c038244040043e188180a07050007540002e170000c640543c06001e1240080b41d1900e90a803100d02000302d000c0104928200b0f03403609910701c00705900017000c004084c14210403440300804e42514450301125000620344582d40010360418040300044041000d02703c0861026400c0454120312114030039840c0caa04955900554502840c0c0d40000c281c144280002480104108613218003a400780c42c0c0081d459841d9590980fe00c082c0b034005401044010451007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 448626151 1250 448624901 448624907
    0x30403050601081207110d060924020f16021206160207080c060d090c1815050603070e0907020f060408090906010f0206190b09012c13030f0302210601 66
    0x750040011100805602c034500c00f0300c801c0e80c001d10030024a50b80c0407502d901c0c219a21050403001c007903000b080c03c028100c10b42c6000082981c504a000b5862460315501044403403843c070a0390095242002481d1030000320001035141c00c4590003049900a04200b09a900c2e80810400c5910032007030880d11503861404200c0181c43c200c0c80354400e030f1241d4005250325019480700011307500e80305409280807465451a261030004041290400903140c8001c25242800f008240c0100542c840d921a00c402010345070014001148421031b06440440e008482048250a060018a0b07000d142403041c1c1c0c0e90300203000540b034188003003a1029a41c512000c02c1c500d4240c0f405d1100d40d0342000d000d081086515216013806501d4003c01040c40c00c908800200b5022070301c895401c00c0c1c0004000421024081da140c1001d40c00070401c0b50340c3c0074107a072480080a170301124603003000384c0500401c003820080002c0035a03040b00d2609480c000c4200b01074081c0007040c00301919000e030080f030b810b45002940c89403410784001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 448627401 1250 448626151 448626163
    0x70c181508070803040e04060b03010c050d0b0423062403070f05070510020309030c010914010b010c050a0210030e06040b0f060307061e1e0216050607020303090103090303061703040305 81
    0x2a1000380c1000c4003c1011030b10000844040b1030907120300342c2443d555814100014020b81d10010740550030004d4441c1690341c030000900508a5401e005c211070f54910301840f08443c2c2c81d0b4140340d06821b100741151140040080f0090740202c004000103011501290166000f094140c00140050804420b1005240d0400740c00409400645846800c2843d01c2d100c00703942e80c00004400c10314aa00001023810541700784220b42c00030020740001d10080c4914504104040030205d40a0215403800200d841c0300d40c03007046001003440d082402881c0c085000d4003000000c1601518030410b040d030300e40240020003400e100c01440b030f42c01030520300c07400e1a0400841001401c02026641310307401001c014084950417158544142c40702e92814044001c107510161401250031049481c150f030302c102e0304503429038002a05450404010305452040740d950003403000500600c00300070750541082c095000d2551082e80844040d502034034021540741e41d107910a1990f9110025035589e036400008090092210800c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 448628651 1250 448627401 448627409
    0x109020313110406051804060509120a030203070210090602370e0f0405100906051e090703060b0301090c020c0d0507180912030e0d0c03080705070c1815 67
    0x419861481c041c01c40180741605a2401010034002c000404140e40f83e0768028800341c2005095180900258a02c01c850614104d4040314074904000000351201008560f05912440c111481800d05513030040541c0a074000800e010118482c500c2c54851b44c200d54043d40d00a24000da0700143c1e2a03446184881d00c041c0c42138852407864402070740300740c0c0c0040164001c45c07861681d80341c16003190601c80c00041c4401c07004071072903a000e8103090901591401c0b0040c41c1040300d81e00a004c03c201c95441091205011240401c08410301c00c405e40071040d42440c0b426540e00c42018a00040c0482e1520800300030354100381c022081030b41e42c402e8a400820340400411081240841e111200c0c10315940d51555a0310303060165940c0c80c0c0c0315014460701c0003800c1e048042c0e2203500008a020311450840d000b070040480c021101c1281c880c8001c10540709020300f046c403c18a8155641300c403035550b6014103440c5035120b0f10b005caa9201e0340e400e00003000d0340001c443c10f00c100300744040400d0081144000d9140601c1c1a04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 448629901 1250 448628651 448628669
    0x301180c0e06161a0a051014030607080a1b020319030203160318050a030f0906081e06060f070807021810142b0b01142409190e01 57
    0x5440b6618542514111144800c012162031244d02d0f0a028118211000b44400c000303000a200d00300860307400c51841030040c002019403c079a0360461400e4000302019941c2c258100b0340104842912800041d40d0000045002013900c0b00d1054041c4840030305d0000410050f00089140c55105054442144084081341b40a6041d0f0074480400c194400012601c1d8003410350394401200740c0d80d0405180c00d8499004000d07507404240c1d0b4100038000043d040c1d41c0c40d00154201d84086480ea01900380580640c3d00000d4250a1014060b18442c140402a084560015050016184d45114040142035140c8951991500c038607803031041c0202e8000d40d03441b400c03d07190303100100001c11421038031740022584070030196a000b01e5034001245041504c08050640d4080e40610100c07510110038043e04606e110322129071803a070381d9100c1d4880901c060328845620685204a080d0112001d920880b024401c1c00002ca00d09040701c0d000800c5121400991600f0301d42155040007202c0700e0020036070040880c21 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 448631151 1250 448629901 448629917
    0x907030621080f0901091211090a051e060a080703050319170a1503080d09050d050901140327060702010f0519091722080d1e0e03030301180c 62
    0x2582d800d41a00540380700341d00350000400c24028513845511020700514005418814031181410300c2445400241006806000c281c00070800701c0d061445410302c00c244000c0210340a8150b0f007404140010090080343e0300c08086c103408110420244641c1d80110701c1030b0000c540d2100000c130343c00349403401c80700d0b103200344041d82c5c8030304d81100381d000940c80c0e1240e2080700002d941c0c00c18801c5040040f21540024001d90700c0410420810b10346a07001c0c21105000384c0449950745140c1c1c004071220f100c0c1c1c5019600040801d4040180040c44401840e086400100c0101c00003460241307110552100c52202203140d0701100078000416028481c041d2045034105042c0f14a14000360b12104207a40300c02851480b558465805040c054030700c102c08108a1014611940c0d41280902e041d5011410348242c2e501c0010403c2c0040c1c404d0001801c04405070560321490040c900c0034904440e0b4024080744101800182104840c1a540500003107029000644041c03800d002c07104203a0b42102d401c284041c040c06242 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 448632401 1250 448631151 448631153
    0x2160e010509041e061103070201052406070212100b10050a1707020c040f1e051308070203030d0606120501080d0e0609030a0b040c0312091a07110907030621 69
    0x100c1c142d1940150041e241003501515040c00104130740f030214000e404607103440300325405950100011400341c25a64020f0000d80c8504c0403590780740000f00202c090f415008000c8841078105500036040035230008252021008c41145c40e43d00b0301c44280d1480400c00e640302c020504528050a6800c44a0b0b8146411420301c0d05200c8064400f644c003806e0103141c40c0b0b10b58001204241700b0020118001e40162041c410700461803400000341480100d2000000e0900c070640000c034034603206441c840d42407227194284100c11615401100d6020300b501b070b03070507000c2002286010310803401180001c040564a0001001070000c060088840c1038010901d10303004189904c006580c8080d1031104400204c0c2e0041c8d4800e1031200091a003000c0e2600203120545034420042404402246001102d015401b1640180ba0507501120160114020b0a0204100c20040c6c010284081c0c05000c80e54403401c2c1101c00c5908040028070020011114203001a07280c00301400103d100400c0b060300000340310500e000d0600b203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 448633651 1250 448632401 448632409
    0x3030608030711010c23060a0e03090d02040c0504031e03021e0d20010c020c1504080d0c0501090f050604150515090a060e10030506060d170304020a1502160e0105 71
    0x441807030b030410141c900c546080c8801801e0300800e140703408900700c1002e11030084081e00c40b2400c80d505242d103440e0800ca041a8270012040303a0310310f400288800300c02080c0b1360800c001051000d00b0707d0100541400044006040b8502140c100a420703114405a083c131450020701d0b100d10315150715601d00041100c038440000004503400f00740250b08052054995951a13aa204c1002e134485010350740c03d10036060102c58003c280d1908141049d01e541240d01d8280000d08400d2060788282e1802d6484000035030f071450722600380110614410f1001150200f4262580c40c40102480e00555894000c88140403c01281c11290741c0320498501080c060342c0f800e17202000031440340d61080b90048040000050403200346071b100310060200f911484003e403e1807000209a40d800340411280341c400c0d40c002c00e00c54500081c80808241e80304000880410b16982c4d03400003504080c000b203802c00c4000354045020002c0d19000700c0760394840d0b801818040001069540c1ca4100ca5009078602a1860010710864803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 448634901 1250 448633651 448633673
    0x603020904020d050c0a09060503190b0105060d0e16051201060608010605130f03080901200c0d020613183210030b0f193e030c07030306080307 63
    0x24040340c1141c000f03000c5080aa05000304071030021b030301c00280303200400d40b40140d0307001c901512402e0b070441700c0c0d84000707240303001d0a102e690344041d010400c50741c0104454a0b04000505400c480c410002c90b101c4104007040349003002c401d485100c200a54142401142000c2102a0581a54070024842607140c4240a04004018040c03513042040010300707145509007401c2e100d00101301d079a0047d91075699a09102c43e10780c010701700480c00100c00d180308104050180d00c66542d92580340c0c0c05440c9419102c820441c002c082000200d821140600400070000c840d100c0100080a4100303060f0502d2040450a81c100c40d02c001f04090f0f01070146104003098110454031441440d200c1c503c1900075114464820390f0003e442c0e03c0204051005c01c204460850011209401260007522501c00800c0e02c4a010081d10000020b00034807402c1203a4050441281f2505441140341402c002081c2e264200c17401c003102d0344201ca900021910010f0b1900400d075140c8a528000c008001c090341c100302190303480601c800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 448636151 1250 448634901 448634903
    0xf04050906102c0901030b063c1f030c0e030102070812060409020a17071203020307030807120e0a02120303010609140406170a0c060e0105040b030c040f0e190603020904 74
    0x112001005448014192080c2d82083d0024040380c039075a500d281c02c0030703142400c03114a0701602001900c8e9031109001c60394501015074503031404208546030122100740201d2100c0069121418070424600c3c2030100c1c2200500151700c0da0081200310710008058401110b2041d0b15000780e20400055000c100d03007a050385c4c40900b041d4107c00c01603c40c400040c0141030802e8000e580b259210f40005807003411049600c0c0003400c090305417507090342c0d181080d500c200029400074016810030080c800c0002d2140c5601035011480342005111000d42c503006904540001821803a0340e403020b915030b0258580380d001c0708894552500118519810034400400b07214103485103140000d407940c4041d42d00d40e03568001c0700180c0406441e160100401c5841d19554240959023035503001c0741c00c603020170114443e002115003070344181c540501c3c0c1464a4220081030b80300a02114100200344070200c2c18403501c0908c60010040010344c071020b4200000505480a18094028400c900e0001d0420060310703070800c2680e0003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 448637401 1250 448636151 448636187
    0x61b030a150806010303080901020307050a0c061b0f081501090510030b060f040905070305042a030b0406021209010209031513020a08010e0709050402030307020d05030706020f0405090610 82
    0xc0e1100c00c5268041e1031403264803085010104000700e155600011000e040781e000780c0d0b441c403060301c940f00d0309800c03440700351050700004804225034189640540038151505100e0080007801c1c1c043d200e4200c940b015a855910005150b820000c00f0081e80312a0703081d0004038211456014103820b00011305855064840c040c001c503075407400c0445140c000c1e072280e082d0280150883d0b50300d528082d1002c050303074080d001d07584a03146800045007005110f071040c00e104582c400502d480510041c051108a041d031150054a080608070005c40007401d4040380c8e90085100e2200540ca40d816090300e24074a00008260550703583c0b0500c8201c09603600040c861096010417a00d62280f511210b00801a070000d25a000e5000407504c0000180c1d001c0c15440f000791641103500f92070103541c0b40d80c500c400340c501c180c801a505a0082c00482c0141c51300c1c1d0407440e400d40c810b000700c901d0a00607942e05c20503130300b19010b0a0460500401d040080c0c1c100514919400320044034400d00300303d0304c150090000041001c0810325 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 448638651 1250 448637401 448637407
    0x406080601140a0b0301090506010f030516050c030d02040308070b2401051b0a03170112080f0a0e09090604051203060904060c1202040f080706030207241407080603060108061b 77
    0x481c1c0756181d0740401313808110481980ca41c1c5401000c3c0281100791034080c005108801e84e494213902c00c0c8a003500410001d801d0540c5000703203480c101c62540252070003008a010400861790000c0301840100001d43c81505440c3d11060641421216110010300351500104c60300c8201c0245d81c07055148881407071003420440e80f03400c0b91440840c0c0031020b01400f0b0210b4400c920701c982c02c1c181c0000b45014161101d00106034960f89800c1050400b5241d10300003850881c0c1445207a48042c001406050228920701e0b108803007201040004000b29070540c1d502c6402d8104030140800e001e024401c1d4100c02e213040e16003500d03500700a80030032202d01000344040c28050362824110582c074861052208014000030303095458584030291101c0300c800500c00c50101c0d2240d04ac0c00505c1900a00a551300d064000700b101041d00309815200800c50a810510882560b64003101504154580e46a40c010f01540d07543e036500d403405000f49442c01070181c00c800c2555015400f04003500d21082c010381c005c451144980c0d51 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 448639901 1250 448638651 448638689
    0x303050f070f1a09030901090603091401110d0506010804030e1e0907030218042018040f1a09040c120302100504141b0105042d0602010501140406080601 67
    0x80c90300a201e002030140c48002d070100d003800941d0918180103101c01200d410151078a09200760b0360700c074004402d4041114141c08111442c0254045d1010902481c005089078060054240c2100d8148607054080c241c0030840003004103103441025800582800c1c640c1440c107040d2009400303608802021071088a071820b45e03a02202030010203c195500160220005040c80d00c0040c01075002120b241060074410300e0005643c0c680342c003a060a18140b607846002d003440c0204071203100d600c4404030003000003402d2001d202d9600c50b07108020074004100ca00213400f00300c440580755030310243c80301c69108181d20418800400e43c081003d000300c50a00d861a0114111451706a04010071800a082d07120300e843c041005100603848110045e010300c2040d5401c04034480d030721000c141042040c0078000740c0700744024040300e005003c20b41c1c51415200407240700740e030082840d0000038945400c03081c0180d450708010001d0995100c00b01526070421076040c80b040b07080c80d910a540e280705114022030401a141440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 448641151 1250 448639901 448639927
    0x14030c04170a0209160f09050d12022b03050702010c1e091e150908070603181b0503010c1b0822081501050603090d0c1106040e01090e0f07030305 64
    0x651a1507000e0321a0000d450800140175449020118641c0490303444002001441d100301a44010341c0c8000305a041c03500c549456550f40c003c2202c00e02c10039403050540c4842c000d4011080105075418100000401d00c0c0000002400d407800a80810150780c14490315034141c607003080900d6401040030041c04400c80f2241c404642081e8168070094450081d681d460304400e28514040c0c0c10b03121084204261000b4004040310064124844c540450300142c04c00d0007010303c00d4102c502c01c12061004821000c030107403210380c3c503003000c00701410031080264810007440c20207000c1c000658106060035445c0550156000d0f8411a03100c0c0000c7c402c0c08001004c00660110094101c921540c204540b03803450340f40d611382969280e090380c0a00140d0101e1300001041e26140c81201d20601c00b28000e42003130601c207007080d160b40c444400b04480c40c0009003481f40154032080064401001e040c041c0d105c103940740010729022520205000107450f0403a601c01181c810740054441c0850b80d01d4649540c0c0c0c0e5890030440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 448642401 1250 448641151 448641163
    0x60c030412030b0d1103100f02030a05060d03020a030f200a0c15020d0e061204080d110304080414030a240e0d050a08040c2301030b030d210603061b14030c0417 70
    0xd46c002d1407805810040d0789402d0b42c0078520900340f2079010401c0f611007000b00144041c3b401801001a80440e543c01c000a22540307001d01ea00c4411705114204450400044407003030708409040590394411039001040c805400e40c054003c0c40000c81078400c41e40081c100071345491a4180c0711007440601d200b446070700e4039101d040301c803580c802c2c1040c05443c2c101807818017010760000d07030202c29250a0001100580018800700c84c041d07507120070301a00c3c3c02c1c41c1c0300c4102c05c0030009408040d4540500c80307840b0045101d4043c060188140c40d40c5d040301081085c001803080340c0c030304203000350103030300c40c0310b40c60345803074100c4110f850480b903600b03184905503554640b2124014403508000041c111034400042450340d8500810010320003603c083c080d03c100241815a82c0402c44001400130f11120a0291401c80b140246811070b40c60a5011074259140d0700c9020a4454a000d032101c040b40324448500c560b80d022120156084072402d0b21461030030003032030b40400d078055801003000c0c54a08280070740d2058000c001e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 448643651 1250 448642401 448642423
    0x50304080307061b0521040312090305032e06200118022805010f1701030b010302011806051e04120501050f0c2107050903060c030412030b0d1103 64
    0x441e5500d007000d1501d00f002e02100040f20320402441e40020b02400c5c002d000b501c07840700900a6001c1c901c0d1040c989401d03500b002030001e809100b400710704402d031058940250b5107120300907150140c0d241031441c0c1000d05040c4800b41500308140b07012030220a40719681d000c1c07003128103d107410a1035130214420311060120002503603080e50310380598160f14038500c4100486803402201c1d605d1208003039568178203010260151810764055a01424030603980908541000b619880c640903070a601c80c1407218800240a0b0025501001940700400856a011603120108200c409180702c0c82407800300003030154005d10b103603201060603040a141d130501d48442610014903440f040d5090240c01410600d008281c1a01c0c51610440301c000001c64200c1c440003124003003080161000002030018046a03282c280213007020003002403c220302c022503035040003041d00883c81c820b1880d0780c9007403a182049010320345d04000c0b400d15040c4810410b07a95a1050400c2c1d40c00d401c501802101106032002905008100311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 448644901 1250 448643651 448643653
    0x180a1d190e0a03020d0306060e031c03061a07021302070203031219020f09120c03101a0901080312070306033503071211040308040302190905040f050606090c030a020705030408 77
    0xa02d8414154002251811410151000c12200781c0312002240c08071072441c1c4042e095444400e07054100c0d45051103503112490030f8600040c2980d1543d840d0340483c0381a5103850906030001c120301c42036181004409800c40e510b0b4004600d4007501e1b038040394607401201e94400000c1007200015071550801d0846000820526074110364032600714602028035040317004034500585101c05141c1034010002000050400c00600424202000700e061601030020b4044240c203800380071100b81507503282c51300c01034080c102002c05540c4441e4411440120544010400c01c101070500d03008101140403140923001c81c1e12681c82441071440003821391494003e400c40008020640003003000010fa51200c0ca20502c083d4400307060210803020401080c81d1b00542c00b0250412900f000704000502d01080c1074100c01c034008081400456a0f664141e04a640c1110140c9030524803402c1c031403c010051090350303801082202c1c0d4000c1405c0002611040d80401003820117416030008070322040c82030810540d0700409400c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 448646151 1250 448644901 448644913
    0x114060f04051f110c011d1c030c15060b0d110c0f060702240106081306090b06090109020316030c0203070605011d0f070206040f0c0308180a1d190e 65
    0x550b103c104418180d0720800080d00380300010008a4045502ea00d003000c144d54120000042c2c0e151b211450607050410340d03011880681c8007924180c415600d15100380079480380414481c580c14004010a240f08000b4422454401c051200d09410705c2600c902c28030454000642c0302405118008510900140d86510b2103521a04003030a000011610b01c10f005aa080d56107600c0e80000d0541c030401e8040288854001c280c006204c190f22a1040300c0d44866884408a05444517480700000c507001e141003502c074802c00c0c20401400b8184080700328010000001c085255183c58501030f0b201c04501001001015113410001d00c80c0d0b0b10070030668137600e0b08070408011550351a81301940318000d450b0025021406680001c1500060120561081c00e054002e48202d50b100d589800007000310f000c04443c042c0c2192004000b0079071071005400d10002c0b008041d941d40e080c1104108441a1503401090420004040b862150007014074107608021240c40404030507800c03000410103014207101c070400c240b01d05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 448647401 1250 448646151 448646179
    0x31e04030813180c090909020114070b1006050901120506011e08150303070c030f0201021c02010e0106140319060e0312180703080415020f01020a0302071a0114060f0405 74
    0x1220311100311a40030403100f55280030040400291100701c0d6151010880c0d08808012554940d004803a00f0380c41490524130080b250108540150031402090700c6400e5481304000b109907004d0b42d1200907140908041d0304190a1b5000244a0030041000040c0e0940b290042841c590042200c80c6490700344254a40341d564086c01d0050070f03101c017142d41103030006892410210a080110407541c4a5401c07001c001c5000c0c0c00c42d00e84000c40c1106050890461007841039110a00d000da603080288582c855001041e100e2030592101e0a468003600541d4043c00034003500c036407a940c00510360300b1142c220408c01481000c00c1c20715400809055024890714040040c0d5580c2e0f0f0700d078203024079104080d0084820840200850841d03034a00640c04002d24244040005001500d928403552607900304601c11501c8500d0000e007a1404d80e00240d0b03080000c6900442c11408100d201100340c0c416600b088010030301c943c50b001c410242c0f101d00f0a841d500840c1c0019401c03e14000d40307400c480180034040c150b410b5154107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 448648651 1250 448647401 448647427
    0x6060a050d09150f050109020306031c0e0301140105031c23090406060807120204030b040f0f020307180e06060a060e060d0606080415140a1802120d02011508031e040308 74
    0x38013101d564801d0700c1c10f000484c8444861017500c0c001c481c0900102042001c3d81c10070064002010241000d106561018007909e40e002d000d580144050750380da10f000c6505d01b50626143c9450070802070a007071501d020a05810b075020b034449182411446441c00840410030700e45a035032013400021a0410b003010404140c0581241d40e10780141025a1060310711a40300041e80d04a01548c08000d10400711000445d000c181440041c0c1101750107610040140542680003918004183e400340c0425820340a40350b80100e60307442902c2040b10300d2405410030f80340020019010f03003803a000f400e082c410700e02040065502d0305810f80d111489020802c110303690f19140084d081000482e0308880c4203c06d4181601030040d03034060341100840d4030704001345588500c0c503500050041d20401e0b00c002e41d881c1e00c0400c0542e40d5240896040300c4075402402d050a40d1040090030f65291001290380b40001a000b000604030010440760341d4640d0307840c00302a0b406500f280000f40d00c51a8005006c002020070582c81b41e0b51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 448649901 1250 448648651 448648661
    0x60f01050c2506090e0103020f0a0e09010b032a131d0604050d0c0201170a0f0c050715050708240d080d050f060d0f050a0b090d080f06060a050d0915 65
    0x5030b40c4400000c00340c0c1c940c0100c0e80034020b40902008203004800400040c20b2280d04042d074440f0080640c01e099464014440754100300b1608030900c0d0317440380801c45507405d0030f001507a1000d1108507103138a540c07040442e0a0031810460383c454000d092804024400500d964408080d071f41401140705c2c14000703103e242c0741d51071a01703803000d0b40c180c095a40d00c6030703034075002d141400d0025506071070708524003600c50404500164010400309059844206c065006a003a1050441e40100d640b91951143c1080c14102d0ba24040402400c5080340351201384004107411030704941e44841e925009150b0001244103018000c01c0d0381281d42c0e00000d03004005030800071442c020b40b03408488101c08001070b580722020600001400d90b21107801100c654000c0000c1a900e140b0300041c10f00407421604441250f545070f440d5100101c8820382e098000004c1400d00c0c0358420402d40d0001401440800503080810005040744144080e0009001000500b02e03510703901d41d00f006484940002211250078401d21448010300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 448651151 1250 448649901 448649953
    0xf050d110c0a0f09020a030f150e010b090919151502012a050c0f100603050706090501051b0c031e0f030c07090209190b04030b0a0203040b060f01050c 66
    0x1c0141090250503040c01080001119031100301c0489852401c413001009501000700c103020151103150b182ca84c800c443c0220b629000850b500d044005151107071843d180d00c410307003100345080b0741001041c01568803910f250303030401052110314800380b2410001800501400302d0300c0c0344050344400c000800c110700e1140e41440082940080c408007041c16140085003080300f000d03000c14048087c1504102d031043d00901800340c02c000840c0c40c034895908840386068074030707410b1144032615141c09204105040c00228001d00c40d60424a08442c21314001800b41d0051402c03c1104103071010300140361f00010401c826072148060306460070500b40c0300e00c42414941703010003441284101c1c4529030003104000304032000342d20780501801c002c41c144085000030358820030025600c0844405400104c040d2080c4030002030040d0704c00d0990300c070310f145440d815150b40200791580300c2e0b205000b00400b181d241c001c0710b030b40305d002221003594078a00b202c016205401910000011803140d02642c182030144188200840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 448652401 1250 448651151 448651153
    0x21030306120a0b04030513030b010b07050c100206190209100c0c050123030c0405091303020105130803040b0a1e0f110313080d021e180105091c0f050d11 67
    0x10784041e42580c1c1d0344100d804001c00d40d4030404001404a0703c154003424101903010203907040242e80c1d031103100b6030040a03000061209000648401040343c20405050a10b000b680c40b48403402400c00069141e280041c0803280607441da66a0b45070b01c94143d03040f128518030040005010103120074000b08900c0d1140340440c0c9603090035070041800d43c0034001540e45c18004074895403403c4801d400c015042c0d00068880198804144004030b81695250025442922280b039400302400403030400900f516800f500040091294180701030200d82c03464200c950058014881142035105d00c4c904500400c2412038600420302051800c00c0b000c440368115a00a031003110301409100c10848442c503441c403040e074270314680012143b802d00000710f4950140c12240081680141840d0310030a030707950b8503040c180318941b80841c0007450442c3c02c1c01596088004e44402e18080d03040c801d03100c02003081600308619100343e880101c4144010410380d8207102e20020b500c40241c0c0c3c0490030f070007005004600c2c1d007090f6801e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 448653651 1250 448652401 448652419
    0x60708100f090b13091b1d010603020a020a1b05130608030307080421050d0c11031c090c0e240604152606030d14040b0921030306 57
    0x548500040100240c4a90414021095250400e0000140310303080c6440e401441c00d06035188050007130304c940910b05010b6424211a1b09840b20b000c0d004d4021030308000361030400504110140b6a41030049419141182001a694040d4410a074600024010020400d0700040f280990030703c070407802c480071914280c4040602c0f405045480050f1605401401190361041c130009000d130788210038007500680110340442a011449103445100100c0000301404150b00184400c003d40035842080861001440e141582d07181c0c070305600e9184d2240c071643c15601c81002800d011042c20603400400019840030300c042c80345e90756600e810120311701150700004040c04129840d82e04012a1090342001d400100964030b4641040d601c01040b0255158000c20081c0c840d041c00c0c0b5503041c3e4100340c001d01072402e52015071440d19104140c9043c8240450750100110300802c01031000d98001580c081c3d0b40c00c80d1740316481e640c41c41c01146017451034050800d52481041d0081c16001d03008001140119020f0700c3d880ca0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 448654901 1250 448653651 448653661
    0x7150f0306080c0d1e0506070f020609060402040e01020d0f0b04060b0406080a0c09080a0c050f0d0c1503150b0406081b0a08150402041706130b07080402030a14060708 73
    0x31a4100c0c400d0410a4000f2810782100d071410150900c1c4007445450075507020180e0410390a1188511982224140c0c007080c2404642600040e0020080301944000d1009203040c7d124181c850784050720081c0940d45408024000b242c0a405441412405100400022514801e10381c00742103001c5c200b81c01980f070000c0c04500005100304840035140140c40e0445140c07200c0310804010b007952440c0000b001842480480d83c00c1040c40441d1460303018241c91804c241c1407604000041c2031880d003d0b4841e150034544500041d0000d0340d075004851107000840c2d10541081e10507005070050040006941c81d034020301040600014005d0400d4404c1a03079071150302c0ea218900e100300704e40c4403040c08071250f0090085802c40e91080c41003a9002c041c035148241c480c0b0441010506a03007042d00580700041c02030300f600e011044104400d960000300d12164249250316602c1d251000b080240c51881004441c10008080d910100180c04906d50701134001e81000d50200d40c0030752240c4050b200100003403c4240130070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 448656151 1250 448654901 448654907
    0xf022e0c0b0f090d05071110030e0f0606031f06080d080f0f100302190e2a18010f1701030c051f14090121050105100302070b04080c0f07150f 62
    0x10344244841c10040c00380050b0100d0039517040c1c2218004640f0305040c550300c02c9554960061042e0104016140807443c046241c0032541403250a08056003658003400030028103581c0040d0000c3e00001c6a0340b00d101d203c40108008001d850f6940001010b88544407503101c416500c122610312030a00c000a6007456103803152030250051064a04a80c010051a02400035142042c3e0640d841d05000d8134101c0b000e603940c0c0e000d0010700000c41d00c15800a0900314155801c0d0703a82007092166000d1502420b00e01841c0b018809050400b45201e40c4c1004180103920701d2480c013030055400c1c0200c40f54500e4410b076030340345002c21201080c4d005550041032640282c151178111140c0008100c1082d8807089850314840490746801c0e0403891241c2d040180d11945103e2246000d8200a110040c801c0003007102d42c1420280b102c03078800100f190040620402600010840422016401c03641c49502c041e51030042c1411a0325100c07050810750303004e018042c07001602c81803a905401c00ba210035228212040c542d01c0303080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 448657401 1250 448656151 448656181
    0x906020604030e0103050a1404050309120303040b0c0f040b070609140a030903030e01050912060a140f071d090a0516050423010306080d030b1c0f022e0c0b 68
    0x40108581040c04002580603030402588440080b5001402e1005030308c1940890106545c141c0715a0000545810f160808140110140400000940c036505080e65036402a0b00003c021000d105008943d500e00b801c450400c0ba4002c2c075440c0c40f659101c13070701400c080d00205084101150005000010f50f03014039004240359515903010740354070705618030b141c40603210408035a030f0103030400c1800c00207450980d03100030302e195002c0003400040c1043d15114000384200c9045800742a449004442040b40010b1680c0d103640d40107400d840c19000c0c080182c8010008600c0d10b46909070f100d920001000b420b0304413507001c9413080784109682e40b200c2e04011400d540c1442680211402451074100603074500c5c00400510308014018540025600c0d540d600d0715080880d200091030009407174000c0c5040502c3c00b401002050b03c0228960440c8010301c2d40d900d242082d14240c0203010700e4211591100f00d807901c1c0a02e1017809000c0c1c01114881421160090643c80340030802c0b5003028014005c42c0e590340c00340070301c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 448658651 1250 448657401 448657403
    0xc08120a14091e010e0d05070b01080604120c1703090309031b0d0f021302030103030216060201140f04020a05030d0210050a1a060f0d020f040315090302121812030306010906020604 79
    0x60025030140b060001c5440c9200c2e148290743d50748503990602d604038100320701072a8007801e5507105d4640d131451502411800c4184d2284000c0c2e031085040c000070550b4100342c04078075603442c1025680b041d114902104217001c0301400020f00703030010040203160700d000300c01002440003ca0036985107021981c4181d40e0104055842d60b046001070741036030300003044021070243c5903000605003080c809508206c04103907071090700100d0043c1c0050012407003141c81f804145010b8000c0b40002c2c080c180c0941d038445035203000100000c503146942c4003c58255152941e880c000b4000180a03a2000000d0b0300d0041d5940140482180071640b4000c00124086001d100c2c9068006040c0800c0050f802072030100310f0690084146024443d00404c03240301a02d1052008014400011040e1520b03246107080c03140048154021001d0386a00b0b118480700001d0340030548442000105002544942c032030b1700b40c13011400800000c5900800c41c1d140c10011a08000f000e1132166800740d82c0d10009030348400040381c4801041d60 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 448659901 1250 448658651 448658653
    0x506090703200105040e13170702011e1206090606090608060a0b0702181302120d3f0207020f06070803010504050c0705011e060602120f07030c08120a1409 68
    0x461803568600ca0150081840b02c149815801c0c0740e02c41e191241d5150050702c0d8042c2184050980e10300708001201c001003a065005d1301d00c1c4c01c04903140c0010703100e15000009000c82400021000002a000d5000d014a000014070b007005010f880344542c000400c1c4c0d500813000400c40700300001841d0b41c0300d440568031038507029140504462614403000a0360f0002c10040b13170720004c0300d803400c851502c038148224030075648003884c0a8401c0960042c07080c1c1c500203201040807070700402890f20000e80c00c4550040402c01401c80c1045440009400c0c06070390007240b1050030040c59054000d4160a960380142680c14001c4820042c141007620400a2501ca585401000104207200400980c40c04c3c1e40425800208815107628080d60382d900c107400c40e0050302c0c2c002d440085504c030446001c00584a4140074000c1030006024102101e07042d484c16008042020720205000168002058480e503602c0403407550203071000f41c83e00025041620a40011566449090f00d0a40700010314002d000c113160003840f9646c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 448661151 1250 448659901 448659923
    0x3031d121206180405010b18060f090408090604090506040f0b2805060403150f1a06070c030b16030f0501030812100e090f010e1507180806010902070506090703 70
    0x20758001088020255a84255103001d4203903d40740c01c85070103200e20f02c039500008180350100e080103800004802c1d460700b118440400c00026440704980030040f00c00449004009985515090078039204800a080d0000b2001c03c00140c06441600506d004813011501480524286140c40c000c80f00000c411030b034800710b0030f40d0344502e525006c14190740780718881080700e0b00d0989540100303581d90f0180c0d008403009003140d0602d482000ca24400c0c1c030361203017504c1d20502145840c11802ea05038503009598500c6001e000902c0401c215000c04207600550380303c40314907510314100c80b40110010000d03d42d200800d044c4a84803992251503c1039078141d0340e110b50820705001c034500580800f500d008182c1007030051908400b050b56103100c21903a1180720340c5802001c0c00304040d141c1c2400c0d0f80340310703414601c0d81c0d00040441b40c06901540480e07a12100d40c2c40d100762030600101c80c038912801c0c0b43e88200c00a01440380040740f40c14854005051550055080f1030080d1510700b1410743e0f41c40280300c0038101c21218 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 448662401 1250 448661151 448661167
    0x603080a0e03072c1308071104140f06040209060c06070801060909090c0e0c070b0f0a06090203010503070e040519050309100e011d0f0a091b1b020609041803031d12 72
    0x1445404e80c1158440c10002c801490300d43d44c8609541c0002401e48420b40103402d0b15400346064090b009480e041039802c0001070038800918090b100000d802c4a20654002c40c2880d41c0703072200d500740c803d0540c100302258401e007004000900028028020035000400011000c074203402c00e4080c1c041820f500400c3c607081203151400080030301901034041c0f042c40104214030000700b40850b01880c0640c04460941c0620304008401000b01c481035800051400e0061004124580d004150036085a03002480190559601d18050f030804500481c28a01f04c006240700505106001000e032641c4001940d040f42c090000e103a05440c03140450b14554005000321130410403034240d00703401c800401405002c1c2d42c8240c42e10390009030461100e4005414843e0780c0d0501c401c01048050088141844a04189480d00e6007803000703c0c18005401310190090170300041e00b40b0b56441d0303544210740d400008a1580ba40020602d001809000c0e64204035628448085c0c500e84a100003003003c444041003c442c1c240b0b00303409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 448663651 1250 448662401 448662479
    0xf03070e01050f0c07060207150207050f04020f03040308061005180f130c02061b09010c0f150c0503060103050a0b060403060906020d0204030309060929030a0603080a0e0307 76
    0x100e0403141006401d00c190106203030040040e02080c0301140142c50883c0c18070b40000d00d00100ba074403071550510f00c4001201c40360740120b40e980503641d05940028003801e111b00820064824007800840807000001044141944650b500e4050a41203d031050720000007107003113440b070044032000200e44410a00802d024079284144401d41e01011b010300c514207240c484400200c0313119240010150b08180704010340158000030251800d002e9000300da08100312903000a00582c41d0304070040803070591259400911890403990005000d020038140419101107400800681050b540c51f8041781c1803001084d2940b90301c0c010340090b140003508180c2001e155803105800707464134000c181ea10650030000c00c0d50fa044240001e0001c0c6000380c03607181040e072404200504690707060740045e042c0031139045031850030090102c580030040d400040c415102e450b040c1c2024000c00480c2e100802e800030000f604000e0503080290080300c03200440030345c0e1000da034883c1e246840381106001e44151080300d410704034070010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 448664901 1250 448663651 448663667
    0x40506040f230f0f030c0301020a0c02180c040b0705250311032e020702120601061707050306040b031009150609020c0d2a0c171609020d0f020d0b03060c0f0307 70
    0x1001806c82e5040e04551012900726841400304600007921b00286c6415418050704100421810a900c241c07503240000d030159403406140102d00700e80f00001019010b000701009850080507141260380e040700c40b8001101040b5016200c1102e1a40c0c207800295914900400c0d801000c0f044001803002050a18101c5c408680e4010004d54410341e00f0b21102016840d40c01040e801c4285540003012a54100b8001410001c02e0303480303a4942d0f00c25201003145581e48041960341285c001c0d2004280410101e0001c0d09099134000058092494065624144000030100303d49100105070b08205080e01c941c0301c00280c7c45850425140d55100140070419103209401d07130445502e403075140d1490182010866503200707030054416103c10343d5294003802008140002424950040402000e40c403e004108400b8441a44108883c1e290301083e0284050003541041c500c18006041c2113541d8108507000f900201628070030b41707010b40314050000742800f4000c021a003400b0725400203281150764041c02110b01c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 448666151 1250 448664901 448664929
    0x1b020706121116050c0904050c061327060b04050307030f1b083a030509010204090f1d07030b01090c140f071a010501050717040506040f230f 62
    0x503590b01202e000c5000140080e0640800d400565034686050742040ca140000300944c040c450345214044c04001140024241094801a07941949a43d9000c4001c49100d4040e80060100110850303c54002e2440340c02d100c007404140b05003000302ea529140030500601070780c0103054040d4441740c41800071030031900e00c207142c041c130554129500350104561864051820380c01100300d54001c8180144c05d5916200d94800f2410131003103c8030740c0c5a60390903c41d0700c0100e42c00c1d1005044e60f803404240d9542085d0103e03405426030980038001800801c075020b004201024a40402c003e4001055444c68800310f0724204130383e040410b20480d6403c0561101c0101070406001d01803040c07032141d104d402400740c40503015001d20001500e03100c46403801c113404803041c0e411030104040d40c240014030580e0380280c05d888c2c0c6550400d0a01020981c0c480311280703540703c0c907044182c0c0000c01090000d02d0384035040002c0c050344c0314081c80081440e03a4841d170f1003d03514035000341e66000c42c0c982d045022038100001544000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 448667401 1250 448666151 448666187
    0x30f030901021b030a03110a050708091f050c071a0a1b06050c0403050c090606390319050a020c01080601020a022101110f310602030d1b020706 63
    0x7088803e101c1c83e104164480c4019800c0d00301148540c101a01842030309051403001d00400c0ca0808401001800d038410b140c001040d0a0b00412900040c1c1c850300310829203480160030040080c1c07441440503102d07410105900d400b9100c0c0c2a80490988040a10702c0a81001c0100c2d83c4d0410101610607900489814807040515100d03501c01408514980203440c0156118100c03a0340e07c82c03c0d41019401d001460704094084d04a20b4280800c54a6010407191a641501c0382500a09903218142260304201c1c0c8402080d11070f26986002c602c0c070040004c090315021000c1d080c1a0401d400b00c25102070107a00001e2016800042074030030994050710f4a250300040500c16204131442a074001500d801d00c1003045440c0d0b1844c8071520b007041100344a03c0161000d013403d80d908080c40006080702601c01e1100c0007481c043c0c1000d10168481c615400380d854514100e0000001c3c40d11603900070364a402c410009155107003424003130880741c2003030075043c060306849501821455045c180203980807000b0643c20b4081d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 448668651 1250 448667401 448667407
    0xf190f05030412020a0b1204020f030109080f0a0f02071802031504050703140c0412080a0c150b181915120f0b0c160b130204050a0c0f0809030f03090102 67
    0x18a0620050001c1d10310301da1a0360038501580141700c010300c29030b0007001303010108120703003440010300110700f907070141d41158192400d00201c00801c0c007402d030364000105035000100f0800c401302c02d01806001002c409564469007036103030f10022a80e49a036031051030202e15560076400b03115010307a0011a40035110b000c812001a0740c07200071500300c40c002c50790800003036961100710941d0090005a07a420880304041d040c102814013012610010390b4a0000f041c80c0c000041e03a030455405102a03a5100307400458240c4201240e94910014180c202c0400380709051f02c0d100700c10032640100342d50340520000a9844070b115a06001400200031031124682001414040010000d14144288000713501c512450724441606240007822820301415440c0039101c144200302514482007400c0300c842e40c00191030061a16000e00b02c0207480070510740a5045810602000b010910340d80000026840666550341e0407001100300701c0c0d80c3c201c180d40b6251203410030005681110501c00107150005040000189 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 448669901 1250 448668651 448668653
    0xf0705090d150f0606090b0c0a0c0f09110a0f0f0c0203120d0608030f0a120f230702060411011809021306090f0e010e0a1407021b01020f190f 62
    0x6200011210119100b19080040824002960254101c4020402d00a024560500c10040d00d10003450280b810610301c04113980b850344004102030111280c00c00c4e80c1018603612040521407418103401800044c0b4241058140f04440000c21a4840212079a07600340600d0381d083d040b5480344810f1241004c01c0260301c0043d0160b94144080000700b10b59851483e0b88a4102c5845d609072001640601c89580040c0400b01d580020441210a060824036000c01c101f903901c5929402060340741020001e06150810030401004141101c00c881603008c00501e14a9580e44c504a9556504603801010500001c5402003a54040d52010708000f410142c100c0b44182c450f80c80400301d0704125650600c0744e400303d90420400d0b800c440714101801621000b10030590500380040c003c2c00d01841101c524480400001d25800840c0c1d0204403180c5290a044866040c01d0b48002e40c6d40c54a4000460094414244100c0640c00069583c0344051160007a010f50102591104121250920140c44a54200350558 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 448671151 1250 448669901 448669909
    0x70b060d0203100203060103180803060105070c0902070c06030615090302040506011b08090a1e0b130302040f05010e0703021204110d140f1204060203180111010e0102300f070509 78
    0x3c00b21203400040162645000c07800142540c9031800416071011074151440c000c00e01d1841140d5001c030b0203080641d41e4801500c3c0030345004c1410b41c02815071a00c040f2300c1004101c408001c800841c1c1c02d07071307030140300d519100e1003512814103a400490780412000c0104100504050b00219170051050409848181d03542e01c04082808a180003241c25038000190742c001860f142d01d203100541041c1c3e481d404c0c0144280045d0700041040d0080c90034546000c108015070000c0c0440ca00d000d50390260041c090001c040d1402000b81c002801403280e4030031100009130600f03100340b0a40d0405034a0300000d08150720b075505c521202da9014031036a03402c070424101c48001f048c4002003880d9045c0c0360100a181006821031420304098805a4000d000c800410080080c0d5a0000980e1100820340d00107203141c0000000607640135103c0c2c00b5610303255080064498006c60198003030649003032088140c61a03040c0d420b82c6284880d40d0700015443d001d02000125190206190b90950b0044607414260b213021402c000203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 448672401 1250 448671151 448671163
    0xf02040609020d0603061505030303040b0a0b0d0b1608090309010c050c04090b1e1509060f1906110c010807141c091a0105090c0a0203040b0f131a070b060d0203 70
    0x1c3d4080c96100c001c10010080f007440307a010006004001c440d405070030100082c0c0c0300e02c0b02400141c0f0f00b8420401268030341d085a406203944500040a480c00d034101807805c28124201285c064501182801c3d50825003400754030300510035892203000d0341c80c00f0b511034015a025580d9160950b03e038407030021240312a40b914445d20080c0c50040000700740520700252258151031003000c940d103015080105203d018880c099449040d00022503890000c1d41d242408150790b9102c1d444000c0c0e000d060050361310541e804080d030b1401540c8199503040b0444448000180d0f83c0d80e10038460f240001c29440018854a02c61002002c0b60761420003100e182540944200001d1480909001a41aa19040f040401205205061308030030301c41c002481d1580340c1000515400c03001440d1041011000441c0070f41241700b401110040c0c035100d01c00750b8481e4510850107030180c2086000c4040d5001d00b050100310146003004030709680d0129030240e0b00e1700c4210742c6d0700258888040c18650700106580c900000507035041c441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 448673651 1250 448672401 448672417
    0xb060301090b090a090215030c160b160503011a0f07051c0801091419020c0604050106050109171f020c0609060a050105060403020102070504111e0406120e0a0f0204060902 75
    0x404a001c0c0c00070070410983c0000903148184042c6460004401612031641c4081075a40c130003005522652580e148404900c2541c4001040518084d043d20070820402d0440e801040c006c00040c5011507160b80c00e803820302c001e014540980e40c205003c420b200210794001c004c00e8540c0c40c500c0381814183e5580307a191440794500324403020040c1d140b0303184540d400343c0e0080c0180042c010501881c1034500c6c9007104010301078100dc2c02c003840001d8022240309250102c0300b0f131142a88c200d07905446e0070b0414500038200d5018403400904d0f040400034a02480c071591a01c4905200003500c0010714409604c0340c00c03d10101c0d5400c501d40c090040314407814040c000940300701c9503000a403030185010400303c4100d54050f08851320801d0141300510150b40c3c009280710036140c0644001801d400845020310103402880c138040e5060080c994003030201e01006028100320740280d00c410a00d0b980504145003961001d28060007d0fa01c22425127000c141d108800201850010b0300000341c00b41c5500300e00301a41d104c9c3d40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 448674901 1250 448673651 448673669
    0x71202090f040303090f121b0317060f13021c14070e0a03020607120207060f02070b160b0103030c1a0601081914420d0c0f090507180f0501050c010b060301 68
    0x80103c1569230080d070340085c032181d034079010200c0000a980c00f40070100c5400c0c0d41a4a0030840001420b551070b0089480000704004010390250a0800c0901002e9030204110042c2d46a012041038481c00440c0a03109001551428a4480740d4400d6000c03280a42401c0703000343d10400510001001d44c035900e009040c494001c1404000ca140032280c064039041c51580800c2c10401d001940c504001d501241c0380007038500c00708100f50742c0e0b01c22080107205501541c0c1c0c041e08104540c4c0c0000100743d04000d007908003034031800301d40c0d0700c210748800d2061402e00e0484015010400407400551000080a04c260010309031002c001440f0410144007001c1e000c08031000102c85000800601c0f0034480500c090480301c003815000300b6001d0314a070300721445240e21136605024000740d658400810022440300c03805824080070140502d90396030140009030009136000c10100321880100440c00003900307894400d032111120342c03040c1540b900d401155954058130424129558510f41d14a0b0303a640c090080d4001d1412039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 448676151 1250 448674901 448674923
    0x603060518061b1c060305030408030903100e07030305091903050c030f160506030601140a0906090b07050726011401082802011b02060307080405071202090f040303090f 74
    0x1040b86020b601510000408640601101010070310a044441c2014201103500d000c8019240200c00342019420042c82400041808201d03464000043d2820b800d04030200c940700e03171136000c50750200e404680800d140c0350802402440882c0c0564000e18007010b018107204038a2000c0c490200d0450400d400450707542d00700300c4c6440407501d000c22552801929400203000050340320300111071542d0003031198a006513804800a0f03101d0f0700598181c000c100740310060642e01c0d681d800c001083c2880b02e01544010400c0ca10740895107411100a85071201d9122004061090810b504100d5030758031007401e211010107102c012400d0407000e008500880c11a5914000c481d410901c00341e040c14002c05a11708803041e41008941c0d9041c0012400c12466020309140324842c00c49840e0b000303419841003020350001000410310060303d40c80503607140710391700800581c1c1da803a4a03251104a01c030000c51000c0d5101400c1800f003a90080390000280e0810300c682000290190b16546400c1400700c151820340300a070500c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 448677401 1250 448676151 448676191
    0xd060b010306060302090618011809020a02100b0112090615080c031b011704060f0203010806061807020307031803140312060108130f110312040f0f0e0402090a06030605 74
    0x600642c006001e25003021350405d901c0c0e038040f4086004440794601c807130707030440c8521241c1d034000c08403a07594611f09040301e06480e440e10604406035008622210040c4a1400c00b241400078511401d803441c1030595628060030000f900c82405840c02150590390144d6411510386104000032080c0001c011105c00b80100c1481e2400301410801083e4500042450207100b20703515030307030007455204800c5421200302e416172a0740c103000300141111025030a0b0303a8400000490380410005800c0d21485c0c04990306599600d01160b10b0360328010680c4d104025078010302089000034094100e5224070f0030049003140c0016600d231180c940c1c400c174400b00400c09800025540300e07040184070000b6803003082801c1a407464145070900140e452032004000d802e0208603450300d800c010ba1488118500c21006048404100d0552403003048c0754010310400802d942e09183c0080d060000f942c01c2c0f0200c1c0c040452101540d0365903000d101c40300c0310003450388400c6640e1b020f01000050f440d104180c020302081054060f01c00c14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 448678651 1250 448677401 448677407
    0xb0c09011e091404060f050909010b04090b0411030d020601092a03050711070b030c07150617010e010b06191211092d12070b1c182109050d060b01 64
    0x8012000f90040b41452401d10444000f040d4260441c1c1c801d07126031030240d80303020312540140b81820400754820300300030200b401d2081d0010721a008901070303410890064440c030f0806d65220081000000940c011100401200382c1aa20000c010b0042c5c01d550210032024000c00740c42405510710760b1300403a81d03410601070101d034050014410014000c0c0206801410b1451440301408014202c02d500c020015074213042010510b5004101c44803036405010064503003140161414000003540c28035817800c20044101101401a032444440143c501e41c5452040c240c4048854900d600c0601480032071300c070011f0508500e200c1c00510600100885440e0207603602044540080d0510061010307030300d001800008210301d0b003000c9140310304032104021100741100481c00c00542c2e900000c4150030108981d010180640b011510340c41c44142d04210039111016440d5400e074030320310040c0014503003280e10034042d400101e80244202c41820000080b503981d1001402840c00d005085403103544032091107440c2d50b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 448679901 1250 448678651 448678679
    0x120108010b01090b0702240a0906020105150913020102120301080a030f0f1b05011803030912020105090709020307020c060a0f020705060f07060b04020c0d0c0308090303040b0c09011e09 81
    0x40034a0302501c014a45001080e003401285c038068400d03064009076058280003504006098100200c4040d10b5080781440079120030f107036200d9200594217190000380304001254640079045001046000a074039120f240c0051110046000c9041d03100380b4001074400500d0001445c000d2598000400307170a070061900509a2124040b810244250340d85003010b40b035005815500d40c0070200303003000312485880c280107025192854511929403003c650a00505506801507000d01e8045d08a0800034902d1200807822030b03074202c9080d000d07a00500400d001e244042d030000c40e000107003441240c040a00c2400000d001d070384400031000110b0642000b0307000c075680501c54500144402c507061410b0010300034446006100389200101001d41d106803000d0a552107078192003049000e441107944410054401074001040c8203000d4020880d02c40004104590001c11288031307943c084003c00382510303000501c2c482900080d01e12418000b4801c0e0340a04504c0345852288a0019a5a015800d900d002c0c51305150758 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 448681151 1250 448679901 448679921
    0x3100e0a170403150f09120905090108030304021f122d151505040e040320010603050d031821110615060c0a08030901050106080a18021c060212010801 66
    0x90240420404901181c5045030b441c48604130102d00c1e03000018070a0002c00e401c1000070013020341c603541d81c13940907440000e21080d9041135560f0390b580d9880d032100c15605c1c00116002580011480092101166041c90001583e0814100800002803031102c401c02d903031300840d10041c210902c40c3d40f45000d9014441400c480304501204109040d84900c180c02040301c0d9001c0c40c8030742a00c408040d05601e10130310840b40103144034001410780d400d0a240007010819005a4204860200b4400850460043c4510b400b2a130f4004002d040301621144154081d09881403580380c4480845607020105500385d15480e0300d40e4120000b61101d2002c4035019041031000e1075240000d6002c0350030042a101d85c00c03401a81900100da5840e00d643c403108051f0702e400c3e604400200312074400300a00c0000d240542220341a88c6c0d164a40e02c0c21661040740e064115070540c2c45c42d450070300c5106072074000350800c08800c0c50004440f003404155447e640c0c85e00b60a9900a400c0500c0c402c60350b10041106036002e2095401e00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 448682401 1250 448681151 448681193
    0x160201080601080f0403110a0605090f0c220902120a060b090115080a020f220911031e040606091109030d0908031c020409180201080a06120f0203100e0a 67
    0x10307040c45044d051803414001d200800b030043d8113240304107898040203042d40d103940c008011b00c100c0c90302c06c81c000e480d00d454000c0044103105d481c041407100e203800c0311503070304510f1054101100160795a90844c0548015070050760030003110005822090b00074001610224024030010446030712204c24407010200582c860903c5095401e200440d060b132007440c881c0c10100c4190090b80310307010030021025500c24280045149140c0a42050b0440c1c58250182c04a960b2100c080250056009012074544411075030b03e6400f069420340c42d204081569440ba800070300800000072505d803100c01d40300490b0030b41a903400440e1380200b0301141510b42005404140301480c500031801c0b615002c05c656590080c0c4107036051542e240303a50142a9040ca605803001000a008244629581c0c05030406400c0800b00e4280d000800365000034010424030701401c001c031004c0b0410217010244548a1421100c8601422a80340c000d607520130b030080d441ea005500303410405002404a1028514040240044031101d205030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 448683651 1250 448682401 448682417
    0xc0b09150a0b01021218100c05060f01050604060c0521040503010f0605030a0807030e130608160503030d090201021213080d020a1509020607060629090a15050f160201080601 76
    0x34599012421602c45c8107212031031501c43c04169005081a00d50f10704203070700b09030348031407030480a075001c02c2e02c0c20142d010390203651003030b12400104411110309008154020108110070400305200329004c1e040203000e43d007a56071180d91141203200001104a822b1420280403c0a009901e428403510741c0010100310308008080c07500000c281c590301c4089000c1d007090300100740002454018400035800f900024004029a0584c0c0c220300c00604050190020500c80c0c124501050003c07480b0b443c0a44070300070000c1d41007400318140800544400c00b0201c1c11401140b2030217901c244a00003074032182d084000503034692414048468036009408196a0456215000c40008262010343c030710345082006d4000300300c080d124008144d140c499010020700d010301c1c0410004444504071140c0c821400202803295040101c0c0a50220900862038101c0e841140e045082010380b81041c00c0c0c9180ca40380741012400c0c000190424040c5030000781581c4148554122000219030b03010f400664040407d0900c0b4403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 448684901 1250 448683651 448683671
    0x20c2106090115120b0a180804180501360209060c030a14030408041e080327010c211e020c040f020f1c02090a030318080d050d020a0c0b09150a 63
    0x4200000e4034038211141e80342000403205000c401c1048031250130541e91030741c071640c03003000131403cac001201003800c8640f5110001c03800c07061070001000708019601f2500503041021001d1055001d0720242c0e01e500304d5003082076050700d4454002030b100c0c811080003e55203420b10604082c0c60b40e021002c4a800d5403004000b00400200100e0642d020380e03042c0d100c8400c002100c0d04000031500c48540010415100c04207401d0001003102d10060700740000d40c040c440356805444015180364459040040c00300c01d1602c980c0f4403000740c814591060402526101d1882101c1c1008400d491420105500058001c5040e40000e4105070140380c00c450078900085140601c0c0305140d44a500036070300c2c003009aa030b0045603c2516000e94041e2586044000e000c41c19190762890044c2c0030807601c00840c80c030b64101e08000203131100c000c901c60924620030780300d05152580c0440940000e500c406141010301c1580880c010204203601151445084102d00401d0400401e070100d0140c00c10052240100c0c03814441960 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 448686151 1250 448684901 448684913
    0x9050a06060c14010f1406040e03180d020f0909160806060a090b040b0604120b2d10090c032a0905040b0d060504030c150903020c210609011512 63
    0x603102e1904103401c40ba0072052840124098849000403210031400c0012203e420190054518043c1d0400c4404201185c654140d254580c001e000c0001100c04844c1040401400e0410321180d0721480200f05440da0604640051203140050b2140700099020b0b100d444545d50440c1c1c030640150486000801c810301e0040001b8190303855078081c25103d0360700c0f250382031040d890741d400601920364010102d80e159500c0343c0080e5141040395805540c03800c1d1000100300044000c041c0079040c0e040c8130301c1e000030703e180b02b0134000842940a00000940d58146500140044d0b41b8890303407451455135a40070525405c00024400103041e8520b0f43c21321403140c21401c07403c10340c214512100300c1da801e64010900b00d000000003030400c2d00520010300824140400c00c010142d102c41d4014441e0302c02e42460303101045002c7c0000448003030420050161344070001084240c9002c560b10324552580c0c007210201d42803043d0485040c41026034900006a464102c2c0795030040e5610719800180c041100b440103540c25580b640 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 448687401 1250 448686151 448686167
    0x2301060c02211006090209010905060909130c0902030709140105090a090e010204080a050303061c050a08030a0e0f011b050a0813050a0c030b01030b01050906010203120c210109050a0606 81
    0x1440c0320040a0b140507001d0b600a0102c8426491260310400c00c503540e030441500690710101311240010040c0c5030100d400d1030300c20b0a441001c04d01400f18985c96860341e9079030141e0002c140054038403c40b51240025200c006000031449a1060307501d001c0e20701e2070030808a200a421491050500000b80610f00c2d054851800f0101151307001d25010170600c203c0f220860080c82507412040080c09a500041309110001009600a450994203900c032003402002d010020010503400514a820541180000c44e803808085e41e04a8685200060105445c40380305103001000c03111003010765115510f102c065004240c030300240c07400f01d0030311174130304241e400c4014008030008001450440010100c05c0900c0010802c3d00200ca03441002c0340e41040e100e0605502c1c690b001d1004a81c050004000403805041c4032081d1800303020103800841c00e2180205007000321031402030001010442c10b0001c508015900c98800d69100d007103150040107541448a042c00b40c82000f000510700c2d030300380241000083d40c05050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 448688651 1250 448687401 448687429
    0xb0705040e130f0201030c112506080405120a0207320f0d1b0902120a1506050a0e19090e06100f0b030c0f180f0a030b010501110c042301060c02 63
    0x2008400303d14251528020480c0c101c01707a112749204200c6050000319031076038520300e034569140e9503036a9800880303c1e0b82e0110b800070f0080d0041004208460021005464120b1290060310411074985110000c8910080e10000c1c400a101c4521b403520940d1581c2c441c050720060303860504488200340481e5000011400c003c00e180394581c10002032850509683d000342180c4101950360760248400c000001c80103640352801c242c617141002054480503100c0c01c0440e0910340b80c2c9400c2c45a264011342d44406611446a004030a1407180340d603407460040a600904141240001d440800104140c608040107007100303491308903044140b14101000090b6012140c4142c0c0460f625619000a2201c1d0301607203070780800d28000880c40b80e12544410f68001618407042c2c80e1a0301e0322a0700b0701000800031303040c80f020b80300681030030050081d03510850300c88803480d11400807a00000140008203007159250800ca54003600340b400082d80c0c20f000d88944d50b00409941ca0103d03600d240386d400254a0140900c0e07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 448689901 1250 448688651 448688657
    0x2060f01051306080307080306090114010906200f0319110705060f0c1b012606010e030106030507080a1707030e0607020f0301151503020a020a02040b06070b0705040e130f0201 77
    0x356281030a02d650048006000300d00252074955080c0e2420b1000394009403025441210f840d0004a408848007910440c5010160341d407030511031500c0d109903015031010b00c194041010f00d1954103c5c04c5000c0020480884241c00199038480110107050070303038121800240e08100c100401058032000009504040c1d42d01190341650781d4200e840301c1c00b0f19100d0320340282260701072820825000403007e00d0302814003000381c0752080500b25002c24840907411031907000d90f403203c90b400803403400c2d4420100e4007450703800500002112a282c0d20307040d1602c07160754480c00306544440c0c1c80300c007003085900312120030080d283d450a003006c4a0707a402404034001c100109000343c0c40803c1400c1995240d03201040800000b030000c00c081c02d080d4040100300a0580282c00d55440c0003203541d591180301f03100b200c1402200340c2c068450624690300f00700c05800d40c0051650300080c00d01c0f40c400031514022155029007240d840307a540c0c1e1882d28200380320280005000307070840c000f06908000401c001d4400440c4d0107034240b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 448691151 1250 448689901 448689919
    0x10b060c07090e15090307051212040311160e0109060609060909020901030b060d1d030a020a1b0b130f0b25050709060b0d05060f061c1103071d0102060f0105 69
    0x9195140c80c180e26031056850f51910140903541a01000410100b4008c000303131803003c555080b040a4030721075083c907000010010000203001c00d00c0394001072801241481580d1480150748501840c0408a070461101c0240b0f50004210384400e51040000a1440b0b04048a043d031500e040901001000e2241001080d000154501c03580e00c20b80c803050b9000001010703207454152010004005240140e40500014100452a13038440000070950b2007038152039008100d040310f1583c0e01542c80b07050006035044405642d0021603006008000f078030310301074004e5200001c541307090240a4032051035800391181c48010021410031240304400804294000b0909900d032a84624100d45059401e80c03200300f446e0b19081c0046200851031000f003101d1914100b0a00564440d50b04000d6001c80d0001510340c0032104224040041003a0100d07100092000e02000403003013500005080d40307510450300d1000052082a280e5135920b03141580c0856031a00384010003561a04007618400b401c01801100d02c252464 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 448692401 1250 448691151 448691171
    0x3020417120714160b0d0518061909122109080901111c03150f180b0d0507060f1d1e04090f08030f060607080f0a03110a020a05010b060c0709 62
    0x802c00410400c0c0e0a454000c1d6080d507070401c5080c01c0d0403013106d0242050410012408060004940118a07240040540340581301c0e40248540a40f159028081ca5074807041c0c80c1000c640e440403030040d0041a5210790b0341741c1c207665500c282003124490040740194900201480810081025198402000e09221075581c280c01c5100d4030b00f0300d00060038501c0ca080040c40304002135241d008468008200901064519100d01c2c0c145010082d0780590900045030700050000318140d42c000c100700c1c06000d004d0b03c1021019445150a04080c1d03044900801d210001035081264000c0c01d03504c00c1e040d041c840031914449480001c0e001184513503491000c014914120540303558a50000170150b0744201100d500a0751842e20a031542c02c200c54509045601000017800c0341001811103035031030343c03051046141000300c0c0f0b640590303a0812017132141019615054045203200c480e0050141e500190010034511032545001401e60340107a62140c0100e0382800703094151700000542034162190030303401164200c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 448693651 1250 448692401 448692403
    0x40c050a0c0f0804050306090d111519180317070503041e1b080106080d090f0b0c01090c031b0915030f11030304060c03030501060201021602040518060703020417120714 74
    0x2413501700562500500060101d0000c00040c0c100b80c259268860050b10861024a191a030260b40102003100b2a400000f942503884c035041411000b10685c00014820944c00b5488540300040c13408501040c011034020503030341541c80c80306910007060701d06a461440c0c9603a481c3c0612110645a00d802445030307050004124228460720302c20261034805a00300ca070f40d901480c1c003030300e0b69200c0c135407050040c4002d03181005e204107403100c1038401c12405180464030303200c03600e0750070b920030345450070035550303c91200c00050f2600414000541c0203400802c10210f0090141005c0b00181c0c0c40400031618111072031041c8400e05d500041265009000c940c1400c0d03040c1405440400c01000840e414000054040b8003260480e44e03c19030705001e41d608000b180c0e22010264202e100740c102000e18540d8005c0070714010724268000c40d600440003107004900d202d0160400d8540340f41581c940b00840d030041803c0c40107050013070100b810300d1071000c000c01c21204a41c400c9078080c8107841d0b01400c8600c0503441c0842c0660 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 448694901 1250 448693651 448693657
    0x212041b030c1206110a0c140607080c031f14010e0306091e0f07031b060809030d09020612180f070b1b1c02030d0f0b0f04020307031415040c050a0c0f08 67
    0x50003101c400da41c0c03411001b00030921020203030211190901040c40b80c51078a00041c0a521a40060303c1e4091140c8540c01c0000c81c0750002050f441c1c4400d02000550151980c410b0103800508901c0f016060054a00f0009450240a1152140aa80208200140c1110004880e40c0402d80094040c3d1500c40c840000d41c02c245803c600032405105001002041100700e11316207114140e404035880d8003540b5140116403d400554400304254811b201d1a038030f420642e407203041540d100400745850310803104d4084c0d2a0301da04440c515202032080c006140c032108140b1021043d4200b0402a00c1c196041602c14121030040e80e4800d0581c2003079814148030303070800300604100c0304000b40382104400003580009503298407807100040954141404031030038040030301a201038018002e100c20703402188a01031000941000741107408060315146403041308442004800e004160340001c540f4035240180520003515800490401003003001c000081d09503a1001080d6041c940c0b04514a4000c205414130040c140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 448696151 1250 448694901 448694921
    0x50102151b070215030403020c0613050108190f090606170a1b080f0a0213090b070804051002071a06010905060f0304030905130b0102120c0312090703060212041b030c1206 75
    0x4c03100034071000e0f03142030340002c0e41c4201c1c0b07e07600300c400d510052000d000503401019003126103110020410f07c21980207010f000c1e48030031205140000c1c541060003a0040e15100c080301501540d40362026814004580650360141c00d0680714164442a00480b85a80314500300d4050011781e803408010a03a0a01c4105040041050000710380d0401c8001100030b44903070b50086c2c00c921688845a2000b40240d0314064070300d10f00e420149541d126540c1300c00c1070360980380c020811511402403444814440440f440507200341c50041d1407421010f102420040d001b2507018180c1c50500c84250303401c2009607990400c9a030700c0c9134002042516600d0390710703081c1e40c0d0614a40205511004c1014901900c002030f91195031840030990841740c0c0c0e07808d413502d00c40a0f0702c00c40d4a1600a60001c1102580200090722041d800031201c0c012503032a5642c9482d410126041920440d512512050901060180c04040540c840c501c20880b4450b441c0f95545428061111b441100070000550b0401820701042d940010041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 448697401 1250 448696151 448696159
    0x509090f0f030a090503120414010207030c06023702060f0d0203281a010c02150a020303070908060115110a0b0411010212190806031c09060306050102151b0702 70
    0x20040c440303101d9899070840ca4562000070810080050107140009100e8207013041e4a0182e0b180504102d520000c91708000c81d014150301c10b02e0000000a000c0203d0f5400902d10303a409403482d20704995945480740614001003031544003140e80358140c0f2600c0d031507400425034119089a55007408440c0d10b1111b014500800744410310100c10002c00302c420300c1c04c00d042d5004040440e0a40d4442e4017154045400e0184d4041082c101c03d0094001e035400ba10b03858121500040580100c84142d00d1801c200340d00c40c584034001a0000300601410903000f003445406000081d000d07149641c10081c0349040c1011091000d0100072100e0f01d101c0f02c2242c14403c10080c6900074441030fa0924050401130400814400460300500c281299896011391380010b030703080310a501c52081448240e004089803201d00203086268180545148400e044410a2004100b84440d444c0e1060051608002804a03442a80700c18155006502078011103849401855801034140c4440300b500000c08504040d01e01400c3c40003904 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 448698651 1250 448697401 448697413
    0x1c02030a05100c0f080906010902090d061b020706020708030a030903170403090501080606090d02190e1f060c02030a1211032b06030b0f130605040b040201270509090f 73
    0x441040d4010f21580e40c0c10f40c441010140c0180412940d0150031121800f15810950040c05805815001004082d50081401d1112079041e11204e080b074040c1c14500b10800c007004102280f2a8050001c000205018009800e41e6450701c820780da100e11540340380030101741d518280b02c0205400f50103071103000c07001690603254614051401074a401110301400703021400610000300c240c90004112003000802421030008103015a0030302100b2248150789490043d40d0707007004980700406416092280d0764078142800c06e501c0f5100b5003581d0111680101d004c110b2011080c00160304e0000700c2c0003d00d40e0107488a4446108040111408240c0d01c05240300e5001c00075004a002c0e007078240420007885456290451400403116400403505c0740c2c48002d002d0f19240c1d00003100c2c3d44410015540c072440c40d040c2010a001c495450408032507040ba0202d4040145905000a550f80802c845144604030503400d4180d410013043d01048040d5445940c2c410010080001d417100c0060080c4022400d42c3c00031600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 448699901 1250 448698651 448698673
    0x120207030609050c1206070203040302040e072c0601031802190b0415090f0317160b01120302100c02100902030f03030901140c070209070c030c05120d1401051c02030a05 74
    0x140301c80c1c075200f419100f000c582c17840d40a01800400c05501500e800d40045141a20f950f007808003800030100c503c6040d0042c0c1c00009101d4910500c508001400104001c8551001c04183c100218026190074100752400288250042d0300305c01d1600e04580466006510904c0d100e81c00205400c0b0750072020301030001240c00a0320001450141202401d561291481d95440d80710503d2038502a1001034080d152001001425030001001021a41420109102c00e1119a29098101c450070391010a01510740c040d42021705505125840030884d101001744207482070004000d544500c0100c00c04445650349041108642e800c110b500302074846001601d0300c1e860880e0003a4024650071858011841b4a51f0001d01700348542011102d00300d0b4010000055500c1da154115500c00c4a683d003101404817821503040410405c0114031462940b0303140d01f940c0c81d100c2000510940d500c01181e01710201da214018455699a8911501404581030369181d00c1110307030002a20306030b0100800780a600640c0b00b0a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 448701151 1250 448699901 448699903
    0xd0503042d171b010e0303010302010c0c1703040f0504150e0a020705100b04050108060412082212030c0315050d060209090f06091003051c1404090b120303100312020703060905 77
    0x1252800389601102a0701030002e8456003070b141c1403610305c2084c0e003003040140010360007a0780000c6a6070046401044454039031130044030b0117000c5c0d1920f080590010404014004070310745240082c0c881038400348401022400f0a010350011030040d407400d07800c00000a040d020703d50381a9226160000122901d4205241848009001502c080c13400340b0300745000400c085900288641c01651702440074001d510050701308580e00240540503c0811010b01d82ca00a40c00c90100607002a82c020b00520351a1546200c0150807984020600710a045c103003c17511100300c0030441e01d0b41c2100d0b0141c549410741c1e085803606400038420040e1103a8084c104005100c2c0141d03c0e551800d100340415039624429850715028070b00300104602c030050180d0b0007042c200c1e075202c0d41d0010941d0154440d081c00041d0b150801d03002d801c0e941064200e100543d5441c5000c0c2004c0c41c01001c4481821520300155245013491702d03025a43d01d24030701019000d00b052a040640c0030303100304460b01c0150782100c0704010a801c140341031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 448702401 1250 448701151 448701157
    0x903080a050f010620070f0e1005040b0a030215251505061c150c020c0a090b030c1509150711031507210e010e0d0503042d17 55
    0x3190503245001d000030b1861010410160603500302c2d84039602d1800c0300c416035850030784548028040078020781c038000621103a0403036940050181000d074043c03107141c214a44042c550786980810311a6040018003001a02c1d640003c80035607070103489141d024007901c0303502070701840355040d416180112044031480130f201200001c4580c0f0311508c4400c582ca441b06081d081522800d8a2483e40080141710020400e21094000d400f290b1240c00d907900214203489035402100c28141c28280543c0040c1d03a0712000c0d2510b082c4440161841303600c10040c1c80d00d50300100c0c0c1da40040c407100500030200d8445c0012508040d4080e0b1b041031100503c4042a842201031048440d005080c1c122495108074680301001e00c3e0202c0c0004241032444800c040503910000102c4120008910181610103422440861407195014500e1906800400070401e0301c0405d522502d00a60343c001542004001d209110014200e505803995508503c0c500c04203074034007a0042019000109d100a20a00c01c649041c01030203410b00103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 448703651 1250 448702401 448702411
    0x1207030510060320031f05070201140903030103080a120e0307060b06090d1509020909210703050405040c1106040b07090503070503060414071203050d0f0e060403140c01090308 77
    0x5035810700208907805400d030b03500303408001d100d4038003400004000030998070100002c110040c1155840c80e4a481c00c00122955400c061050307a803500d0411451a0f024000c1075401c1700407404045030b81c82c0c807071511501d80c0010702004051302030000301c43c0c81c610311900d58000c00303076886042040301d80c04000d14955294060902120300908003032002e4014074000c010390b4054007000e000040c500100380d0311b00744001e80c44e50043c50303c0d40d540c180d58000740e01d42003e901c1c81100760900900f0280c031403000600303982030010904c01808004204400003c3c0d0f02c0300649040b501d00355000b04030610450400d49800e08080c44491071440b8010420080c02600c10701a802280ca9032503a030b1403540c4900a00d03884e018180145a0181e004001280c00074550f09001c84104501d6019600c0d815181c92460448801c0302d101640040c40c08102100b26008074440e5404002c07003580e0030003144500b020344a4499000400141c18020a600292106161402125504080c00b0000c004102c01c83c07902511500c1c080d60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 448704901 1250 448703651 448703653
    0x30f07020d02091f150c03080c2b0e190b0912030a020a09080106081914030301081507080402100e0a090204060f02010b0306040309170705030607081f03020f060c0c12070305 76
    0x300000d4410596400c090b002082c0d9507207507946d0540da10b00b030316152030280c030754030f02c01d0810014042082c000d844010350542d1450303551030444c120940000d0580304071100540047d0042c07a0441703407600f4900c0044d0001a40f140d211992640d03100c05542c1002c403000403a4145600002c200040c0102d1a4000e0200360001d0301ca2510a03a183c01e42c8500301c0e0b0180c001c0c03a5241d03008060202e5640502411441d41c1c9101d00007030314650200e0f083e12800c542081e0312140b1258000b60000341c6c14100154240c0e0700a01d1031810300c4151409030006425100010f01e040e041c0500619541019110b0b40511405004801015907980d47d54050082c46884e0b03a410342c0d0b006500e0031141d02000d1402060142c0200e0701503640341a40350a202011003507040e110440c41003403003110000501500c042c0400d900c111550b40710000700d454400d580c00050300e01c0101515180120074414801039032030080001c0400300c2500d01c1034407000407a03a05d51500032216030381c6a00c011086d44100401c08002810b80980388520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 448706151 1250 448704901 448704961
    0x1050c030a180b0703021803120408070e060f01050304030c020a1403070803071a0606070609060c12090c06030c0203070507031104063611070b040b09030c030f07020d0209 75
    0x14040e09a52410810b00500c90384007140880e00a40c805d80141c20f181c0158180000701d000a00006072030700381148000d600c40040820b0410000d00113001038401030030410220300c410b00e89000043d109400001616041c80303804800b19007410304c910315941256a0103048840706545840b182454168500c00151092145080200b16a0320110541c2d1003154044e00102c1c480c1c2c040c6021a21700d550042029030000d03014404440800e00e18014418994000c0c0300014004c982040010601852000b92040701810301845400281c9545601e1045941a00c0c00107041c54882c00c04030b06610809902410b1403040b10400310038060703001030361107003c036007220b0400c03003181d1b2040351150344014040c81c1070141c140060008600e2072404148007084454000010300c0c480c0b2004000e1503070308240015100c6000d42c174101720401607040001504108000c0055040c00610440d06540f4440c8101e000c160a402103400d01c21502d651080481e0154020100015450034082c442c00c2610201e900c04050b042003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 448707401 1250 448706151 448706171
    0x909100606050c0c040c0e030d050c10021801080627090d0309050a110123090f0105091c020a0909210f27090c05070b060406051f020f01050c030a 64
    0x180221050740ea4103c02802421880b442044002c0140040c0402807000101010010342e909203c801032000e642c0e110f9588600490f234150b4a844100f2000c40710140c41005031a06050211822450455007440d02c88215542c540c0864292401000100f40403902c1c003000d800b509042510981c8134920310812607104204024044040d5903c01c0f0015099070400d5117194045100040301101c4000b06041451900c01092620810480a20361442180c032001c01c8589072880c001e002440c03210424a00305080c11405400142c01150081c03600210281440d2100308544072504070400602044004025545060900030b154103489841c10308c0c07810410490441081c024000319200541c20350343c051654082083c10043c049020b0f18181c01c0e65030f004800980c41295000e80924200c0e0703a41c80076101c031032505e0106900c4501030300e002e10540c108142400243c8500c0c24902040001240d2450b001d01d010f00f069050400c4002d1103c8203508000800c4001148800114000c54002904001032254 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 448708651 1250 448707401 448707407
    0x608070e130b0c0f0909010f0e09070b030a0b13050901060f23010503060d0c08070801060608091c050f03011d0f070c060209011b1a0702160303030c0e0909100606 71
    0x99464000e001d11640b1010840343c2400704040c1c14103041010184e0303e4070140074005601160241c0c41940c51041c16401030050101045a2a4105295a00401206092892030201404020488400107564000529455807130100360700341c40c0c66004042003070341008107119020300031501038600f00640c3d00c003000944d071607051111641d01c20650a1b180c007200204004444592006d0003442d4041c810030070140103d03a0443d03010f0010000080202445e074a001545404c2d5a402c0d44010244030300b01c0100300510308081000c11081403815020b0440d8903c5240a89840c02088811098928040004590720010394020040c0c2c140d100c550070101d646543c0b202203080300441c0d1410005513411405d00005107550083c00e95000141800102410b0281c030300400b05820450550341001c0c5400c25034128001d072125180c104281d480035000100c02c0d40c64820b5200b1240c0710050402d51303901620442c2c80e105200041003005e001306004c0781c1d41817140c0f000303030340f4809074138076100c03141c50443e0009210380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 448709901 1250 448708651 448708681
    0xf10050301030b0a110315040f020c150703150b04051c080901110c030d020303222a12050a120e011b0804050d0c080111120f13060608070e 61
    0x50165691880e40e821a80c3c0d8240712400540b0807140141c481c0c40e522803102003c1c01035803081c000145805820000502040241c1d0b40c2d2011700c0302000d104200c0c082050304042030603034401070040c0b103240f190f0f169010200c00a20302410742c0f900e0f100c150312002c00c1224070302c0010030450348211400407842480d1882041c0c441c0700d400006090410401c022402035014030031b142c80d00000070302658014440080880d00f4088004160740058000004108a407007a000030b8500408107a000103899030a241d5403641c100003501c0d0700703807075000c0031000d141c2440c11b03400e000030054444e401c2240e818250070b1415030342d1408842011129400f850424a42d0944900b0345d1a042090507035505460390082d004a400b02591640c0c1510500c804101c049001d8580d40081c4603028410042c040700c00b03142100c1942110300f081d124101c130000030010b2104101d6881c9401c3d8115080c608580d0490b222280040303440241c07008020010345c1404400140b90ba00842e0070001c41d003a0210f0000680e0f2184914a2070300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 448711151 1250 448709901 448709929
    0x3070f0909031202031302010314010608040201050c0a0c06080901140f0c090a0b0714070e07080a05060d0f03080108161208030603120c0303071b030f030c05040b07050601050f 77
    0x1008004200244041e00110492402800c01c0303034144000b400c40c082a680100da4036005124100c41140c21940d15104110184d10030100b4100c9a50401c035004240321030140c030281c100603011030b074018481001c0c04100b9443d80d003c035140044543d102c00c05805128222000b0510b5460076825a1850300344480140c030802520002e00015a04c002ca8044103030852100c1540001c520400801c054145100030700c4101c0c002d0101c03612811401c2000341c50408540c0014090400c85010300018680114031a6001b1030094008211071761140702003032400c41c584c2006815001030078250750605802c0f580e00b82c103940c8800c00b5110052035080c03d56030200c0e03d600c2a030f145c02d03007610140000710700024003540d0891402000d6641c080c0c244c4410031950341241c0d40340a100c1d04000141301c842c03a08130241c044070300d0b24003110001100300c5480c040d00b00a5808088801d1545a200101c086440b44044030040d14058002035114102401c0c641d5598000340250303409901007040b80802e92074499001c5c0125 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 448712401 1250 448711151 448711169
    0x4080a030825050f040f091d1c0309060f020a0305040335100b0c010e0106050f0618040b0d060f0b010203030f010306020c280525090915180c050307 65
    0x2190800310f419902003c640d000404050202040b103c49940903d00140300807600401c07035401ba220f00c200141c140304900d0055034040022020700303460140c020761903007695041c00590040182030440190182c0d01c0701100c00c2d480080c1344c400040c0c01d81d0000d80214042d55441075141c9080c068013080313801140006220b0f81140d1083d001c1c00300700d420295408547d0011221900303036615100c61060300700007038900a594507003020100401c1c0034070900008041c00c54014802d074141c0780c04113800e4071444401c6440060040c1281c103650f02d0796002400780000c090150303150481181080d40050100d00308106155083c40c20741142da610010680740a141f400c10303044001e0346150341d844025405501441641d0087c0300304100c8081e80f20707030b14400c00507071403840d409400140c2c6001410b000c0d802410380000e5402148060801050207508420740720300c01d800142500c40c500b0b1400d80204000450700d40203007080c8000600d6800210030340401c0d4422040d115115403280c04064445000340a00303032103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 448713651 1250 448712401 448712461
    0x90b070815130203061201050c0a080912030c07050f060a0207060b0a140d05010e2b030606020304060c050118050a12031103160c02030106030c1a0c070b071704080a0308 74
    0x30400e8683c01140c0200c0001d0680d0a040b10001c0308500390340b021924298440740115502c0412508900310552101c000ca025080f10b0401e000040f0b0f9038003014245000d00c1e203001c1240340820504014044082e000441190103030319168401d1000382d44606400c907a0a400d00c0031000301420704280d1242a94210100c2c40b6803520f076403051085803100c200b0292100d41d22407604401214051014404111810580c07100c04e82140d000347c480700302030040050401d80f82032001c02c8155400300c01d85054520918000801c1541401c08502501c03150611800345c2203034501503001c21500144103a0545d1084008813091201c241c0c0903000c0b07600d140d02c1405c40c0f8100300300242242001d103441000080b124185045c584070242c0109084442580048401c1c101721101805030142d58010035440d41c03000c40301c3c12301c0c0c068100b10058599110b031094540960f800305094007006060072a290141c1c400100d100e03120343e6108190703503032107282920a5011400d040e0202d5a0810220840d0340a40c25200380d0b104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 448714901 1250 448713651 448713679
    0xe060d15030b01031209120201020a1202010b03030c010e01061d0a090807050a0b060a05030a032c121501120519020118060207140d03021915090b070815 67
    0x405400d030351000140ca080c0c2030102000158000d422a8040e50048012445440d0590000303800c44009402000e141c0314541103280040c0e0f8005015104144e111401c00007420302d050040c1e016002980e509503040c0804104205140310540c400340c10281d0110007401a13507626020601d42c030500131070400034440760000007103000b10a900704114581c0719110b0103162400e02d4641a041111203081210000481c0c42404200c0c41d200044001818040300907000054055402800e000880710200c5840e40070341114200303030110000c01000001c000703401c00c0d198840d4540402e8403040300020900034510014004038620038050240c00d41c181e0b100c001048003403051055002c0740c00380380408904015005080c135102411410310040201080c0d0010094141401803d0514040b51441750340504980810781010a0340050440c0c403841da4a1488003c00e078007070500b000c409030041601240141801070203810005001c15a46c0f1411140c3e442c01c040d03448170b854900101c002c09041c03a6115584801c0c501d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 448716151 1250 448714901 448714927
    0x1f060905191107120c0b0c0f160f0503070f0b010801020301060e1207090f060e06090c03070f090b0a080a05090f0d0311090411041a090d150e15010609060e06 69
    0x800c003014102050f043c285180d03030744244014410b0000000400560400c0c00b040199a070158001c0395940030142011061181503c0c0c81c001d80400b4054414405404018001c14950700706038503400c68252030742c0d00b105040183d0340940300c400851b500f010b56400040c0d074003018030079241a503000381e17241c200d456401d1081000c0300d003c0c40300b0f000282c01046c500181454041c443e0ac04038011600000c034500b8a0400c1000c43c00c0030041034940030f20001400c016108131010700701c0c4d5110b0703000c1c140b503801050a82d07411907441c9450381249096a2000500d400155041034041d13100b4802180207006550f6810a801d0302c0b543c018401210692061700202d41c8280250440303104d85215684080c00c00401d2000174081e1106540060040c51780000d090040220651900300081119004036246c903981801142c00b540b10320b00007804d004007625036500d03601c0041c0c0242552100560803513007044801c2c10f903a450101700f8800c00307010070031403a400222070740038000e418440e0070010415401c0040340346000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 448717401 1250 448716151 448716161
    0x91501210209210c0102010603020a0b2802010501030b06030c0d06051302190f3201050c0303040b0612010c050909040c03140d030b0405091c0509031f06090519 70
    0x19202907000d000702203081c0c44024a112141400e640031800706803200841504028004500c4c504590410f681800980c0b05ea00380351084036665204155115024040000041c5070f0016103030703000340c4800c01e480340c0f0b5905411542c1a00d0051004c02c43e5500e07040d00b050b603200d00b000415600841c21003985408202c80d0392225a1041c0440c1d070440c010310956000419059000c07586290148104c0c0c0305100080c80c0c514004094a01e031351a105600b075019041000c6800c1207564092800c803107903403c0d105139205001745c4140f01d0901c801c9980f43c0c1418608400240403c403007007402411804940d0b1400c410502514459502e2501c2e600c0c03034080400140035109a00420556070031443d410008001176825103402140d4640390003500400d1a00b60008042c0d61070310642c13500c07507400c1100344541c140c0080703403c81d01c2038000c4140350b00c1e10b1390360796090301d01e03001d240c05035503042c003880c0c3c4031101750f00750440d2088071a4051042040b50544680b40381c8211141950703554510105c10b00025107101ea20743c81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 448718651 1250 448717401 448717457
    0x103350c070501110a1b050d030305010e0a020a0c06050a0b0d111003020310060c1106030705041a190c030e040c0905041119080c190509010215041e0c030b0a0506091501 74
    0x100c201c1d1501c02023010030241130401c50000e0fa07a00010000200c0d600c03806c54120300e00b04400d5180841286005010a0740381d48003820b000d40c1ca0011400c2c1261304d5010007407010001d0000f001c0f0300041e091660801004858840c0103000200805489601c24402c50344680c68550030084410b080c001d0403903040c1c10710b0004880d08100302c020b01c422556220082c501ca012555200c541e55410408008e614213152154900b52680910815181840d003040b41c00800e00b00f031912a10fa80340768141100c007400b507252002d0700705107481c2c0e507981c81c00d034040304c60415154251030620640002054269440c800c0030361a01d03090040c00401d84403188540000c94108c021200494100131440000d10051420880040041000000c4c1a8007d58060103000d40c0841083d4003d00c891a0544404580c001c04c050004424501d5003034040c00c00641c10141005180c2100e03940440303140090502c40105403d46400b440fa055400c0000c25102601d040c0483c62001a940c0740d00c2641c2c000c00103640001c40700c90b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 448719901 1250 448718651 448718693
    0x7051029011112031e16031a0d0302060a1a030604082b09111002120c150907170d09050d060b0d1208010b040e0103350c070501110a 58
    0x11420310300030100800e034a02180001255602d00300410400d51500c8038001e07140c0217560401c2002210300301c01c000702903000142e04000c9903080c0150103c00702840c0d80d50744154802aa0601d44003803507400283d05210714003120303040101010030000e240175240114401545a4040030008000512081c06010b0248500502c13041c4a00b0010362034103507521411480201640c0e4211480520000c001c0400401d1f4080d20080c481d038000540003900c0306003042c01c2c007400c0000003402510b1107908011680b91032090102c40e01403400c00b0314045444803844c1c400d54640402a803894100400d000c6444d08152400d5107845081030314107420300002000480041c5c03100c6946558500c90740d00e43c0e0000f002154806c0c07c03280502e4464000160074120181c1010341248410f0006101c05c64508142a040d2a04000c50021281e03010b224a81506041804080701e00200e25101c06640402d00c0904800840d03d07040d60040c0d41c4507001100c0030304111250b03a5071580402c91010105881e45541c4225840c264 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 448721151 1250 448719901 448719917
    0x708040e040605070e0924030316050f0d030e031207050d0615080711070501110102041e290405041d011a091006350c0705102901 57
    0x2a00d50340d5554200c0e01581c8140c2c4580c20842c2c1c3d294408040700c0d21140460703241002c1d00b070a82800340050078030034220b491001880e40c000c40542e4108155803035103205400848581c20a03142441e12100d00b2804c0a19501c00c0d07103a015030181c0607000701c0100c1c9002c00002c40c05c1462541401f070702010702030400c2e028407004210071040d000c8a40101070140203816a007004030301e0804401460548014000800c0020800f50000d0714000411084200c072001d1070141c2481d248201260300910999005c0444400741060080c10320824071070703d40407158182001000203250160304455841103060f0030040c0304080009200ca40b07426440000a5203150711000306d00300540c007440c0d08640003005048611007000c2c2c0e010460313103000b00c1a6540480d5000c4d14201e45440c1560191210080f074074203441b0381102e04506444c5040c08000f2005402da0301944c0286418411040e600d2544198010780d090300401c0500f20004039107024240ca0f0b00904112907801070b40031104d00100d0440c0039000c0d41040512 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 448722401 1250 448721151 448721159
    0x30a0608010606170a060b0d09020117040f02010908061501030f150b040f080307120e1807080f010b0a020d0e01020f011406120d080a0b0406051011070b1c02070804 72
    0x24440c0d00040c0ca0b107503c0d00441e082103440100101e584c01018281c116003000d2050081e12a00320503500c43c00540a0042500d071114401a2a103007071800c109441114218100024040c5151104009034001c1c0c032000c83b00740d04e03000e910383c842d8400c40b24102e2903550f0104003a0154803940c00803245d0b404020002408030034003070204041d400c8681c0f0030a61800d0100d010300c218111501c0340001400c0900003185014459a1080d0b141b24402380c071b140912041d11100002034032646a00e1011001030030f006846480d0020700a00208400e0b254003d0b219298000401c90f40c8800e402c40740d002044d0307002082e18650b034107001c840c41a40000e24074114094070550300c0c1c610b0070900480014114030440c0401d246008000e100040300301500c04010790384070009807482c903500301090540140c203c03500803130005404804100a02410f50000c0d03041525042010b00269115802070050007110054415003507a441205803203008400c0c90142d18031841501d240d14401c0d6500900c042440380c101241410b0365 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 448723651 1250 448722401 448722403
    0x191b02090403030e060604020901121505030a0f06150305152a19021542040b01030c021e01060e0c0703020f01020a050301030f03030b1f08060a03050a08030a0608 71
    0x9441c11004a1384410301004043c13400e00005501200581c0c0447c01d001d40c01c2e00080290540c0f5180c0d075406640c1e609040b909040b201004406000d024003100c2078950f0500c2c00403014901340205440d05464200c0003d03160240304006011aa00180140a403001e2119202d1b903510000c3d0032800320040702c207409030001e841504d4080c01001c052901a4072030028420b907404c0c0d200f440b1451021504020079420521002e00390f02900400001c41c98510301401e1400d0f84910359110b100203a20079807041c2a03010640c5011858454000143c03001c5c000e000c201c03001582913400344203c040c0540c100c000c0902070703000d102d00008600d103483c0c40085010f40c4d6448818058100a5070b000004d4000022000c0905404010303400e110b42541000714034080308038000409038001804020320301c0d03148106140a1500c40c1e00040000034001340307000b010b40c14400a03841c651070075908039000301d8444000181d072803400940390800c03603401501600700400e44d5a01c4581c42d40c00140040c5680703a481c0808585900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 448724901 1250 448723651 448723669
    0xb04050d0636030801090e030a27030b0103110901080303130623060a08070e0a0b0105190302180102010b090604180803070201050417190807090335191b02 68
    0x105500340e03500d40c0d0300b0302e042c0244401d20580220301d1090410005a54041340041154020310385450076222080b000041c15000455545810b015819600808810301c500341080c00d049901c1510b41110300c0441c0c200b80b20b503003003092041500d180c00500000341c1c06a0f159110144c103d00c2042c0c00181c10042d07100301c982584040c0401e09990380c1c80741c10070075607051401e03141c8080c2c202c0000800130345152001d440c5031180000c5c25480d20b60b4681b41080e81c00d074020000c2c0c0b4034085a4032101e00c00802d10390001070003900b100c0012070303900c020100c9032078a030b50062040c1c01e03918030081d2441907142c0e1000280405803813221003100708050360000080c0030440f004091401b429517039002080f00e0a060070203164a00c10008990554441081420441070f00706201640e40d40050418540f540c1d00c00100f0b6130104180c0d80007401051030a4800c80c90042034100390722886041e0301180c86000242503100d050360044209040350f2004204040e107d044c002c0c1c1c10b1405041030148012130f0001c013903001c500050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 448726151 1250 448724901 448724981
    0x601152007210f0f2d020102010c0311040e040f080d0506041b05070212010b0a090204090e0706050f0f041d0601090501081308030606070204020a020f06010b04050d06 73
    0x508620418800000c2c0001c0810502c0b0507214460803210580d251114030225811000f4400b90080395114100941c0050048044c11100c3c80d001103802040040780d80000e500008a00552030203080c518603034064070454995501040c54a4141400c00003040c503007140190041d40c800041800c01c4000600300001080c05560503400480c03507050030070910081e00d03901c40e0b00e9514000c5214811444643c0507054032101d5404513404d1201c05442c0110900416104904a4001040a5001c2000c0c00c09400610484003581030420513104480210703034481c02240206400242c1c02c01c030240515441e000a0444103c140d043c45207072a0382d4000300708901130040b018007a5982c1e0388003085030540c0c10145110080c4005e083c00d82413032a140c1d54950358a010100c1c010a40300f004030105038561a5401a035508550140c000c540d581c0040d00080c2d034407022003651450500c10040082207800892040d14115080a84000c01c2407080c3c1c2e83d030b1000f6140120025140080c5910340040c4e414198012741289 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 448727401 1250 448726151 448726153
    0x8040b0408070e1e04080307181203140901050910030608160503100506030c010f2a12020307021f02030706090b1605030f0a150801020d0204230306011520 68
    0xe03502d4081440c0d10404004e00140310310035124088000c07403926144041d80507034468245e0b0398a80e5507003c1600c56a4002080620304980072a000c9024446030745288006406515203c0042c40300843c2000c0c9031080c0d400481c0080d0b02070010082a0130300a60000301c944250a01258458842101903c0d000d0303c410080804c1c0c0c0c802501300142c0c2030a2102c0d10944031051000e110f6032030541e000c41e60381d02c2c4c002c40e0070707040101160600c6003a80c402c40e40e000301400320740911340131903010303803c210180c500c0548103892448510001215281c0004100d42d11554082d00d515000a40a0340791605040d510144505501040200c40f00080051041e91507080c80383c43c041e0400d08124066400e00d681d410301c40b00500c0410801c0c800201c00c412503560380003e540b400411140d030901c68940250349543d215a07140d40c00812614041c885c9038002d841038503040a01c00d00040a07901c1103840d9040d501d000f254164101e600103128030915410f0540044601d414042c510114440c80030a20f1501d00740f0040c89 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 448728651 1250 448727401 448727413
    0x708010302011707090e09030f07110901060216032316090b040b0108040807020303160506091219121b05040806011e060e180f091203010602100908040b0408 69
    0x2103681100401c00103100002103c055407400440c05042d88100d8000c03400d880790a20001007907044200111145010342e240842d4542c9118506403005c1300454040c0c7c0c3c440c3c2c0703001d070000c42c0c1316100080c1e04908046018480c075000c0c1c650f03103c814000b0114028444140000c0c11a40c440e010100102d9140082030a24042020301e0840c0282c119111b07801624440c40c140001c1c0b00300e903a4011140fa070440e07042848640da0303140368800a4598851088114000c2142c5100c0d5814428003040c624481d68a01054612252040609610611480d23691149802c405414614047e00c075100755202e143c60a08000b4102007280074442081c055001d103400003031030010b8144a840028881e00380100100b20201e4868400f0071840791030183c00780558820030200301010202551031104804030b69480c01e00c1da10319410198251070842c07004680c0383c030662003400145d2402c6030008086a040314002c0d4054031043c030ba102459405409d8454083e54000400c0c040891148041d03402040148810001006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 448729901 1250 448728651 448728653
    0x207090e0a032003341412030f0703020711090a0926040b0c010603021c0302010b0904021f051c150f030807081b0a0804060e0303030112170706020307080103 69
    0x125009840310f0110034064580c605000c01d0000140c951401d01e0254040200d14044030301480c00341c600c1c0d0101116181d8a80704014441e03c003e2514000001a0036076500e43c00448060315035203c1903031400d4524285c1d0b400a01c849200781e0141000d10b00c80e40e081d0741010384c4c030740014031007401c01e83c0d40c400c20a40c1d880600c020040c4026039809880009901a00d4164038005d81e1030450180f0720401d0b01800c0d001541680c040002c3d800b85018503401007106021005010b290030000002000482c050b40ca041d003180c1c91454000f03c502d120740c0d801001c2d24050003100c40035401c140380846400041c07240600980007117900c520f941c400c0b03425030040001500360850080743c100c9c440950100c01a9030a050f07090000c41e0481d4101c50944d0b070803403000c40c0c1da100c010703114621070340c5114442c01860044c48540800c0048260040c4101da446558082900ba80785d010551244402e10402081090b100c44090000c1cac2800c00c0709500c06003d210480c20b10005490b05002c2e42c0c01120224001030312000180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 448731151 1250 448729901 448729907
    0x406030510060e060a030303050712090812010b03060901271802010905060403050307060203071e0f030605180f0717070c02190815090c060408010501030605060d020907050702010207090e0a03 84
    0xb00050420102d8600740382041404900c003ca05400090205138484000650349402002d840400544d8540108810391490170519070681240c11219980054580001841c02d2000140c0e40204401820b04160364a0501a6000180348000560031401380c000d442c07420010901c52070004940c00c0180400e809030f20f20004041c2031094221520a07941803000380080ba100000303849a050703010710010b07942c2d00c400c00c081c0c907d00d02c0707400d1400c051180103628525280d401404240e1141d02e5840610141e6280d40800c09649503904440e14185600d50004868100e410041500420941000380e08510341d0207450000c0c003411542d100100749100301072000c40c20040083c140c0044455009421541000b141c40c0d260001e2240e021074480c05140815148082408500800d5100400d42c59403070f82c1d55143c8901038002440300f502c00343d00c0c22000640a0600e51401e00c41198003c080d076400d913890020940710740c1c128501c2a41184940100860250b01034419207100e98a80f20080c50f8440d00380c076000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 448732401 1250 448731151 448731161
    0xb03100f14040b0408030601020111031608090c01050a1b0204060807060e04110304031808061008160305070618030f110f0a03120e0303120a02070317010513050408090406030510 78
    0xc0ca007140004010031021600380014150056400036440d40d42c1e450b0715004078054441641100c2c040c071000020b0004070011244e00b00201d403520703210005d05545429000d602c681c40700b0f143c00e010400400c0b04050683c4200824400f450710000000c240c0400764020608588040d0421421039209000501c030680d0801c135032146030380c0101c500f8403d981c0030036041845804064001414020305980060950400d0b9100c0c00103800b02004642c918034028905040685061007032500b40d0081590702010300010700c15050540390400c0086c89074500e00b290888400e10303850b42d8250303003070600c020110001e02140000c1841c180510f070f908011030307820b00c00c0010700c0580c81d01140c0f0039090500300308005510800c101a00b80402e0800079082039142000c20b04600c1004031030403403608004100144c82e270140d4003504166000740d13988183c01071403424141c0940300a00a9560100000007050408000c6400227a071062095802600f06000340021806803100c0b07400c2243c59400c03030fa60302d40600c8054418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 448733651 1250 448732401 448732421
    0x112020304030903060c0e042f0c071401021e0303070905040212040303020f0906071b0e010e15040e100617010207020a12020607050d080618060f0d03030b03100f 71
    0x11031031414103503006080c01680b484001c00058580351031424139406182c00d400318050161080c071042c60344520f0a070155240785003020300c000440f520814450203000c291002c000041004000ca0b50510500000c02c5c0350401040781181305801c118136003280010018880500c0c113000454590900000c0a421100300e60002e0303001d60b1040c80001001c91104120740e401ca5098100182e60b5100040d0321007280c4030b00107480781c000308000b81000400440d60400c407500782084071a402216143c02041051080a1003498600074104001c681c540040c0780009850020003000040c88407900942142007144c0c130403c2d07401803076685000300300c020f0b030701c082403008014010700071071809080340c2c0000e049804a016045007140108100c03c11915041c04030b90100790400200d903042d0000c1400140b034608100c07510f41c081d0f80105807900582d228600c3c000d00032807006081011071000c140601005c080311071021703070415883c0c4c10383c0800d64409001c01c0c4501c1460345000701d1100c0c80a40514151000a10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 448734901 1250 448733651 448733687
    0x5070c0510020309010c050120030405060a09020d14030d0e010219030b28050a0b0d0b060a30060602070515030108060106050d020d110c0d0809061f09091101 69
    0x140050780c403680842100d0070480c003401c08a040d1030080c01c0c000c3c010f000e0124a1032901e0503016034a9030054441025511882c0301c2d47c04c46815940d00700824090700c007070407800ac5d00320800038a44800034180c0035100d0141ca0311b00040b2801d141d0100348103010b07070707000700c0c60601182d5000a02e804a101d5844029040700414101401142e20308000300c1c5010403e440303050849210301c8a071500006408003840c0c01408001c116403011500d07807220000d194090b242408076580760080c0101c4a00b8031f00c040e12a0502d43c1c1d1181c001000521030030b2410310498646c00e105002d03010007603083c460b140740305070070207040661300400c41030f0f0500062018800b1840012020401d0610041200c8680040c410741540c03401e1030322035100c0304640d0081010340110301c03c10354000c0c02d0030703a00480ca880550151903030805020484030203000800d010b0b14000800e960094107900440c0000c1c2451000322010b40340071440100c0c0c1c0b0b064554034800304048481078502106c400d100301000030b199683c030000c13041649040039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 448736151 1250 448734901 448734919
    0x20c0a0302012c0a03031106010e100303050c030c010c020615040204030c05060c030d09030c1e03080a020a0e09090304090e0303010837060501051003020a05031801110a05070c05 78
    0x180019058030f6035941c04a1001c0030350411126010014442801c88030380c0a00049080c0e0b4581c5009080c00ca1200b19840c40c621421000103060007500c4240da01410f88540b004081c6410b54404949607803000012012a01c020401420013007024407550a0402003603000d00054205102c0c49065003060200062180d80180000d1020484000c00c8404440080714030640d1800c01d094103506500a00520302e088914014a00062641202c00708466a01c01e0034070030081140354950341072085100c00054002824000052a504c285030b00600c56185241011202d80650b440040d240c01e00445562103240c1000c14100040300a83c000c401017540c1c948091800c56044c1102ca503070728103010500c0c0400c01143c94070541034000b60109007480039420103072565085441e04180000c0c0c502031040e1400b414107415400561446842619142d050503500c040c61521540030540590300c00086644155503a60401003181680c04010308c203244050701d0707450f280d0303a40741401c3d9030b003170041d51046004417025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 448737401 1250 448736151 448736153
    0x3b090601140612044404030b0415020903100e0c030105160813080d0e07051f030b0f121c03061a0a02070503061810091703090307021e01020c0a03 64
    0x102d8292640216507030f450307102c0e40e5101c2c140240d20b4407903c4542011089400920400401c90301e00601d00b40c58130340c20219040c0440c2801020301e100d588400b80c1803d8445001c5000507500100415019030b49103009801c10b9500700010381002c1d0220500c0c1082036403032400e004c0410092200095120007100200300c0740c03600880c40f001c003e583c856032000b04030440d40040d01c00240080500100c54110720f40b19102c3d1856540e030001490001080707036052040080024142c1341c200303045007500e800c4510b200c4007500300c000190003811800780c0c4144c0c06041c5210415550701c4000c0c003c00c03810350070001000304000f500701041c030800181c0741c640c0400d03003000c0b414859011542002090800d83c4d0840658403205030200f01d040200c2d90f0003444e80740c0201c00505c070101114400480609500310103440c1540300301c5120000b06c54a1403002843c14090390303208000004110301565200000000380c0b0701d040003540c001079403002c842000d03d0700c10003444808025540c1c1001000300108098507400d0b0f402c0e0071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 448738651 1250 448737401 448737409
    0xf091504120b090f010609231b07110603040b01033c080910020d14090307060c021906200a050c090604150305060109243b09060114 58
    0xc0c08000d0034282002c408151906010801c0142011564008000050301d036603480300504403c00e1424900b5500000c401340110080045501500c0010070818000007446003a1a01e41c011000607503524484043c0c8000310740b42c0d20b0045103d1889034400180c151b05510344485508180602d200600450034400e0000ca00c1c0c40039500b1703c84203854032000000010303182651951054005868224140c1c8009080043d0001440201184240c95032087c90f50924050301080c0104003041c1d91540c4144010400180100e101c45005400601200311414a03909805603100291707000f080042d01d100c0b01d141d0000214262a070743e1041c03040242c24600019100d003965009603001a030712802100000c18021f944c0d40d8440003103009488803040c0200d0762402d019031108001d1084c240b4880c14a6600074000c0108600600c69144e44619070341118149466101e00102e0340e405d0100f14003403c0c00032070000344c1051602101300005218541c4234035007551458103110060b8004e0950705100020850145e079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 448739901 1250 448738651 448738679
    0x901151e0317090d0c030210020115031103070b040e040203010c091409060609031005150306040b0406020a0e0406090902010908030a0c0803101d01030b0601050a0822080f091504 78
    0x50882a01402d21020511400152080b484015070022240d02c4050811110895403003c8900807140002040c4d03003183c0c103038283c400e103c4c2d030842e0440c8402d01c1400000d41200e01c046c5401000380c11201c11079150b51034031301305a10035008608030008180030070045240074020108980410b150030680d043c9451440700b41c403440c0000b6035100b4186500001c655803070705d030150b8583d1200100ec8480e0100c1c0b523102c560052505880c0c1400350a007940c0000340500300000c055011f2544940440302c0c60743c1d540c403400c0003904074070120005c2043d480c0c0081081ea0311401280e0150040c2200000c9882d4180b0000d08a020b280d8486a0b943d0000e20a60080300d40081d60b141c5000c2e0850f001300d660b50384203020004204c0003500f10b40941c03030315251088140011003658606880c800c40b0b032401144c54a00040d501030251242c5400003c504030001455203103200222000d40c0310103030610003078004968480364a40c1112210255400d4045000d20070703072400c18034a01101c030b2507610580c91b240c107000000c08611 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 448741007 1106 448739901 448739903
    0x3c0f040510022506080c0a022a04050103111e0f0111010e0102040f0e010f080604020d05011d03180a03080904090f0c14040c020d1d01020c06030901151e03 68
    0xd44840c1100e100c00c0e41c980003407080a40c0d880092028100d88865450500003420035107012b600c881c080d05019611490320740c0071030342001081c0250410030030000da4400006205215041d00e59100c400021390003032074452041307240c0700c0c0d503076000d400c1044511b1107644c80010b0015041001f0250350303082d41d0540c4103e100907641e904031600c1e81890b50042c000e00750440c00c0441c0061904843d4485424400d500120751103100700854060301050040740b00244d000003d5070300340d0040c034110340075446c107040f11000c0c0d04074115154159680200c19005004556035803010080c03001425103021038036484111800d815446003c90100040d4494000c0d000e00d0034072040030041c60011414044000703690f42c40382040c01c1694100341600750050100740c15400f801c4041030050b00c50000451059012500121318903100d90312018040b003035035126441a40c0c078194281341c20010003003540212 = true := by decide +kernel

theorem cover : BRFrame.Cov 448561151 448741007 := by
  have h0 := BRFrame.cov_init 448561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 448561151 ≤ n) (h2 : n < 448741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
