-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:35:31.570818+00:00
-- url     : https://prove2.me/submissions/3415804f-f59c-4d46-b7cf-4557d8616a6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 908633093 ≤ n < 908812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 908634343 1250 908633093 908633107
    0xb0f0306061e1809100602120c010221060108060d030915020f0d0f11010515060705030c07030303020c010b0406030506040803060109170717010b0f0f13020c01060e0c0c03040524 78
    0x800b8001540007490064042c2000074103052680c00d544021b807071590f00101100c0030001a142e11a034003600d10802076540a0082e0003820105400c0490300180c5081d0300e02d0f04e46401c038001132540c90f00600072880b801d01c0c1d085400c046a0440d600070191102c81c500307c01c1e884c20b40a0140e242c410500f11509e02c0e44034060f40e01412a5020f2600c18041c05075558a0700b011441c030b00c04500fa208140c0d007205440b03913100c2850300303a441e0400083c08040d1090301640d007040c8000c0303081810a5425030098000c20340014580c0d841d20402c3c0b040d800c035070b0821542002200d05503101c00703075a05001480201031000000108106e40e004021000041c5041421403038803074411035119846040368801d03a0b000081180243c001d113003060040c42090301d00904690100d030700c11001c200b110400c5d140d4807500321007e561074040300742903070004211003203040f030001c034100345040a1516440002040e0030b5216405001982100c5008400c65044480c12a1480710017a561080c081c075110003608034219041d0000b0307003a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 908635593 1250 908634343 908634367
    0x80a200a1a0a2309061311010f1418010320030c0d020c0609030d061401020a0210050d09030c021002060f0c0c0111070318050f060406110102070f0308010305070b0f0306061e 76
    0x1c620500101d0140c58003506d83e0249941828000200100005403407100045154490a00d0320b1040c00c0c14035101c80c003c88981100705603603000fa60b41e02004080c0b20b242e0709980d60940541c078542654203100145483c00503250280c607020150103061100000560151550b03010b405a4038049082c0068900d5400e000314400d03902c2e0f1000724190700701c80c01c0020020784107481e203030b86422104041c2c018000c402c10765800c219008510458120500105000c9003010b10f80c0c92194a1041d482a251544108150b0041040ca822140c001004541c410010000e40c00600e080710750300840d0ba508801c2d1030300210f140b0f42d4050b10039107059403030410700412180c09259001c11010100101000f405440315168014050300c1d580500315190001410002001001c1c49030082940c006e480b08001402c3c05041e5880d8018038031017810a0b000100d00c1300040c420300c082400304200510074222101d10300b044022681c80f581c00001c0c840c611070440494420b40c0c581a0714803050b00006a1084d103590b074080c18901d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 908636843 1250 908635593 908635661
    0x50108070609090603020108070503060a081905070e1605130e040308011e0303020303071b0b07031d0a050703021c022d04050903030a09030507080a200a1a0a 69
    0x104030009841200010705069a4130076001500c2c0c040e5900a0725607102c20050301c01c2e61002d0185078210446200c000707a030500030720401134040c5164240e002c0d035001c241486480e100481d0081300b240b04a02c0280300030409038000c0b0f03aa81380940d050046d1901c240d0384044801e50b016901141ca05c02d0780d00204410154000d6109050315a02c400326412000c40702c141c1f0800ea1003d0000501590040011900c032600501d800300d01c04442164400c4c0c0640d084c0d83c0c00c0c8004130b0a81799180440c0d2242107030381d482e80d5421031044451140c403004000003880d40c0c4860340d88001601c0041c0c028142030042e8081d04030748100c0090102d401a000c40d50840e580d4090070014014604001b00c0003201c207501d20340794501801964000c07043c0100550464546801200081c550004120244081048a080091111806400881c03026280e0b04001c1041c14a146c26030040c020f0740b0115030300540742c003000103010201000c6848008450160741d90790b60070741c7c000044c041c0d0011070400c030f80c0d40045004981d1030070035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 908638093 1250 908636843 908636849
    0x3141e0c150c060a0b03073f0f061a04021b06010501051e0c0a0f0521040b1c020f0409060828030e010509120a0302060702030f0d0e0102090405010807 66
    0xd200003026074840c01d0300054040d010800300c09401c6000407500d001141e40210001d00341c01030179603c0c00d903030f5a600980c2401c00060806070131300d1500e00e171b40509003040d201c00701d401d61199100162409555103202c1d09406206000300b40075500c41680040c00000d0760814560240940110b41d5180800051400581100042c0c41144641400452254403600c2502c82c0c0755060b00301c60790714948030030503080309810181d10196988039101c00c24011804000041c020f2038001c602034124190503500c101d04110088043d00b843c1c3c10200002c00800b904601101c0041c428401d01030403e18503020068040e2198003070500c0c102c01e01160225040e001c992021089800d0740081760f501041620305c44400a045403c0c41000b5068014a81c0100c1d001341141040c101c41490030624009200b0005410018008900303441c540c0000590342c10140c04100c01c0e40c000f032860006500f0614071150280c00f03403003800c81c0c2400b0103031540641020480250103170b070010040240180302c55a1540d80c0d05507920320500c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 908639343 1250 908638093 908638099
    0x302060a112b0906020301030b01090609230a060803270d02010c02120a08030a06060f080f1f03020303030a0c02100b030709020a0e030a080d0c030509060103141e0c 72
    0x450115820034041c0d044407a191040c441a1019052600c03495402485103003000300001e40b14414030340015094401940603501c10b0760050f146505044007070040794100c0e00b02121062501c03150159804030011070303502d90b08007100e061030707155698420000906420703806403844c2d10000c40d604a900143c1c45594240081428130b202d01e812541e070400614183d8094080d0114900200d040d0260824041e10300c4072413031000c11142068210ba64034001d80c0d0040b100251440d07940c10040c04038030b07445064034000d00451f10300003d05003415044c40d514800c000d003415040c03029403511000e07503c284003180d000035600281600e85900d04515010050541210701c98010b0148a0390110325080902c40c90380508802307001403010034109160392000b0740c090344295040c4072424260784031540e4200b1403a40800e2007030031a10744036410140503c06582d101c003440c1092600b04010407074034007400502c10381142d410181a621080700070145a0030220b08903030441e0200300601482c49140303000690082880410303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 908640593 1250 908639343 908639351
    0x309051e12010b0f0a0b040504090c0b03040302010c0801060315270f0c0f090806072d12200304020616025a01031104140a05030f031905160302060a 65
    0x1640400c05c2901c8203010704030786c0c40ba0510040c4080d0415600c0454214030a060400034503446686c400d034144c10403501200140e448100b142c2440342c2c411401401081141400e0200307000820b92404075061601940e41702c0700602569506030320728184020000d103840038040000160110f03002024190f500740b0309001c5181c401d054048030703100782e11407012151400702400b010303219041c040303d50411040d0000d80c0c0080b1001050300300034104865001d40621510f811814100d03011a44098600380d2003075290b10b1081e001080c15080d400d8007229481a4101c1316582d076180c05105400d8010105540a5084000304519454442c10700b1145030082c990500300340011341030b41007510340b912000c0d11004c000050034441c0c004804858200c0c1e1010b508141000705004418451408554010350b01141e00300c111000707031002c141405d100300005080280c000e840352400c401000c1e6681d124410035071070000e5003007081600b03144c0318109413a01c8412a03016150808a54140290f0ba03950503284000141d04d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 908641843 1250 908640593 908640619
    0x12110627040b010219060f090b0703150b03071202030c160c030506060f010516050c060c0304060801051806010c0609020402160201021b0a0510020709020c0d0909090309051e12010b 79
    0xe03001c10303c43d1005d07044601007919940d500c8007034000014002080e07502c0f8a81100000d80e444007407807080741c0765940051901e01e000b039501050805988100c20300c840800a1084043d48003191101000e46c48101594a8440400700b4600303215681803810ba241100c0503c10030003010a518004503801342c0200c1d0403948a140c1006070b1070b52140440341c04a00100b08448091040900414080d4040c200380c4800180a102195480d80841c500000c1c9801c002418402c1c035802201c5240900010380d051445c1e41d1115120703000c01c46019002c0b9040c403a8030010041017040300c0c0c0120344000d601800940d2103c40034410300c0c400301c0010f201240940035900f080c0031452841c031440b42c2c142800400c03a00400e4984400e0001401c00c40600100f107024201001c0b800d8901800103026404a42c03000b00005621840000c0c4018101d8120f2a80c4038104a9140003007030303104031504150b6404440b912642503000700c10200241c60300380900d82003110601a001c4844040d4020100070360250749080304c00203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 908643093 1250 908641843 908641847
    0x50a03140610120210110d030615090e01061b170403030306050904020f01051809010e04030f020d0801150309050d080a050c07030503010311210303010302100912110627040b01 77
    0x10b143c0183c2d05540c24004591015207000052444201c403641003d090174a4400707202420084040b0359400800d850712002c00c040d40c0d04048103c4640801c4c68102e2010342800610000d038441845040f0070014010038040302c0e040c0100c2d401e201c0c0f6900c001807450f02c01a210031090300350000d22065000c0380c40e00100084034109600c0091156030700500c003210040c140001940c094101003544c408458407201045010b450705401180607183c1754200d03030090701c0c0925004081d803c2040b46a801c64100321850010705030040c0c030f91410354020b80145014001d11000480040c02180000b034060700c1446170b03035115103800c00e40b5580141c2001c08280007030350340e0000c0b550003440b4814006002600820040000c2988101c004001c05401098940880d400003802250880b5040410240f1380001004108500e4030100482d5440441c0c1424002145010325150601880800c00307400d400d070282d00c459565940740102e9000f103c028081c20723184805c2458184a160000740c1d074074011450030526101c02d40c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 908644343 1250 908643093 908643121
    0xd050607020d1e0c0507051905041d0607080c070c0e07030f06050307060302211611150c030702100f0e0106140d020112020904061d07030c09051207050a031406 70
    0x6001000c3c800032003006540704558a0f1607980d4165894051a08003003103035654030449400c1400c002071003010450400041000302c44166a0303c8442407401c50809a0031040801c40c5d6501c210141801c103182e940302242c46a052082e40402040d030000d188c4d001c5121185c4100e024040e0240e690700300544c417800c040d0303032085802d540078050380f50740040420071929120b50002c041105810202000070300188489940880d016520303038112180d10601000c2d05940800e4034000c40c030980d4010402081002040007c01c8405070103121205ca00200003200030b03000308010080450507400803c04107091007240002001d840e03030f09a0155080800000d4680c0c3c0c81340812085501c002c09440c50301c5010740c010b6a68404a0010b03061581d000d0040103d00e645038400d01e80140355001141199a6030b01e403c01b029030200801120906107002c071903980b440d92207902c540650311b050355103115440040c0c81242ca0460603a00c00c9503c400c1300071002c4200402074000c50144000d0108132902502e5800c1050080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 908645593 1250 908644343 908644367
    0xf050c090c0d0b1c03030b090f0c190239041e020310030b0106030b0901270506042706050709060e01050a0c020409030809070911030408180d050607020d 67
    0x114800d020b4014a401d550b0302030220858018800d80e1001c0b00d40604000c164030f04081540465a41c038124800f40c100540459032140d0244100c014070f18190030300b03d01e03900900552480d103441d0545104800c50080103030400c400284003031400e80340a5640c0044542d000341c1c56034204000034940410050606014031400190108602c50540c0c18030209807000313400007001c00c0030401800d000040461420107280d400707802d0a80d404a0401018000d2106569040e801002d2500c2b1500708103428400885075010b00e106400c002141503100d010000d4050a1111840e068100c5945003101c1c801805504142880d4403030007042c0110740d41c410081d2144200351180358045280e103410072a4035071080c270003080300075a242400001d900040e0081002c0b00d000703000842c08507881d4414010003201c10840c00f1300400c9142d105020000c1001e2140c855400041c00c014049c80e00450b9468118140180b00c85441d640a002c0129422050405680c3c80105464000c05030041c2801070641d80d100c2c03c1c02d0160 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 908646843 1250 908645593 908645611
    0x6060123180a0b0304031d01140712110d050304050d050901080112060906020c03070203210f0705030c01090b04030e0301050c0712140a030f11090109050910030506040f050c09 77
    0x910007480361030803107440058207140c0e00c02418403001c41c03802e035030a01850085000c2e0341d608004685005140c0c800414108145050088055480303810303071070110848012076800010f40b44e266401d040706441d8000030f01c1c004100c0780642c08042400c43c2d072210255100324080c008440c1403101f002000d6903d8481c3d0b008140c002103a402c0180656070340351a8403080d0b9442040000751065841d1140c80c12138004014004071901f00048110651404100c1c44038080f803429a01c280480b56078019200303910600b81019024100450290b0a008092050310004064070001b848680c505191a0504d42e504036400c5010034101007941c20310b414144580c0340304004800f5007914200e5591524407100310000140d00400400143d034030030004144000d02024401910041401d40b002c0b5a200e05071018002404101c0e003043c00254450383e4444200c408036030303054602942c0c54490103002c09441c0300580019000e403045a00f888100443c00328510121801007003501c42c0380d46020100301c0030703803010344440107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 908648093 1250 908646843 908646847
    0xf091208030f180109030c020906010215070c0c0e01030302030318060c0301032004060b04171203070e0114070c05100206040506041407050d14010c181e050d0506060123 74
    0x2107114031480c44a400410715403800342c1d00000f41100300c2c02d413202c8042c00ca0004003500802e10071820400001508850240007034400d14000284000004a00400610030402025001802d03c10940d2442c400713403128a00141c120740e12810042d40d81d82c425039611140044185008085000c0800c0b40343c000c0001e2100d0502e940d20b035840e80c54403092072021514102d500034801581541e114481e03035005112208106848502d03100c1c542c5420786950f0405042504101c1d602d404001b0340c482146d85c45016030418074810104080101d0b01154506800b0038800d8000820006012038010030004403941240d104a0b0410b084504984071a8151002403413039100d8408540054041c8045034070030055038085611841d0717070720001041071814a00a035115980480844a140401c0c0184291001d40c0e04000740b801c0044040e214482c0c40522528484099901d0060885c10050441c000141001030181c0481221400c003151501e50030783d880c5001c0313048100c400b0321503210140c804450f10310b990a030314 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 908649343 1250 908648093 908648101
    0x5040b03011e21030e01030204090504060f0e0a0512031b0a05070c090b090a091118040203070603090309090c030f06150306050a06170c0903120c062208090316060f09120803 76
    0x242d05c14110010b00e5060540901002c104a2514801c040c8982d004a40105074104410380b0502140e0700c600c503002141c2c0200c120007006c250001040809500014030182da240d589101211498060302d4407440e075850001451030002c1d074020b02500b01140154a1410400d80c1c41c1c0301c0c40c040305c02c50b503c01600204038000103a0070181c641d01c459101d0f401101101d90702c01140000412000700d080d5024400030642c014030080d0b06080140d000504007030305080014404584001e460156541b04e48865552a0358001440c244a13812140c01c03500c0e1380700244200703a128140e9104d044107000303000c400240740680000d4140f501d84001e9040328102e407129042445854106250704c000105041c110b21420001d4440350b032020021448284081013406480e60008000e00342000e002070214500500b03c61545d01d2440903503141061120b61080e9016516101000460f0805800404c0b61004841600000406c6a0411880c40e103400c100c0d6603650200b912003c0b803a031109821103001e005070405000003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 908650593 1250 908649343 908649347
    0x70b060105180310060f0e09070b070c05031b03011428060305030f041e0b030610020a0f0803090f0f12070507030b1003140a05061605040b03011e2103 66
    0x3068019440d01e02c04040707111a001081c6000300c4443c056510359600c2c041000201c00c001c0500c00a0300074081c100502d401c0003c602030f035401a80c0501019a0700000f060340421040390090f00c001c28002d0107440140113175802050b0384606084c6040e0180d401c0141c051010301c0304030441d0307100702d001650011a0488550b0b40d10440b80310a428000c03450358071800440030640400107040c801200d42c0300203545604005e800b400900c4121a000b0b00c840c141b21060000c0d0b0f0100b820b903680610300350340000c4225107a5030201e181c10286100685092002d41410342441058001144500101c07001c035809482c1c88003401741d85e40640d480180c0c1d0740d04060035a42e4000343c20401001080d00800c1205d8585031640c407140155801620b5074080c140c200c0d0000c108000d010184243c4424140d030152400250b03548031551900b500400c00200d41e001c14001c0c5000718012800e450140c109244030a441c1d60b1504803408401654224940d01e111240c0400200000d50340c40c84130210001c90301200035440283c0c1d003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 908651843 1250 908650593 908650597
    0xf0d030c080d20030403030b150a0e0a090f0c031503080d0c05040e0712050708010e1302030319090e16171b070f03080609060f010c02370506070b060105 67
    0x65056441c0c8407424000002e01c1c0b2141c0300b50484610303c1140c1c1d039062a01d4003030200c6d4000000c07140294403a554a07022042010140e80c9131901c02c1c14000700640c030f028005014001d80750400c0c500c0e0742c5012240c000780030306a03021682030046a05c0c200401016051130309020f002611004041320800c101300082110b658000003417801150910505040d205c48a0701300c0c11604503010740c00100207034020290b41001d4000c0300d4015800e8249200203506007885c050002c8002810703001c03109122202c0b1011501c00b0030448100a074280859030810003005001070440e0b10328841c02d050a10410081010909420421044c5818544600800702002402842c90000003882003500164840019444542030b00080c0f2942d8410441145841c405103000ba1003144060400e6000380294002c0125603103d52000d40004038003400c04000320340c11840012114011040964409000d9200750700f81000483d4103031108840301074004d028141c8540900c40d56005150016000c4401c01d03001c00d841e9406100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 908653093 1250 908651843 908651857
    0x1b0402090901080a03090b03060603011205100f0e12210a06030c09020c01200a030f090c0321020102090d02040b1f110706020f1c1803110f0d030c08 65
    0x16090000c0280000c010501c2603010441541141d01e0032820158028070a1000e0401c40a8031425402d105011900c180014010340030303998000541e49051140420564074041c480c2c0005000041c0d46409040240042413512000c520841d0b08141680e042641941e40c1c1049180300e05803001488000c0402c0c00c840548822403960b0790f000d011002c168001700b8900548269040135980f0b0f04098400ca0840380c40960450000c25034142490304140c00c20100c0e548482c0e58a808541355080e440440700801d84244020302ca045001c1f800010071440300c09501d070501d25010080c1c98448544800d0f0309038480c1c08041c551114070304100c480140382039401003a140c0005081084141c1c0750803000c02448072208249030224103a89aa90201c02e001c00580000d072902d440030f09080c94503001c0880ea60706440c0200f80003815441c451510052042c8107051080784030064000003a40d890501c004e200347e80d040201e004000e0350410b2040c50030300544580100740e1590f00e400c0f4544d210340382d003010f41c0c204078 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 908654343 1250 908653093 908653099
    0x24081f020915180f0d0f02040c0212070c0515032509121a070c150b010e03100207020a0e06131a0303121005031507120209090f1005060c1b 61
    0x807940405495000243c001c410078140e010229a65150400482c0c5004504142c070840444c900301001800c031456140140f40d0540300440d121003048400d074180400c2300100551150041511000d00060320b00c90401c071041580d003c0c0c40250408000a600d11013280d111110a0400c1a40d000a0300582283c400300740c81031500c15030050300c65140c80c580d410700c00001d0340c40103110340c09030912190710b03454260003400f1810640c0d034800195a80c610115182e01d00d5560f020340d140c9644101e80d00500c800072108170020f09803004c002203200508000e4009107010780c09020307242800300300400b02c00760541c00341c1c800500494554102e440345002900603010b0782031b4403000d00384000c0a0b603182080a402650300d0300034861034034034142c00540f00800060b44001e02c41e0344502c5014014011003003130941c100d50145418003009480c158104041e21404c0c6041e80c1141c0160b040040e407000307501d00e580c0149006100c4004856481c8100105401948640642c507000b001c03203038070303501070050a041c0e0341e0b2406 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 908655593 1250 908654343 908654359
    0xf1205010204090218030615010e06071704080303040510050709030f0615080a0b0f0c0405120c0a090e010b030c09130204060302040c03020406020f0a0302061801020c0124081f0209 79
    0x3e0754800341607030007140d80345107003280080c42c0680d20b140c1405690b0380a00b00344106003440004d00e0000300321160040100e40500b0000030120140b01034205200310b0340050849041e603c5a0b2008413603034075882207800ba9801c2c0501048492202014025180556180e66403031010742d0854071019121009404125081580e40c180700801e0b0900c400480010150000a000c0305442410000710401c4001c02410b2204019410444002c1c24842500d00b901d005442403011003020b42c0d521840c1c000e200310f8440d8029000000041d40c0c00341c5402c00c10320031444500034041d500111050694941112024aa1021281c4006843d14410300f51003610a0b00081000c1119590385e004202211030502c000310010741c001409120300398040002103030504104c4010085682c0780d4034001d480713500160a044508403426280e0310050004d405480c22428050300803ca121050300005a0b502c40004806141c10f0031180d0006248a000c200030081104040000c48a82074641c12040290b208410091b403200c0d01c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 908656843 1250 908655593 908655599
    0x901020909090714220c02070806090d0927150b070812060109030506060103020304080f0310030308070314270d03050601091401020d120e0d05040302090a060f1205010204 75
    0x18010042c2c00b400311a400360000c41e00b41074640320710004140c50503006124503000c44038124494004910610312401000501d40b495a000700d007800099800401144a004140180b4100105440503185081d8489401c4141d845400100355030b91280b80c0c109001d006070100305000007075000000307a1049100c1a003c15510f0f41524100c03500004810398030b80401140400c440800c02e54056007100c13007401d080c021545035640722559103400038030060415030088081801c00035418265080304041d40012612890100c4403018820241e110650019038a031010038490740c0a4400da040c0b4980d1030b03180c4116903982d1099619815428841c0e5003500c03030984030101e401c45040c0215401c9810656000c6414203003440010000d41c49034010645540703002c0821520350380c0004035680e0200d942e041c05c10882010340c4c1402d008280f070300a14441c50007080850403106900c10020310540f0700c00ca034401340b5902d91501c100103c03802e42c0500104008400024851002c1c424402e6000900c214009032425407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 908658093 1250 908656843 908656849
    0x11e061232091501300818040f0209010221040b04030b090d050f041e080714030624130e151501210207061811031603020603070809010209 61
    0x160500c0940c41c80040070080c480c0c01c00e014001070f20941e82c9256030500301d5060100e85181000040c800003e41c04440941030b10914802d50a025055007100300d151f2120108107011284800003182c0c60300c580e00d815001a034460700f62098840d001c1040e40200004107011040c0b03882e5901000c20f80d915010107020029000510340d0041001d14464154205103040c200681440e0040400c010b20a0250601ca051035182c02042981c04540d00c005207441d204108252014031000c803900203140500801d03001284090240d1035041c009041941110f00c15568000074001110600031281c00444d03101c0b007410b2040c902080c5100345c041c00e02030300282940403094024541207422186502c80c4a001081011410b981c0040c440000d0007800d11040494014120034458a0040365002c209940491420240324813a4051283d000c1403035000b240100c076504062200c040142d012920074031800c03c0625500c024240d42d0030840e1740c007500880c00c540320790300d0954040d00000d0510400e59400c0c01003e6180e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 908659343 1250 908658093 908658161
    0x3061b07020607021309020109172d07030318050604050a0311180a061a0715021305030a05031b0f03030109050402010c02211b060403080c12030f011e0612 68
    0x1940000018401b90648005800d06180d50b02c000c10403480c2c03a5880c0e090000c08144500c02d030040203000660a241c2200405200c00b03081c65012181c03180032170200403d6003120007016003200102521190581d1132040103d00d2096000f0360380c0160700034508000159054000001260380240304c03c0d410703004480340c4c10755030404883c11540c0d0b540b2171100700a055021000a03211111500350140b80140726200d2121b00440040d462420310b0303001070b450001d11342d10030b0003502078078008060f5100400d441c03c01560325045a13140440c2c8a80300b036141c05054500190031907840e003100d8041c60840e8070f0038501e24028080200268140410107210030010f0b51901d4084410b00b29803000c007403001c011201020301c0c0c030800c981c5c0d0900740b400c21805d0000958501c416201129400b0031501d640d061640029410840e100c0d2031142c107271601005102504030b07003410180c16182e2400d550500c01c0700780308086449018a103c1c01000c10600d1260310944045034000c501d08034071050310385c0c04040440d80b1815400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 908660593 1250 908659343 908659369
    0x50d08030618040f1407080709021201120209070309080f03190b010e030a150e2b141c060305030a11062a0a110d0e010e03061b0702060702 61
    0x40100108105030303803500d911000c0c8020320481d0304162500d0207a80e040c03c0614810405489003a0030b5400b00701e030740d408021b10001b600c2100240e4800d155200c4024029402a42982000000600000c107029901300b07800c903440380d0024040d84894445503c240c1c010010a00292070008041101c84400c080c400b005500400300c0c03c1c6061000340c2c000c856241200c050550709070401850020800c1e05a0b8002102d0f00260b4000c007890029180b40c84d0020010100c0c140c000c0c0c40c071b0080c540b116a0710254450040c180d031441200c00f040b4025001c1d4100c0b191103c210032241000d100b03200c202040b0615007650215000390010000d0016100d44401d440d6401c029200742c002030004154162004040c8600b5400400044880102000c403d030b441001001c5004241c2c0c0840c0003050080d131141c415a200700b1200c001d181a03c40c81450380350000e0540d01c1ca40b200303e0104a0010000340941000901d1038465500781d00a840c010b0301c00c1212001c66841355000b681e00c050705012190169582ca903001c142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 908661843 1250 908660593 908660603
    0x120d050a1103033912061306270207120309020102160e070509030a0204091515141219151a10200102040b0d060f060e0603040c0803074b0804050d 64
    0x80d04e00241002509400c03147c00b9440c66041c0901000307041c02e403440c40d400340c1d040d2184c110100040540941c00901401030040c06004404004041c029003652049030341c40c4c001c1e801c0ea084000086240182c904580c402c000f1a2840c0300c00180e015840780c4084c0c810035070002c0507100e903650107800103002c1e00d50408040c2e5202117045031801c0c080d070307543c400c1000c01030704035600d80b15462074803903110340840141000070f0250014500d040d030030420510041d00d0148440c088050000058142030b550740c00d1b0344036110502480e04031078002d480c50f844061246510f00808001130044865412503403003250f08850100031020308103100ba125400c0c0003600203803451003032441e29030044060340e6042d200160711401f54820007510034001c0e03503800b42e031004846030181c4551399a903d5910300f045200c00e466001079810300000c20004200080c2d12006140d404403841c1000480039a18413400340d031542c0e034104014080c15824041d45141038000000307039081c050340245040a1742c5a006c03607104041c9101c1110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 908663093 1250 908661843 908661877
    0x17031231050708010f110d02030c0c0712060507030e1b0301060819050c011112070524090106050f0d06051024090902030c0711120d050a11030339 64
    0x100f051400d1081400e0350750301d00c4c828071080428039000c041c075100d642c106180d201c0c1c00000180603038544078101c503509200d0a08440019541d10341200d20034071a5882150302130308080110310054405d0054921188096000d4225214007000c1145a41143c80c1211f03019500c8000000f54a0410701020441407c9a0f01d41c00461284c0d251082c2840f140007a000d044c44849000300044500004443d4000408150307009c0e950741071070601c6482c0407100000c4161410011040000c0d08201d2003016014401c020020301410f5210303c200b0a013014040101500300607154609004070301d141d040103030042d01c00d840c07050b41c1c1600c915480402d0100c00c8115180014640b0100800303543c4002d49400402c9003072401c40c118202000d058440f0312520102500080c8448682e000790340e10703011606191107014084030140900800c000d4403d4004403643c1000c145020540b005120f00807045034412180c0022105940b4885d10320800e840d120302c29100c11303040b030740640800903003540b0005041802030064480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 908664343 1250 908663093 908663099
    0x303030901060512030a27031b03020f030c03062214030901080c0c03190201142802030c09010c140303280b100f051210170312310507 59
    0x1204901c42006213800a6104210003608264004862012002209900d11043e000f80e000074007200400d81000c0d040964004019005402c80e0b0b030320320101d0707200380c03071100d111500314003010307281c01024202a405401220014601003008a00c140300385101550302d0400310705545a1401041d42c04424003c0da030b200181602e01c0c0d60b0000f041070390000e4500d44251500300c0d0300c221b090b1240500d1f5540b05126a40c0e103a4035950302e00030f400104401d40006800c070000d203840451011007180b010701803501100d0003c54500e00e010a030003101e214846a1040390302e804800001116001c190880030355050300540000041800c0c00c2c0000d60140c50090140080c0780c2050081003c0b40c4080008514030301c2c0303020704565050f2520400c41905d00c1c61403e0000c8400d41c18101034501d4407403c4c0040c904655070314104007086842404000c00e4549040803914062442d04011350349201c0c1c07201880311250307284001010f1030700701d1201d4010008400b4050180c039800c00151704200c603030000125965000312400b8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 908665593 1250 908664343 908664349
    0xe25120606050f09041218150903021302040506090622080a03170405060f101a040e0f13060f140a0c0201050903040f17070305070608040c0b07020f091503030309010605 74
    0x258000c3c20b0300300d0707031a00d20342000d40c0c406503040e640300158400d000d5021002c1140504004120004040180c00b00740c00b0480804c00030400c50040c0000c074800c03080c2103191005581d40e03109a4050382d8001d4012460b0417402c404029a80c2c1081c14000741030180420000c0600801c1c82c0502c4c0100510402060400300a18000d441c0d01c0180c1540c0d0600303038001c8d0801011400010f02a608404c03002010b5155884140350000c40c07692076040108840342c402c499040000c01d640080c412244883c50010044d1104050b0201c070350400d0700e081481040e02d5115a01142d1302c0d0780b0204001c400300c44001501a10a80c0f00324003241d04841d282a00c95850506043e12502802850b920a00b0200a5850213041010002602185005020b42c0c20b8514598803105801000203e0180d90454110307501d4542d90720009002c0c6404131011103c0c4446084001031580e4aa0305480200354020564034a4000380014020004002042d50700c200e0b03e9a42040541d481c11b100a5004505035000030540d18244418 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 908666843 1250 908665593 908665609
    0x6031505091603030c060e0d1815050a12061a0c010e0f1902030f0604050708160510080601030f0e160b13090b120d0201021308010e2512060605 63
    0x3151115030803501510101000382c14151064a5050a10482c114440c0c10098010b110707412401444d4891101043e50254020204540c41c12100c04550040c1d608c54821580082c0c22075104800f00310180880b401d00c500448074840041442d400c00145c0580e603491207413403290809001c40c030f03c10000a0f500e01044003030007a24030016603100181072070461000364554038031841c0c2c040d07a006000351a40e04115075041c0008940030b2414001c965103400c19003440c41e00c440307039407190340040d10650b00701002c1c00086105007011150020042c0c5948680610155000d4400503c0170b4100369072025a08074010092040080c40750f141c00003081d50748801d4482801d4008140c10a2604a00a0060858245c202e0b994031003178030414007012800e03c000002142907a0080466025a0300032445004c21321039055028200d8017048840303454046585142243c00c91703059016000c210340209648030480d01d0340c1480b4001e05288030007650142540d0b041c403811f007081c107074004070340ca00d864490400a40ca00034007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 908668093 1250 908666843 908666851
    0x412020f010c02090a110915130510020c040c11030a0c050c0d11040f020408030d0203060a0e2502100608031309020f03010608060402190e090108030f0a120f06031505 73
    0x20400b0010b1a2500050052903005200c65505904c410300000c0294210301500e00100c80030301000d0380030400c070040c030340503810201c07a10441102000000548d49031008048800c0c00e200d401804010043c04207100c090201c9a038580180000c0350300e860640d00c000c1004001c481d40c150b07500344030808146000303410122a691200d1040c0c1025611030041016008801c0d11418101c40000b02c6413a0703610104040d020b1a0b0100f4658040410248080719260b0000c41c03190504031503800c8070303c0e100c00d4140f040f00700540c2c0311514496030b001681c69003001c1107124604000315004031038000032501e0810041e0b805a1f04424804e42000ca00360b160700c3c0192841c0009012204400c0d41030565128102c8024001480342c07208011005000c1b9480e502e40c0d50495045500901c0a804410b41c3d460b005000305000c101d250740124400c1c00000b40841e00801999000b0303500c00c03503071890046200b9003101c0b0b40044000b0048116568801c000f00b03991a0311078140198440c1d0000600128042380d542c0031604020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 908669343 1250 908668093 908668097
    0xc06070b040804051507140f12090f04050103080d0f091208040c0521060c09150d1410051c050c0f0102150103052808030a050a0b030106060302032e290412020f01 71
    0x1250350510001081e411003448540c00c0b64ad40300d1104100181800302e00a03560b03900186030900110a108802004109848019000b8008101c030702c0d18400c1114503800c0081c0c4508041c02800c042103100d901c540b904280248080710b0b040b42c480000404108404a201007510344410380c401071500280103080c1d22480400b1381904007600c000204402851203150007000b0840000d0381d03104050142d10400c201400008482424584540480820001401024841c480041074184200e05c05038400c4601d0350300c00043c0c81c1c411801000d03c042011124111410350081400500061203a510410f00841c0580000c0c1030946940e40f842c0c00038213024180c80f420400c98459100442c0c01c1404a90f005230341103500044940d81e5145481c004d00507244c5141c0d15500f0b00c880003a850740e160300a9802001c1c514203580443e240320000c075000368007a04194010112000c400c02841014405440c50409079400040607105202e84410443d0310035003180f940c401540d152001981862800110651028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 908670593 1250 908669343 908669353
    0x30227070f030b010e0f040507120207050109060f0b0109030602130308030a050a0605060c0a08130305011514060c0a0f05010e0f06011401080106120b0103020c01021c05090c06070b04080405150714 86
    0x3950100e40300204110096014640368004509d80c240701d82c1881e8040c2d40940011500c2c1c054501e803041c0a40340d10002135402d203040c441001039601442c8100710344a401611940d10042c0b9568540010390080b22080c80100b0304214000042a50b110046224200b80d40d4001982c1c5000702600007214515003150340100320510841c490201d00141c010703103103a0031003225034070b038006102454194003d070b8000920550800c441341d884065a1105070054441c0c0c200309510400030701050151a006515455815a02c03001d03c20000c1000c0d00c940c55180342c001c01c00070a0540400d14200d2800c0318040505003254840c500400c190b01004951100480702440c0094180d49001001000400140c82900107030740d0f603100300e00d410f070702990450300d41c052101c0080d91900d008503224910036070031142240d071407401d10300042d039102c1c400f040244030100003e24940c18900346441340c8610b410001c000311840802000041001d0382d0713a0704210602e1031030b000d226555006500d810070101d490b00391410502d42c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 908671843 1250 908670593 908670617
    0x140103020d15060b0408100b0312090f0d06020f1b01050c0d0c020a20090105060f031b04030f0c21170f0409060609032a030227070f030b01 61
    0x121a1894507864001d09802407202040081c64014181c5600c42120071400040016860348049601307154a000c6400030048180d231345080c182c9624000da203c042401d41004040700c68a42160041400d803030140042008940ca0f0791030500703c0e0b00544100c0c5490701d0128520036035804a080e041501f408000c020701c150704140c204240c0b03134040c8100f05060f40341c0b51004001010f20801040c1603841d003029005030361050340d075000d1a0002c0d64540b098004c0329400000728030343c20031808590380e0720320b08802d10b8034590322a080307400646c003080301e0342070030860400000000c83d00c407d9132511100d0007151503100140ca04451a96080380c2124034028041040c120480450b181420845510144000503039441c0811030380c0007031520841d045044214a08040410066403041c40c100a991040c600f42020420071400700703415000001c4e4602c05601c03040d505100605000100c45040003030540d06079028031081c400c41034402c40844444000460710050311400c65031600484000d50313801c1c07e0031004881c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 908673093 1250 908671843 908671849
    0x2130b0d060209120a030f020d020303010308040b16060f0209090a1b080c090a081506060712030c030e1c1d01050301030605040203070e0c091f120902040f0f0f14010302 74
    0x11202a000d00081c2d40454001e0460b2a500c1c8200c030306000a40c01e0b0b6042c1a41d51401424641e11850008018455901004d000700c2c000401c51741a01d4003e07843d00c0c00c151900492064a5100b8014100030400c09840c030317000107000c0d005224280c10030140140c3c641912205224108500800d00343c0a41d042c8001d0000301d00700d07030904503042101031418800550fa01c504811841c03156249203030300b0082d007860000b00713940080740000000680344002c2089440d000104400c0340a90b0601910809030b00d0150000b080c000e904c1a403d1080908001c2a040c6200800790705040e12050723402c000060b064203c1c00080d82c040c500d030035003100d4202415200b005c00d000080507804140801011240e03240d01103400d5640c00c20441000342407190140381c0c0e9140130880f2041c1a04268007d41c0039800c1a14940c003800030482204100c41165505c250001000a00b454064282c0d44026038019540d00700d500100300d05030160140720706040102043d031034120340d038030070490300040310003003180c4041401400140c1e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 908674343 1250 908673093 908673109
    0xa50070e013b030d030b030d11120304140607020f0709050c04030c080d110c281e0503100203041a0411040f0504020319020906040c030e030c010902130b 67
    0x19428a0300c1070407450019200ca10400e910058154802d20441403191400c5a0941c60544088181c0036905400706500040d410366600d640c4039507045c1c0001c004410741030f11401070046200e04420407108400810414926198820740341a075809403240504600030100f002102d4200c00380e41f00a0840b220392039650f80d250480750061103845a1100086511840910305540285030400c1741082c0c02665004040d541e242070b11180c1e004a0700300031b00103440b4800491078a0102d18040d00c220002c69200e0f10b145603503014000c1800980b841072401082d24449682d9200ea4822075503e804201c80c240720406260040d881c1d03090f0001401001084009141015107500581c00e1011003000d5440d81e1400c840d502c0a00d0703071020313001450443c03030b07580480031b03908034a00460082d800c2d10f5110700180321740c2034040b004a10194000e400040440d4880c00d0a910201600585140009201c180480b89078110f600440c20750302e2aa450304603040a600d0320b0a043c400c0a14010f804100d58216107020516007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 908675593 1250 908674343 908674367
    0x10c050706050d0b0a090b010f0801050f0607150c030e070801020c03120403090e0c09130b01090b0c01020403021f110601080a0f060b0415150c03080a5007 68
    0xc101030300b0f400516008402c09001c028607105880340c4420802c0d0041190101960004203103200408089004034005410380f200501410300004550302401043c0d031000b1411140c100710150800030240b440d12681141111a0341d000c540000c010041e603180c14140d400bc0c1460b030340304200308074000d0000009c44148001020784104c081d81c035410f058508081d56800140613140f074204114403072440d20010040040b0440b203601400c0301e00c0108104560740c01785e0b0b490105a25001c24041060500042c08000319108005032400351280c0c00704070820203c071005540031500f1110600e04a420110003c13803281110024245580f501c0c000680e00d0261642c00740c0b1010222001c0320600c4815040003402650252080c0961244042801c3d10504980f0130205d1044d14101a160464881c0860100c5242c1569511000b9111121400d0003080b0a80d018902d6440c0b514000c40786541d007a00c510918011401d40a1096440300030740340301c149107208071300c2c0840c4c0c1c41c2c01007048040e08440540c8034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 908676843 1250 908675593 908675597
    0x11d1009050c03030d05070915051204080c100209280311190b03150901061d0315090a03020c0109050904060c030f0501080c011209020a0512031e0705010b010c050706 73
    0x1048441d090040c1842c1040c1051500350000280340703207480050760042c9000d43d810390b5415002c0e60707503800b40c030110031544405030700001c00030000c45804100d564401b07034000d030050200034584484480c550b1301c0c058035101c40081c15a008220311581e850b02903445036040c0501d09554440c000d5030013001c008103a00f400018480984d16413010000c1e00c03080a0761130b46042c0803503616801c507140c0492000942040b55500c41101010355440340c1e6080a030343c154122207064650300c0d001c8c1a409403120200c03031000d010a0300351152000b800020750313040d5a5207003d500c4200180541c5000c609000b030805903440481e9044c40002071007040310340c40b40741c2d250f5400303500541d00044601c10b40000724040d00300310164000c614100381c00401c1c008800b20f055480301200742c0350b50902c400403540d000213480e2a0b070400781d0310008840040003541414010402a600c800b002e0700d01d04620740e00c0318044600301c04a4038080110100d006c5080100912130065003101c2403c152078902c0c6142d6039540e036000180200d0301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 908678093 1250 908676843 908676851
    0x30f0e1b0f0904170f1318090519020103020c0a110a0b0306130f0219050a1205011a0c19060b130e062a03040f061d0a0201052b0b03011d10 61
    0x203008840419143e050f00c0d511480f130342c3c0b8886848035005542c201e0007121f526250403208201e1141c814481c0b019065404406061100a448135034140c841d40d6280c1681490340030407115030390760710912100d0800c1c2d120704038420646e0304030828007a501c2820b40000342906020824002e82d40d1b40c14103490345e0b1822403500491450402107120f000f070301444d2100321840c5038146040c0c42c1580c01c035010b0440400c0381c0e503442081c070803142c41031001c2d00e00a11840505034050a145455000318500070210100c0d0307103045030380c0d0120359149a10b09103540c031801c1c0c5060b80d50300c0320401a860038483c90b14904150320001d001ca0300c454494141ca88002414608102d034090780c122030445c0154020455070310444408a8032440c090604503010000032001322007980c5000511014502c0143c620181001e2480090941030200c0c1d0042d142c0364095600904d41010b4401a500500254003040c0c00070202400042540e00703000e0103150135540001c8035007210460099044542c44000146003002c1c40061001203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 908679343 1250 908678093 908678123
    0x5010f080f04230105191401150201110301080609070605040303021b150706140a0905100515060a0c110f061615090c032d03050901030f0e1b0f0904 65
    0x261103088a84a0f09048444003041c4078088040d480a03100b044241c46000f9618a210712040c01c403072401c03001081c01c244450051050071141e5000c1100003086000024a40e0100002c0c0025a00700b6440347d80598414010030115110a10071800201902d062490902e030940e580a515044040c451810f400d02102074100d09644003014029881d0242c900317503039501010300344007000c0c0414003106010703c0155408070f120304074035102d900c2030950440003901c070301d803d000340d0340000e070001800402e02031980120182c00c5598200c000c066210560b142c01e180c8060520709031030941c402481003407280c401c1007081d9070b007919503008840c48801022541013400c032952421061220034031100145070303880d0408040400641011080c1924007e540d00f00c2014102e801000c03480541c5c20704401c0b807803d041d1070100064041c03400f42c240c0040c1410702003100203070542107204650f5101d20501650340460080d140c4600030b591020b01100040d1070100f03c1e05a05408140c404401034002000403034100c0c580 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 908680593 1250 908679343 908679353
    0x1030504020a05090a1d0606090f0c0909130317011802070c0312180b0f07020418020d080a0f0804020604121e050313090e1e1006090606080105010f080f04 68
    0x30b0b001900d802864082e5a00f8031003035500080c403192107070b131815407014814805000b0300061503910038500100203c8003503698002044401501404d40806007009008902190b5603160b819442a00c0c02c100c00001c20380c072828010480380000414081c0c0a03488801400401513400d5240803c603650030300980e40e10020b1401084281c0c0c0781d4406800b0541c18003981800c15803001441500030001c25103c007906442d8218080c0d24850080d151900b030400304110070040c2041d07004a040080031041c858882c20858000c00d964190085044031400b40003e060001241c020300a100150101c0c82d1034691403070b02ea40401d0991050340183c500301003800303003a0b40410030b40c4200e0280090044e401180403c40038505142e80b0b801c107a600c140140340c0d450004c5070800c020710580311024200001400350031503498454610a1045031180400e00a580300f207000719040b8014a4003c01c1130000003e5900d140c145d00404001c010703080b4504100740321407803850750b541c0543c81980007503260515000f81d848a02e80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 908681843 1250 908680593 908680609
    0x8091c050418020a0f020d020a020f0f03101d01092f030d0201020d0b0f06180f041127060a0e010903020a06031b11190206211005100e0103050402 64
    0x31220070050340090208854610b900a080024020b840e01710244280d20070603a1644407400c0076000690200003282d02600d005002511500c00240080446c0403030140402d04000a8403221000316840c0c0101101d0f410720082d60081c4413125600030411401240d44244800b8884114901400000445980c424082c000046d0300d80c44028200c0f140c80e0f00c5c0b82000f034081d4000403110071a0038030303124000520b401c1c094110b0054050040c00703149000207008190050020b03809016400055005248106071141c1c803450b0014804188401d4a482250b624082c0741044061111105190107003401040c0d01d0721025202e100030035081c0502100d0000004860ba1000759101a610514400e0b0008101d80c042c0c2c0000ca900d17143c40a880003500042d1410303200c00310314142940103527000c05511405940603100754a02c95200600442c038158bd50002401031401101c19080640712500c03d000100300e0001850340103203815200c01c0b03a00c03008904082d000080c1c03034000c681850b485000207004c5540d1020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 908683093 1250 908681843 908681849
    0x21801121526070b09010f2c030c0d020f12150709062d0f09030204060b03062107381911060106030c17010605070201080708091c0504 59
    0x248800c6202c0d59001c10061100c0a040440c5000900b4501c4051101000c80c4038001c2d030f24040c40c0c00d460020010011982200c00c005400c080100030031111102c101740a00c044136000444643c4c94000542c17504060800c203000904030b201d06214003049005849011000038800400c40f408005041481c131613506107040d0507020604040d648013000500358000710400b0076551070b0754600011800303010102c0d81d440300014031201481e9030042e1141d02030b0301c9032080800302506c40c58096501030b5a9408902507070301907003000704e00c2c0c8408020400f550070604802000c2540034800c00480e440346007056500c035115406402003203c5070b010b507031400c814100305152050482e003003480c9200f200310100000d2504071107480350104454449110201c1e118140d240085161840a0007259107880d409900030b05c0c0e000600018884030f07178840422405114441c900901c000c0d140d040d03031501548001044044c0040ca00000d10002900f405090080010002c4403840c121140c20b011180d02d110690309030050764 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 908684343 1250 908683093 908683121
    0x20606211906090308070f021213090e1e0a030801180b09150f0d03051909030212010c09050105160b090c0a140f010801060215060d021003140105030102180112 70
    0x7280704000c204081c0d00c2a18580c0c0241e07604000341e10744000c1102e01c4040743c188040180d0100c0d0b214599000d04d40001e008043c405008161540d45d100c4440c82a90300d406110f106e55041032100300c1c0b41e03c503c0f040f01018003a0f0180507010003580d641d8003034a0f25006001d20080c0505c0244c40210303903c102c3d40b2001078454000c1c200002407034214600341c1c40c0890715801500800d0880e40821050030328044d404c000e81e40c1030f102c05091901d803207255a2080c3d04a641c2c0000c200034450000096180e280d0000380c24089134001190104003100003400c41605644038030f04000f02080100900c110a410398100b46a000707203426001d4079a400003500d4412056030b0503506c90281e050006107080d10784d013000b031200c1090b03405018580c2020010340340008240b0800700541c22031103844950703410300904540c0c0614010000940b0311303001d40125541e07208580300d800201c0d42d910820960506400a16130040c101200207510341413440c0c00c50541c0c180c503564a9130510104002d403441034201500101c094200103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 908685593 1250 908684343 908684383
    0x9090203011404060801200717070c06140307090b13050a0b0d051b0306090417120f09010608030d0b010923010f020c0a0e0c070507080f0c0102060621 66
    0x72501c0700c080e6211030402e2807280e071521030001160041070154810f20b101d918803601518160200301036651b4007200c000c03203d080c0103208800320719444001a010b964003400c030600d01a42000400f416072411a1002c015954080c02000111039224a050094078211171078103803034055010780414489419005a548001100340100b69032180c90b01804c0c48a400443c14002d58032040580880020301c6002c8410704c12040000030207504000705030a81092162014426240141c1c084030800d8000d400703102e088500c40001d01c407000b41202240e5400000400080003914544480c0b26900d208030305070086903d460704d845603d540e01400301e140092000c00c450320603c2c030940c6400c84482180d07020080c04119034035a41200a0b06c0003030101030b5100d0140039a042c0a0070902880907881c0024107503980540304001140000348140300d20401441d42a00030300b6082c4505100d90f09001c504072380f41d0704540c0140100105955405800403035103030807000008940c404032025500301028803029070642985 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 908686843 1250 908685593 908685599
    0x10030228060e240702060a12020a030c1e08071805060705060108070f1203120e030a030b150a0206150a0b19080606041d1009150503151b07030909020301 67
    0x386a000e103600725050440f5145000011810304030b44003a00089070300c00d208000c0107060030b400424075511181026104007a805040100340e078400143c83c070001c0c2d00c0d0451208000d410034003841c01014031140f841c146c07040b60200181000c01c000e2003002085440320000b803070340100340c80f41e0002d088007900c0903543d0209401d00b5030355858207214030f8680c0d110f000800180d42207125202c8056402c500041d000c400640c0c0c40846149607a840007048903a5901d0085111188c100700901c00c4c0c80181c1c070302040400e03c420030090410b1101c586c00591010402180390402e034003040d441d6000d4440950244200305030000300c1c0c9041d11540080c075a0303a90000c3e0280f44080711040420780110281d4420803655175200c18050b190107544256a110103407080481e195207041c82c0c2040d80400c422100a290664400c01c3c003041d1074003541440c02c20b681c0c40030305000d10300741400400b20f001282407001d81581010030342074000d0b244000541020b400b02248582c00c1503c00c0503604000c007a000401d41d20b95031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 908688093 1250 908686843 908686847
    0x3191b090e06070e0d06050c0f18040b01020105070909090507051203190203070f081b0709060501080a050103120f120c05030108010b090705090d050703020a060509030607081003022806 81
    0x700104044092152200090403d88540550000440050004032194420b03955903030103000041c000781c091038801d00c8101e900381d0140e4050442c1c000c6c07400404070401c4051090004503a01c0c04d50007030440e4140b800b080200c9401454080860303004000000b101c88180c10240d00f850285c0c1c001c0f65000c200301e9502c004c1140008050100e007004c000c004820760f000b461050344d903403243c0b82c401090f40240c980a400800c003810040d1201140e840061002c031810007007070504081260700281c1ca155580c0c5001d010319684031000790380c0710111050801031541161540260340d21070210510402001c2c05208050351312414505200721070034181480b01d450612005019908240200c00b00c0e9031070103850080c18900001080d020348560f4503080c2ca401207010601581c11025a0143d4042c86560780010041e01c8101075000144556555183c40303800e210101070030328002900240070415075005200d1075044000904c402c403035045a500440152100074001c51002c1d400303a00500364420350000903195 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 908689343 1250 908688093 908688101
    0x608011202010c150203010501140405150a02030c160911120402100507050709093003020f13120b100305060109091e0b06030723040e0307051009051b03191b09 70
    0x148c00340c0700c0f0321404501c00c09010903401a4804c0c1544006a014686204a8088000c140480d00c51069a00c0c09000316103607441c2a010300101c000e104000d82042114000b50b102c0e064241100c000f0703071440c0c10407080200c0e8403944086d1000c1d1042d01045604004103010740100c45000341d000c0c0a0310050350781c948a6000414a80340181e405030b452058201e260b5490192908c1c04004403003a401030480d0b03440c0b085000b900001c2c0800310319101003140800a00c25004480002d2024030312042c03407400c551900740e4822001815105068402c2c03041480085c201240050546522000014888503982451480910b8000001e0b424031a443e0040060100d4000060304c5140c081e0119400141d45046150541c01d04035032080c0440304904414000e890f1680040c5010750040080b64102001c60b103030542802a0101d44045082d5140d054008200c003d01241402d03400d4044000c1820b45d071a00403076101c0c480007413046140250f0306001c1003000942c0d50b6070f1405d8844010410036441d01e4040290080c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 908690593 1250 908689343 908689349
    0x1209060a1b0c061704150b03190813050402130b1303061404050615101808120d1b050d02280e0103151401050a0e03030319050702070608011202010c15020301 69
    0x4044030400301050560721101c50203586e0020441c40000030050010000b4000100301d150b00d030003550032011501d50840d2101c20501d01aa00c01c035540c40c540d00c5041104041640014003480c010301225a0101d600d0325200212100c00d4121030b544c1c8031410007520405141d802c000c246500e001c1301d5003c581001c03848203100741c0c480c804175003d544506101d55601c17250ba140c11a4810381e080c4180d011184a1404c2d2061824002c0b240312015031220056404d140040d4440d140c27092001c0b40230240d0b0910341c010030620300e10340c1f14105100d4014280c002c1c95407044900302c0e88015000033f155603400030107022172074a007128503240300c400d841d940030028240c5045107c0c1d1400079003084264030450395a950000100e903203108440b0303003400301140155005d030400b4402c4c0741400810764085030103807020700c01544104605c1c00803c071404019100032003202c0300a0a4401154800d19051002c9a080303000d490550340b081038480807c40c2c127440102c401f4001114014140801441681d400500c01e40285043e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 908691843 1250 908690593 908690597
    0x70e030a1a0a0b0a090914030a080906070507120c0f240b15070201030507120c090e090d08010303271403010501080d0f0f030b060c07030506091209060a1b0c06 70
    0x107951140100c040039a41c000710126802050498100249400ca40c0300a0f0450f11401c0840b4402002d01c42450564001d02403001c08107880d9070421012035014409160b0101c66030405508080084d00ea040454600054004c01c0c80039018a4405224511035828810b561210140494070003c0000c1c2200f03840c030a0040d181103041c4215140540351000c02d04800910404400d07090803025001140070f401c01400030000e01c03c00c514030b041700401c20300490b078041446807250315070145400b0314101d500200808030001e40e080061100201c56102c420141101d030035180a44d402c45074cc0d00c0d048200d000700340c50b0400809141400180d4100c4002c0d120502e10400c0f0000c0000b40ea88030442502c070b0310b581c12010002030780780d007003220b03024010110f2003601005441c001514508140104000d5441004200e080364440c8034108104801002402d0b840107100026003c1c0d06400804821503008001c403291113988042130003101d181c880d16030781089001040c8201001e40041c14041c1070340e2094060080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 908693093 1250 908691843 908691893
    0x509241810020316060209040603020603091f0b01020c100306090e10060602070303081807090509010218041a01050c030903061f120c03020f0310020a05041707031a070e030a 76
    0x7024500210a4505048201001400c1903c40d0b5035428025400314070743c01d40c0710b0347d0341001101685458010b18440c00c1d10500611301d0420441501c0b41c01c48004000250340341c14a81c804103241da0109508400386401e03038a070107110881e56000d1b40030b001281c200c001c601c0d04c0d1010540d2100c1c0000703980d1840700c100150400c5605e45030070040742c40d0072503408080d010951003800301c0d81e0502d104c002c00402001d08000e483c01d254403040c002c4103540c0f041d82c040b08180e4000c0354442c50080c402d0040940c0c020708603010848000b00c0355181445e1840c06ca0001d040c0040400c40b40b51500b0203100311850b1060040588401d85403019a0740841c980c001601c64038502c03040000704100c00300911210710030380c00c0480414020300d15820800c880c240039a01d150117000302c15001d4006079090003d001c0150054403042d440701c0c03d003048402a421a00001502c4d9804141c08002003410300b11000c80851010f44030400b01d030303a0160141d40b000c1c0b840c40c0070b541500c00c4c01280c0d4240403003071020414034501c40007400313 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 908694343 1250 908693093 908693119
    0x10e060301060203040b0705190804091404030e0607020d17120a0606050d0b0409052a011b0305160b2d1605030601020c09040506010e130305092418 65
    0x48a80002d00982e000350f030040105010710100d10001e0005a403055046401d4401c0d05150b030034403080c2000d411070f04410041014442c511150140680002910b4480d076000d15181e00c0007004078400c1040ea030700402000400009549801c83e03084100d942001c0c3c1c0551001420244100c2644203a04111700c11481d400800d00300c690501070340088600b13a07541d00342440403011100700180106017040e0762203a501c41180c0005035042c01141102212902c2c032903107031103c0c0301c40c1040898218040e14100007000b00140c8240f0010607903010100c1e01894032035107615038000c91590304d09840d000900000c481401f000701e030103010b50000100000e00403141e181e032035982d00c0c010652201640c0c2180710310400454500090310607009075610040520488100700c3d8403601141c4401007d441c10303505a00400018080200c94544107500034040001c0c480384003001e910028424010000070b68842c140401842d070303003040c007140c0429075541e06402e1f05950354085004c44005881da080907a001d40d07582c817404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 908695593 1250 908694343 908694349
    0x30f0d0305060d11130f0507180603140a1a12060702010b010c0803130602090d110307080a030c080901020717011a271f060503072715030906020a0905010e 68
    0x181001980c031090710321480030114100a2601703100d04511100c0780c0d039907034070080e00412800344500810382c5031240c0020064802c800038141e0055004a000d05007000c4a80140f40e034505401644104031900c0055001c0d0401041c010740c6a100401c26489a1000c02646803a1400b1510a01850540d0020001d0029940040d00d00e0507031554007811082e03007030002480507881e11500b00074003481040010314069007000090036043c0711303010070750352420301000c401e0300c6090030070904000c0e0404400422a48800fa03800820410b5008001454041c0100e95801b20b44d008000b080060480700080e017065246441442d1f0007800070501a1604a03111030701c040050508500b1a4174400c8078001c43d104818504029503800300780545014aa40c90800d0411801d00c000300c0c4c414081c0c411a601c60b40c3c0da080c000402400f0141c165541e60801c20024403000c1030200b000c440340e04a80c400c0c442c130b034054145814284c0c000c24042802900941c000104079001d1644034400740c0548034241c07604100c10401000b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 908696843 1250 908695593 908695609
    0xf030608010b09130f02030718050c120c1c1406040c0309030f03020711090117060f070f0c08070c030c05010f03022521020304060e04020903070320030f0d030506 71
    0x724a410644441c00714021228413200c40030a04c0c042c581211070703e0f5481c0c0c04680742200300d52000511000d5084400007221083c007a075900451650540360030700300240c0c000c600c00100949003c4208100090030303070150504644840c06921407040c00c00411803e012802801101190b01901c0307180342c88000030302c580c0030384603212441d41c140e51003804003e5035040c213800030350003034809440000b25809024400d80e100707480507010b40902e098030344500461590680c5480700c0604012444c8041408201c80c0d180e12041e1600320071400c1c50800c90080081c1000b420f40c0c07041c0c8101910611a1110101c01c2c0000c003025001100c03002e0780c070100c2e020046c0f00120300701d00540b0081058821188d50b0a080c4209501e41900e02c18003807803440b880350a0000310142e48404501d150f02c0036810105040114680103000b515610744140d9056142840310340002c0d4882c125404001d040100701540d000152014410400c11001c01408643c0c000c4143c0c940d10759916408426540041d09290000c0e00781d00344261 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 908698093 1250 908696843 908696861
    0x24091e030e060d090503040314190f0f2f0f040c09030f0c1e030605060105090d12020f0d0309110a08121c05150315070512060d02040c0f03060801 64
    0x901ca900780d4500300d080280a5200d03004a00000c0e03210313007030303a004144140020b00c000c0d4440c5540e10101c2d0724181c449070600c1e002e07100e5801c07055049009200482d04001015803038030380c41010715011000350303d000e00d01c01e5501c40865404103801801c95030720f00848800c010f1f00c0f0404440001c20200000200070556881100c3c140c0000c807841010000201c20b40308800050303200b850303444041d54442c50030840b00300d81c1c0121283c40081194040080c0509071142d150407940a280c554a440001804074100c0311140c000180107011050396046540c0c400d0084d481d6a050303841c1274a52080258100030050181400262222410f0305465109454800d402d202105c0c2408060700160180c5c1d0405441038102f82c5c00d100c6500c000303090801c601c1090f03103da01c0c4514100320308003c40d0300a0701c1c00d0519021341010a5158504a0360521213440e81100c01e4448032402002030310f2050341c414000c034684800291000b901705042a0300080382c43e81141d5502404042a40c1c10048203658074001400c4c3c500c0c0741 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 908699343 1250 908698093 908698097
    0xd0507020409080717040e1e0402100e0613030506060418261c0b04050621070914160203040b070305090414070201020a0314060906090424091e03 64
    0x2200060601d0381007512054051410581804c0c03450704d44d11004043c60151020440000605000501020b81140e8106104c0b8001c2c070580c00316904400c403034034009440a840380c800941c100004500c21b407242201c0080c05011240c03030780001d1002591282003030108980074081e0500040481c14144203501200071078808110002000351549a40300b0b4103e00d001071000c80d10580084040c12500c020300092051030501000d038002000c0d4032003155003440703060307104900342070078000e459841165680d09a1007a005a01031202000d50440c6064610f5200901c4641019014903080b00004802c030b10400801c040020b8015480d001240c480c800c5004011580c103041c04902c5c04a8440d80c01f5008200c40608001002038900e10000790344281140c00704010707900018510030301d517850b014201441c0010380032203801e41041400a401c42c02c0040c8102c3c0280d90060000c1e0038050300c088040d121540300c80e0701da03040e020860844409001665015102c0c400401e6a10084a28140342800842c0e019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 908700593 1250 908699343 908699347
    0x5010f050919020a0b0f040e010303021c021b0906040906051501020f030703050706051504150312031a09090307141b060c10052a180303090a0902090109030b190e0d05 73
    0xb096100d041c0b034010382490031b00444103010100b0315410101c9038501841c02a0000c2003501042890606003030900000f19085401140208075560221850f103840c1c650110f0f440c1602c1c1c2c0d51080450018815140040c00c998100303001d121b034000d400006844510002c0c0d00751080303884d0311007402d941c900c03410100900040307040060f2004115075601113504807c09004240d40468000300217010b4130301c01429032410581950041080218080d4500c60100540c1418000000072840503c100814400802e000700e0140700000c0e80381005100701d41c041540002000705611040c5002e0303070380b40c03a203001102038030700551710118031480c12138195103140220400500503807040c0b21900024010181044034a50340380c109858040b400d101e400c85210a030203074401e481e10b00003260074079003410106015000c1d030401c20480c00c882c0c48882c244003d0340c030681005643d4454403401201c94417150343c40604142da03032205025803204010280c0c025504602c81c01d01c500d075141c85696480c0c0700c200000601055003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 908701843 1250 908700593 908700599
    0xf0c0e04061403190f020607060c080105030c0d0b0a020d06030b0a0b011701060c0c03061b031107030903031404090906050a0f0e06060f01030608100e0f01231305010f050919020a 78
    0x10302440d03400d0384d101e07032017602e01c442e059408104607401040c021035210352101c00b142e074025446050703d80140822002080496050301c00700b0070085001e44050036100d442c5000440d00d401640407100c455258480401c14070780c0ea424100c2c0070103130995a101d8118146220204150320034142801e20710b0b200c41c01242d043c0d04c1d112040c1c4001000c2c4008681b03008102800201080d8180710380310311005201d02d4101c908125250040444420001d038030300c600014010700700802d500402840680390f01d410805c08151542c0116402070040d644048405820407404c04108441500085d0003220508401d101d100400f003020810380b003040150441961002c0006080e502d421900c02c0d90000d010b041c0061400d450f015210b0500c0c0c1da0304108211035807a02469402c46c80108070640130328251400070040e00d40c0038000315400c0c0c00101c1007100b075030300c01d80b000c07540c020400c0302617200c100e88c00802002907081000520003d024200c41c140c0290040c20181d5558240317030780a41a00c254020500400642 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 908703093 1250 908701843 908701873
    0x2030406080c0d0e010f050a14040807030809030f1908130b07030c0c0609050d0f081e100503030a0c030908030a021005101a1909060c02040e010f0c0e04061403 70
    0x1285441820f11500c130801084021020311401c0d201c00701d08400410726241054894007039a800811152107083e032003042001041240091760845541071400f0122500c9480d0400d2550240d01c105c0c0001d0303480028021103030300b00600382d800c0b528080e88842440f07568111004d1080030015101074034041c01800021000b0340329912100400b80c89040000412405854844c102c0341040d004451950010b808000010b8104424110040161902c285145040c20140072406ca0180615a0518803240850390900e50301d02c04a0141c1000380880791034940c00d0a0050120303412020030b0300401d403150800310b12110003004a5165400c560001d240a0034900e884034000c120041c0006507042e60901c0c04104030b6446000301c810780004428064590140c044512030070301084070135a007407220844007000100e4004600303c140039012640001c40e15500e002150140004241d0400c41a04d00302018025a8200c5007a13805010142c0701005829110780250b081441c1c1301c1400c0398154840b01081030184 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 908704343 1250 908703093 908703097
    0x21c090201170a0f1d0601090b21100203340e09150301050405030711030a020906060307202103010b04050607050f030406270506190504051e1002030406080c 69
    0x45240000500681290613200464081041850118001480311901d0440402445004d005620b204000c88042e00c000221500b010502000800b4509010700800040034010000715480c103070380c15943c070701c0d004036581d6000807401c00d10071401910301e110030040d00c007413401c045503910140c950030080e156680420811a000a040c40700e1031844040c030210b2508c081c0526802644a0001941c442125140c10100401103021441c041c3c1c3c00b144054026035944a6502d80000050320f82c2a0783e501e400b4001c40c1c0381036410300d0078003185030000100c1c000b4003000074840f880d40200d0300a011810142000040443c4820311910b0003640083c00700f4012450701e840100706940c414401c44c1e030248031074810281140c2003a8850030204801e20a00d0389802d9042c02030b0800e0b072444844012100d0b04000c0040c1840c05003400415192400c1c1c61a018524018408c0300e0140600500c085c12900380f4040c103040c503000c002840303030103008408800c4070710b9400001620107640180d2101ca196036900b1106402a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 908705593 1250 908704343 908704351
    0x10504142a090303040b030907060c05070b160501090302070807050429031c050711040e06220b0103050d021213091802060706060f05150306060901030e10021c09020117 74
    0x80d071003002981402d5904200810082110445250310b9140550019007007840660161003408001101e02c000a000441d40c070080d94014805151150b070000c0b8501c401007134a4100400540c0391040000a040d0000b4410341150901000c036080307680c4035000d002c241c90128503607008859085144840200110286ca520759501030102c40e1011316a85052960403141c0c140180800e50004120051040c0c08000598481054409020710346082940c90b656007001800c140314481a01c01d032907022100207000c54082600107168030840c4d6120300b4040e440e113020341046409031203203004540403440c1c1e0000340d480c00100c1904a55425180103071280161940200400780940c1c01c0c5100c20042e80e0f50005040128040d900010302c03641001d0020031f8000568011501c146c04060030b4800481e00310044a41c040c506440044d107604000c40160090002d21038000c60346e010304101d10910b802540c0c0580400d0f0440c526201c080d100c00c8607030303800315950308001070b00094902c400000a20306003030000c0c0e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 908706843 1250 908705593 908705671
    0x15100309150b030a20041503030e040b0a0b0a050d050601090509040308070207180e162105011812090608061008090f1903030f02030c220503030a03020301050414 71
    0x12442650707482100001005072a00281d80c1c5401a001050410344521f0815804d1121055409401c50b100500b107032050a208a204075220482e94481d5116596140020100c01c043c8030b071117034141e002c041c1845c0c201d005020760b220300d0600083c00c00d6105481d01021100080c080b0607658aa03920121821100240005c0c2941301d03a80d40041c40181400a0404040c03d00300002402c2107a010150300f4801c00d04124104c074011044180b05414010103a41d00da0002e80140d024017549a04d0060301425a00c040c00b01c0c0c40140e103500e04113001c1c8080d8490020a125a292280140c44600a4a15000580300349411034005010101c0d07250103580320701c0d00b00c040c030b0b41100c1103c090501014500000d42c0c690301408c03013900c0001c100f05509401908503102d080641541985050b050028090080740b2111204c460788041c1e040c03510b282031840101030324006c0e054036610351a50317038080d020754402e11501340038918124840030700c981c19800c0203006941c034580811983d20742410f40707400301103c0c81d42048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 908708093 1250 908706843 908706853
    0x2060d27020a0b030a18031115070206070f11100b19030b0106050a0c0b01030302031b01020306300d0816020d210b0a090f060b070309050919020315100309150b03 71
    0x41b8001c01d90288010a43c825552000ca107a2115071031800d01e40000215142c0e600103900b07001d64650003040b080d03808070280c90811181040c0007800c0f210a6034841315a4014061807000c1c29503154030b0780100410b03001c20398058014880714452107603400aa07110107405000039000620000c0d01c60340042c811040c0f2464180d028200303e413160226550282c2c02100940d10020f4000ba6220340f42e980f200005881100850461528102180080404400c448181606181210500303450720a141501d1000d4600f04d540e4000290405088100700f5603440325040c0d020000c0c40c4040d880013440040031041d91b070300e8107486c0004000200d4250300c104a4419401d440c1c601224058032040c54603002813100c1d480100710000e8800c0c800d0212240340d08074205201c0300f0402c2c0d00120380c10101c600120344055401e40060340d101d100e088617412543c80b003d140075000105101001452405000741124202d58034100720b030f00c400e01501100d0301914011700347d210001c418600041e49910020200c00c001e01a90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 908709343 1250 908708093 908708111
    0x507030c060513020603070908100c140d150801020901090e0919020619021513120513240f091a0f040e04050d081506040b0904060302060d27020a0b030a 67
    0x5000d0740c000719080d00002300050020440400100600042848228400c000722450740c01c3c001c01c800c0a80c121403040e0800001c0002d0341ca26960701400c016885c100160511584030102c0d64080c3d4407420009000804160002c0340d003000104600f40120340f0b00e40100000c1c06031410b481070080c40c0380ca099900180611228000d10082d001e181030341071095018001c0304030b40d00e070303051820040540301c81c81000301008140005100c81c1000c0301c00400b103081090320341729604100a0102c01c190008a08055a250705a4880c0a090030381a20714036580c81700309105035004012185550b0501c10406040520310f501c091180c1888024200501c03140c2c0d03094941600d6444001c0013030002d030380c1142c0c03503805001210102507000301900d801440150a0b45c10350040d5000040b20781c001d0340104100c080d00000c0c140900d0780c559001600840c0e0182416850307804058181c4018003544400130192603001c007419459030158107031040e120f5402029601340c542000c0d02d00c0d1054200400c80e10081c1e9a42c4020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 908710593 1250 908709343 908709349
    0x1701051519351c1110060f05120c01080a02161a010e07050705100e1507081512070308070c0f090f0b030102120406051b0d0b030c010507030c06051302 66
    0x504866003098a00300000003080c1d00070000494103141080c0302e5008180d911042c050300c085031011424581c500f00034689000444142403411514402980d07518014000400f10f1126000c0012540211480c0c4540d90390b25480a4480100c075980c1030000d40c180002402411199015140d10300c4152a124004102943c56640e10003c82c2c00d00820560b82c40010841c0341d681d540e240764810560b00c2e00c2400c0c02c0382d550f501651002041d030060029034454958200540f802c02c80d071714040348140b1860500303080c02d15014160300e1050300c02240c18600f07080c0980c19801c0034202aa0000c0ca03160050034504d2554840e220b054214000886210704c01c1e14000652030301115201014080040f00080c5148003002020111b8070b21540031030081c0d0040c0000ca108450610545921a0700305c040440e084c0d07030f041101c80c0d40f41e07403045003143d401c4404030300c01504046a500c403e00150064003110b969034505801910302d40140000100090340407511440003600c990003071030700030041581000d00c2c450310f9400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 908711843 1250 908710593 908710619
    0x40f1404031b06050c13050d0c0501050d09051009030f02150412090e19050105040b0916200f0607140f0901031d0303040507050105090a050f0d0803010f1701051519 72
    0x280940f0404082031b48403050904046c1a0003c06c811560040054170b680c3e1441443c520341c3c81403506210001c9040449031400b0b8000341c01096104040d1015000710110950003001c003640c050740052003039a60300300300c1400029581ea0000103042518907550b181d5a58121144c0012143d400b0010810800107800e40000e01c46030041041444a2aa984d46c0151003411144160b110520441c10421018115218103d181e0f4109070000c9070150002002c02055600b54080b100c6028803c500100c50b070b50140c800302d60382205601070410380307a891300e441100710b40060310450380c104441400c100c444000b40b0300034002e105c40907040c100030512aa0f0074008007400c00e405001d40b00c0e10340000080008020060242e0800ba00d800d00300282440101c5020808903901401960f018207040462a07800342d032042d00c0b003400342e41d025600c84d03665030f1a10310b11051b0b05414422120040b101c510744003045401802824071440c1d03c180080410f481d0b4104101610502610703c103000000001e0200b00c013201c2e460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 908713093 1250 908711843 908711851
    0x3180303040e070207090e1204060e1f05130b090102030924070803340e04090b040609031d010c030c02010516030f090603060b0702060304021815040f1404031b0605 72
    0x41e0600030706c0e04100509403800c00e4000045504004940c0c0400e680701c0c1d0541d01690f01d145816250380d007502002c29959800341d05908001700007515500b103580d0f03025000b003c43c00120800c40f40f109986141e1112907020b500b000744d000d40c10520818a681c00d00e4006290b041d840e0030316040315605001450100f0f5032050009450014002080140a541e200c01412050100c0c0c803048900201c8882e10080000007200313032004001e845818901aa9650b03000203201541104e11008107003080c0c50907000030800001d040700490b240c0e0005807201800125031081803101038541100030139099074100c402803e0903008a040c428280b012040d07a011454a80d00101d120751260528550104006030070302c2c64940c4080101401c0c40418040110101d094449940c3d055440341d850382c840740f0000d58020446000d121030b402030042001940d10306100304079201d58060306c0411984030700e07400e07440c1031b03411950280620402a102240000c0d110701c3e4400000100c4240c2940802180d40e111000d54900755 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 908714343 1250 908713093 908713097
    0x3040812070203210906010501180503011e0c0804031b082106040b2d0a181e0b0d0b04050f0d08010e010f0e0703020f0f0703051b010e03180303040e07 66
    0x10a500200080e040e071900145104d054048849290450400b0395031841401024108058880041080c00e1031104075000303040c00070000c0c454812280342c46020701e19180110000d003070824071400b02c01c030b000c1e83c00207000720303015a125171118a001200100441d000c050440316000c00700100d4000240c110203d071a03018031064041c9082c00c0050811007610300c40a880340c4286809040d0b007030348040a803d414407001806403000d140c072880c0f40c0000c484141c2544000341c01c540b400350310041e0300500e038010b141360403040d0f41154140803540e4424080b10288404141c100c5402945400407454039007049903c54440c004031020000d40700c1241d41854007214140c40825500da005110500200805501401003c54210b187d980381201c85610840050300328424140c4c0001c0c16102d203488441114900001d000e96180e5810580c42c00528551011152000b151500391031400b20603418050502c05c43e000c42d00850a04d070b40d659500100c6155280c0e141e501d44802c00000800419031403105114820035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 908715593 1250 908714343 908714347
    0x618020a0e040209060102071409061818010606030c0c020111010609150f050d120f12110c0d030b01050405150903060106021c0201051e131a070e0a03020604030803040812070203 78
    0x43c070500c03644800113031165040d5082180c040c8034010303146000c216614400c680e000c9007900c800003c1869070307468440c48503200d051141081004c400c80c40000d03000c116514020000c4030303039920302142180c0c01060b1403c00140034480c3d00c009580310301c03260200e00f182200001007e607514070300c10f070440d008040d10600b20b40c3c030110304020242c10284114010034054544200101c000c1d9901650020106601350911142112828210b84242003240b03140c029580100500f40040d1001c0303507150841044004903100340f0440c00c90051090182209401c0c06869140c1000e00b40320030407080015600d0108044442407200411907602048018002d02e200c1c0c0140c0803141503081d694402e10040d02c030b04825603040000b480b0014103680d0a0b0039110000c40c111801030b80b640c00690400380b100040242645544002d20126100b8040701d160140841d03494800c6543c417000103000c1d0240003440b001c1c2d4005c1e001e00c002c20128082e14000c56016110f02c0c4054034003540040c41ca40143c100703558010050b400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 908716843 1250 908715593 908715601
    0x103060b030708070e040b0709030b0906010905070f2c041103070e01090b040b0d020f03150a1e05060702030c030709091a011401120209030a1109010902030705070618020a0e 76
    0x707202c8800a042580d01400302c1c2420104501701104010344010000b0101c130000441003807146900c1c05c00740d0b038061071405a0b411302c000ca850350b0b02c100380500c0512602d40004914801d02403d44aa01015181c4603c0200300c20f6000c41149405980d42c5101d20941501d100720f49640c0b00c0c4a10302c0d04a60140d5569200c1c2481e4100030046a001c69000d410700121110601019046900782c81c11600d14010256803424a000b107030380a0b0140d42e404d003070800404401c2c00550340c400480c03800060415244041180e036100d0791885001c103402c80da10310320110005e00340440d0501100800e4028000f40860704d40c2c04062011a02d4101254049000c056580342000c0c10050501017154030301e903503000d2040c0b00794144241c4500c2d02848011060601071540c0c04c0201c1115150180d0385524001401d80e441001c0609110b00e164080046851280110400218070314840d4401c0e40c4c0214041d0351100e080007420354510b401031440c080121402c540070548100180e66801885000e07280500454901d414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 908718093 1250 908716843 908716849
    0xe060c03030a0c11120d0609060305030702010f030c0516081e0c010b03030901080a090f0c14120106060804080703120510061206140f0f0405130309080615041d01050103060b 76
    0x43d00319402d401c0041c43e43c400b1074260700001d00325400c2c0c44400030031607483d0381000102006200d2588400c44c4141094400810b209010018240d254000e0701c480302d1401b03041008034210342800e10b00c2070110b001030101a400c2600c4c242c003030007050310400840e0b02e481180481107180c05001f000c80b50200740009041c40e5504400c4c0105a80743e801034004500740001040043c0c80010300514405615559140b10402d20100c0a05000c42540121640c4221034540124909400c01101083c0c00b42028448550840070144159002c58845070382c0c0302e005440301d0740e0382d0301503500c501e8041d4200b1410f080e0b02003118240d8480c1d5030184042401030141c03149001005070680c54a1006c0701a418a010b400300684e40c044001c204100604071001194500842e00041c0c00c140c0001051350414074000411400803041081d000c201070003900c41e030040136910401d0640d60740c0115204115800704180203502428a40c208110310020358050040c0f00d880c8103a2582110801d901c01c2d5030840d12031441c0d15440c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 908719343 1250 908718093 908718101
    0x9190f1e05033703120225060b03120f030426030a06030213020c0c0f01020a0803090a1103070f0b07080903012307090b2a030301030308060a0608060d020904030e060c03030a 76
    0x3c050071544048060442d10003030b04145020b01d0300c83c081c0341c001810006030710450655510700f031894800d030328080005060a900422210320364600a01c07403900d8400707a0030314140035110501080c0340040d1071603885950358208000d041141c518155001c19251401c40d0340403003d10b100740d0000c0c4000440f5403840c0100f041d4a000703202040092803040048449015007c15000b070048002d0f01e040c80c21300640340040340782031b01d41c1307001500c0d400c1e010007403112000002c61041c819038000d1502e54409010501010f884920a1254624a86882c80100400d21054025205440c01942210f003032021210100c2c1c207450162401880b40300108841c038400030341007940c885c0c02106610f0082070040c1002410340c400d20035140d00710700c940104c0a03054058860065179521520802041d079445e541e5034a00604050815680d181c402c0401a0002c18264401d1665504c51900141090300a0015400344500094064820b80401009680031043d5841d00070051800c000f96200030f599034540340d0002001c503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 908720593 1250 908719343 908719423
    0xf040f0b1f02120732010c110709060f060e0105190e01022a0609030a05010204180f0c0c1439030a0f081b100209190f1e0503 55
    0x70f4241480b540c0042440305026880340b41c60700101c4a03145180d44010444544401e800c101250308040c8000480e5500c0703807050178088018012110404e4440111505607952401100c10314452076004010080c071940744820551418101302d881c0c540904c85408102100d080c0700b9010625200300d5540360f503030400c0345960b41901001f2066405000c840000e00340340070351030147e20540300860940c049a130b05010001070310364040000c5545955a41002218480f03852031504418070303048203000102010700500c024010343e40d45440c444049991600d030070018030488200c8611810402800c2d12000700c54200c886e2080c0d60301d0102c0300c60f0540403070b000c200740301c202c10f8003d401c24580040051044400142e655501c60040d03912006030911800d002d0590403518402032144e80a4083c0d100e01650080040780815a240783e411606c0c0540340510000b0f902c01d11711030b0003080008200b00c0c4920b80802070001c0f0305c0654170f080c2c3d82c1c0d01c00000380392400d080b40e00300310000307034900f00c3c2200f100952400c009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 908721843 1250 908720593 908720623
    0x91b053003181309111002011b030507020609030406081306090606180f090c0b07030c0c0608010e0c2b0e0604061b02210a1124010b07020f040f0b1f02 66
    0x940b1049a907540c0d205005c54070340034040e0307100f11400d11aa80c000c1d0001e200444540c540011114101c0310000c008d844107030703210009402070501051050b207001c01141c041d12015221040c141d202c40355020f00c6005da051b800e0301c0b019640c0c0303030740030004070030f402140004c00005d80490410212040044212070b06110b011884501d0a1541c90004140114600444400210403070301c8001074201518007080546008024441000c4007142d042c0e0449400703810f95040300c8001e15036a680131401501841607202c509001da01d0b442014038000d50306034100d2104200032a0104800008494141c0b8100c41990101c40c29900d840f03986880b0413002000d079440713030150310040801c4201906045100340e071110000594100000728007a400d40600702500100c0c040100700c624100c00003100000c0800d00517541502c010205000140b2064204155900140c000300103c40c00516034040000030002401501c40b01c64031034510b100c00b5600c0d0940140d42c02c01d40d03c040c00c40d1400202000b42402d40e01c82c200740c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 908723093 1250 908721843 908721851
    0x11010501094a060a0f06120b090f1e010c05040b04091a1804031d01050409022a030c071d0402090424091b0530031813 52
    0x511040040041c2c4180048005100d00d070702d8004000b01801600c4004400361034180598481d0181c4005005480303105900130401005c0c60048034a0181c0b441e40c400c00ca000c3d0400000000401e034540702d042e0304100480221044410001c100030300707048115903d8098244d141c1400c0d216001c2c20b0144045012242c50050b1409003002d40c50a0030340030718001c0220142d81e40c2c880441614040c0744620404070000c01e2080c01036801181c9401c45c1100700c600b100043c8901c070340044042042c19221901d958161282c500301410b20001000030741051104c51089440b814054941d05400e080c4240c450348520051a521005015180d180540c10350181e03100b04503d0780600305070b80600c0011034009604646443d2242c03030354101040001c08072201080540b40e554051070b0100ced4980d1103544464420300040000b4448440501100601482569041624000070142907003002140d554034211880e81200c1040120003c64170311380104000c4000d20020b2400c80c9014981600c07200300d0190601000c0c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 908724343 1250 908723093 908723111
    0x604180b040b121e06041a0c07080315120c03060c0d02040f0305160f0e0a0908070b010e0105130b0916090312080103061d15070215090a020901061e0f1205071101050109 74
    0x6800250401f59407203d040c440454220344181048411880d0407619403516030529008004030500300001d000d00c50070241c801e17541602d80111b0100c00c0348400902a000660320310108c1041c6034411802c9e0f56500740e00700400f040d100440300b01000554010f90080001000007924140307041a075410000c210b070125242081603100c00c51080d42d0069014030081081c0c20b5514010805001d1800003c0942c1c1da000300116004000e400e4540c12900e0840c0c4802082000601903403c80300069201e90f007000540c070001c4d072507900b400018550b00c084c6181c5030205654917100c004501840b51390000009010100410502080d0301440c04030300c801d003101401c448118007581c0d940303007210118980301320b030000c00003040540240000f610124010010f4030051802c2d6940c11b03202c01d80400100d01c680762410010440c00e00c503803408000203100c60580d80110800c075400760748010b25425404100714110700c816404015034006d00d40030300560b0b1a5112450341d6008051300703460050300248006842c20010f1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 908725593 1250 908724343 908724353
    0x1c080409021e1e1e030703051933031709041b05090409031b1113090b0109020706020708070308060114090102030a0509120a0b0a05060604180b040b121e0604 69
    0x2005003e0307008008664035001d81860b900c1e0400d800952881e008000300070044a95050f801c00e92040300140841c110300900c00400d0011550a0065400c1d480540340200540d6440351111003240d0391041c0d4004000e035941d995514803c52252149685104040340510050038540071704a442ca050002440170f41c40394800080c0701d401a2010b00d44255200d06414091500440d4280c22030182019805c20700d20180c00d100c00c100a0566002e4040c28045200e042c070390700184100c0503c154443e1484565034070340341c0d0f040b000c0d4000f0380050350403035400c0020700c000840e04401031203441c6c42501d0b10145450030200151600002914040f4048401c1000811581e40030003200c00c03441c06401c2198070b13150b02c0030200380b41000c0b456116045203d40074010080c08415407801d4460002002d05001c03e903610014007034280210b20914480e41e0b54030710402e44a40c6035070001140c01c03501800c0003522030071045c0062881a011b8104d403c0c1d40d0045030f500104e10220100841400a100e00105020f041959170703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 908726843 1250 908725593 908725627
    0x312040914011503020a180f1811030112080c0a0b0f090a210c02150424020307020d2907120e0303280501030302070501090518061c080409021e 63
    0x1c1e850804d58000341030140140101c5050b03010f04140c20700c4500140d115501c80003211001c0c083e0400300c0c0740100151408840354010030889030281c000c49811369180000c0100481d80b030070412100200103000c0059032100401112400a01138825149c80e410a55001806003502070070b09100364010424410101d9852103c4429a20480800200062a035142114031071081440254008040080a481e5800c0a0050020345041ea09610207411050320114401510708500101580040c0000805813500c219250300180c041c102c6082c040c07104031100c1c118091407014140150780c2c00d405000d00f160b03116180d04c0e901c00b0740c25010801a4141b650032a980c1c04000c0041c0496051a002050680c05044052031422200c0f0401d010550310703403401a48421341d500071103001560000d030000301031038002c00701c0c0b4250b0000100e81d01e8684901d814018031300f2203c0002c0717185850301c6208200107100303000104002c0040000040c1c96070220103503100315a000c14a900c4204c181030204080b411442c1c0d00d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 908728093 1250 908726843 908726879
    0x5130209032802060d0e06060102063601020d060306060518041502070b040323310f06180501030519090f060603030c0506070206090d0c050c031204091401 68
    0x5030800c1005050b2407414055961018000e421030b6021070840e14112060300600c084442c0442139440c07594852004aa071214100d0b4240503480400ca0320300c49411441c070103020b0b08440001c0d900070380c101400d15242039030301c081d10b400131190703580c0000c0080c0220362050b2000342c0f004560003d203d01c0004080001345501800c0688101d1a64003c01c000c0000d40c0e040300c08442c1d101c9020612450036007000740c03030110706200c0a03102c01040e2003403041c00b85c84442110302c2c1910030404001c40085803d0324501e421404920340c25104642c450218201707000c100958010600d55039013001c0034540d00c1d40000d00d002142c1c0214181414442031080c4640003540b00d4001280e8031100241500c8681010800c40701d0001000c8c0080d0310f440004418035a1200006000c079000301c044482d036403075209007203070798510495200300e69420001400b000a403140d0312840e1858010700880b4000c02103040082e003001c1669240400c09540040c04110f164018010044040180b4210001c158900984020081c1c1000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 908729343 1250 908728093 908728123
    0xb0708330604050405180105060607030f050a030618021e0c0a02060d1e020a17070206160c060204090e0d0203040510030c03020c070323030403021c15020c070513020903 74
    0x20690002a1100d00a0b5401000010401d0040e4144105000e4000d1303101d100888070f550904000034240d00f0701c3c800b110652580f40c0d0f500442c6c05590903048483e604520b01c01810162500000140c00d0840e40b648200601c0765640140d44540c0101c42003001e10f80c450b05140b82040501981120384000314401d10340030b8040c6d825560b100501541171f40100800407403c100180741c42174030010b8505950240913503209a8442c2c200c1e42d04203451303614100204403025070041c0d00c160001010304455078500e0002207141d0428010910141e03803064242c0e00103810041c9c1050355541a03942c640000c22807075400c0800c81c00654505410840410006000c6c10b03806014941c50742801d60000380b081d4102c440c81c511360400e170b4456903168901080300c2e000ea11066615200c18250010308114048200c4003100d84c001d201000068104904e5415000d1101d0f0030358880e558a48962030bc02c3c12070006041c1082240050100e66090400300a070000c10a1900c545541c4180040d0301607442c00500c01915903599 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 908730593 1250 908729343 908729431
    0x503030d020f040b030c04140316090c050c030f0d110a05030708220308010602100608100525020a02090c07030e12100f05012105070b090303040905040b0708 69
    0x502e0412100c0c460380d44041d01d4200000304008540e84094050000e0f500e5140001d01010400c804155681034442003103c4900b005050401c6241216444a0602d041c942032650410044200080c2140c0102c1c650440c2e02c000042c4070254540703640b02d5602d408111100c103500301014a48020b1550200070081010311080320007150604881c6d0648400b1866034103413548100b895483e0041000e00300f0300c00d04005d0301c60740c81ea25091302414090340041d0f510320001007114a18801504015005c0581840b011a000c218026683d0f1401903000e041450143c0042c102090785106200c105080146020030b0241e0500c9480c0000b6032008890542000444040c0120b0092161250401c0204000c2c60f0109290040d1a00c492a043c0c01850480d46454085113074050005c010301810260500c0040568002030418040759802001602c600c00c400380c2182c3c01e00c2d4803071241800300c2e5000d03107050b540f030181c003000c0018140e03010044a520401c00150114070171030b00e940d941e080da003038002100c52895403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 908731843 1250 908730593 908730607
    0x3021c09060b150a090602120f0d110c03030403080106211505060a0306060306050406050306160e091509062d12030301140a0801020310032301050109050702010b09010503030d02 78
    0x142c0109900300c0000b03103244815444400c00748910ba108030002404900450700006141e400460b01030030344400c03030161701d150810749114010729074084000c0003c0c2c2c0365284544186008144050311007003034910000c550300d06240c1800750607003a050f4081000c00c145a01518044040504003201c5010341140104030819003042402076102203030061078020788081181800c056254100e40102d41042d141080166107850510054491b50b0042c10f8040e8880804a00c20070740385568020614407030b00d04840411155000503030108004e80300c200c1d102694800c0d0071541c1c44c15010054012030b0403943e4802d6040d506801c007801900711542e00591155255501e8026204c0c104403600c00841141903030398961711041300703001d003d0074803042c940165800440440c00c4e03e8140f013180d0003079204554005401d032131035961f401d8451500c03400281a10420b0f010314200ca0090080d14040d01d005074000c036991800d142c0090031114102071091054020100411540e10b02008a622500a031a000741c1e40e115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 908733093 1250 908731843 908731853
    0x4030c1724010524032205010e070f0b091f1b05060106080106020706020c0d03030b040c120e0a0c0504050c210601121a010c061b1107050103021c09 65
    0x310300d03403180e0305840720204004032221140d000c240c1650800c0358405081d66920481c900b0385080300d110b04160f030404201089094000384681c100f100c10841a80d2040320305030303845c02d0035100094030a000c6544000700134808110b45a01c503d0240541c62506803c14a001000844010700224000e0b82040715070f0022103682d2280350b0003080d6052413081280e120742c43d0f10f0000e654140912800000070659000421400d10124050045880c01d0380180310042d4400c04015015041d03800840078190342d006111a1900c442c0104090071016072150b00442102c7c40a6800381d90341d41c40c0c0d003901d43e00310740703441c030005060490300d1030960300151400903680d9203a0390010000c0c4a00414440503080d0602c8503c0d1001e0f410f108144690310a980382a817176000d0310b06090580b50092000303007040d90000f007142e00f03e5100e441c1e00110303d40a0640800c94042c0711043c201b0211341007403180e0004081d00d00b0141c1410080241000501c020f103011440d00c0100c401c841d000b03c0b8070504408066417680c8583d41441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 908734343 1250 908733093 908733103
    0xc01030c02070b070818120a110a180509010b01050910080a0f090c03050f0303010e01210611180d03020601030305031806180d020a3804081e04030c17 66
    0x11404a20b529598a164100003000e0b400614a03d1150640d07118050b59a04000321180680400742d0024401035852799038034101000024002d85d0080c066141c00100780e541000e55460060540c040091242041c1509500303541040404c0c5050000400036900b480d2100c00303142c0103a03070151401c00c0c000e0b01e52000c000041c09a96007407501080c10083c003030703050081c40050041240e01c94011561110282c0318a2512408244284d5040442000040191101021106050304541040e02c8451016580d80504869030385510425010010070b48411070b044400000400c0e000c03c03511101c2240345039600135034030b00c0140001410000041f02103540e06410703000c0c1c0c40c80244140282e5455141c412801548010080c101140d18400c5614041c481400402d00624180d008422400200440034290072440072445c0c0210041c030b0700c005400081030721300d003c00c3d00980c41806550360741ca03c4001c0d0210170301205443e00d01000000c010400004400c2031452040314103107805280160440711206042c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 908735593 1250 908734343 908734349
    0x1b031d0d031e030e07030b07021e0d050309011416110f060a021e121005040e1b12060c130609140f220e0609070506030c070c030203070f060207170c01030c0207 70
    0x24070a580c5c0100411400d2445548070b140980d08442404051114107007c20b060300402000c540c00554a50b44d540b48100001c1d40d0103140c5c4c10001c90001e00b44940440721160480390400f40881541142000c164015440c85401d0010001004803040060080d9201d05028020603001907000542d1000b00c80900d1000060240041030140c40304040036141500c4078084032102e00c0d003001c02d0300c08506442e240c42091601031030b5070010a03d0701003d0b04090303c80170341e800000e81d01c698120701d48003003c1da08106030fa1241040da50100e464200f840c443d20f0344410756800010a02001003810f201070b520301d040701100c03014103d520040754840f00c000701e9080300310b42010f070114102040c1d00c01040c09c103503000041520030180c1280c88940c1c038030000359101e00c0540250356000d5400c0021a90412200c4041e107955070280d0410516146d0b2940007034a010304603402101200c046c004100419501805088000d01c10294640c228481d0b50b824039032035803400018a8181541d41900b00c9900d4030030000c036000703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 908736843 1250 908735593 908735621
    0xc0f0904021906050301150504030321060b0403140607030c0f0c021909151a0423030a12020d020d0e0d4e0801050d031b031d0d031e03 59
    0x1950b2100340040141e803007400349144910307090355401f080a100d13508032022a40c060762503a0700c070003200d0803540030140728103040f80440d51107450100326415002e006000462241800040d03d103540303a121811700c140103098000b414134061155039415040440060700c001e452034295030b03846141c4001a11080100c9643c0301004200c0780220b100c0006a00c81d07060b040480750502840780c1e48400c04641c0c100081c2001400040c144800c0101d08195000c2c050441040091001828490320209140c524504415030302d041c880900c0d124a41d0301408070310055806840541901d603842c0b580a05064403080030240035408010201c03050181500e070311344004101c0c0d200564150155422907103d030000144019894044106201c0c1c0c201003a248002a0750880e00d81411b10b038603020400c465500001c00940520801c9504140545501c14140280b03d102e61203000000c1c0c11141004800c01280041c2c5001d4184242103130080b0b078010600e03011040001040c2e10781882c03201c0c4110b020303014014103105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 908738093 1250 908736843 908736889
    0xc050114070f08060409110d0606030605280e0a080d180503030702010c0203120a020a0c060203100f080a0f0803061c0605010305060f01141516150506030c0f090402 72
    0x9040360b000c0308980c0044015030318000c2d261540720400c42142c03030810005005503020700a4000d03d0400d0341c4440425401140c00007001d0340e4a4560600384c47d41160001c80c2c0c2d5080d885200d440e020340101440c039074151503602b000340d040d55240245d520341c041c00e0003401d448800310380c2c182c0c8030b0b41540010081c1d00841c0d10103054004076142c8165282c0007a504040035500300810245411700c00010f90380c521000d51000c406680344c0841c01e400a6000d030b8115004c2000788012074020034101c2c002180254805000302400c0d0f460608003400000c0c15401c0130721507400c0701003007002180103e9007040307005812505860352a10f0784000110340700c03088802d210000e50380c01030b040e05004040d88040e040304e004400b540c0e066514803074022001d4100b409190848410761801e03202c01d081044940702d01d014004c80244ca8074061b101c03104000c60039400201c80243e0344e80341d4116088501d000d1a50009000d80c0105005546c000003c0c2c1c03c540108085401204030a0008055686030f12200d416a40030920100e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 908739343 1250 908738093 908738101
    0x708060408030402040f021c0e010903200102041a04050414010821040504063c03080f1c1b080705091905060f030103060c0507020603190902040c0c0c05040b060a0c050114 75
    0x3140d1180c0341445812440e14154507040003550601a841c1c45541c507035605181e0748841d1462401040337840e5207a481540d4280b00100350b07200c3d00900c00618168003c40715898514000400c020740b200c40c12298001c80348003004200c0c01d040001c19480010384d0a00070104d030341c0c2d00885094a400703690b00240d846814040c0c009151440e200c04c41c10003401201d90f0f403114041c02c2d82c000341075042e07000440c1b40e0015205002c1000c140750001a00d1403c00702c0c2c2102d45003090304060b0300c5a800c1008031040610799100c40c00c0039030a00c00e80350802610910704142c5c044d8503101d68040e0190103110130341400303640c7c11030f080c070341d015488020240034000081000e6221001380c03041001c1e41d002400215560340c5407100c0124081e00460640d410a41e000303168502c0e543d02c4001541d01c01a540c401001034540b2401c8580060741d441c005e26440701810b80d200304c640c0c2c106083c900c0c407a0b000741c1c0c85640214507000f4814159103440c0b01b03e5031036040f01d0400b0012030002d490f00c603005200d452503492001d0385810903c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 908740593 1250 908739343 908739367
    0x70e010c020a090605091605091512160807170a1e0f09051509030702040b0f10051e2106060d020f0904060e071e0207050a0b09030f0708060408030402040f02 69
    0x400d0303070030548009031b6651307420b01108400e00d601c20300c1001060061085110518202100115003c2e0f40e401841c1010008405110729000c10b0301d000400310307040c41c1c2d07002c042030b8842d10744e907400703034082c40c0c84c0001604c0501840e1680d840548014a0035494410010200d1301048210b0100004450104202c0314092001c1e0020944004115084c0c024000f401880703020400c4060b0084072801e010b54500782c503e908100c020000c04008940201072580584003d0f074031482030140e4100c07a030311902e0741e0301e9010a5100c0700c550443c61548e0010014407002418101144c80200c0003a01c03a0003450312500c800000038040d00a900394120000e00000d80702504165803000f6103071904064038280072542d101e8255582c0088112020000124401f51071088805050110303501500c0740d0040d10840c82d10b4030003103514030701c017600000c816420010b00120755003001c00164a506040c100a4080141005034194845078041c0002e050301c00c012000c40d0540d5100d611480c01408105c004659900e550b200e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 908741843 1250 908740593 908740601
    0x1150b04091d19060603081207030b1207051e03030403030f0305150d06051518010509010f030b07030e16080f0615180c070206040f08100212070e010c020a09 69
    0x1030400d05500b4a4100c440b0300d0141240480e10301c01c400c0c081c09218000d03080344460800b4520055404a441d6140080440c203904c004003d050f000041083c400e18000101130309640899003024015400041c0c00b109504004c60b1050564404403913080b1503000d40a85240100045809107616000010700041056000201c1c904904a1902d040c00f035039960000f01c030b5002d1000201c185c2c0003000072035814009141e40e070040b070f4000c188441040c2810001800310300841804501143c404d906c01005220768601007013501d00420007221070f42c10513801d40da158400781a01501080515071600f00c0728100580078800230040a5030240d83c480465599001c1c00c0e035401359090b0880c440e00449003c18040101e2403400354411070081c041c2151060030446450000400a00e04c007900e032400e1200c100141c2d199030003000140f40000901900742c0c1000c52050401c140516500192403041140c45840c505001440d0350202e401d0130400340710038601d00140e03021201d100c030095118030000004a401741c400e605c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 908743093 1250 908741843 908741849
    0x705030718300c0b0d0f11043807050c0904030e0603100308160b070806150703091d04031b0308040201030905030c0d030e1002120a05180a0302030304020906040203100302060a0201150b04 82
    0x4030a10140c802c00b507640e0107c80c8400c00e104007414080005101c0400301d2070135940080605140303000f0403c118941000944c408507070304005a0305c0003511505103c1d040111040d1544126440c0c2c4050401c0e540c041c0500c3d070645c0c4128001c2e88048001407118031410118001503820510031a50340b00040c41c0c6600c02c81c542441150460126000b04546a02c14199203128240242100c1040c006c08410311845801651040b402c200c00b0301d201045d1096180c14840291350100002e003842e040510f4050604052146408004040902500046944044030360340182d0203080000780c07031549050090541c880c4400d005200e10400307003000b203440d90541c891041207081005440d001c528a0040341e041c1d208020b0620700404030440410f1030703c00749501460b00032850359004e4075200c604121180c00d0400e007110550160700044100303c19810140c10366607205404640031072a40c0b5008007038500c0d181c0b01d404044e00568012400350b0066000b5440600322030909540f0440c03442d40d800000c001c07940540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 908744343 1250 908743093 908743117
    0x1404020a0905040c050613120606060e0904330e1506010212041518090504021905031903260915010b0a0503070c0204050705030718300c0b 61
    0x403001038516010320400c1e00403513101d80603d140501e030004210f016084204000181c0c43c501800180313040040c6c1e0324050b407a22645011850391701e05503014102d0f070303840c90030030340540440030070800050a4910310051800480800106542e4840c0700704070644604c2010b100780c0c1d46003621348038880b0400284000074060407006092542e645800480e1503003240c1800d0880310b00244803c3c1300505200d9405c5600380018075080b031099501d00186e4529480981c00300305280d64136018441903003403842802e0740405601000c28505c51411000c0b0707686800c40001060760b44244140c4070101403107010070070030041d1070007098202d152040b0075610384c6000a80314282d55107d0342071001216404507071071604803103043e103000381016051901510340d43d000411a4003004102203556006036100d1040714050751480c0d844a40301c1c40c021101404c4950130401d0380d4081c1d00c0c078540c00c10040c0d040815400c4140c4640d6941001c0c0c21201034407018079102e9003402802c44843d0314000c5070780c0000d00c2c06020030210f02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 908745593 1250 908744343 908744359
    0x12120e062107021b0108060f03030f13150c320f060a090c052704060209040b0d052104090f020a080c09031b031f02030105011103180f060409140402 65
    0xe0380040e0380d6207103020a001102c10300304030980c241798003540e207580d44154003902019441c10341c0d10001c1d0450340700c010f540e291a080401d00701400140380b80c000000d000207403c4414240d001c11409000c00640b100d00a00052000c501584890040030b41c01c06030100c99154004656401d5007030603210b11007041040000d00c104000514500e101e80100c0d20b005030851542a1a9070400003071211030301900048000400c241e04c48030384d01015260305944581e009800050303c84802100b0001641c40c22111b403441000480100340220342d0225401203000c00310701c4000512a2070280541441c040e6a102403102880c050000c4883d0206400070581300d51207035550340540c1d40b252505040b60068400140c1c01d0303404400102600601d07403c018140300801821606007000c03040f16119200003040c40901030a4010004100c0781d6004040340002c001041c0145043c00706200329840050030741c1162a1003a2092113400d40c064032440f00f164040c06032000280410b1400742d0501003a03e0b01681e00300e00900070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 908746843 1250 908745593 908745601
    0x905010605100c020618120a1110020303100b030601030f021b01060b041802030a020906180109081f27050105010e181f06081e0708030412120e0621 65
    0x403601d2240716880c0c0c02001103042480300251001d42242106c041c130b41044010641c01120304080040540c0e1600c2290000e50b07c40d01c56003445118503c0603c030700250340c4240b080c40ba0700340c4481420001d56041e00d8840d070310fa94032840124050440454800380c502d00c009850700c3d4125940405d184c092803054000d10405a80751540c60007031003a48140342d68800481c04425140c4450707001140c00c1781003510094140520746c4009503103603011311310b16403011a88100d504000c1d60042c5000000f00004d0001c2c2081c20782c0407807040703041d08071024003910303080d91a058860031107401e019403e2440f540690520010440d4500240201003e000f070b01e55078880b2600090524081134903c5104515602c05040a80000803980e081250b8a441c0003014544a040c0800c00035801c000c04100b5030903000d10102c0b24401c0c9039281342000a15000701302e9941041000340240e0660b004002c241da90700814682220000502c00c0b40c9a00910303607116482440020300350758440503004643d0b1400c03158101d1003060b1319 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 908748093 1250 908746843 908746847
    0x9050c0f01090306200c030c0f16060309150905250b0d090c050909030403060b040905060117030d021207020f010b03060a0e0c1503100f080604021012090501060510 72
    0x102000c1424001214000309000281490700180c8806502c103500000383c0c036210060f0810f541144120301c80552000c07900c0c152001c4200800b00c074801d14000030307080208400b503242c0c0310903d407401100c040c5515440d15130200800348c540443d90382602c0c44c1c04c100a109610301144c0756009000001050f050303041461421582e0700a5140446800a1505142908107688a4007406402c1d20543c0d840003801400955501c5000722544075011000165603121b045161200498081c4d03140c65000d40e180c0580440051800100f0905540c20310000c0c2100314400e0341d035030f0b14500c00c03130200404480c0041203042e0043c2d0781019042c040d560a40071b480030000b85889290132180b0b408142c80c0d05502190100c1c0410100760300c05001400900c040d03038a5918075102048440760160b402e1540181c00000704015640c0101d84480a40300b00110b40e0200d80c0b4100c642d0b41c0d100c4003d08060311400e5000f042d030b005e082c000d1140d02004c44101c0804e100e40075070381c24100e00802c00380c81804d00841c19003522005040c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 908749343 1250 908748093 908748109
    0x2060c04050a030b06120f0606190b030105040b150705011b020d02070e060604030819030e0d091509031a0414010204180b0315011403010c17060d060b1309050c 70
    0x180c0c018102c00507952443e211088100c502034040c3e07421500030000440141070500030f00201c0c098160041040703041100501c0816280c4040440307402240d020240201c5907a0011641100c404403000300d520340c20a03000800326074080426025400c0e0000d03143c0208003064102d5425001c49981c0721301e440c490f8600076615951a40c0f09100107801030b50040c4560380c0c0d142c1b101a0040e4000d0310850078562640d54065065015043d81d40c506209031480d4a11958140240c507490f03140940945404564414064140500340c000c2200c0c1ca0030b07202c10070116a100750040d00c011600300404070745200b038100f104030f07078114166825500c50419110301480c584050088038100c03a0300d80d2038501c1080900300d000c0000c040400603264140640419010104282589a406002d140700c400c000c19080e10304060840d0350321001d280c10300081208201d0317041000340c0c0081c6d001c034007907403d20304100c00351034020010700340340d1310055001c1104c0050205400c49035001e044828484c0040394075000ca00010001c0007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 908750593 1250 908749343 908749349
    0x901110a080402010804230106081b0a1202011e0f0f08150913051e0c01080609070302070f080c0d03150e13030216230d021c051c03050702060c04 64
    0x20442841c0441c00551040110356403040c01021421041043e6007501c0760443d10241d0601c1c202c0e03440d6181441420000c2c00000101d881051000d101c01078120082100300c1028840c90040e400902059825640207d6116802070b03208480d40380c1c000c196090251520704402c0d080b00014155030100c2c1c0326540154122030040284c50b1089402c0503456040001007070004184d02c50b0040c2400c24080014420000400040c0781c0703107042070040201d480b2062401c3c11090f0001e04010707160b410f01029482d60402d050700310003545805a6580300310300304038105004447c0c0c01841a40e001400034442040401c500220380f50341d0340c0c1070019420000342c0451000c0f031402000c1c0311506500200313070b5805020400d01140740c0b090054480070304001b8a41c10340d0842c40e50106030f0384902c8441601c0c030381d03202000c000d8204000301c2c2c400c4860b042c5500442c1d40d103108140d2908000001d00c5c80d80c028010f0822130030a20031021205480e54a140c81c1005001e817900307983c440058420300d400300d03544607582d80a40303040e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 908751843 1250 908750593 908750597
    0xb1803011e14014209030b0c030415051f0b0a03181e15050f0601080f240411040b04090b0a060c0b0a0e0d210606090e06030c0d0b0901110a 61
    0x9003404805500303007000e10004d0702d588408603000c5a00800c8140c611100420f12140c4031050401e15506001e1700d503a00c01006240c81c1c0f0b00401c10080010b62110450031a00c1081c46d0004850380c7e01c0b004c50b00c0c5605001030510b210408000c00089441600380102032138100743d1340c14440451030006035000d81c42e003c58003c0200355030510303121241a0007009000d00a0140d454022500003816136801110800c0d81c00c48000c03030550040043c10b580055140b6000152807140d080750b403812103484d030500c031342901888034200d2141481030005d580710b1704501e000d071062010f8141d40f690340302c103280c03010782c02403141c00300341402c20280c031b200b45c90104240d90440b4155161610f411101e44c0d01e40e100240c00400c903248440d540c00c107680b0b100303c003000084005101c03901c0303103250000e4203110300040d41c48103200c01001c141092800e000150344072207040b04803072481d400c0c0c694940701e81c40000d0408602d980c1043c1c000d840c07005510306000c07508102e01d0044001d0f10080081c0750303031002c1710702c2c0c503119444080b40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 908753093 1250 908751843 908751869
    0xa0b03010e0c0d0206040510020105221a0711010e0a050d020304030215210109090605060a06050a182112020a17070c05090c070512030603070b1803011e1401 69
    0x18203140c40e0a004480c0300400c9146091f484000040070340d207d0b41381d5503006030741d28810030201091841000820b424404000c8108040799034900804143d1000d6035404544d040d804100904d008004006001c0c0c1c1403c02800080120083d441d901c1012840c01c1d940c40c810078400f202d00034008000c490030360750043d00c4200f8012a5810008d0303a540007504204150300c84410820300344011100035400380c080c060b004182139a01e402e0a00c04d45001030142c922030a820070040008940000c00c480025046041440c0c10405c00300300c441d000c96050b41302c1a14240780000d000d203c3d004103417080010a1180032401c01ca0408020704030380d94603101d10014000c215810a044001010401030f18551b803265403c4800d19072075002180078400152120a110b5030041406801c00070240114032907600395020443c2907103480c000182d56010b40c0d00c0f5002c58810000313120307120b02018885854843c4800750080c006d91000078082c203003034464a105862154035000c46101c1c00802d10b0b0903507040312030541002c5c13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 908754343 1250 908753093 908753113
    0x9181608011e0b030c07050304060509210d0e040b0316081c08010b07020415030b16080c0711010c1205030a1107030e1e041109010905060c0d0c020a050909060a0b03010e 74
    0x80f24aa101038040c003140d43c07007804080000f0307100f0030013000503162640d2440d80341e81041d010f2190144203490402c03c004048102490281c80c001504c3c0312200e0245840d012610201000c50002c0400c18409c641601603a01c9902c546511a040c6204031001c40301200c1e010300e0400042e202d4030a03452407400001e003c00300104588090140584003090000f00b00054035442c81c2003000010303c0b980d00072110781402e202049003941402c1c440d0a140c900703d013441ca88500c2c14110350855481000e0008044103442ea03119062640f140500d0030050f588201e0172206420684400751042e003085580014140c2081180041c0404000594007403d503d500c8203121180c4807002c101a140818a0070b00f900000c800c4003645c0c0350b6580c02a45403054240c0707074481c2d0300d034407020004004190136000740d0700960702001943c0302d11200080b035000d801c1c02460710b83e21285043c40017503090021079210a5102520b001805508200801c83d03d0160710300540400804402400741401c0c2e403403541c02482140c105161603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 908755593 1250 908754343 908754359
    0x10f0c0314030705040b030f0103020a06020a020d0611071a190c1e03020d02040609091506050f0a02030702040c022401060f1b08120415060b0301030201030209181608011e 75
    0x20750f803c40c00e641803007810540c81d29003403c11a0000c8440b403918414400041041d170a204c00f450010b00201c0c8094456081d00d500400c54040d0080001420240d4540f14058a466142e080d20403896010300011862034008048000c0c2c40703009c0d100702400420261040072045201c0c03003081601c031555103c3c4400b664480010704c0400c40301026100915408008080c1607070251710081000d403625444d0307000c0d03050600c14120101c80140e103ca103804003000300c051160581100a88041c2c82c0b6041c0d000d6030718014100200c0c154020304000941141c108084406600e401007203805028410880200d011128018210f1800c042032203490302040340e030460389402c103104030b900e00380032003034080c011542d94810b41c0c07082c0c8181e00684030503903044425018001044200340d20000340380101c03282489030078100f503500445031006110080c1030640c0001c0c00103140d00e44075001d10500d2401042e0079100c0c81e088030885000d03074005445000144010f40042a140506600c10260564400607e60074500384025 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 908756843 1250 908755593 908755597
    0x510060506160201030216050f0a0309080708070b0a14030a06151d0118050d030203070b100308040e190f0e0709020f1204140307051506010f0c0b15180402010f0c0314 73
    0x40310524641f00050900411420030a885003400c460000702401c81a50a004110350300d55084000c007600202802c20031044000b807190103484540d01c04507962150611306482202c2240b00d000c59605020040000c01074203903010b14100c0d45603084c031541450741d2010440f8291440c21801c21010040101503006521131032420890407021449a60b020741c40e10002040381c00720b13200c11801a800082d4100400a0350040950130100012075800c0941c216583e0341c0c140c0c0214000c1c800c01004050000d082c440f15004070200460150700c04001807000218101e01030141c00c002c103082440354860000c5d812845200b05c4040c54203840c419070030700d501c000e18064840406401502c0c810f1030164a0b060651b8140024800207100e000107096036407110703005440415000345014180041e00c030382004441e401c841d0321450560300070940f406503624400e80c410f0801d8428021900240c4581e00c5c4412010040456230045000362221a20001d100a0844d10100004401030020f24100000c034048410000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 908758093 1250 908756843 908756857
    0x50f010e150310170102072d1205040b0318070605040b040b0309012408070f03051b370905040215031504050a0c0905040c2010020705100605061602010302 68
    0x5042e642d407550ba414100140d058224403c80e00d81d6000582c00d0130007408c0140c281003503040c0005140303548143d107407a07d16012000c001600203101c00684d800610311640c112800750004000c091344a0134245058807041e12540c000345498801d090707010607030f58055801e0380c0845044003117107440c0c1800d080041146401c09440320350300d99241c4260031820707000e00584904101c81c9208590002c0c0c907007051146841c04a600031030a60300100420b01c041500032907084201d186000321958240d4464002c034804000781700e6218600b41454845004081a018030501c040b422100d561011f592141c3e45481201c8003614000c0d070240a070b801a00c841e40c480c90255038032404c0c0780c42802c1a0503c40c0301103010b0b140200c445c0710000707175104800c02c1542d030485810405844207680c01c02c040c0c0e2070f048015142440313020403242661104540c1740b11490701089044c040c2003604c8070a6440354030500c0c2c00c1e9a1402140041020702d8180300000c41c481c1040310035a60140710007e4600341c1c00c02071b42c0041d0003d6204070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 908759343 1250 908758093 908758111
    0x3190e0307020901060519030b060a0e03120406020a0c0e16080702010b040609020403051b240d02040f050108160207030215070c0611010e0303010e01062f0304050f010e1503 76
    0x481103101690f954a94540200754035100c042d41c90707410329240c11f2039010b400f8a032000d1503e040503190303140c1c80d0901079511125150401d10404d40368080024030300044060720341410400041c1c0031400b140d02091304010b0902c41c194140d00181c950100702c80501c01204c2500b10040c482c2c40303031901e1703510510b6625045800d43c000010044014800704090321815002141010340000f420010000108000c864000440d03000340001018040003030903059000b1805442c610f03004c50448803007009d100031600411180703201155210380e54a8624140d5036640701d01808944114001811000b00300c1000c0d041250b141d001d051071034190740c01c000390a14098004a0fa410b4180700c0400010344604c1413501a0106449000703804200341a1282918400800c2501e140c10900040140141c4010140e0541c0e1280c00c00b104241044842c07010030568018403ca0145500e00340c140309040c0210041c400d80d181984c501c00c0c3e504c1004010f490700c0000c0017829801c40042a004640300c49401c01a40e00041a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 908760593 1250 908759343 908759347
    0x30a060b12070e1f08060c07030e010f200114041b06140304030f03020408011d0d180e15030a0f0c05040911040c0219150e0f06010603020d0b090f04140303190e03 71
    0x11459145001002c8030400f4240c407000a070441854ac2250303803003c070010b003441d18800c841800f42006100c0c0744c44100e290385942c120f81c0c40030518802034001108140c45040408144d04c1d05080280c0751107909241160f074041005000f28066100b001d10041e42c001c1010740c20714685490303400b161000301c918101020184d0034040815044070a010755004807280002696811402c200d0b06400e1a00c1440402c042c403000c0b2070704440c485076a000300c004580d0007482e9080c2607650180004060201e4110311a854001e1060200030058481c0700c0c050494024010b0440301c58641c8103000895603044070141544503289001c250354030786a00500000210752055030031000c588240c070340400300c038000c040301d0348041d0034030040c505040707031191049481607140200f2140821002d00b903103d040600641081540005464040441c075411803040c52401503c000c6543c50200100e4a680ca8142e80440b001c40c1540030768010000004141c0c0d00034006c1c0d48440c3c0c10300f0b82040703d40c0700900394540c8450540c081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 908761843 1250 908760593 908760599
    0xd20070813150807090801060f030b090a0c15020f06070801051002120d1a0411031b040506030c031807050307060507020406080303090618010507080f0402040b030a060b12070e1f 78
    0x51850249101c05a4482c2000d5042609014010040a030401b2080b6854041b0800c1030705070b04c0c028441100e400000b601015103544843c00c0c1001c400100141a14000450009000c440040c0e03182c215070307140d42616001c60b6445446500c3d24001d03150030300007585110043c40985041445c401c0120b01c0f0f40100c1d032545003400e0f002c40c1690020411481195500c510f501c0384000610085c0b0207400048800700714004082043d05480d005c05400200da0040c151401c80c5181c0100c1c084034007501c00144815102c2c034101d072540000c3e0b402240c6100b03c13803101ea81c5111803583c002900d0402d40ea00180a4096117003884c008482580144074160783c070549916000071151814030045008629403c050243d600d4504814102ea60f000d0801001030380c034210400602d80d0b840030324103030000000e1180c40d400e500c880c000034000e008883c0722a603050064106c04010071886134810041c11006a07004014003c50344110740d119111440340486560030000060101005150841c04124019540301001a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 908763093 1250 908761843 908761859
    0x304110616030305152d01050c03160210030207020a270f0c32030703020706051003060e0703110907020a050f0307052a0d03020f0109080d20070813 65
    0x1941c0307a082e03000c01e80e181c0a0280c15454800e2115528209441e0001d9181850b13014140d509940c1c121106030800c2d61101c070095030302c2501243e2100325031000303d0380c0b5a07481008844a094a40101b28421011a02820340c0700c1d020740262404d1940051000031160302e07101d134104130015101e00101d01880f41c244400844810351046880c00c080d80c101c00125a011101c01400d410041c0000012b00e038182c904840c0c00c10210250011150030102d0003580307a448008040d13000c0d0042d43d80040285040c4000c010302003540c0080001107a020700d5050001100d403401054462081e0b02020780f050030700500c0c041403420110f85c66a0002144d10440c0c91030a8140c6505080408480d80400d15410008819091203001c100b400403045949500401c010500100425079400c02019240901328440d842018140288007086240001b80001d205020942c0ba00c81c000b0384c42180c200303100038584442c00040d0400c401003020000c4410001c10320b0255540c5944249801072116129400c0e840e1602144801c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 908764343 1250 908763093 908763127
    0x21009060b120109061109130c020712030206060310061409063c01030501061d0d06020309010f1a10120605130912110316080409150f14010503041106 66
    0x4000760300002d10b064451030401c0503103845001104034040140b00148031961800f000e4a91a070344c8c4080044c44031141103040c0d08005040d4089807101c52007040c01e805058002c542e00d131103148100c0030b8a0150340ea241c4403070704aa8542c0126052081003000030f8110317061407455641c111030020300d1014142000c403601002e00d06090700c1a66508031344500480d25190610b13406044203c01d003814006c640c10000001c000300c218502c0922035080210410340b41e034a4003d0201082c60700010113641e07a03d400c0b4551340c060610405070032040c1e45070514480c01281c60f56400c0100c290000d002d545500d4418030700701d500c40d40d8600d1200501e680e80b44001203a40d68111380040d030005040380420142e40e00e044c0020754031100c41496041c007541000400c40440044201e40a40741600d6840d12109240d060075081801581c106055192400307002049004604800f01c0c1100c2d10340c02d600c04881d0320b0711107120072481c50b00300700d0340400c000f400400c0c001800046800824840a0b10550610200c2500aa450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 908765593 1250 908764343 908764369
    0x1a040f0303020f0d0c0b06010503060609100f021603051c0504170106060809011a041a030f0304081212010303050a03230118060b030c03271f0b01021009060b 69
    0x159000e1240d42da0140d0040c003001d0f00c10613041c00c10078030000d0b060b21001d1103040d004106d0343c10003100000080440c1d0341c0350240c46000390b005c0c14061040c0d4014402400d10f90021071210054450400c440086415001481050300c0d07011000d801c181d11603822500103005015200400e00c8424080465100c003c207082e01100d0500c03000118682d0f00d001406803190720060801c007003590400c9090041c80301611201520f442080c0c500095848609680c03104041c2821200f9906004505550410102c0003024100b502c1034141a030b9030100030940c0b0002c45101e00c40174400120480d00040000c41c0c02100501130340109820040717070455000c14200c00785a01010f810700380e00000d100501103a5a01c9610719a00d1464142c104403041c1010344840c12804010701c04010220000000382960030000b03d10381038504480c00420b801070308201020386a960581a02c134085540b41f0000b40f03441024003406045400680241c00f00c6540e00c43d111001d403501400032b8941b80c3e01e411080300180c5440303403507402c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 908766843 1250 908765593 908765597
    0x11031006090b01050f181c0f02030d170708040219090203090c220e0309060c0f160e04081b0607050904050618010e2a03070e0d03091a040f0303 63
    0x8107030804000794102d4090a103031a04100c400e000d98500007007034000b20781c854440c800510803003890700c0002501d00a4074a40500110f1444c24800e020803402c00160f180e40e40c03085003601c0020f0004a011141d900c108039500341c088510702d0101741c0203070040c41d403650068005840080075981c0d600400d00062541c1d48090010350703000041008080c1709200b12420343e24202d9200c0204c82c445c03d440d179501000c0d07030030800d021995004200c280042c20411030b000703103030044c0c079190b00d901300006882c0e200c1260000800c494090028140e03100e00c0d600103040306480300c043e0745002c00c0c2c58070380325010075800913141c502c81d1402280c800c24550f4400c02c03070b192050a15503502030b5211410340902003a5a401750869008070261490300b40314254015005054030840010340540f07a03500d0849124441c04109001d605c40d400e14519084071007100d006500c1241c0030b8848208902c1c92509010b840c00044501400290882c0000d00020120302106014a000501d0391410b05031075800e842c15801980c0e00441c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 908768093 1250 908766843 908766851
    0x111120c070f201c050601050613030c06020c0a0e040201120903020f06010b03070909110306151c0212010b0c060601030e010603051507021e0309090424060e010828110310 75
    0x907691030000000381046000c00d2076504402e00c01d90f10717a03581d42e0042c05001d1240a0101d0f20030141274504802d03d0007550400c1401c854699514000f80d115602003103098015443c0840c003041a081003000302e801181d06a40e1454103403072151001d4002d042189048046000d054005480c060080101d14081c010074104a580c90502c844d02030102c0390b00340d100346442424100d504a801d0f42400c2900d43c80002507841810030050603558049511900c10342180300c221261100071140740ba0760150000108a207401c00060340c84003441e10783d0340110403076a0a980e200c200055000e502c030340c110f041c02c3c014420012500e0f94807591380d02d0900d03d4550b00c40c8011202c900402418a9041040011000315040c100b100490902882030b02c2c0c0c0f01c0e01e031059028142480108080052044500042468007120180904007020ba1500503040500c1044840c0d1400000402c5030740c0082031070849025091030315030110028000400d0035000c960000e032840c2c0103c2121b59020380341808400011040d1810020b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 908769343 1250 908768093 908768153
    0x6020d060302030318120d020a0f02010917010e100218010e040209040c020a1e081e0f03010303030b01080f0112020906030a02040203040813060e060a11100e0c01020111120c070f 78
    0x40300c0104054a012900c0d1f021400b000401c640100d40c00e224150000c15203201e5421500050740d040e1307034542c011500d030f5050141050b12284190f0017842c0416030a02600d00c0c0c00754813000c002c16030107074a022041282045030081190341c00b60140c04942c400180015041c05000000076040703640340c241150158100b283d03040d0411900c52600d4602041c80c1580c06103840c01519111518002d00306500810754481031141890342c0050281d07010240140016952581c50346801005071201911140c0851000e802241501c1c0c00c20102c9416104100740c103a50304051707502007120310500600031076054061045031101580722400194070643c0150f0020f6941c031000c110003128510181d2000341000080130b031000490340d400088810130b401c0e070310b0080c03501e505e1484014100217840e50b4503034003249480b04404070309030302107002103c10009030020000003403d5080c5100c01e11400a03e100b9003100d0304001545400e402d0041c0107050700038140000794a08690701e048001c0c403912499280c84502070890 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 908770593 1250 908769343 908769349
    0x10030b01030e01060803041e0f03290f15190e0103121103070b04050f060712240302040203071725050c1005060105130e01050f0a060c06020d060302030318 68
    0xb84901142c0d4600800610749070442c0d0540728081d13402101c040c0403090b01d1004040d00700d880044060107404c0c80940c026592494802d0003582d4807420018a10240703081c440181010140e054400c4e02155125040e6541b4880780315282c80040309201c0d400020700070480610100942d10501520400408401a50550070108480302900410100300b1110305e4840303038442000b00540da9025406031906038103840f44d2a000e03080184034000342805100300c0042110302d0303500150342c082c10f610401e4208405282d400310102d155645000391111082a04000c00060900d5402903511a01620300340301c003100400040c6c0c072610420307200065840304508006040038140720369035a0500082c10180d00e00f52500680039100c6030107242035241d0554a50001b03240343d0148007210101821801040c62494440c071004810b0102070051030700644001101e640e0500700601080182d6240d41c4684010b40b502c3d64401000e035020181d4050303940e44560300040162800c001070305080381400241c0180c2943c2c6818 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 908771843 1250 908770593 908770601
    0x30c010f060e07020a023a020906040c02030f03070512010306090c0905150907030605040212040c0f060507080307020703020604142b020f0f030303071805090103031e0201060510030b0103 82
    0x704115049120b4140281e0940005808980036415070b1407e00800240310b00ba8100304c10040a445440c0d081400c040b5040d00480e0f012987c0c9100310303005003040d2100b6081c00304480d0900b40c2d000250f48100541c44810492001441e80f0a1107071521390710f4403103141d42042411038281e004944c1c050300c07854002c0802072000e009902038000000100501d2400090341c003d0b1580342010940a03101603404240c0c0c82c0e119802c078802415010308155921044517030f010005003400c443c144d400d00d441c4140480e500581d149040b08990403030383c0d014203200403074460351225400602008103621074008004016114840034000600e04980b075440031104140901c4002e000769003501a04075074040d44d244201062500c42107076140c040d01c4030a144403900000c50f07490b0007405007865140c440402000741080d0300c04900000040007000808130940d4440c28000964001c1c00000d0106040f90201d01140c200b0601c1d0040c101207520000c603e403940d68011402d4010810701701c00000b501d030070f20002c0325601806 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 908773093 1250 908771843 908771849
    0x80a0803090319050c012004090f0e1b0a05060f25020d032006010b0d020d0b090109060819030504060e06070f03180830040b132402060105060309030408030c010f06 72
    0x30440c06001e504910307c1c002071240d80a074500240d6503140c8a400c40106a00102a82c00214100c4047d205603142c808008002c001445209001262010980d41484416a07040610320300d00c3c11b04103080b801c4820803042b481c9211010b501408031554004da070701c003104904100e00a0312100c050070041d0014548069400e81105090ba01c00e10040141c04021022140e980742480030068840e94094000c070040c101403134855a012102500220303108802782e01610403104604116407550200013080d800405202d000640816018042040080d004076242503150f04018480303407034941c5903907602184483c0100c050b070001c2d05c18520240041407280030403010b8406031004108444d11103540c5404e05a0010080d48082d0544442ca403104400c03606841c060b00381c1425150300c4450410881c6541c40301d9100b07182c07422015a0300720410281d0000000a00012a030140c141d40e030801041c80740c2a400074000300b6081c40108000214450184003504c0c0320014000003261100d90301c24004140c0346a60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 908774343 1250 908773093 908773121
    0x63303080f1605030a39150b03011a0102010b150301090b18090c0307062d0903050d0c0b070309050613080c01061d0a05091903030b2710080a0803090319050c01 70
    0xa80e251b1000e01340c00c58108089a40711070311b10301500d6010038480c041c0040846180d05582024000c41c4d909100b0740400c02142001c3e4002c000030751001d07080007100c54003004410340401d4100018001207a954019108800000c0c01c80f0020801a00181c404480211040c881c030b078105036401003440c42d043c48204c00914803883c0c60b030910701381040c2110042d00800701c02003c0100c05004442068001c252080c000c0d41c00c0070949919201c1e81c0030107412002030030001c032900003400001501d0310f8081e105460200c0e4110005100c195181100580b071000e05007419951031400344a5000c1c114424010310001d1f03c030800c080803e20044489040d40d01c40054180c80d034050411040121140d80010040020140c09c0c001843c00c00c81d9040550091444507107803a0844824020040e408008040c41485102e00d8807e0402e503079600b90764006130080a00501a50750001c15148000c0b0380380300043c54112109900380da01d082c14100d01130300c035408081c0d2050045480801d00c001089002c0c85a00503208034a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 908775593 1250 908774343 908774417
    0x2071719050c0c010c2603010e091603030807030f05010801020a020609010b030604021c060212180706051c060806040302070302090702061e0a09063303080f1605030a 73
    0x700705943e150703190540340700e040004d100076142c00d1002d5441e08010f46206482d40211081440441d180f19600c2409580000310010010504003100016036055812a407540303481840d0940c1e40407104408054600d104042d110358001c0b00c007004174424a80240320341c500059444580c03c80280c28000014103121050349042c040c0c0c10a51004144142e105604440c140001550360380c00c010070644a00c0007400040c804625200c075002034040607070081c1c075100c10100034643c1500305c3c6641e90f0751500910002070002d001e40e40c0d8940e000c4c4c54004d14145c00321400300d4031a0722008014a03000040341c040c0c0040c1d0264404005504012032400d41102c103c2c0f000c1d00c982e14210000090742c009042c0c3c0c0428055070368001030507681031940440e034003581c064000c0c490512041191079003060710111824160a58240b5030b18040000101d52040700e0b44400c005040194007040f8150541004810030600e80441041c640010024801400c1d1f4407210340b903540500d07a81d5000c20ba01c0900c00300031080d02e41c500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 908776843 1250 908775593 908775607
    0x306050d1e14010e0a0308221e0618060b12032b050906180d08060d02030a2a12020306060f040e01150302031506010504180207171905 59
    0x40a0124510105288080000d0700c1292414001624141c050440b065103007008401e010100801c10340c08582c00307507481468580340c407001d55002c00c42d001200796240c803840180f80000b807942c0e00791401003881101c400d0100541512800191840c204000305110207071104c200420109100c1c0d5000c0e40000d86503e00c20300032180321142e40b482140e50b144422401d06515084a030514401c22403070041c2d0103024845414103142e00c9595000079181101100d141214002400c800051040210700243e81c0b152201c3d203840040c810100003914091b078140c00b03081340074400304004011844000640d0002e61600342c1d0051840d400c100041d40000440109000212001d6940000c1082d00b01e41c084900c00c141942440000b4020200320070382030b000d9400c00400320710700e540030580d01040300d0003581074860760100315102c050700c034404440d000e010071014002403002c9400e440500d0355a80003400b0040c9000c81503210803945041440915690480c0043c009108502544030044040c0b1241007140c14807034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 908778093 1250 908776843 908776853
    0x601030c0609060903030e13020d1e021827090d090501140f0a030e070603020901021e07061202070b10061101110307050c031314190b09010c11100e010306050d 70
    0x7013188400780420100e104044030560340c03400d40c440c1c082c6d0700e8202150344210350b40e510000b8102500d103143c0c90702020085013002179514002c4031034030381c0c00c5211151030f000030000b00100d085059040c512441e03540d00c90304160507208501c103401641c001009140070085428014072071920340e04210304004480c0034503200e80c42128141e44400e184a4201915581e0100085005108040601c1ea0364407581c500018804d070107074014480d6640030b0703080d070341042d500d0000d0600b284100c1030290942e40c0320807000c204140c4901da0282c01c00e580307024050701d001003c3c0c80d880d1660b0019504011820319000b42041080e070011100c3c070217001d8003402070166502c9440125101c0c0002810503050206c0000c04003a194020700c220348882090b0030b1b09070001c0d9165004031104000c8401124010400241d0080e80b0200181401781210303101e000840c5030001490044486042500c0103e03000a41708a401050f6a034000f011868002181d440c4201141d1001c00141611255413200d40551240340180d000310f2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 908779343 1250 908778093 908778107
    0x4090e331003050a080f19080a060e1e040515010f060906020616080a15140f09192705060702010c0f0504090903020a0506041b06110c010e0103110c0601030c060906 72
    0x54100007025100c1140300301b900b845105520001c105d0b054108542010745800504d0075000d140e16040c204002c54071030b0f54540c92001c0c260740c0c07503500001582c0c80c034800c4138003078207280c0d40a40704c0d00544085075040543d01480ca01d0a13088101282d619800621060f980031094000622541c4000c15050810b0361803a002c0f40d26003080d0a00b00010040041c90783c0d180341d004500c00802c0e00075580c844035234600003821500da140350240c1c81503440d2340445403145001e1150754060807407140980e1010340c0341031081e07004281d03000c1e824050614a010b00e461002c903644032500c0c59030041014240626048400908445401e20040e041c046980f074401019903125054078141c07103240b240040d101e0054101a4031302000594010041e104000801040014101c60600c0e00031440800300d140301d854500c07d80d0b000f50114041c2ca210350002484030215031050110448501041c100007501111640c482030460b8000b08200005034000310041080100000003440146844e01d0111a0740d420548014000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 908780593 1250 908779343 908779363
    0x40203062508100f230303070209070e01030b13020a120c0c02011202250c1a09041e0c030911030a0b04170d020a09030b090705010504090e33100305 65
    0x2900c0b100107101c841c3c0d44116440a40400b50000f410700f581d50f000101d8078403401c41642d500b001c5000c142c104600300001542d0049078000d100141c01c2c5d0303407141d08448246102ca0050f0405d91581894400d90326140d1507480340024410300560740307500405000d480030600210030b904a0b4600380e8540c6007582d004500480550b42480d001590740c0c0000701c04000380c003c1091941c04040050b0115003c1944140300952043c894440b050280b80d86602869115600900da100d41103010041c040e464a0541e11098034124062544410140490000011140d8071000400820750f214a0b4805004404004081c4141d04400420b00b854003945c0c2c2002c2100050700c01800c03540b440643d403810300100c1e001c0e6841e00f2242481151105100e141c000c2c51201c07144001e176a405440800320b800d995000c1130a0081c0c031410385859190a1a00345d0010045c90380e21049852402500d50459400c11184030301038221125060105201072080c01c0b00440d120301030000c45500c03004507001c000040d03021500340c0c00707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 908781843 1250 908780593 908780597
    0x108060d051b060d050906190603030203040b0a051308010606030b1903030804020612100f170601060509010507020310020405031615050a1b0308090f162c0c030402030625 75
    0x100b070450000c2000d60184003d52400d5a09082c00c10074040340004603036200300c9400c8a11000203e0416055084958900004e401600200400d104041400c002040c0c084da092034914600000f1200f4900004601d821804c4140d440313440c10131000758540100960080d01700c0e5000e0300214001303088044a02c1d07500c0010240581c03000041c0c1990354240a540d51000c07400c805c04401c1c54032170b4410520101d02e0190842d5002c1c0320343c001ca69002c09031120340700c03110040002c00d0564284141074445400286807141001810850400107850602035031044145585015841310b0801c000c06007414450341941c18405001d007070402408885030801c0071040301c682009035888019200440744003207070032110001c03042d22540000400da40003498030302c610709020a07242d00640c204900c0e521004442220460801c0007101400000056814111414001c100700510f005100c480b4083c4003a084519440e40722001c02007005504040c0f0075582c1c0300d03950030b403c5501521000080b807003101005400400f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 908783093 1250 908781843 908781883
    0xa06170303040b2802070b24010c050f030f07060f09030c0b130f0b1807141e03190c0b0703050301210204050a0905010b0f030d080a2403020108060d05 66
    0x8641d54401c185101801407110740d50400307043e04104d40b0b020b5405840e088035024001000240420003250b60300051007003482e00d042c0e44070b0140c001150385074000070040d601401841500c1e04150010000ac200240c070001500d0b0b15881e4604125007210780c07000107207a8141c1401800c8c00000d0703128001317424490b40b12507110000d807262501d0400341c0883c04802000800c45440030002c0c0840c0c400c0c46841140c3d80c80d1008401400d00e03103007580341c030441c1c03040100491a21221403c5480c1429100c04022214048010f0103030410001901d4400e605a900d400800240c1002c42804501c214600c090041c681c5014680040e80ea03006020344014402d00303007a096504c0f41c00c0e071582072100348080000d40041083c002820040c0000c070081460a20455481d80390050101540c20680040d0303142e2000140a000170014110064440d50310007071442c0710351b594401ca200c0c003c40314be0705c1e03542118400b9400d111041e415071002402c0d141000d0138140c45103050010b002d00055000400300e03400e80a500c1410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 908784343 1250 908783093 908783101
    0xc2229070b010e040609020901030f0b0a0603021c050c030106030311160f05121005040303021803060f04020108040203160602071d091e0a020901090c23030f04020a030213050a06170303040b 83
    0x240042c400311b80001e510aa6001c000030a000030314400000a130301800311449540c6034440100110740c07462000039000003110000f500c40c04001d024145a080c00794040d00d01050222001a003100d075250400c070007040c0c042ca051080301c0000c0101c0352400c8840c8071440d4515007000007900b840000d51152034495000d000500540c2c0100b4040d10650100c0c1050600c2035042c6841d0150183d0030070403000b6800101c92115055078900004d0b0580600a0031b402e100641c1c60b2074004444861006000380c1e0184964060f00c030100800354401c02c0140344580c0904006070600402c2100c664608600701e88a8000c40300340482c0c074001244002c41c002c0705200c4000449a0502240d0525030b02d404007940c030003441c400001d02d0344510341060000301106d0351120341b204010351012040e582d0100d000521804140005034100c001c011403a030304540010000500c5590780d034000781c0880680707052100100d44480510000d010300c0e0040e03034064003e181f04802031868001400323a45c4d000080c405058842c000c0049 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 908785593 1250 908784343 908784353
    0x8011406030c0433022109031218010801061e2d1d040c0c240c02010c030606080c0a081b0406180e0f0c2229070b010e04 53
    0x102c00506040c010712950000d04441d0000c1400f413500315828070b0000d1001203420520229600d00ca08203006c6030304041c490003c0e001c210719001001c103590544185021402a4003030b0030050900412000202112043c00c100010b01c10001a44071205201059034041d100080c541e580400d2007036680713032500e88045018030502d400c0b80540c07540159012342e850441443d03607014104100c1048403049401030043c481040c0011a0240c15a03000001e005192032310003d0700780410030740088107220b49510089c1210700c003007049460302011a00580c0d500c01c4001243e9806014080c02010b070b600307004011b0300c0c2829490710503104548021080000202c001801c4184039403d94000300781e1690010303140d6480d00400360941c1c440c08088916800c2510000400400c0c18505904c910768107243c189181c2c840441e200c01d1070708401e070907402100501e8164000e029401d200013000380800301e401040300b80f45550b00b40d42c0a03595034030003002041c2007220201041841e11480d0441c2c4c0040c0c141c6074242d03120700700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 908786843 1250 908785593 908785597
    0x8060603060d02040509031215031e010213060c0b06010f0206070f03060f030b040519020f0402030c1c06060306140a030b1012080d1b021c03020c1903030c08011406030c 74
    0x25407003890407046c071136904000006807180c800003488050058981c03103003078005801015070710380c0c0c50340c020301d0100f003078050f60450700b08400c04040c000b5050040c80100c3c01d0542d02c079034002d0000901d2010500b0240141c0c48141d0740c01610030b003001c40c115000900003d444030001841d484c24003807154410303510544241d00032001480d00480c035400d2203440c1e242c50300c001401564141c0e12485802070298014080c11400291594000c5c55101555603210600010b50001816420074400a00028196500120a03640789080c0400000b800c18144030b409011601e1540040c081c04042100a010b0782d01c40113022802c2c0ca420102062450f6144815180324074080d0b0007064454125014440810000c1c001801048c440c051080c401d050368403449000c0d82c5024007042c1c00580c0700114002860f44401690190019149009454600d00b900001c0c03038220003c140342c984c81c801e400d0400c1410340c144242050420a498600807551401c2a62001085a0348409218160000100b0328010300401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 908788093 1250 908786843 908786869
    0xc0318081b030403060b09071d0415050301050a0605030f0a020f0906220209010e090603060414010b1e131b0f2a030f080912091912030e03010501060806060306 70
    0x1143c0d5900c1d01c91501c040500000340b8901d0007004501c2c04550a03502520100801414030100704401c070301c104080001401182c4091481180f801c01c01141c561028000c66108486281012a80c146440181880e1049850000e0b41d80d800c11401c48006955003612481000d0044a5070401a00c0c0d140000303011410302c2010945c81000c1d540c07540f40007401078001d040801c00c00d0301c5040640840d0020b00014450841700c0ea54541c120000040000345040030460101d14200c0c00040d04044101c007041d0004d84909885a082401d1440b02c8842c0c070340010b1100c81901588001d00c090801c001041180343d80308481c00062107600e0b441141030a204404007508084d9101000c45000040c03846028481440b85054000034412a4881101d1340621120b5004a01c400014050358803140100c544a030002e0004e2503000044503040d1303a4070150b032134603100a003084000c03555001c0501d24028244110b0014654066410708004020350350700702c070a4030350086041e280700f50390780d80d004009004102c50007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 908789343 1250 908788093 908788147
    0xa0522020f0402070c031707030807030e160f03050615100c080915040608070c05060106200f03040f080a0f1211060f061216170a05061302040c031808 66
    0x411240140720b16a140502182e0249011f2407070325503d8641c1f41c45512031154064003240c4e0880114401074880d0b0f0003910044421b03000e07034180300942070101942e24007603880096040320b03c401c00e09c1800030074480036410030303000c41000c090a10100080b03038000b10001000d80604c21105040c5080c01140c6044410794440101031110b000f5140102c013049400c5400390030005507900001511040c069619849034541000c010038131a0710b008000c07110070f0f00c21465401190750415040e0480d40d0108001c01c203c1030500e014646460070105180c00401c800d40c05200268880310072800850604110840c406401c8180fa04800c00d101400366150b031400070019001e4401d80d0100401c040340c00c40d0481c0243e0b82110b440324059507180e51607582d8001c81c411580004000801000740307032103024a443c1001d000106803440b14a040d120030f41000c004032540340c0d03031040040740f50f02149480d00c29400400130380d0178200002000034544c040b03820b620482c0100031800004003e1030900d40f840100307484031411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 908790593 1250 908789343 908789347
    0x103020a02150a0906050a09031409030111030c1206010f0f050a110a05010501140117010e0a0e03070501051501030501030302031903110a090e130305180a030609030f080a0522020f0402 81
    0x1441d09001400015070941d40c0903d0071000c221f99500070f0141d550711603010744e5400b510b0f0600c00000007440d0b112f00c3e6682c2c0e040d0750326075002e009280342c00c0145115007602072049445240856000010050050019042080600c1c40080c42500810248042c09452611544032407001c0c0301a913140000c910002c855114500e14a0200302054108074140c81c462407600401c00d0700480151810201c503103050703c0000d064001805004686110194008098500895120701404031075055034041e50042e64540d44440401004170520180784008010a213003c2280b5803441c2c82c02520ad0144030712071009244c0004e030070f000c40e038030035000030f14031203080c0c01829a81c40c1c903a035025040720381d00e00c40d29041f40141c10008084dc64005c0b0568400c5030107840705441d0944429003070b101c0781002d25140b80d11440c1e886002c0049407207803040c004068801c1d00c8084046200c1c0202402c6004001e007682040341c10023041101e4080e0340e0220480c803400410071018085040e10000311103014171013031690020305c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 908791843 1250 908790593 908790601
    0xb0405030705010f0b18040215040f030627122c011b170307030e0d0e0933030a081305130207080301060507021c051b0108090c0103020a0215 62
    0x8401040414802c8000700400d0a110500038180d81040d09000d5200400c2d40941d036080700341e5000154070a00c02007407140881c0c00081c0381c1d00d090f0010b400a48401d80c0c400c0d428010000544101c410b9000b00003c0c80c031508030303181c406140e01c0c1000302004050318100d0441130500c3d80641080e114200503e07500440c408010003007495818034641c2e69500046030109441140c038a0031005840c203d030066411907000c100001840840d6202078071010816664003404100b40805028409174000e041d0384280650504e1005c111f05000d0180040595106440c410320010441408442d40d145408420440c070030403100000c5e080180502001d41060000958000c056500a843d04203807202224051001c21045910400300d0103075100040822108100500445001e00090244030340f000700004242542c510399144082c190000886496214010440309201205014103200fa000c0ca03143c486440d081c0c44c0700b40d68448807002103045c1640000c14822047c42400807250a00f140c151406403410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 908793093 1250 908791843 908791853
    0x100e01050901110c030f220f030327090c05071a0403081006080f04020607050f010902010311120115260a0c0905061e04091805060c040e0a0902030a0b04 67
    0xc41294503403115440e043e89441d0180c2c030282902d1000c240b110085041c54204500c0418591100701d10034070b07081041d01030100010841c01c801014003c200c1c681040705240d0710b000342500080e02e040c4e00400c08041d141002e90f12070865a08201c403800030000c00c030003e12210640302441101e501a02c00f0101d40400000c050101c81c402c1d02132480b941d11032801e0790f110110702d151980035010343c1c000280e0b15400709860410841019812a00043c070062400d0056500d9524016070040055003594680c0001429582c140c807400c103c01c803440802500e0003000694600c8608014061203071504141d03503000085601c83c40c05081520700ea51800350500d00c01d0034040e4420407084881c44134140c01e00c68110a0300348a0110b09003101c3c03014105138144985d20700349000a01440341d0f80b01c0c0d1840700b0301001906001034001d210f5428078001249401070340500b0329500f00f07500101805000002080308211381030105c0d0034681d0022150000044044051000078104040c408014000c4e4103a2800d0006100f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 908794343 1250 908793093 908793101
    0x40b060d05010e0c070f030309050c040c0e030c0a080c0607150c09080607090e07080a0908041e0801050606120a0608100b030d0c020901050d15090804080d1718100e01 73
    0x48956081d02c2c0207950b58131455420788110130000309904031142c800d40c00a03000f5000040c0f280d03c94000c3d54412400500400d003210034045136a00003440105581605040c18820031550000a0f42e03d00301c81f0b42821402c590b100b1011001c41d01a00000a00c0020300243c440401e020fa60743c0001070110b00040140140031a150380105c0c1d04d103018540c04102c2490040840400312800803c7c001c0d42e56544d140300b5079a45400410080066072109810000100c4210092001c4c10040d0b40406105c0185480c04042d207a29030490304060b07141c5414000c1998803001692070342c8800c1d0910404955490304000045c158030b81c03002c90035206180050914204070b07040340320343c0d50040d0101c408200380140e048841005c03d110187d00080c0c20001400300707040000f000c40f20b06010b5060342c0082e8007600101801c8503c8000190303407a4002107010f00c0401003d0200202a1415140c2240714651050302952190303005840e040b2501121655802250000c1c0010b1007200750411041103e0f5800342c086038003070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 908795593 1250 908794343 908794349
    0x307050106030b221e140d1403190b061306020a060e06130201140717040608180c13060e1e0c040602100513050a051f02070f060b040b060d0501 63
    0x4950140000ea52500d42c0400c254421011082040c4c80341640d031186518034200c41d191400456010814101103010111b0300308940390f62900618070709800380d030300801c0380419070702400420104009111056204100040c07080b50403200020f005100c080015010f84100d0054000030301d07040d40c0004859401250003001c66005030428400d2760040c1d02415119002240c4443d0034031031488100700507510501c545030920200c05200e0340b6044450716442e00d8000b484035100e000c000e00003028041550f000c141c1c0d5800100220441e59030a04d00f504a42d1511a04004180600101103002c440340405411150040011805030002400c1140b003c45200d0351050200c0c1c0c102102002240206d6868000c98045402c182c0c05000c00000b126840c0d0042c003409880701400490302c4150b940401d20900400091a100700028244103000c0c2d40080036826520380740c55107861040c0207410104000b20444200241c1c003d40005001d8840d8000a00808040c0b807410b800c1480460310f043c64400c075074841416 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 908796843 1250 908795593 908795603
    0x40602030105044d07051c0207440d020705125206030501060e0603090f0f010903080903070f0f1a07200c031b040905030705010603 58
    0x252840440c29441072481d00001401c010815201610440441d2203c0f250040e103004d200c840e8402940b03400902c183c102803419a0035412003110039206080265001d00d215020340050442140b410081846207240005101d2380c480360b020800d0381401d5802250000a1000c10000d48400c11304141c0ca81d031500c50060580c00340c420f00b140843d5030301d4243c0d601c84506640000034204020448a10f8085901c01ca00401c050074464046410300040c3c0c0e5a2110211180125500721030b440980c034508991003a0702041c1032500d050014080c007980100505684101591803582e40d89451002c2840c20000c00d8450310a030180074044904441c06400001041c0c1c0a0341e10a01d191301c6841e01e040e101c0c172031540000c040a0000c0001d0000404004544100d90f010715011032202c2a003500210801d82c04460650001e4a800c020f95075011281c15000041490340004006802c0d1902c00b107075455003100341000520240c010800c410f9a5160004400700350b00c00c05490300e5040307030f00c0c04c24040e202078002244c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 908798093 1250 908796843 908796851
    0x1210021813050f0a0e070801110703120e0d0e1f0509030d181403030f070305030a050112030c0803090109080f070c06020f100207020a27110702030c151204060203010504 74
    0x59003401038007849000d8400c440001c0a0f039240c00829800410f189104034009020345080000d0340c0200b0310940d059840e0204020707a8800e0940f03030007041c100c1401d0201440e0351405003440c030980400100300140740c82c5814074543c130381c86000c00121000292908403200216064020036103541c054050005010203034102ea40021030070406036410b0550fa8030700c00400c41015420401c4485041c0d0506000c1d00140075a071502e112203c52403071a501c41c45099001c194000248440e0007510f22846006149104442044040c1580d00601d124405240074101c040007102155580100b940010b400503440154a9a80d0503e00c20b0403507103070481c00060b54000090040010300c035001044480d50213401401510041040b902d00700300035001058182c0c0c120740c0315800843c92001c0040d0010140702c042412444100c0ca40c4090b0054841d6040c0420110344180149001a180083c016883d444221090352007489601c005520703900030108102c00c000c41c54014041803040f46c2d801107040e00ca099030284 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 908799343 1250 908798093 908798119
    0x309030e03010204120b04210810050d0b0613150602010f1d061303020c101d0f0105091e060a0f081f03060509070b0406020106081501050f12100218 65
    0x1d8201d01135840740b100c0c80c11848101e000011401079400381e2107407048100903001c00d0180c2c0090740c2a441001d00381b000c00e4241d414440740c0b0394044074440042c90b040b039171403500340180d65400305403980141c40a4040c1d40f0b5640485040c0d04503400083c0128103010360b0b200d015a544000070f0182000c1c4c1c044856051a18428181c02091205045008050b400042078661500e4210140030b08040406404501400d01e0b10f030035540e54005c0c1d0320702c0c1401c02c0e5540c10000b0310340c44128031001200840b19201d0011051000b0705a600314003030700e2405104450079003c0c4048024148011042c02c40742a9101d41c00280c8401900d4000a402034818003c5d910266946d035000a103e046112008603d2011080806c003000002c8132608065070185d100c005503841c0c0d560701c000300d80b0280c1294001001507512503c00f80703c120300421008036030281740b0700e8607001075250801284004152555032801140000d40d45241c42034200110304062814040441d42c03803110070f00040803241c0e640d01c01846408104008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 908800593 1250 908799343 908799349
    0x105070c0801020d2301030b0f0a0902180105090a060e010531090b01080102030c070b22051b0f100540050607350301030501020904050c0a0504060f030e06070309030e 73
    0x5d4181c81c0e01c00b51001071911b4011841c065500d00500e031000a81e00e80c10200e0058803000803a00800503500008000e9504040800a40e40c1c002071200903101c1c80c1140400c040c40b4070700116070440d24165098101012030406200e61910031240c03a4034490103504540d4030060703c96101c02481401103480002c0c0d641c035100c2c010b0030303440b00b900c0310050040c09020100c0880c0303040e441c0390303005101c0c8520b00080c0b48540300c20700c0b05074454402c10f64450700b009496114030820200054803503081150b4842c1d8201d103101c0007500514007c3c0c441c42c01c01030086220070ba00212410030004d840c520707140a50700710f40d0110312015414540304041d034625201c00380c009a9410003d003910f207031541c4200c80394400060300800031030b0800c48201c0305408888400c1c2a807081800e10000f180694041c1001507591300030b81007440156030002d06080c100b2082041400010f55100c0c0c1034609031151490306201c0c114179100c0c01c83c040c280f60100a4560702405080c00a0560185d000d95511403081d04c60102d007002034410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 908801843 1250 908800593 908800661
    0x1b01031b090306050a0f05041406012705070e030a060b010315060c021e1309050115050604090e070b040b070b0a060b0406111c09030317150105070c0801020d 69
    0x650300419201071080c40042c1d0309070481548607481c4d0b800000c0c242d0030f090040041da0029201a50704200c00c2e46541d960903000d218aa0240c89a9901c1601c20316200780c0f86901c560001080404440e036840205180f144a00b4503942102030040c1180c00240032428407200a01c030f80710071140400e19110f00c50b4450300d819a809e0301124400d45070f019080e8429024440e00c510b008030700f03400b0050105140141aa550381c0104010b007005078000030500d09628003a4210342d07a94441142104864070304110990f180b5044505640b00035401080351030050a0032880d000c0c45402124100102213404a9084040000350400300d0260300e06841035207542684034201c0d0310300c0c050100060000c00082c045107006480b0758819114031800c8441c280c2d440100759171b00d54810811358001540400d0204107140e401310030241400c50b0501068401c2c1024000c07001c0c01038403000a0ba05201000c5440d0341803001c0c04040700004c1090f4002995201041c510700307401080028038031200010044400d0810000c00c00f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 908803093 1250 908801843 908801891
    0x3040e0a05070f050c0c1003020c060c0c0316050a02031f15030c1415040311010212130320090406060819020a06180807090504060b040b0f060306040e1b0103 69
    0x2c480f014a481410100d910740c0c481c032a08042d522440348000c50584490300c100002c400381d0b550041e114400c840303030181420005041d0684501040c0945500841c001c0110303000c508140a075150414802d2078040c2c140458290040e525005413840c0f032104400e0030704400c1c1c65800300d00e02008038103200c45803610903202601002d00586414901400583c4441180d88520803000700008138107009244801000d03846a00107e80708071003803640841e1544c04001000307680400c0745089040c007608546802e0207078510700c005402e20383d8145400f00b641500c0640d001c04094040c02c200c03601d24140c2017104c083c0c09584102c1d402840360703003900010340000c0c22015104a90007400c0004d003a280c164121012815103000c15842d11282c44005166441040f504000740908040840c1c1403516041c040b040b5400b03c00110b0140f41060400404c41e510402000c5684804568288d100d480f030303038003040050003040c0e5164468400d0034080d10a4034400c5d11222804002660184882c5281c040d1041c0d074281c0400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 908804343 1250 908803093 908803097
    0x1810020618150408070203012d0209120105181e060c0c011104060c0201081311130f02040303210e031903020712050306010e0306061806041d03040e0a0507 68
    0x301058000c451082000014462802103801c00c40a4a4400040d03210542d01110a80d900180c80801c41c1401c0c0184081030140e0340b81042c41c400352403020300030404143c80002d079140c0c0c001002200c681d66034142e25120380d0600000c0041c0d107000da0031000c4080d94020f80e00a144112000500c680800d0038096800b40384010181186890b21f48882c3c1c080d0700055170001040d500d8000c0390101488400c00307000146215034410f5407458507400090f107411000303460860025105807501010441003070030582102c03001c0e40c074100600925032042c0010060540e408140a000042c000203040e031104001e64400010602400c140c240301090000311244070034942400d030014080c00500401c01c652240618219050162038042207030384a01002104040310000b003a07003c001e1011a580c4040c901e01d40d40c206400034400b5061500c0018108800800003036090844840056195207858103c892164540c00108000003601912640c40e50850701924260300b40400c00076001303000501595010300025 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 908805593 1250 908804343 908804353
    0x30304050303070b040c27060605030402011706040f0614030c0303120403180504060e010e09152d01060f1106040c030201080402220c0207080a0203030904230408181002 74
    0x507540f0349001c03000080c41651412440b09000865100210012103404092000801440c04440c0181f08482c01c5403c00c6080041c28010400180d0b00310800c3e0000581c42c0311912410790700d138030009000d449800e00554030103042540008104401214001c42407004500b47d03402000164140355680c028280a10719103030415011501290082d42d4141c0694140700c08410b5194984021606603400c5a000064441240340100304813640c3d007c0c041c0d001145003014020407039000c602c48440401c081c0c1440711031a040010640c04014140d10320701000c1050494402c00c0d80d5030782e0042c00740c948050941c40403880c48500c0c21a0305c6400300701c10748102d90001840b0005401c40d001100c83c5107000f80100e82141207010b00325414038003026503809200380d40001007205401c60000034208034056101265980c8040e000d200180c2d00401600d5642006a030700083c1c840c40d56140c240c0400c54500d0814103585004140414048118005d1441d60f88404090a5103042c25040c0001034a80b240e0fa0340050b000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 908806843 1250 908805593 908805607
    0xc02030a0e0607170a1101021303020a0b1c020d09051c02010b06070c03030c0212101b23090117041209050625141609050f09063903090705030304050303 67
    0x9040103070845d1201032a04d4210385003108000e60072039000200501c0c0300b03001d4030820411460054440e80150901c44006810403107491507012903520000c5c40300072165004100e2840a4200394099040e090f00403080307518680c441d5401d10f640e501306c800c52000550800b088801c850a00340211413296510603800502c8500d582c800b11014a040d01c0102d1340114403503020001e91104020b25a020b03034521000044940d5503000044084044000e01403d0003000f680c07a8010030a001c00b40001910029081641d64a12100491301d0209000207005003104e40c10501003446404ca070340380007946003500c440c80f002d611402086514054000f00c0b00440d5000a00341d8400c0710001c41007440c031485807091484e28028201d6140c14181c08815a8000c0d0b41141000c109403403c0d4003869400c110b1324200b0b00d000b810070700741450300c1740c0d00109404016501c9600e00191400d440b041c010742d05298201001a40c032609230360f030342d0685c0107685003801031151000104880c0303400301c121000c03142c00900035803515038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 908808093 1250 908806843 908806883
    0x1106070807150f0f020903060105030606030304140d0f03020f1009020904110f0a0810050f0708010b031f06031d0105090c211c0f020609060a09150c02030a0e0607 71
    0x1007405105040b01e40c9640c0c1e03030f0941051600401420706100e000142e201d001e10780034545082c40c168003052007503029000303029251310040200d9050700c0c41d408810f83c0c80a5404041007942c014110000c15003c3d0980050040c1507010a079581240b0341c10043d103991500414800b02510007112010791f100e5440d0300400c0008040c0d10b002c0249880c043d000c0136001c1502400078111004550007401c50303801c1201e403c00e503030681e4454903070f11811628000d555801e0402c4000d06144050143c07a240040c0000400c060182d550304900c02074464404c1c0400454880d14014050300450680d44a0b00940300e04409510206010382407103900070b01d004007440340118040043d0b0310724190a41e00d602c00490120300c0102024055040c01d046600ca0800c001801402e000b003500c079010b5100c0c4c04541022003031100341d05010500c607400001c420320200e6512100d041c00c2d5004140842a510700c0b501c0c018130103201c180c000c40503024214554a40e0001c6c01410028801207205019008201000905802540135 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 908809343 1250 908808093 908808113
    0x501060e010617010620120309010b01210509031b160b07030f0f050903010204030804030c050d0312020901120e06090105011a07020402071e1a07050705461106070807 73
    0x41b04405541d0801c485800b41541040004144061b00c0c1c00000300b00b1041305002d000b0440600e17402e20740802503000901c0c09442c048040704400e071615481c2c60110b1141c03e0700300143d81d40c40707180880b01c0e1003541c0f2409101c0d50f60301043d5481c802d03014090350b000036a0041a000c0c0c074021501034844080701c14942c90215010f007900360740d100900005020100c1191000d1000c2d2016510071403c042d55282182031818440b40180d00451003844100c10200000c2e41c403014541c1c0860034140096110f400c03090041e156444103180381c0d85400d180582849a500c03000990340c1c018201d88000300200e90f00c1c5c2c40a01c9210720148904050300b401000038000608260303005110045c0a241d000c02040455400b460811285101c1500c0c1c40003113140303800f0461004502c40760004541d06085182682681e0f0307c82d250391703c144008041c102e64403200101140c000c5c0c04104c1c9400800d203081c44420394a0033212100c2c50f402019a42400010b1402903d4103050003265085504082c8883c00c2c820959a180c0d030398 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 908810593 1250 908809343 908809367
    0x170a0519120c02060108010e0304051804020a090f1d0303100311190b0705010c05040f0909060608030d0f0b0915090403050d0c090302032415120a0501060e0106170106 73
    0x841d814007212480704140c400c0e0541041c1d0b0340d02502d2594940108036095540325041115250010082000207540300c450840c1c030810400c0207003c1d00e035200c0c000100d954425034031034a8600e04110340c007184d8800c01e40c000c200441009a0045000320340c0d489081d580c0c00211069040d8a910702c6044c804500344461440002600070040000c060440080d078844a182c2e5200100a103000709d140d20403c2001c0c001c6140800c0985491401d1501d442e855080c9c1c1034052160a0b0816640c84003d000c0c09001d4101001a01207c001c40c1d41d02c00ca40301e130060041c10390b13900c0052a40d10b4003841e04220b1500100d500d0040c04005118500f4284a00402c40c481c040074100b03d05210013001401c100e0107031405000304011072034440020107861401450b0401c3c4001c00600e0189068507020303100c103035101c12081d400244022400480104400210b45005603c5800407407503c03400219004208054001da4142c40d507025042d51240d070f9440090740e040800c81d0010847c2c00d0b0840051009a10614042c440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 908811843 1250 908810593 908810597
    0x18030a050c16031412070506390418090c030803180d020606131401060e0f0411192d090302120a050c010507110910051c170a0519 57
    0x80b2042188070010300c0405600807500c0040c1c400350801d518800740a589001100c4419040c40c00c600341e030f1070f152204002001d03401c140d072414910302c0040300e1807070300803400c0158441002d01c0c02c80c0c600c280d90420703001071040400d01d01c07014034601114007545c0907000e0002c0d8050301102e006801c66440e9062900000c00564020482d1240b4a0240c0001c002598080a958001d0038050401e0350900c0842c00112844808580c24240c0c98560b0b00110280c40d41190781510301190200440d100081e58441d03002e142c00d0b8001d0810b108203c02d58100002800380380c110020020640418a9055804050407d9008840025600b00f840b102d0f0010112a040200918045621315100d600041c2c05070300d440c0708003441d6880300c030344002002400c01c0444181d030400d003481410a0721980e1010802c042c1c40a400780a8017503a0080f42c85810612050805494002c0084a1600104035040300000040406232500e00040c84011040708001045659580c183c1d65100e1402701041e90656132450946c0341801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 908812949 1106 908811843 908811853
    0x6130201021b0f120f01060902040f0501030905030d0207021305070c030815130e12190311041409281a0a0b190507050a0803010e18030a050c 62
    0x22016045421500034184681c0460a085c0c0282c8450020341c282200030482d4030b419000b8009840c51251700400741c03684e0700d00442c140c03a00ba8401400c1c0f038008002c0c110750b40041d074004221a6001400f03000b0404044144001152006c65074100015583d4064008050340071000365000f8024000580c0c00408450000e41101c0e002e842d20256546d90f1516901c0c0d2a40070b10402d81041149203000c3d4544e01d51000e240c1c00241002c1151002902e4402010340000d500400c3c0c1d401d882c0900444003203412990180000e100c00600902401103913021003000e2550020155449007014174000308949058104c10381010020341d20451044008132342c03d000c43d50b0a403080d500143d0200c0c18000c0f5916030b500d4180c80c184900c40e000740003806a48180c1041c8504400114100c4008c0c1c102626103a45201580b40340c40610390224200e074004001c000c00a0744200040c01c040b40c20841625 = true := by decide +kernel

theorem cover : BRFrame.Cov 908633093 908812949 := by
  have h0 := BRFrame.cov_init 908633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 908633093 ≤ n) (h2 : n < 908812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
