-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3647
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:50.731075+00:00
-- url     : https://prove2.me/submissions/cfba5779-c0eb-4ba4-98eb-d2998d7849dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 655755395 ≤ n < 655935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 655756645 1250 655755395 655755427
    0x903030e0609210609030a0f030e011104030b01090e0601050609090601020a052a03010501060c020d110934080114030a0f110901120c05040b061920010e0c010c1b0603090c050105 78
    0x51000905644031980cac040e102c0d003034110a03114003c2c0c1200b0359a90340e803031421000c40c2609120f558840c80c81e109405043e00008100c01c0d0403584010103150030700c8a0328040003203403040500910b06621501c141d00c0c00003402404514200d0031065200445030560f8510181d0b2102e071084458444e074540380051012942000c20b007480103805507610500f00c2550b103405401c00071307000749540e400340d0383c0c0e0100310210071250004416501c081ea03155100c28140e010049464090031080030102d5810001401502c0d80f551001c44246001812240780c00c0d49503c81d44013450b030322003003918048213842e1001c0960612280f90760051a960448000e465510b880d150b1410641d4010240319a0b192100007000b665074a058a00c5448039110350200c00d1003404001d081402140f85440c2907510340c90071182100d2042c0304420b20004510054044500800011100104490001ca40f0700440b8000c01541c81c00110208000e40419200000c2e10700d4039081207e00500381d540100e041040410002605081c561 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 655757895 1250 655756645 655756667
    0x30f060f0603091a090d120c08010302041109150d0c0206280905010c022a030a080703020114070206010302090604020307020c12030904090b010e0f0105010903030e0609210609030a 79
    0xc900020302001ca0310b80405241643c80051010800b44c8090006550003c80c01c4500f83c100742c2c442c140d034208008002400d464059031500c7c085071042d401007000d400d00ba00402c202c01029001036180c2080200090403490748001d141145850200d01d05d52341d0304c81d03442030000a0b05540002c0001e0700d481d441c100b00c551180019182890407514104d10b030b023043c60700b00001d02603020f03000740003e401070140295141b450340c001c0203500480d4885002105041c0007048090140940603295500300c5459000352030b0b1203080c0840440d9650400009001c5400310b07468050308040c4c0c0601402d502d580104001ea11000c1c0c9880e01c030341c0c810001e01000940010780400c8441c010341e51307142820801400ca90960081090603504103003070858900c10400810720070b46c140e0f05000d07602c500b56200c3c00c42c100032130304c0c090003107902082c9661300910200b405030201e41d542403c000c0a980c41c1409503c046604c480301c3c1d046903c01c07800c8002144150842c1400030350f80c030468231801103003130006070b40004058076508 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 655759145 1250 655757895 655757897
    0x20306012111010201060e0f0906070e01020703080702060702091009050901020a05030f070c0213020c0111120613090c0b09101716090305070e0414030702011205090f060c0901030f060f06 82
    0x200000c202c10b034000c0d004000144502c01001000b441c00c4a0000034006085070f10b14201e00401e800a900d4602800d080707803a5030030603402082d0090840d51080403c0e40a41c4040e03134003030030030b012000040c1c2e16100074500c1004111040c80040d0700d030054000a80f040600207840590041c080481c110358000140d036441754010510800c280c8038100b05841c2c900d10f07420080d40240c1d028401481e80f40c03e50b00181045a656002008105054600c0e00400d00038001481c000124000101c0d00600d8480c0840d40c08100040c0001110425541d8018040a1550041c400202d0105040c07800e86882224948464954140f449110405c100e07111400c54005000c0818551a6011007a07518030078902100a10741c403008a440082c8c6980004c4469941200c0441da0311070261401c50507001c2c040140c43c2c2e81c035410786505c10382c800301010b41c402031700d40103088000c980300d071007443c1140380c000300462406200e2503203d0346ea4403d0010001010349080b001011007607800c202081000c1500c0c4501901115a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 655760395 1250 655759145 655759163
    0x70e070e040b210f120405090705090310020d0b0f041b112409070f06020c060a050c1f0b121b0301060e04080a0f03183504030203060121 60
    0x40b8800040180e252108002c908040b0300d0180f600100d80010b001d00b00104540840e502c0302c1e10819038142621982c05201e0f0031101c0c050102e241d50f40220302402e0024002000da48414a110000b2000c0760000a9914211a00d4056424550a03d952041d482580c00c0d40c090040000c00e000a010302d00c9503030108010084410038414840301c00340041030240d4202d0f0704e4142c90170258006500b40441c141d80845903030152000002e40641c1e1000494112000b5402030400441502c0400040da0406c02013401800410400c600030340e00c0074845c071045650b6201382c081034400d00346e808038101d944411055006805410b40c1c9080681c0c00524010700e541412004d02240303000348042030140c080c55000142c0d0280364000d00040152600181503d080e840d901d4000340716003154101c0a941c0c0d0051a14651408403801d00c004c40c0f08280214035402046c031004004103c04200e0a1803842c100070040c2b031204012609100b1440d041c0b003002c0c018404074240c0d04814400105801c10826414002000004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 655761645 1250 655760395 655760411
    0x1a030601020d230409090c090b0a030609020d0605090d0905030706021911040203040b01080105060105070f030c0201090323011d03040b03090109050604060b040b120c010518040c03020c070e070e04 86
    0xc803a50b4003120f00740c550304080c0e80719651244a0310290500e0941140e035590200e00c04209285a8450140c80c04401441910a42d14645540004042500f0166041380042100c030300070407501e00a890048483c0d80051002201400c0d009208010940116101307400c1700000f0003c4941c000f0340201c0e0741440d000309a480c00c81d075262041c003c04455034403076000780c008410802440841c1f05524102d0702d420000340b0842e031b20f00c0c00444451281840041c60002881545070100c0c1c4142511410a441810400c56040e00d9407900300341d0420a49613110702d403408001c8400348500a001d9004290032203412410119210b002c103a03100e0149000322610381101100090500d0401d401441160380c100060300c00074185402c0c44030140110210395401581420b110311401d00b440880e02c03094203a918090003d0035250001103c10b03034800d15450210300c034684c1c08000c10381d1f50340c0702d481c240850079100181d490b1b5859415600b405090750210340c041d4480410000140e030009030f1550300b040c0886000031416 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 655762895 1250 655761645 655761677
    0x50c040801242105070906061b020a06050a030b12070f0512030a0c08070b0f061203070317090a05070806040b07051204110d050613210e120f06040308011a030601020d 73
    0x50f01c40500600144107045002a100304079a01400944e0306640d00c20011040840704e200c0d4544044030025040a040c91f41004214400d03400790409065a107000315013030100500051007544540200182a000108100005020310007070100400e01907540c4071802d888840201d4580c000c0000c103100380a6801e802604002c94001103035070165000d12100402d05050040d116000301c02c0319200d002d90302a4a481112a0307000082d074480c0e55050760f03a040740d0711240d0130101103400043c1209605d40305810100001070000d11486001e05800c0c001040c06242504051725481d901400312130502804100e84d0005180c07014a9551094100c030f2010103504034039020505014200703c016105c0d0080c8400e00041c101307411190700145004401841990346803010050358000704144040104641b040d08002134241107200c00170002d04001502c840c1e20b0b03404140c500b4134400b101c00700d00040c5500014820381910301420340d40b804200c402d1a05501c0c000340040e68800bc07919050061210802410b0070070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 655764145 1250 655762895 655762949
    0x1005060117070306051e06090f010311040b07210c08030c19020d110115090506040209041407020d0c15150915080606030a110607080d050c04080124 65
    0x50360700300300d03110224501140002c0081c01940103151244d40c40d2000c9180380d490b0302d212651090b4000340320074601203a94082200d4200d004508505041e00c603000004e0648200340500028a880965260740b06054074042d280c0d2004040e4480e01000140c139003034946036115540381141607000140799900c1c0c4070080744c001e1a0045909a0b80fa90f01c5214036000070301c3d8040340942c200c00f440c1d00d800f0841c0012441003802c0c1e40c0c480c0340c1c00011aa0b6400b040064910940000b178001c00080c7c00140341c086010b000c2829501d0f4150035110444400040c0541e842d4100084182c446062420032841d002e0342c0d80f2007803040c000e00743d030101f000c0e12000e0b00c0e0401c0140c00c00301e5006002242c3e0800041c1082d82c0c00c44009000d07403158508070300a010004000303040c0400c00300c1d60940d01100c640646080c4104205d0641c0240d039090700c5040302404003e580080f948101d5000e83d549024040c0c0351072a0052040c00d407004440145d850392441e07105d0340c1d2120451050710080d030300d010a0250500045072004402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 655765395 1250 655764145 655764167
    0x30a0902040204151b03021f06090603050607091a03010b07051005101d090706140d090308041103010e1e010905030d14010510020a030807052101170f10050601 70
    0x300c02c0c400140007941c498130300040b40e1554910b84400624a10800c0e40c02c040e800c10800280142c0c00100c50122801800c18001040e8056010001307070702d5456028200407545150070848071640540d00f446074054001000c440204a4010303940003003403410150b16000d010610443c102c0d500c010880100b04801031003070000383c4901c02c4003001245005600a100303440e240c0310740441c0002c0b00704040342e01c4030301e00d408034861589400244565884e0850445000340000c811245007501440030441c1c030040743c019150110301a41e645140c0c1e05203410720491034030300540c26900c00c2e85060480c5501c00d8000c1420032031005061030100da8148010a25070251904010090003170200041c01c031120300e1150f01814042000307440b0481a0381c1c0320414003a882491004400241c3c5c484003004001a100e18942a0701888501e083c030700b00044041100e00a040b00c0e8129800d588a410042c410300344101100d583c0c1c038001400610b03005280c8280382d519540d001c108240075544810008000ea40502d1044d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 655766645 1250 655765395 655765399
    0x30204092414060609090c090111060a09020a092c0118080c0601170613170a02010b01111b121903080a050105181603110f04030201021608030906030a0902 68
    0x810340c581c0d41d04600080c06580e4207070300c1e00d1100c1c1001c203040b0700f00b86003621413448024000c40307a61b486441d01d42c86140c004a43c51410051000078068140c47e05100c0c1c1e40c0200380d21440440d00881a204002c0c80c855150000c10090f85083c42c3c569072184401074400390a00c880c16490900d10101d1040d902400082100412584c100d109450810101130000c01c8580c03500e8041c1c0e00c0903601c42805401108007a500c40380c05c2c0d40400041001d01d54200c510052452164400403a8010030003801c01494100b0264000035035552000d90081d0758000814440b42c05015002c1c3c1041016540754008208040d400c041c01090644c1095140100401c0320040c1c030303802c65074022101081d92800428000d000c40ea14600c07142014000213590130484145801c0c20029585c0e4201555801003c183c00711b400c0d40070760101511000c1081031000c81c000104098012450385a64071810741c0006441d0200c200f80c8031409030700c040010000d020300801681c007a0310080743c03003039581d486422908018001d50b030710180d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 655767895 1250 655766645 655766693
    0x30a091403130e0112020a03081c060608070810150f1b060501031e120305130c0b3604020f0f1c05252703061409070b0403020409 57
    0x502448552003200841d4050081d0492aa0300c170b075070102e844510002c1c02508103520803400c0c000580c2036000b603d0422119408011403c1e4404018400d54219510078008581040f042c42002036000c0300450703102c1c15100d54244170314501201030464400039030041040040308080d00340110310401407000c4440d02c40359540c0b00c000c0c00d424404000c000a10003154179003c40e0019200d142d045140d0000c0eaa50080c44007006004885420781c05804000e00c41005590b840302e840340054404011031001d031144919080c3c4403000180d02c001720f0400d440c0ba0091403d031208100603e005051061103908100b5503015884a0240030302c603005005d4000f69010420001c0780001e500c100c0301c0e03e14845035170b80c407000340061b4503002c500088801c00402c3c007960181c1c2280881601a0042d00e074081030311581d0000e17080b00b440f804c58603100507a05400072100680c8070364240c0ca201c0010565a9048034034180900002490168035014500c00c40c44002d0142d512a07244206000c4005409108134000c815a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 655769145 1250 655767895 655767907
    0x6030b0906100537151106090703051c18031208060114090d050718022109070e06010224071202090604060804060f0e240c030a091403 59
    0x45a240d01c021103034801c411000d1400002c00b403416a200c629181034010783c10810458032040710001c04034080d480031003006103040000d00b0b1100c00c00d48038050007442e81c89645001103090100c1c205400506054015404203c040c40031039030209052455000b14042e0990f000040c200030b0300d01070030788003903485281c007504030000c2803244d00b80743c804c82c00501d9622210207503100001076035007102c3e9071703c8100308031030030b1101414070704105500036449402541204c20309540c80401602c0c9036905a600140300e500072070700c1c4064071031041403d0806582c01d00c1445445c5898912503030345001501c5400c0f421300001e000f01d80d0341d900902140b881c024581c041c00c4c50000c64521181e401034815203c18000800c441ca400f0081c1d0715078030a40d5100c01009211600d400d261803000c0340d14000203030066690310750b40c40d003403001d0b210307544941d00049040c4400f4000c1c120318402c0c40300d58441e60040c03502e11000202d040144507a42d040440750722641d009000607003540d50703041c42842005659440e50080c48000380c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 655770395 1250 655769145 655769161
    0x90a0c0b0304030f1e0c0f0605071d040b0102151f120b0601031a041109040204140a060c051c050705070803030117011a061b0706030b01030b01030e0604080d06030b 72
    0x1903100d070b80a0340b104103040443c0c4408484d889681c0d214580b9201c80040e180901d180b29021460070f103800b0303098401008035076440380c030100c6209965600114003c3c2c800104120420b1102f001040e100712008c101780050000042e4691002c1000c000d2030882c00f000060003038031803c100c01c222100b010210301019858840d045a4502c01c64030a03038400560100041e015807282c005c04d4204104c250010b0507401c81c01042c400902410130222404407414411801542c9841c4068402400000c0080d21007850840134042940c00c80d030404420010f04031440d1021880c00582c50303114407102c00f01c02a048034442c0044a05005178000141036005a03480000c101740e00102640c1a034225200d80d03840e01c070041c14042c1c02c030b9a103a400c92451f4072070784001e01d28034609030340038020215005100d00d120a1007110718a0502c074040d006a00800d0381d81c540542c665034148503a0620040a003402c1040751400b90306a687d070800280014a16880040e0381c003032072280c5800140066912402250301400c150003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 655771645 1250 655770395 655770397
    0x271c02030714032b12051603020a03110324010f1403060d05011b0e06040303020a060b060405030d0207030b010b071a0606160320010510090f09080c0a0201121112090a0c0b 75
    0x55a080080c030501c0d109045e0000600c40c49000710042c0040020407034010700141c02030340080c0406001d040da910340f002080550380b4003d510520804800712101105000d1115038081c4854486040040c401600b4085070b8104102041c450042c00c540d94583e5500d0001030003405c03803c0c50040095080c0564110385800030070181c001040c0c10740b5030005200031391013880350718000d6110180041e03002c8040366001ca05640c3c484190228080c10f450325282c0c60354046894504042c0501740180c2c4075507030030401e011000740309034007401c0e001c1962490320200d519280d04040c0003074100703280301e5584d4000c81c00c41e556030fa08070345600c5003907094524070b000d13a410003030700d9100010029249008905206d0340c0c0302c41c042c41014407a003400b081d60300209040200e0680107000142c00c0c5081d060340c030540c4002044100300038204000880c401043c500d0381500c0010707c5640c000a0b134185309070400051180394410302058035070b219a802c408007507660762040501d144c104820801f41002d4810f01c00441c0550250b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 655772895 1250 655771645 655771723
    0xf02060a0e031002090d110f030a050607020c03030702010e09070e0901080f0111030702150411030105150f010f09050f0112020a09330c020303271c0203071403 70
    0x400380c0300060035100d583c00503841a510f20603070141c545107041c00082c8003847c11b01002100981400115501140428500580c1c07481c2503540768003140801800760781c1003000407600f001c1900a14100761542c0d0010f4400b4581d80c07a0311b40308401307082c00546e040c5d2144d1040e154012000b40180842d5a50b800c4454840030021003440003542800b402460030142081124040d400d99401060864a400c002d00141c03500500216000d0b4440030b00e42046075024000c160042c502c04044172084000d00c8100044010070324641410300107a481c14103103950304464410100c070015114034903141c0e46240120f50440c184000441c2c42c078404030320140402c2c0c0c0110f020301903620b00100302068030719003000203030f0050a03801c1c80010103001442411442d440b13404180c09551020302124201015040051078100c1d80d0036134a41580c8104500740b01c60310700010404d900c181c0c250902d0118200e43d40100b0380380c41c141d00a00c000d48840c666184011344003040101d0a00d103600440721380c0c105040100c40d000141d05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 655774145 1250 655772895 655772899
    0xa02270307090911060702061c0606030e0604020108071d040f090c120b0c0a0c080c0606031e060a020702060c0d03090c0f0b0d050601020106050a080c12060907060c0f02060a0e 77
    0x1901d000301e2007500c988038a81169400c400550a111a50800c0082d1984644001c0784c00c1740d010b02006c500007940203900041c2845070311011030480e00300200142200c031a200103507160343c0f0034000e101c0940d0300b00444981103107803450400b0b03461891101101d50710985030091034104c2c0c0f62400c0100ca82c80c140e440918441d10645001c0d403560303928050300501c100200e13005060007104001296000c6d810b000140001001410049040013490321a10007540102130441c1075034000200b003102516091000d888083d034542001c0b00b10070560401240d543d00b0080c030954003030794005124802e569928040d10f0756024000120703440003140f02c1005004e0820380800700e854281c03001d00815000d02010002e030946034440300d1141084015040f0b20f0281c40c0140010341036541e1110007142903111901028050003141000700141c1d0b000d0350522858160044200c45cac244c11040070b000402401154000880d103151521002d11080c13400c1016400c0000c0710000d502c041c00041081402e80c02000039200000e007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 655775395 1250 655774145 655774153
    0x2280e13090c0906030c2306030c070b010506190e06091906030c021c08070c0b070905090f0412052101090b010f0c02090112110310090b01080c060307080a022703 71
    0x1403008000f040d6900e0380402064080c01140074040c03a00e035a50102d08110f0b032030104d0140c0c8071000c8081041640280d401080c1880700042c00d1043c0b01220290038010320064520a01d40300d04050900d0f505a10304008104000000e9640d031714580ea032000fa5111110001c000580c800a00d501450341e01d03c90b44512343c0440d003012018209180041503020b03501c1a0009140c0f41c00005800444620f900100300000340b251001903080070420040102c0c0c0709402d075132076284801d4104000c100b40f80b6070040011002401c0d510030807001400e02c402e10103000069082480d2243c802c202c03450200c40b640108107004030700307a000010b0440741c1904403201086080e210340420100c0883e00715101004044003a400c0011030004100e003420402d00440030a024407005900b1640d01d030b0020341029108030b640181282c482c6070807018400ca5520b40b50041c100c1c44010110941c111011580343d0000500c48824000c654002034003140c00c94040340c1009585401c1001c8803984020020000701948904074040c0c42 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 655776645 1250 655775395 655775399
    0x4080105070906110f03031611010c03020d0b09060a09050601050f0a030b01111c050a11030708030406060f03050d18080619050a02040f12050307080406110606010302280e13090c 78
    0x105034035a0045c880c2c000356195543d150003445070204019400c808001c1c0310840034070700700803e00c03880d044400340365005a5191102c1244d8015990085002c030700c542c4c01303a4148855984d4150300a411a214440085800c2d074803100160307880e02820f4540f1075a0000020140d00196042c3c2c0b108600304000d03200c00071003059040065a681600d41c1000944409403214070204c11700034030250180010034540012401e000b40640b07030454009220840381e0090120602041080b41d0140402400b50302c070300424440e2a6071074056541e03140389540d000b0310804070345c1c800d42692100b4660001c1d00015080b90303001d040c001e80c00c5600e05000094001410b1400c004a4807808440c022102101d07039a1055010b402d08098048034a03410506044030135100810070800007071100409400100520344a46109001d0300c2002424070b1001802c60f41058070401903c050f00048500c52501c041c101c801c20404807203c01800d482d10080400f040d58007020602107602420425002118010b1055174401d400b95 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 655777895 1250 655776645 655776677
    0x5010609020708121f08060f0702010207050d0f090e04110907020615120312070c120e0907180905010801020a27030f03091e030b060d170d0204080105070906 69
    0x80940100100107000410074003c8604649211a400c804992025200e800600d4040c0c1170b20080e503401907505070884002c00c0910b120500015502640c540000c0d40b400001e0b0352690340b0340442030180302c2401003001000300c5562086a801c00949500c0006c1070943c105414050040d0380b501144a01c200c0b01c11001a20052010074901d0161200320348068a9000c0401000780c400c9003c051034009100901445810b81d2a02800c1c44c0034a400d526000707a030034010306082101c0d020304000340e0244036400c48010b003a03440f100b8505500843d24074101e103a102c801c001c0400010003541c4540c1009080a0003c41e0350413040d4000c28200002d51945d01108061484c00301101d22101c00303424460081c40420804140010582c06400384a0729150b0b51441d2501c0c0342c54609800800c801c2c1d10321040040a000300404003c07910b0701b0800c221400e421445560303927030061100d070009010241d0000400c0c0044d01c0c0d0f00d180c041d40e003c2c6c813484000340041d142c0080c004200020500c20400019911005884d1207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 655779145 1250 655777895 655777897
    0x51e0c04060e1603140a0c0210020f0406080402060903010501090c12140408031305160303031113140a1a09040c050f07110f090f01140a060e0f0d1506030501060902 72
    0xe8001070469000b90740d03114100701c2003a415059030001e0585602c00d15994900b0303a44002e00c50400104001428a00c1c036000900e88001c101948503114810402e402d101c08509088e10f0480b080c514003508556107601c08244140501d0403456055803c050002c2640310403600000d0030031466030b840c12508134020170b2140c01d903071100081da44806040404140810540da0007554440c5004180346000d030a55a54580743c80c10325400754007980400342d014010181e05001343c90708020160707009400c21030300540c4480300c070a06e84140100e42084422000240d1120b030344d098001c09602c00240b400022508441c13410b030348a100102e2080786040c518103c0140100166035070080e1420342c45080c03040e5603880240c20001050240c1e480464007002c0000703030303854400d4584100d4945140c01c066514000d01e01d002c41c202e000c3da0314492414001d050001981c010144400c0d9507080f00c02c4120981c548011603d12124007802501c200400500048100c20380c2c2c1250040760321400080080f15541d0b01080c0403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 655780395 1250 655779145 655779149
    0x610030201050702090c0403051f0c1d0f0111031b010b0603010b16151b12110d0203101a1306050304020d02090405250302040e120f1303051e0c0406 65
    0x114109010310f4000d42082603806500103a05817241d07203040e0f00e940f0388919080801d90300d650b0b07024851542c082d840105000c0c02d4002081070500385a040340300900f060078a042e40c50494020035044a680c10240c0c811100400d2411588094070781c2c800b5410414120000466180d040355820500340514a040c8034003142e040f02c1d04148072508108910700b010148050f042400d5903100d0b03e000100070011a04d210b8070007005075103112818104988080503005622601001c0ba210307140c03040c0c0d203400c816910211545070051160041e035030790354252600f11503051500300780c0840c102441114440c40600f40100002459150100c00c07581c2d0742d034011100c0b840300712402074100b10030103404001403e000300f1007900f00703120308140c500340c08010f600d41c15060b40751f80c1d404151042c500c2c82002075003480e1081070880910040504030100ca554095006441100c03c1c80b9402e500c0000c0c5940c01c651044001e4028581c424183e603014894944901d69003404c11b4484007840c000c1044010341c1e0b203800c0c8a5801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 655781645 1250 655780395 655780397
    0x1031d0d110a0507120614010b12060328020a08070e0601170702030d02252d05032514030d0b010c050a030305070921030e090f01030204090c09090c080610030201 71
    0xe10141054410844120b0700d11702183d08130385460f0300c415081c1180d0001c0f800303804180b010540b03500c05694811070180010303100600030f4100e288022120711107208143da414003090600000d594403440813894442050b44010658003c0c0440803810105041c0e8190041c00243d031514600147d00c800002400070503110f40d805603004200e0b802046080b03070041e107540c2c400403440c100002070031110340c2c054940201003112002e0b00c01050400070320b03140c01d02ca0300188a07140500c12600b02541c501c0d54030300c0740280360542100908e000201e112030024108200b10307400360380e50705080a154602c686d0b0342c10540000a8003410100060003d501c580c0e4a015070542010040540100c1510700354014800503100504014035914007007948904e0030b10f540e02d0300a00466104c00920103080080c801c240740e84a6a06c55035000050040440814052905494045400081e00c05413840c0ca03025054099201440391410002d2240c240100090b45c0c0080701c40100c03d44900380d903424040b8480c4101400024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 655782895 1250 655781645 655781653
    0x313090c300204090509160602070605070609050705030a0b061c020f0108041407032001020705090a020c011e15060e010f080606041a0733090201031d0d110a05 70
    0x14100d04a00752031800d582505000c01071a007500c502d1440240d0750200c586031503d0b40145c144d11403010050344200024601d46c4007038924141040e400909521540e04040d02c0d0548598848050201c01d000c3d600003014020704990034041c8510b02500709280844903540f00b00d0000141003810400c50400c00f411540c0240031812104d141001522a050301400c290f51401c00841d40f800c00d464200400405940218100c1140d2000042c901090b1800c6494003411504803543c01c00143d00e9040c0043c0e0420306511003d40c40701c009601d21801440307201451030101d00c03001c04078114520036500c4400b4a5991207902007035152904c04c03e60707a00c1c3d480c01007a4000761186500c1003640f0300c43c4101d150444402481d9600d0581e8400301c0700b02c03020f5049400740c01d0040c0010303144100a0549503508150a420710082901d16a240c9000c503100030641b840c84240351284503072021a031081d400580651452065000310190114030780d41c0c0c44c0341114040380454280e15a25440400c002288401c03240c0c400020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 655784145 1250 655782895 655782947
    0x606090108040f120e19050a1a0f070b012102031c020a05030406050c0f0c01090b0706090606180b0d120f050f0a020c0f100807051b0313090c 62
    0x464a80d2001007094443c0c0300c031010b0710000501d6100d00d410181c0703425551555000c5018041041e10903010050381100d0b8101502007046489092401c0c0c200d03111003e4070684851101c0304030400c1d11810364075a0ba160000500c2c4010020020203245c141c8180c117901900340000544160103041c86090041c2d4594010004102013230090440044900014415500c4245403a03841d00d03c0c4d600207030021400300310702041c186d102400410003921804c1400004110000c5500c0c00a050714141d030280610314100043c090083c080c940c0c00c0711a40d0750740f06104100895540341e024001c2002101c14052007400c24904030b01c00c2c544840120501034004010488403c64441d040d10a42001000301013408400d014160030481440040e00d1214050b03005803184100e00b6040100e10103030b0200161043c4401a41143c046a00010440e44140306040180c0d43d40d000391261110040e0311030f8485028400010b0301405440c030170310a10b0440324035044c1031210300a24041910050410521040b10706504100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 655785395 1250 655784145 655784147
    0x1d061305040b060408030f0702010e100c080703050906030711010e0d0905092e14060c0a0314040503010c02070503102d02070602070b15060406270905071805040506060901 75
    0x109445200b0010515450310f9034807a080c1e401c64102a0380520300d481d0102e541810b40d6003040751640b00400031541c6c005104612003002c2c090900c030300d0001d01030040c0400e607901014050720850300661ba00400c003d481c0c0c0b92046000f0000285050b80c3e040d594200a4440e441e618000340320700400d10329031241544541408180403400d00001d00b14400707288011040f200c4174a510011400d02a50700c501032011a0801c1009030300080080031081c080c100c100305000b0b255202250945d0000e0b41468041940c074501e84038680700c1d01854000796419440e0020008059800042c603404542090b010340e5404c5c101c0c444000205c80e80d0298000380100b14141c1c102140800711030000110845102c01810584141c40e0a0200d800514007291051006030910401206603001000004c0c400c58a2030329040c00c1185c010b1001c4e003510210b19100c407411603403d0100d00441c9544020f401000010059450107917001400400d0721880c0c0c5640c0d01180d1800704190409004003840b80c500a0b1100c4e10b04884400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 655786645 1250 655785395 655785401
    0x6060f050d17131e0f05010f030c20010c02060901050106090e19050c03010305060604090c060e0f030a06140106030e0a20090f0a1103090604022e1d06130504 69
    0x10800401003010005210808601900c2002a207a44c12041c0100180160b0003e800c9640e6003284000d00c001600400090380e10501141700158a484d0103c0c4010141c042502c094080b00051108000e42c9005c000c046030056101000181e151342c215411507c0702d070603442c01c9903001c2c0540e80001d1400401808920307601a092034100f004920710104456043d0081000c89205071889440780400100400c01c0c01020003001d03420100454041040d81c44680da1070183d49014032906041c0000101c202c0500d9541700e140b4008004094240c418010007440c000008000c151f6504801d540c1c00c4c800420154843d21410204d22268001090381c45002e072901804c0340380d46c1254a840800c4028030840d1a00c1c0c582000d400743c8007a000143e528100f4240c2103041d40c1c0c500d00000411001842000030400740001c4860b00140c06a0306000003c8070303056200d90a800000c18019070003034000c03181c84141d5204002d040898000420751480d04401000c10000c1d1141c0740381d03044001e44110050000d8070f09a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 655787895 1250 655786645 655786673
    0x150f06140901350c1e010c0210030608010905010212070503010e041104061d0702070b091f020c060703020d08010905070503150a05040e03090f040504051c12110706060f050d 76
    0x1107501d4840d02c3d07041e150243c00e040500c007405410b4008642e000720b10b0400d414051002094034101c1c0b80008101d8000900860075501c001c0d00c11680c052810000b2406680f000000d00a11002032102160304c1c10003501075032000c600f40c003201c11584001080302d4481d00559042c0c400020041c56645c8403502c40700d40000c820a44564069540c40d0b0005091881030f14600c3d440c0ca0702d00b4084807500c4e1818010342002c0072076102e1203a0341c00c00c10400606944032011400d2990252050420f1401242030881c40d01c9500201e5507000600001d0f40d405140c0c0000d0002881803080d41c0e00718050b80c903400b220040e0340003566070f0801f07c0c0307051020a81180c0360600500380003c01a10801002c1d03519000181076440304d400c42e0320203030000030b1501403904100703442100c4888262414822801c0542d59070350b603010740a8680140c96040340c95000468815040741204900680d420b00c141008441c0c2c002e526848560100c400a00d0403400050f501d01c0243c2d0001101d030002c2c050368015001b501c0f031103902c0b4000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 655789145 1250 655787895 655787939
    0x1318110a03051f150207050405010f0e09010212010e0103121e030b1f0f02060a0c05040b1b0706050a08090604050c011412250206010b07020f030a150f06140901 70
    0x21100e10610f500140322000001c1009a03015a401010420040d0400040d07400c0240101d043c10018804e61540d010a0001c807081501c0d18543c541d0769800f02c0340240150000c112600007031100010b12107480800c8141139a0044811800701a5a07001c00e440c0031042503500308103100130800452000f070095004480201d0050515058107020402d03c4801d002d41c0030440010171444480d541903180d04000666100c46102c0c8104503642c8100c4002c0d241c1c1c015441140e000000020342c041d00c1c41751030034068941c0c030460001c80d41c0c140c3c0c49a0014045400000702c0070700255000c000620804400540b10380aa42c022000d005000180c800448800c48001b4003a00407950420098000d031441c403a0b01880f0725030b0040d103480c4120303003a1012946004000d20101c2154030000040c803480503540212450f6076411641001264016070100e820001c1c05000a8407009544c241c01ea4904016084107420403202035080007140e071988902141c12421000c402e0f040407119005104030300c424200c1000c46070b51 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 655790395 1250 655789145 655789171
    0xe0403031b020303070921060b012109032c06090637090806160c0803100e06030a0b01090f06030c08102a140c031318110a0305 56
    0x400740028524445000e0a8401039200008110b0031075400b11030030000e0020a00c1500c501a04441504c000140c1004d014102c280c1e10b19a0120aa0142280c405401002501c0a14088148480d0030080244850039804100c0c4d4a00744282d071148a540e0000b0203080c0040310203002154000c0c8201034004420041d0401c0c01000400c5502c52030b02c040321980101031012041c0220000d241c1c915201d100940c038018860329000a001c18180403422035448021060801000340c0402c004640c0000701000c0548400000014040480f1000074820182c0721031071a110520b468000901d960f4210290014000703025840044c052068690441c0011462826021540a8803500d030802d000000350300520b401d03407203072000074030940c89405211642103050b100d9004500921000c424024003100b9200d0401c05400c042c404075a9024042d1a4011000411030b80c4505c4030100b0303602c038004140034040e0641d16400d0494141d103818040c8489501300810a9400c00d40171220a81c0609800382a00580b2b00c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 655791645 1250 655790395 655790411
    0x5031b010b06130f0506070507060e0a03170903060601020d09140f030105010f0305010b0a0e150a0905070203130b0702151303061b08151c0809060408031903020a090e040303 76
    0x156220103400708402c490310480d0094507103001c01c00c1130f071596800940500740c1030024001007a004100c84048032402c1c10280040c0c450440010340e16155070b0402040790301d0f07084891143d0400d120240158a205030115840c9446a000581e51400031100c19030008030541c0d400d01541c02801c0c8240c001d4207001c3d04810b104030850300080c1c25a80243c010342e0350000094020824050700340100d40c04054162150542d80c0e08100303030034125002c0182030403004511910300c1c04403030300c2d485442401045002c0c0100305038203141c02d0081d00c03a840b68403414000805900045619501c0030222885103078000e00e500340030041004200c40e250404d01881c00002d55110001020954902900f40800e805940e4183c0920f100c00d80074000c044050702c0302d9020034042c440709242c0c1c0c44046007034441c03078144603000d944c9800501e007001c0b241c400c81c62956046000400c0000b5141c600201812071081d04030442080020407501c218100d014012035a4002001d9410070044160600030482e04a0700a103008142c8603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 655792895 1250 655791645 655791649
    0x111b030106030c080f071a070632070f020102180409050f16030b0f06010c14010f0e07090623010c020a0b070c030507060c08030a23090d020c0d05031b010b 68
    0x207041d6010b09040c1c1c000f000e120401e03442c140a41c00140003603100c8035543e007c0140c00d05249020f50500100310316070ba048801e0b000300000c14407010b1031201c0502202d2008040d00c24028044090394400c000c2015200c00b20942030042c020394501c06028643c109101c0f64103800c20004e0085d40303c00f5200f90050403043d101a010a0042140f82d901c000c403590a0a46145480030000200801440e6881702c000b0501c85640ea010b5982c0801c00d400076135400d1000001c0c5101401030000003408031031145001d011420b0140d021425004484e02090708100031980c440c01d1700742c031580d0702c0c10301d82e070700da050600b102a80c1d801a400014418009045191125160032005407598070414080d691101401000c00400c0380800c10040034011519240441c59044c0d51045031a001c0682095010380e10740020965038207040d5003002560384100341d61402801c00e002d0154440d00142c0e81c0800500501d02034880394105411030b081180c0d401002145030107150401d00f100d1002d1200f9100b415501c1d1243e40d00a5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 655794145 1250 655792895 655792913
    0x616110d0212010b1f0203120408042c090105090d1b20280504090f05070612050703050c0418060902031006110106030803040b0705160303090201030c111b03010603 72
    0x4405000003654912401004048880060002409850b042c08210599070200595049560914080b04a0784a600c1d1a0302cac41d00460304514001000b904070101d0301300390008030300056800304014110302c0c2c6804404500781d40c0c003214400301c26403141c0c0481c0007180c40f4880e640c0007107554032480741c201c89440d91010315103800b200420f2800514884600890f20742414040301500c02d00c4202030300280c0840703a201c0900b400740301d2540700c0c658804014041c00115014040e80940c003106440d062a11103e0251124906551482c0b06600d0200041d0b075a034003a115850064404039403480c02d181c6411024540a5943e501d050f115035142c49001a03035124600141d4042e90807440400b00140c142030000300100004a205000b0344e0410200b0808607101c0c800f241d801582060100489030340c0c0d0319055500b0310a442034204107004014101b01455459804440b01e240b00340c0c2d00344454900404215004410ba1000c0c0400750000c240190003403550300300b0003040c0b071406400031940c2507480d2103100c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 655795395 1250 655794145 655794169
    0x305070b1813090b070c0302060c0c10060605031b07050309040e01020c0105040809121f022206050d0c44010f06020717030901081005090a0b01030501050616110d02 72
    0x66a840d0310f03588040013a000b84c0d440c0d0195851034503111448858500954403180540b0300d5842c48070001c4e034112100b5050254210750464000d043c0305d4542d460740c0084c00d0794000c607a0022441e50340900717000d68000000448016542044c021400c01007110304000c001c00114142c00803a41d400c00c00209a41002e00a00707105501800100b074a2301454418001d801018020300712460300f01c4005141030420811541c187d00400e20740040e206c13210024906418108689810031061985100040080d800001082064004c0f00c0a0000b49082031041d140d50590702c00032441611304046803041207160b6050401551145680041006050820031403105802c1e0044482c2c4204800140501601081410018256500514084c1e50305035481134507401944036090400507160b01141d090040c0d504040080e1000601400c4070f410101140001040d24000e424082800c00c40001954030700710707059074080c00301c80f45600c5502000d1f5030342201d40509510500c0d4400b84448154003d42c50381c86480341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 655796645 1250 655795395 655795429
    0x3080c16031e03020c06130501140906150f1011030d090f020f03161206060b0a03090201080c090f060c0307051c090503060c0f03180318040b0a0305070b18 68
    0x1c40d5164580b0341c2484900054010024940100001004494001203c0d98808a680c2044400c403079289049405442440c408850340010740f802c5c030001400100344a030041104008401c80d1903000c6013880b0740600c504000380d50001d1048030200266004440405a401c1d044080d60b18250307105e0100002c81e091040103440e04051041c0daa003c504040c8030085103060304900400074003500c00c1c82c810b403807621800385044461201c001d5000700050390700a0350142002d002c030551030301c00c640340090052054000a034001420100420f0a02d104401165050140a4509401c180c00381c0148031883e4003801400c2218481003180c3e0001c0b031001e1000202c60b0031b8111041d04400684940200040aa0313040b69229401a1043c4414542924100da8011b041110003075202c1d038840c00d08076a81c9918204100c2580400200146c00b51107119103216903400c00c81c2d0411484c2000028010a5441400300410642c0000c80078420424018050202c681d54088408005411034022490300d5581d40c0c2040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 655797895 1250 655796645 655796657
    0xb070309080604320703030e04140c09010c0305040b180915030a06090f020307081c030506130e0a0c0b030403030606030504200d0212070e090304080a03080c1603 71
    0x44101a4400c1040006160241c014035890500e6111810f020b210700c841c04240c081034a0604a990002010b40c029000c40842039400240d96414080c01d4049030428841c469854035400c54290082c4a01c054003854045d207609082c400040019119030b15000000d4061200500000410404110007072413180c41006030100d40e4520f02e070078002d8440000d0140e0000f0141010203000301d80700095850306080d000709000c40d511040d428203802c0f1061135207000e5014000c2c8000454061030000c1d40c83c100f103402d40d040b0361080201c14400c9040310000d840c569408490500600b90510181d08801088548801582c00040e501e40c1d490840c0b0045900c8409443c1c2d02000b0881416014410400180b1080c02e0500c0145400e81e0359078110120f095062141c007454034800099a20b81c00e02d80701441e540a4501c1903400024481e10b81d60f541188112000480f40c0000182c1c861000301c155411a081d48000301042c0099580070b403582c90000389500040362040c000d9100900000003a076503154020f443d49 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 655799145 1250 655797895 655797907
    0x9350307050c1008150f0405090105060102060a0b030712080405210610050916020106080f03031008070e0c2206050c01050705040f210503070b1006030504030e12070905010b 76
    0x2203424849000c1c8402d2184050f03180080050740c11907203a56001c405034241109021070344d000920100f8520803a03a4106182200300426404150310043c02a00c00341c085a0036507490040741d00c1a1246031b0b00301030709600090010006000940c0f614040c00748070f800820b0400391554007068240c0c03c0541d01400300d05100c1502c00021100344001500040c0080341136005500704404183d02d9a001f030003c0960b034100c1d41044601034400e50016014100da681500c55500072070746100c0d6a84c00030313614450b85030420b04000400101c0003426808a5042c0d8154004c0c0c4c0d03440d1040401d80d41c114503400100074402c1500c0d0f0450182c0310704c1e0301d03018100c2d94903643d40f00c1e01a50f58082c21607000801e0708040c808100800e118101d001d0105104990390510b80b20301e440c0c89130052640c180c008810042c41e03484003080c0d80c0d003000021500c0e02d115440d90080d0040c265a28041142520701c01c3c0c4c0e000d03020601400254019042280c142da0009150700101d505081d1784000402c11100300340c1c030105a0786804111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 655800395 1250 655799145 655799153
    0x70206250e12030c0d02070911030637290322030c080304060e2e020708070f0f1e02180408090307060e0102011d0705010c030c0b040b0708060303030709350307 70
    0x541280c07405244527403802c5150040100344003030041580740500740d401c003050380001807209a10400495611074481d1215030b071005860912030a40c140042c1c0004028040d40e014011b0a045d00d00c40c400008004004403400700b001244082c41100036030400070000214004581520000c40c0038074800d020000344041e110861509080074800c18a043c3d00a40210354600340741e030b00c08201d040c040c0d80c03070041e034502c0c01d4070382016240704034000246801c051140c00c0091086501c5034148660041e42d42045000c1c41705080000a031040c5802588004402d41e10b02c1507110009410f0f0f400344c0300e000010305d080341202c00a481c0003520780c4000001661780380300301700300d50742801000301c16508000c003e100c000403000700e10b4407401d260090904001401240c0d0040c907208080390b030580b0303403c6004510710b81007500745503080c0c485c00c66144001c500b0100c0403a0b00381c2400021640705545698420264508040c0e820356002c0c2c26231425598054590100e0040044041c0c0303115042c26410015541c81401c0d10f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 655801645 1250 655800395 655800401
    0xa060e1e0312070201092a12050307020a0506040e0f060109030503030a06090b0d0534030308010e061c1104021c050414030c102003070206250e12030c0d020709 70
    0x114290845e41043c0980e4000b841011140241c0300d400081040075803020740c0004a0980d0685c8040e0748084081e220900f0b004011000f480d00d43c0c000d4425454a40c3c6030821302c02540314602c1030740380c0801e103040014051441c0240e501d401070814580824107607501e840c1d0a14540003902c030481d54954904080040304254440c1c640812400d4442d0b0754103810b5038a03000d40703c4480c83c0c108006d00181c11401c0d6034264413445403500c41400304034207006258503420024a524402d0050400c1c0c807540c00082461441e18483d5414400001486030003160800c0d510100c1d415601811103401030340034841c250f100880d200c40040307588107803040010f4500c1d0a04001c1c070b041d0340c1d101c10310006400800c10041c4041001c94101082c8080e2000402c0ca01c000210f0301541c21256003000410f040c011080c846150380c04036102c1d00400100070440201c8054584031003025230345410300404900080346100442c204114032890003001c08080d45d040c207084a941a0030800300540038001a04440c1040c440d25410b0305c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 655802895 1250 655801645 655801651
    0x32105060a0e1b07021c0506010e010906031e020102070315020d0f0b06040e100909060b01030f2a120504060501050108100f0e0408070c0f091d0a060e1e0312 69
    0xd00d058140d0910032040c02c1e800e0309180b03100007001e0f400221036041d502c0303484406542c586070800054030140300c0e0424940b600710078081c61101482c44000010a418240a80010f0320340000e074101c05102c0442103c0201c015803002203040d40a080350000119028018114206508260241e62001c2d00c078102c000f00d500750210031805030b1a0200f01d42054940c84140d80c10f507101c129150b0540c0c0c49444910240c0d40080d442000c1c11400c011080c01044826008145501d00a88090103800fa0080320001a120352a518040a001c1e041070f01d20b5045545c0c1c54907214400c141000e612000c081000d00302560011107003a00e1030b58443c8010089940e11848040c0d0203200d07189005421820300c1804c030025501442002c0c411240b03c00440e051003040d800310303211554032407914010356640301c001104550151040800c0e162501c81c80341450103a0751000f640d0081120081d0105801c250b40b078038001c1c5100c84091850780305403400210413001d150f024140f40001c12000795114888002200301d254402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 655804145 1250 655802895 655802909
    0x10b030105130b0402031c02010f0612021f03020f1308160b03010905040311030c01150618120515070302180f030a200a0605070b010803160f032105060a 67
    0x401d04121080680340ba507402015030007400c0c02c42d651541d000091402c041507800c1110800d44208000c03545805500c017000000e280034044c413190783d48419110350301143c910041c3d040f05000c00d10011007500404100d00c8604141001030400000b05510413440d0030040c003008890042e40360512444100300100400b40d8440001240303494101844180180418402c8075041c0d510351002c942050f004001e0700140d60000c008883d290a00040305a018060384002e12a2aa001400c0441c8140c890700c540b220015400e04694409480c1c0035060401c1384206000b03032154054540000003103000c0c40340c1c403405080f507985e0140e119420002d080d0f00c548010840301e4802d503240360036104991000b2510780381c580c0c1c01000300d110110003513100096009920307400d990b1002040c2c3c0b0105041d07804c90041e08005010300c441940c00ea8840b00b4440c0d40740700b10340803801c1c018031451aa400080160400c502c00520a14050010b440d160070341c031900c004240c0348141c400e500c413410040f0908160310346100030030034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 655805395 1250 655804145 655804151
    0x70c0f0233070b0c0c07140f06030f100614160c05090c03070305011e05090a0f0c030911040c1709070f0f090f0b0f060c070e04050a0b070e0913050c1011010b0301 71
    0x21702a22180e40c1d1250707108502c0c04142d1500c0b03600450f0b031004807101d01c84601406240d940e2a0140355400038500450300d410180e40b05500204e6003d04c80c0800100d40710400c2284d62908001d83d202a92100d10108100c034522091000402e0f40d40380c1040d082d01400710407a1454803424500800380684505800034826048002c22007503a00c0c00c0c403400c01c82160000e03100310b10541c850524140c09014407a07051458141442c1c00c40300c40715890740c84480300c6030240e000c14a9007415007040205541035034a00d90001446404044540740804402c0c51704514240d0413907400c0707070b6210406031503c03003664414024501d11b044100210602030064441c84030501004110101c401c1e4001513400c0034a58946004203004500c03200c3e072803404c0001c00041c0200804c0f1004034503291a02d00e640d40c2e00c51350110303083c1e5010b0000c030707c00314000c0c2d586091124004004000ca0390340d4015507030703130740000a0701620b0134402c14501220380e45603a0801044605c06949921008410141590955403684100360082e0300d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 655806645 1250 655805395 655805407
    0xc0809160605180312040f24030203130c09050433021804140105010e1212071109040f02030105150a140102011506080f070c0f0233070b0c 61
    0x1480408007610440d06159840e11402e400d1000c0005901d648a0341603c28011a01c40f402400400391040300c0041820100403603c03840308550680510b41e401084d080290558a1014007903000745500294030b00b4483c2c000b80064a600840142584c08030204c1d80d641c4c410302091220421000c0702010124981e14454198030442045aa0240d140c0c602546d50124017241800501615240210701c028414421020f00b184209112002032240a0128a00c0381c01050b05081c60070050004000700d138090075081007940c1a015403907000003c01ca400c0141c8114400081c0e0740e4400c0301e0700450044030321121000c414410715003103540280c806140d943c42e0841488269465201400940c3d190151000b200d0310704900503409050110265402d4070b5a05201194050744551024881c1da0f0b020039210079500d8050054500c01e00303140d40508064480c9800101504003c14010042a030740400030342d0381480842040340e5103511181c1c40e0604500006d02900340502e5141c039540041b01ca0502c40d20700a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 655807895 1250 655806645 655806673
    0x10507020112090c0f0b031006020a05070306090206041211041103100302150d060b0703030f050c03150d0b0a0c0207051203031f0503030d06030201110109082703010f0c0809 76
    0x3140201140b22070312001c0301c0b030401c0240e00705a00180a09120b031a9142d481d044c840b002c40d0401c8581580c0c120301454006071652001400c05409504503015104c3c4078155110038020f00144002a40c00031810000001c0340502e5a030440310250017403a1b2800d21546000800040d40c400d402206d500700380034010b2084400455003220100d0740e04035406901025103000e410350303602409120a8030640b52a20004003010030400a200040c480c1d03900b00402a8443c100c0d100321b900c20395800e410b4a0081c030004010304028440e58940600050030304927055842e688080420f14200c6803000c800da01c40c41c00003002c9030100010006003004852000401d002068501e540b400002c0c201c0c03801d104001c054988041500c0c1110340a40409070550f41e0782c8401c0300d00507001d05610301c4104d000038100100c0c0e801c106818030400300c05035409042e09107010305400f103280282070000803080c00203a4098600b030541d03800f40f20300c8000500075480405c031070301c0860005d41451340081401c0c0a640240c01c400500d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 655809145 1250 655807895 655807907
    0x1211505010302400902060c071a04061e020109020a0303051b03030c0a050a090905270c09040615050a09060305010b01020601031101052a0604060c031a0904062007110105070201 78
    0x60008480810f5040f04e6036400d101c0075090844010b074200b035000840703414960b000300e01c043c141c3d94042203030b5a0740450b402c40c424441c80b40d4450000061202c8600c1d0003c0300710094446400e0203d48000301b1241e405400058189485c1e81c8100e020510000700c007480c60358920085e00c00c48104101840c111324106404032918821003400074100640002d10105039802590100082c1082d0241046103150401d01150008541038888801c2c1641460034103e140300060040210074010380054556110b544d5100e014040e01851030b0b2a01c0f55520000c01c898036000c000b00b00500d1202400310310149107003482400c403409105074a045410540051000c0380c00000020749007003080c43c00960301c6000c610062145150a458400d88107600c10000201210005100340250b02500c0100101c0f00b480000341c0c100d6156245080d501c09490030803054070b00e44a82c446910600580006c121211380140d01b016031228000c041500d2071000c00c0070f9080c40384001280140c0d42003070802e50b180c50981e0b0000b07444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 655810395 1250 655809145 655809229
    0x60115050f0a05042408060a1d06031f02040f08060402011b05100207140c013b040507051902070b091212030c1b1501211505010302 58
    0x5a0380c00081c01c0c02c0c1640f154040310b004145841e5082c0744102006429110707540d0f8000c2c10b00c001040000464040d00d803940111b0200c0d00d00c0b0300d4440c56030b400c241f00400b010100a000c01d1b4903005144442c108034000d00d1a07038803020880301c40142d60780d00b0000c0140d6241000d07003001c00d9030740c891420040181d0300500f42111004080007001e043c60420b10703106e490f01018140705d602e01800420342c2c00400846845100d501c205840c20f69151480e803100441e00001d0400340000c6801560596642500c215011307542c404810700c4103150455203070070104055481c20b03140c40001030303070015075500f1055003c420906031070004d101800c44540340c9001a890341c09066600c0d40300324403002d0007a50104c401c00101c1c094617002c41e80c19443e40342c55029911190003401140e20052000485e5400c440c40200c0d1003404c1310103001e6070201c1a4206085804900b076a180c2802201d401442100702162030aa0407020030841c86101040308d40c190b2060010f1045445003401c00e4800708041a04104004044113003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 655811645 1250 655810395 655810417
    0x2060c03011a030933091b0f0607050105070c170405210f06070e0f04090b04030c0309080604050304031103010507360801061a0c0304030b0c0408060a0e06011505 71
    0x41c9a0312288001c0303040400e1807002d000c204000c0003000398035208a000d41229401d040305a05201e6076120b21240d07c51080e044800c08000b25001d000032240781c803500f151441b80000e0101c40c1030a540d540ca1034215034040d10100d01080103503140c2c0e42000400300d00801898003000000b401c1910746008100604090300300700c04040044006014801c004100111302801d298080f260705080480001d082c8081d240c0c1c13041d008035400d88105101e0b040900030f11103007951051600800342d84035101200c180c400107100703c00f000404100011550010000320740654000d40c091a540d628620344901c820b42c502c2034460182e4100010040c520342c01c40f4403503540c031a1086006d0a104420140c1a541c24142103201c0c4030035280a1000c14580015407080c010b503900f4810a007038180703150710074035110f010760740d5055585e80c400c000600001e00c06000007500424551095410242c6a01c0c24905065044404040f000e47d078000c1c00c8010241003064a0041410703c03401080e0200b8244000e20510a5002d070803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 655812895 1250 655811645 655811647
    0xe0a0f110d06021201080d02070b09060309240a0506010e010e04090501150f0905152b0f05010b010207050105032e0902070c08010b040506100f140a0c020102060c03011a 74
    0x14065100c02103151503003584180b045503902034010004001c100203001d0160a445494282020135000240202c103440000d641c031814501c401041080651000340550402e024141840780020a0030002800090300a05c18000501d082000502210002081d06040040400700c1a4090f40c000c0152140d8030000d90300441c10750300d64106140540128010310f5030809000c4000145c03013002c4e80a1609403504007401740416100c52621424081300418050f0f401803143c00360840d007000d804400c141c1824582d045504030034080c0c607811000502300318107030f85030307516003103050391960341032181d00040e20382400c110781941045c00e50f150100110a00c80281aa0b8140c0c030342c8114039008000c0c10080c80010811766807807025141c03d4403601d07003511441061b903003080000d5081c1d203841e019081c400c00c00036055014240d05480c08845d010000d003407403000e01410a1050940300c60132170080c01c1700c102a1322040c0e00b501030391000a2901000502c0f142c4503074028001400301c101d40c0b1440700c0d03402c100010340c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 655814145 1250 655812895 655812923
    0xc030e15090d0501060519060206010f0b0a0c24141e0a0c1e20011e2d1b0201020c03030112380a0b100813140705040e0a0f 54
    0x3c80c01442d2a8000c26801191800580ea8910100e10418142ca03156400c1c0d54041c2d030b030b030f0140143c42c05240c040c260980d031050040910061180c0003c0c004039010b414940c1140301e460f0311002518041801000f0129101d95044101e0754595055680113000d01b030819448101c4088056076818000c1c000a82454035940c0715081076124100040c8503240c4010740c01076217241c1c0000034014500c80d4200c010708502c00c80c20a2603605040c8946850b10080d41203103481202124030040003000d9071807107c00980b40e004000080c00340310098600054868081c0010861007071200f0304850403427800030004580c010001c14521410101c25281142c0e14007084400d0b141c00d920b400e562032401c0041c2d5440140c400146110001c4854400c004a0305840047c81480c0e01c42c058103405030341e0790100382034001010b9045120b00500c02e41e00c256121414510440020720107540d26411010b41401a1013580d00115050085280c248101042101c1c1c42005000c803140d6541c03071102031001e5090180c402040000e40c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 655815395 1250 655814145 655814153
    0x30f0207060515030c0904050307030302031e091e0118060c050408150a0501060f020604110109050d05100c0512010e0405011d0a050d020d14180d030c030e15090d 71
    0x1980c1846074401010700652520440000c00c0603c0400d90b0f03403085c49907012a42c0745091522043d800f6980000c00381d454205540c0b011f0300607500c082d00400140e055144c081a0003100300184da0302509888000c1e0800000c0c0658071080586844204a2141d14200d03034941c410950222001032298801c0003c101c00b1400c09040c0c841e030085500801003801002100420b0001104d00140308404000b010031903641c98880c11a4102039541101e400342e0302c1180071a000c82c00c0d8082c8031a030700005151030310b02030391914042070440c10264400c64103907014980d10811551103015481c10100301d85080c6050410240e000800c3e24018400d4502c000080c03004141804000e4110001078122043c3c00e0011040803198a643c0b0502c1820594041c041e5102c5881d20f50300c0490b8210f07288521f40e0310a025480d071440000e2142e4840480181181c1c60100794a0045c0c60ba00c944418241c000c0d2901d02c4000e40a00380034040704141c4426074800d280300341880c0851600322040d6815400e00703803121400b860451030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 655816645 1250 655815395 655815397
    0x2030105010e040e031201180c020705010c03081803040b0c0c0f060a0f0212071514060a05040c0915020102040f0b0c1506010c06140a0b0a0f031e150623030c01030f02 73
    0x101b490440e0004c8000424a0b552140400d01e081d0094042003101c0720510004036200c000600035540020340c2c000d10440030038482d22515811003034901c0120034004804a0a40c41c503031040d404600003a03c00308401072040b40600003155408020340e00841441d1404000031500d104e2101c0490621081000e403407a414800c00c5081c2620b00b00040700d43d9900000e0a0403800b4401d81142403c020b82003600380c0d01c8030030341d655003240500d0006d44480c280a040a007084040e10f1130545800402c03e0b41e610001c0c0ba20410b880c02611883c2c40c0d000140d581e400c040090204000c00c0d0401c6913005810400c2080348140000c40021041d07509900c07402e80c2e00c40e0340048034400381a00c3c021b010303c2d017442c080d501c01c42d4464852901403903020804000d01445c66080c061003c96900c02c091622000200410210b00304100c1c40013501090360407440380c0c0000d80e035490101c4681201001c01d80d5640c01c000c1c0081801411500000f42401d098000c01e0086100001d90740c03140b01a015041580300c828070040d003081c6030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 655817895 1250 655816645 655816657
    0x1090e07140f041805060607020f0f120613060605010504030c061d10030e0712020d0807050309060c060916150f050d0f15090204121712010b0c1002030105010e040e03 73
    0xb01d03502e0f80c0ea5a03140112210143c08105020641c0d24240104140d0b1a240045070a0140d0140c0b10300316081030003080110ba0340384c0c0380e8240d42010354154840803482d028042c5602c20208683c0c180340701e120078140f040c00c0355455007041c0d0501204020500c040381e40032010000311174003468428182000700e0100c248140c05801000c2c2c0250050311400070f0141c0607000f100038000b00c4400c0700d0006030f45402113061215508800b940100f552a096000b080c1090001d007a0b90740607a0880b0703d04040003011030901c1d0301c442501d0044d50401003d10101d9101400342c11440840c0c00310f001203550070519000410155000e1160600c10340102c0b41c100f05000c0d5003511014403a003141042a490002c04460142200c0340650303223482240f40011076115154420b032820340c0c8402100d0310301a181903580d6090002d5450030403103044014003210001d080c55184440c00303031074004d002075182c6084600a51401e202090030b0b610a5005100502107030341d10190b4001920030459021500c14900070289040d0707c514 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 655819145 1250 655817895 655817917
    0x3080304060e0c03030301050f12070e040803070e0d03080619031713150c030c0f0507090903030c110613060207120206160e060301060c151a0a0501090e0714 69
    0x4010801407112560209140e002c00b10142c601c00e4154108054403031100340941540b061410040b40c0c018103024203c80350b03114201c012186102d480d1200829110000c51b41101c185000008015440343d10099841030b800302540c2c4003a64849a41d4050040540100000e0140d407844551102c5400e01450340001035401c040e0102c82d814038000d68140c0c6500002e01001c43d217900303040008190340b8441c1d481c2007040080d50340e1100d042480da400c0710f8200c051001521045000e550b0f20000c03070b50906c80e050003405a0300002488130103e2a01034103694507640c4003c02d003c04446d9a401c1c0c03032008142c0c9503100700c2d48000d8211010341c83c54507000034040c02c0302c040c0c40801a81c1c0f11141035a000150b41e406812840505040d500305d09804032214130700c102405400441c00d100420419008415680d411407051183c0b8941c8414113100e04202d40201001d0b640e100100c01048640d400c0c005030040180000303192010505040a8000a410074084c010508101c16044c40001d21680e40d000e88800d0040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 655820395 1250 655819145 655819147
    0xb19020a021002010f1401080721120201050a060504140609090f190b0612030d020901050d020a090311150412031b030e0a090c020c0f040e0d03020c0d091d100308 71
    0x40c00b0000f402000d807440d405110601e4500701180b181c003c881003074101c5e144840104801c1e400d01101d6440045610303070b040c0b00401900c1603040010081505607040034400c0e4000619072800001c018280c601c40d03401607000310315000364194001c0b2a42c9415601403c04d032a44d04694607102901ca14100518003080d0b114080c040c2038034002d80445203004c54407400340710070b54000e0306ca603020802d59209180c0900310fa5801089004440c21254000d44425001410003504084030400c0d00400d80e0301403090840000d08824041c420044100b0303070708841d0b0b44280e8002d44a488640e015200381c2c85940500c81e00c0c0e032740b213a0645003018445c1541c0c800d2095036a042040c402c0207490081c5c071450140000900c01d40c0d8415020603a441d003071241080b2103646134000c141480310380c030501c4065401066510b410907101c0c9412221404101301400110050b90380050707960112007422030400c1c411040302c070104401d605003081082c4481c440000284c84041090320b00d5101d4201c10390b00756049500003080c0d00d40c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 655821645 1250 655820395 655820419
    0xe0709061527140907050a051e07020916091410050306120d0503040308060d03202505031203070f120902031e010e0105010510050c0304050301060323070b19020a02 72
    0x828120071683c0d030000c1d00c0d05404c54403502000d503101c0c000d50034984002202408480b0081044003001c94140ea000030701c1614000598001c140c00c2c203422205000e020001c0c01c0300801180c0c1c060310032802081042040180d86d100c200004000c10031171058035040200100106040744d890100380c0c030a00320386d90116600314010600c060802e401c12030b402e0740032842c0c1500007107580c1400305107000c0781540340c2e030360015900100b082410f101c2843c0709074010501c0343e2054204d204544540ea0540300806940c11400b10b89040e007010300c4d1803449644940030341003d20a0000707441d0001002203110100342400c081e900501e1060000805442102946c54851000414050200035084280c910801c400a01410140040c118241c0b4000c1c841c4c80c0d01700b0394951403101300501c00d10160080a9021003560318040c1d079403000038251402074100351030517440d08240f45442c982d5405003149826907031001e041050300d4081c4d0b4803400d0007010014540c0c07010b4940101d40180c400c1c4102c2d41c3d1594020721002400c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 655822895 1250 655821645 655821659
    0x1504021f02120c0c0a06050705100519060305010501080f0a05150916030b0402041803120213171c080f070c06020d0f0e060604060e04060f0b10030e0709061527 70
    0x401a02070351702030310300300b40d01203003051050701200d00d00c030b800c039000b0000e00307281d045e00600501c1c0050550703108a170700488800403442603004400c01035000d03600124503075040180c001d08161024a404060382c1c000c03090030340098000b0a5041c1d030745c41401180c000f0303580d6004a0070b040c0340d100384800810f00c40c020008010415041001400345000307440400c04c00300b25110b00c03845c0c01d050342ca010703010449100f154500c400b140e800809102c000c0c0042a56060307601e8030428220f4180503280c90407034029032141001d44102403480c080d0210b40d4a004c0165040c4003030b103103951420180c124401c200080324610184141601240c50110110710204403100d410140c8000070011030030060420f0184402050b072034600340c040d03002502c40228001d4940d1b1a540d03580001010a4103d0417070b05511900400c1051b0307240d80c40c5981d168000e4a0100d403424072001320b5400c0000d5604186461403800310304ac08a491364034a140d40421982c10b020005074808640c00c0e40c14900c0320180700060011100c0410f0b00b07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 655824145 1250 655822895 655822903
    0x21080a03020a02010c0f0c0b040212010e1b0409020a0605070f12020604030e01020304140402030a0e07080f0705030109030c120905030d05040e010b09091f0510050a021504021f02120c 80
    0x1c51010341c020010176695803002c46e080c00400012000080304003d0134408540850b44807038100344010094404041e0105040d401d40c0c40c3d10090221603000742542e120b2116401c0c004110300041250b041020a0f2103074006110804c070b030301417901000004505041000100980b600d00749030840011281c485e5070f480000c0d940d8034222801c80c0004e038140c612800301c0d400041914166400303524040080c2c1e88000520009400c001d0804d4821504e4415114400d4070601800d00a0041c81000d0520100b041030f403c0d10b0000958803041c040c1e85440070010110340d0203002c00d0700715a031141c4c071210b512444000446441d480c4e50440713a4140a01740301c084916130001c0090040380c240c00301c61600c80e81e903100605264003451891a070040e180000049008012007409a0300348201000444030545800114209502010565003c1080001c0c26050b051f010800c20404140c04540811603240990224501c0038918280c642a48003050f81d00d001c40740203001282c0000c0da0040269100c282070a00c4507a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 655825395 1250 655824145 655824157
    0x31106130203160f06030c12020301151d060f18120601261b030708030a0504090b0616030806041410170304061403131a0f15090121080a0302 62
    0xc244a0156000070f00c60901100c28122401c403040030b8541d81c0360000542c05841410303510700030400600c03600003d400180c40558060105403500130b4806044c410301a061000c031011100c540b006842c20105260f55181c00c4940c41000012a6030322031503640c0d0a0310381c05040d07031002d5521200544102128440000b403481c100c0e502420481d00c4510148036480f084c150900b5906802d40001a04140c00d89000d441380803658005421280030b035540e00001411a0800c041500c0001d00025040040300c289007e4110f103280101d0b0490703d02a1031010a00c10480006002001c2c080c5100002e0b0903540c4030303032052110758588c3e0304115081c80c00844a03882449136005420030418100f002c80501e200001c182c0d402e90724141c0320b02c20400e03510701070458a9000100400b52a034190702c0c003500042c40c800e0384604d40108284807010030b420b00301d80704060300d60000d03c510310f1400344000040e110741c0c0e000c00b6141152110b140307006600c940302c04030300380c085c92940e03000c1d090351702c00910f441400c0e600da802804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 655826645 1250 655825395 655825399
    0x4020a020c0102060705040e2e090515060f2b06030305030a0c0e0120190516080c01050d09050a020409120e030c1318051915050606160311061302 64
    0x13542d403401400e5840b40620b00176808003010100001c0c01d419003803915810800c03c0300040c0c1041c160018408400b9022940050300501d85402c1070190001d442001240d040600302e4405007060040c8032030300041d01501d00301511600009a4110b03211401d044039010b0565400000e020f050b407a4100a041a4025525030080c946042070000101b8410380346140d0b68103050b07540e0300c924030751141d2040d070002c4080720840c0e05000e039062840c1100b2240c442c41e89180d11070f1025121404449055060703060059100e6007a98000c0720321001d0b20baa11000320b500b51260344400040600050505500d01703070303030b04c00002d42151810120380e041c4060030a48001e110141d660301c201c1e11800e0010325172202e0782e403000d00707401c02c0c80010071544c00d146070780040c0c846081f1080c4003009003009440d01e0380313091924400701c1d48030380c803e8401005000a1201d41000f1807140001030240d0b05205001c51210f10410f0f058081700d44003000d542e001c040c4602507410004220b1811900c0c00d00b005031840c001d904010364100c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 655827895 1250 655826645 655826653
    0x1202071a040312050a02101802190605041a0405130605031605030d05030a1503080301090b120709020c070905010b040e13030e1005160c08120c07030201030b0604030204020a020c0102 80
    0x10000d221480100d600b9241e0120300c0d0a040ca00c1d040c2c013542e06411018031340f001d45c05200284007801d0050710070303507070595260101c80040400703d0050082591010a8080d02c810801c28140805500079084074200c900210a00c01604075040402d0024003640e004113034804d0041d04622501c004a0f0002030503202c013102658500f0305040020000b42d5810312070150140c001d8401c01d09c0346805000034650095078a0404102a000c20704500070910700c9801c1201e20043c080014420600340740301e40408880140c81c5249044128404280d82e0601c41c41041800c68000407004d507910310500447c0d00a004901d4184481d5071610a0046190807501a10000302e4101c80051f6206240c00ba1115005130961100b40d0546254030911070194038900e001c9050100800c425800701e07090380441c201041c0030f050403d65641c1070207012420300c03880e1081000c41700d000344980c1204140102e0100d08403642401c001904800740000300b07407540125031020350b01503c04150701a00b03640100d29203c418400340d080e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 655829145 1250 655827895 655827929
    0x703090608040b130602090d0b07030e07080c0607030201060f0305010e0c06040623040b070606090509160b0d1107080a08010b130902250507080c01080115030c0c120207 74
    0x200c666101c00c90b80a040b4552040210b12202c60a503400010140601c001510b0550108042000d02d14080002c0752040050404c100001c0c3c0d042c801c20000400c0c18014242c2c451800500d240d80c3c80c21801c26511445000802d202054001d40c42032000b425101e6000042c00d599042c114001c1c100d9001d04038003401248900e03209403030a08110380a41d4016110000300d02d81d641840b500004031004010310117001040702040002c1884081d04540e80310700000b04010f41003400c00d2090b40e00c05084d64070945d111044070341e0848031220b100c4050f20100d034181c58903003542800c00009400b280c5450710751614002400024062081e000b000f140b9030030380764150542d0340c400140000748030313030040c2c44011860a0b2042c4040810f0350020510502e030ac3c044200040000d030f05550080c0d103030040840e0780b54403405041101305010310010901002c00d080510003907241c4070000d0154155005500304043d03481d84a002d540d0300130b404131640300e600f02c400d1150702003400d00083c1d545d003494010030130010358480b90 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 655830395 1250 655829145 655829147
    0x1020412080418270501060305100b040e0309150310030c0e2401020c19240212030405100e150f071d15160f0803040201030507021911060705030f07030906 68
    0x3d00008440c0702043c0b03007904c5850320102c204400700c590110307281d54076588000302041c3c0c00c05c0801e900e108038440003d90f40200404000486603091842120790304107010000c020b6442d40301201c6441c140313032415541e0303645500c1c01803901c7c40c140d000200200c408000c0481d6000c8800d190902c100308101032800300540085411000d1085240c0290051b4800404802d850030040f00c281c605a00c030b0144070b02841d4441907600d000039000200c90b041500481c03001c4908139810041c0c0f0340190301c60429245103041c55101c05841e642c0e0b54100140094072580d41081c002340401074598242981c040180560401e40c001181c1004240c829030f0001d140088001c41c1c104580e000c2074010314004280c003c51625030004201180c021481246440d24190856408100121f50b9100381e984100b03501e9640c2d181510025045820141c80c10341154418006041c600b4400050040210f0b00f05500d642c0c400030781c1b0006402880b50400040c0107000114089800e065100d020f45545407098807030410468807644 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 655831645 1250 655830395 655830401
    0x1509030c1406040209012d0b1806030708041b080d090602060603070602150705040f0803071a040b070c02061c0b0913170d020d02070f031d06120901020412080418 71
    0xf40180d401280c050040000f14003148400b81d181c0440500e0111160000741c0c080c10702484c580c04642590f40c0000d00c0f0b80d20700c2c0d610301c2e00030141c00101c40c1141035043c0580000d081d8140180b00038480314444102c001040d003610001001081100110b445080011000600f80d202078880d46016114030b4000c981d043c40e010270060207a41c91a4028949540c0c20100c5185207007018210a05222040102103011040c0061050240a11400640c1d03039640d945021390210000700510b00340240c03508180400229240243d0341c0040b001d10704100e8400b039500000b00f65208454289030030301030055000601c01301a030402107030303128200c03050030241d0b684000703510079905a000002c03d031040400500005520305000f501015004500050410110307860060032603100d420242e9010b4070280303071941019440b0150340c0380e642082c008201e081c9404070101d0307198040d5444c100148508038001491800003541650024250031180d07542c02409400c118440380d206000d204011207580c8014912024280 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 655832895 1250 655831645 655831651
    0x90c0d0e061303050d060b160c0b0a0903140c060d0f0b120601030210170c22060203030705180a03032102161509150e07091806091509030c1406 63
    0x1489265002d003255011226a484841c00f10581d560301c420100e90200d020f000f42c6004501503001e5042151a4105440303906820380c040c40d5031410412035030781e14651040c0041c1c05c0300c0c1e00108004c810041c2c1c541041c10800300200d021781001011078400d075180300c180c001e904c00c2000610100324402107c0180101c0c140440500502039201e07400405c010b080008803a15807a4aea8034281c00c8410342c586001c0c400d050103480714030600c90301003810551078001d4214642503070f401c00361407003546207001000383d00d0f400024144000d21601003404d903c03485040794001c1c9100c02c000c254070071003a00d80c034010b00040c0080f1000c1c460503004034526111762000b4400c072030850350790040e1040da05825981d00c0d6079031590050710103070740703521003c0c60400101520340144214000300c0c1c01140782c4202a004d14546140c44d0b005032003441c1803c80c8048a0015006d40d08035158002c000440c0e0440a4204803031000c45c200c03101d14055142c60311100034507910401c48408107200d07440d1007407045103861503d541c0300707815 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 655834145 1250 655832895 655832911
    0x507030e0109110a050414060d03020312070801031205030603070b030a090501060f06180308190c020d0303321605070507030303200304050303131401060b030603010509060f18010902090c0d0e06 85
    0x47c04610300d49012400900d010303109204481c074001a0b8081c4100007001590b1050211324603400500400483c92134140e0712400c2480c2c030506504d000400030350380e4444d038850300b2a0312134008040f912840351500021101900107000344401d95650f0078002c5540c070030340700e0040000c003400d820101c005c0c818040c10046a811014990400005814025003409041c5c13214040c490f80c5c0c81c1d01c8006031130722880d040d506802905c00052601500000b118020508800b800c3c800c680201c0d080b1030711160120643d04020324420044420305103a1061710716210f6840090041c0c85101d00000c1003644c5a00b01c01c81080c02c590f0900c900482d04102c50015000640d0300402d81d80081c40000d07146020b55591a40c200d020b24909501503404100640c01c4441e2a00424032110000040083c1030a09014141e0010100c0009000c1454070b8604607060403c060102115525000d4031881d030030400b5005602c0d2140c00400d110706505094040341415400542000c1540d801c043c244540c940340407442c40d22800b10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 655835395 1250 655834145 655834181
    0x161e0503011a040602100e0115152709090206070501020f030a110403020a06030f0605061b0c0306090601030b040311010f230702030406030e1609020307111f0507030e0109110a0504 79
    0x20407a484000791800e9880b0031959275070313007041c6442c42e208080f81d817004001c24520b240c1030903190306004200e10400c050702c440941503031035042d92018a00da03a600454021801c00121461a0300c0041c070680706000300609103600206104528284010055024140b941030811a80c6103101d040c0d035480c01580700107540414086020015075010380c02c10310520303016000000d480343c0c4410000301c280d04460307a8559a0114080100100c80342006183c0041c0c004900070040741c64514a101c0d600c0070b050000034043c03a41800400c040501a0110861003d440e4009004184940100c0d00050130302c400030702461110303810b1480148a44c000c0386030250240d940554682800c0030015406080c800300c0c000e423188650352940001040150104014011880c80943c4c1ea092443c0002e0091131403481710f600d51303008000084801549000c0415012a908202143c141c0e110032043d0001c09040a800d0707101d5003004050010000250449c0c0d184100485a40511984900500c0119524001c205c121644 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 655836645 1250 655835395 655835413
    0x9010f03020112050702030c0a050c0f06180409021503090d0e1915050405031507032702040f09050a05070e0a14010308090409081803190308161e0503011a040602 71
    0x940c1360842540090340d4011a4a00440204401d241c23520161050b281604010800b505030b03e00313200c400c11850012a8110f00f846052004d030351140c6001201c0b54481c60791611854119114940d042101c3d00040f140c094692414800641d00c41d1a580001d0f000a5a002c1d60700001d440c003500071520240c98041c20340000e604118a04114030483e4104109200080c04009510f60b02002100315001c0680022102801c090901500361580219005404929183d1007a040d404042d0f01065450b011140840c00e0081110100c0c000c0a4881c009480707070040a9641c402d00000064200843e0010005404a41d5440c1280000c4400300041e8240e00b642c15401040461103c80c0078101400008000003a042d030703a43e4542c030305640714030031145140d00c1200b40f4620500d0306001d28803251607c40c0055070508483d43c0c1c003c1c50400010500b050380b1404d480300c0b055140c13060385180d104c00300454180300a002071007006015038000b4414a2400030070102c800c00c440300d40354156011a00b0305c0d00107002d109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 655837895 1250 655836645 655836677
    0x302070302210c030a030209030c010e0105070f0201140705030717180105070503040e0108071811040b031503030a030b09090703080306060f0f16140105280605180609010f030201 78
    0x2000c00c0c0b40d07546140c0300500481e00300707030302c140300410350000390f920010f9488038400213260400949501d07503070610130000300301800d90b41c02404688140f984414402894401c501c016540802c540302c1d80a4609000314080c03040003800801050580d014880175400301310502c0b105912882030a0020b4160200c0c000c54000e29401100a000b419100d142aa82041d44603000480c034004240e1180c1445e0740800e00c100021502205420162200700c003080c4017161a800c1c1464003441030f071140c1070350000000001220441c55030b611640e208402001d40c1d68401303039020b005028105011185104004034008146400000501541241d41c084101070542c0d41d00001c03c942a000641190310f2600d08024409003003c030034000300404e0f1307848905c40034030012504110b48648c145451525080e0700d03203014406c003100b40b01074030b11030001181c9604400c03441c0411424040d0040358030040e0032211100d86200c044001c4809680308242c103230341d0300c010340c4c0c0d858949241c014450b21029020940080c1e280403c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 655839145 1250 655837895 655837933
    0x90b0102190c120302030d0c180e10050d0206090a080106060e06070b0c09060d050408031b03060f100908070914130b0a0504030c120f0e0d110f030123070e010302070302 74
    0xa0f600a0060303a0602d01c00280308000c4d035002900b8900010703500f0054406c91a80889003102130141c00102d03001d03603d0500390f00c2111040901136603200c0c01104a0300740031942d0389022103600c00005070100305816a5802b12138080c0c00d00e030041002059500c05442090b0624200740d40000d030700003c4028160710340c00c2080d5040d503c08030410340c1000c010802142040d005e0300800b4001c900c00d103580ca540e464a00c4d100b100c1d5a0300d41243d030020f44030401c240112540c1d402e0340c14405181c00c80d58070013040c4074028107030f40214681d4406407035406403001c0022a0800c0e5444a04c2100d00780c0c1580a031079407285817907418071310104c41c010000105400882d0300c5581c0c66009943c45440780c108004201001e0b103610302034400c42084500083d030100382c500303501a840200a03101542c29900c9440c0b48005ea90350480281800e035005004020400e01a04196000d411080c3d41e07800021083e1040d609625900b504040122a54404a50000801da605500c28800c9030112501039015140c14040b07100c003001c007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 655840395 1250 655839145 655839179
    0x30b0f0102070b03040f1403252013141b0c030a05070f0204050c070309050a080a0201080a0617030c16031104021c020a020c090108030306101b0c090b0102190c 70
    0x1440b01d821b2040c60005006c10103480000c01c52000464584103411041d600c9440d0940000052124030303440c01740060300a41c115407103400b4140300c1d104400058004600c84602040070360450030300340308080011261400403e402510103020040140b00001440303017a62141075010020765008000b803000b1544070350007502203c0d1003101900c011807034580002d001d40c1d0082c4c440065001000410204040d00108131b6802042d0540e0a40724161034000c4280d00d59a1400c00641440b0160001507813a40c26a40198080c000c015020f41003003610f1b006003643c07a00000c83c0542a4455540780d1000c04010545040440b07a010b42600c8031503444000748000b0b5040408040440140d004c146c09110f000f134009090060303255401040c0b600703044820401d081d04c06910448150f0810024000180c807406042910361015081440c001d40c1620707861000c0c1240356402400b400e02d40400401d600055410582c1c0c0600c0903030855088500c00d4800b02c40c00038550300300030a0221103030002c01001c0b130f16200000c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 655841645 1250 655840395 655840403
    0x5010b03061210091a0907081c031401060504060801080714040c020c090c0d230c0928090e06070e09070318050c041803020c0405060a0b0712030b0f0102070b0304 71
    0x580030542d000808103407544a0400c540304220b44c0170402c0080165901c00d50b0205502c0000c20311a8603118038143c9401407281c0a10451100e554025842c034002d400c9100100d0320300300076180d250f170741d400c00a0440d0424094030002603041e034000074010000003565001d40345101400b1002e00c0380131040100502000700d4003015401000104003003644c1e0402d240340314030450000c0558652040040c01c1c121800307100300b44d903205812020300003166504404203034403035a00c003015582c940d07a4000040b055499100e440000c081c00c0580760f00320900009290080f141121003c0c0070308505135484c04d0700d85400302c820340c0014003038805240652600c443c20581014440c100064003440800e810b008810341c2060030b40f0140d215a81c1c840140c14079108418039064401d507110906011035900940fa081c49240c1e2034403440c0c41d40c1c089006d590721043d9000082144181442d540c0d69a46001031944610403243d0000c0707403a20302640b00e0760900c13a0112201c0c180503400307052243c0c1030035840e8145800260042d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 655842895 1250 655841645 655841653
    0x409050f0123211b040c0905240307050702030d030903020d0c03030b03030c1b0621070e09130b150105040915080109030504030b010f120305091801150e030105010b030612 75
    0x40701400d40d9640f83c06081094000c2d01205a44070060900d040c01c4460840c0a18541515102500c7c3d0201c510070a0382c1d03044841c0c441803964050b10f906d070141c044907003c188540000a0082d8141c20100600405200740c05641050000c040181c0455610710300c003a000d600000e0351401c0c094481c41140c94181c0c840d0500103548456000464915003000c2103100c0a0f50000c01c480d43c4090b1019940040500c0c1125400d10b00074544000120038032030742401e44c07850b540c4000130510b5240070b80280000c40f040030f811824945081800b991402403466420340b130000d00c074800309030202e20000c0c00c0842c088042c0c403040c5c54180303003480c040c000b03001c1d100b94920024042da5010540203420b00807a0358850080d038a083d00c1c0e904504081c2c90031074040e0701c800c1d00003c45003010400c003218410040586038050400544401000c0c001c2282c4401c0c48a910940318811400402c45428200441001c0140e80d80c508201450050030b16007220000e0040084061082c80000c1407854001402d8807841d003544150303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 655844145 1250 655842895 655842919
    0x7050a09021c0e101b0207050105130302030111180a0803030c070c030503040806010e10050a05060d200c0d02030309070317040b0a03050f06221503080c01020409050f0123 75
    0x804210f400c110b004280c0c680100000d0102800c00b4000e900520b11a82403415075903152800103581c401043c4649414442c1c08102c000e142c40400319108000c60b0050000d100c0c49403a8aa0480f05503c400d010610b14816903500510718240070000e4000e40d10800300071450741c0c41e80c11301e528003500101c41c202e8030002da1102c0071001030405d001600040212000400c1154180070180360040d40c000d10311052070294800400c00c80ea11041c8800840c1c07016a4000d40c0c42d460205942c1c05425031451131044032000f05040d0720289a202c2c020400b015816090311100c2441c520201d840b480240c0d5a0310450344a18001e002003546130980c080c28082c091045403406585490168654004104c070780c0120f81c1d43c40c10000043e84040e10240d00500c1161440b60b00c014140c407404d045059040e120796800d5803407203105c2504004500380000345401c403458603201c5c83c00d543e0a6010398420701036004a10301b8070340451090f10700c0c0300d0140e06951100c005030b49910b00d4000c45102168002c050154840c0b42d680c03003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 655845395 1250 655844145 655844197
    0xe010507080f0c070f12030c08040f021905120708011506120203060301060e070c0201020c0a2303100e0f0c09090a1203140f07141912061d071107050a0902 68
    0x7117140c0952190914040c402d010800c041d0443c2c455504080a0003a46000c100c00100041c06844106504480b4000384c85141e068440394841d03145c100a03001020754444009008001403a0000c4a4a1900078040811031a5200d070154401c0e1040c1030100e0f0b01c81075008980b20b803603000f947c1d00c40f07005000050b030160b44020031040e4a5040d80d4080119050803c00015542e060104400014040d65000e0900c2d142403846c05070000f06222101c211101c40e10b00178501d66040c401c8112a180000c01802040301c29012a80c0b101001013465202d8890b825440a1605150f0501840390b1361001c05002248615204d840101031244070a0341095911030814002041601c442070240081010201a51411f038401516181c42c146981007181414880032461601d804a9846604000c1c40c2c812108421070001d580581819080f0010600d4151459400200900007240c4a0f003015542d01c0c01001c804860f107515003c190243c250019072095051007140f150f6001850201e04404080e0513070380040720 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 655846645 1250 655845395 655845413
    0x30405010e040e061f06090608040308090705031006180c0219062702010806010305101401050904051602120403030c0308060d0f060204060e0406140f12031603030e010507080f0c07 79
    0x10a0900f00026200c02565501185405ca02908260500090036420040003501d070800c0280010104584e074400548510000c0c489200204409011544584440c1c443c09010300200c1c0144803201c9a541c0b0700c1c2800e52454001c1015030701541e0081c0c211054100c1101c050480310440c180d510b90b80760710907103071800b400904250484808184801d1416070358400100080b9007c1c0c6241e0406040c0000c0c8002c601244118204403502c2e051441600d0241600580c1e0b02e014402507190722610344800c11180b000d0000300440303800000d40c280d0344020f00720046004140110b001c0940010b011b43c0d00751000038010b0b03010b1604048010805c0c0c045050795640c0b000050050203080318841e8001c6001c200356500448900c6642d0300859061001d58208880720f001c000580380300910030303504402c007031035162548204600303082070401c00d0720f0342c4818003018075110703441d560001c6000030700d00030410f0f400386818890140a00499078030b000d003948400000b0800340030040e000d049101020011100010841d43e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 655847895 1250 655846645 655846651
    0xc300d030212070503190c0309080f13050a0608010e1302030f0c0a050409150504030302090d0605060a0b04030b071817151501091e1505120c0903030405010e040e06 72
    0x25401680c2c41d896041c0d9040c031140e0142c210400d110041c400e001c1944503d000d80c440541c02c0c100c001030110f180c6d14088002d040c149102801d400000242e41c2140340440f801003a28000c513a000260042d50b5009014000d801481180001095600107010100284101d81d0304615441c2d410f00c2c2d0101e558002a050111318030031014180d1050301c40c030480d800c002d540e80e00286800c40382085480647d448080201d90f10b0318401401c1c030303907400001b020580294107903003000b00d02404141445030145440da00800040e80c40600c00c3c44100070014041360440112810b90380d10407801c070038546480e1419074820b007000342c03200c1c134403110510f010a03a91041d03000032000c0000b038002010f01c004080051420a0000351102820b21041128121581d030480102c40445081706080300c403840300540804140d919a4001e1030240f592a04128207c2d03600034064404400790103501082c58982e51700c030040030b103c5c1043c016010380007848200003660050141080d48040a04007042507180030500905280b021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 655849145 1250 655847895 655847897
    0x1020106170d0807030c05070624030b0a0b03120405120c1003021b01020901090b0f1204031e0e031b0a0305030a081e04050604080c030d2c0c300d 64
    0x100756140840c030f6010301c0d081d030400390368101040340b03025504008190f8031500f0000f4142d1a10b81500c00c519200d02d1900300c1c41c40c92032020b480344e40d48d01c900c1c0c0700120420950780c0c0320405090400f001c3c100d180200e1400f125102e02c0302b44a240506d8482441000b8a203400020b240340205552520b03552039030000401e841071117517001a52104007584030a4a84c03107040ca03000f000c0c0e106008510151760000c200070300740c840c0303000c2246d02c8401c60071089801e8130800e820075000d000343c1d034144010550841ca0920700c1042d4800054400f4125440445082e0f06640d0015170550102c00c0c5190140c01e404030454613080054551001c2036113a449080c0756034416500000000c80c00010007043e060388008288090030081c01d0200c0605042d101c0c16a50302300a8000341c00001c0005110703000e01010801c45402e034907440424001c1c2543c3e0203050ba490003116809800040540889008210002c1203050300c904c0001c0c60621502e1100700f4145280c4024405018900c0780c80c800303800927000030009080e100c0c00c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 655850395 1250 655849145 655849153
    0xf09051005371d011802090c0306030a06091a0a1b2601140f090912091c0309090b1203181206010b041d01210813060905030f0a02130b0102010617 64
    0x4a0383d12608642c0b117045c1c4008440d1121030183c00580c1c9000c80d444d000b01480d07032815101d44581c400a810081c40c1c0c0d20040c00c040c6040c482d4000c0041e580c43e40102240030800b00d81e042d40e07401c90038209a40c09100345590003030301d80c1c82c8039581c540903980e91b01c00c40d6280c0c04140a00c903810580e0b06000b800a8112101c0321606d003550300070f1850412036800b18410191003440c2d0300c1c00c0481c2d640780c1d6a0241655800d455002049d09201500c0e09962400c1c81d10002e07011a00325146414013402501c2035000303501c1c02d5801c000030f403042403c1148902c1808054a4001c500c0c0208000c4d50b41440c405445007540e00000c80c004a001942040103542d01a1580840455985141030349402c4040404000c40e101c100700e610041084003e02c0f2581004c0d00d008181c03001617a402c40c54690f4291040050134420b1981c00304003c200107034041805000d440083c2c048804040d4650542d81e510405064000c2d0700c03c42c641c0300c2884a5400350040494454107000200d903482d290301e0724019100100980410642c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 655851645 1250 655850395 655850441
    0x703120f09050304230105070f0f020607060f0509030405031015090504121106040b0f090f01060f0f050909030717090402030408030403080a140c0a050d0f0905100537 73
    0xc552030f170401180c51468070b40b4864a050b00281841c050400c02414002c054014072091001c0c055407115034550080c1555501c0c0080e183c0600142595010003065500d00400541e00b00700001c05c031010b40740005e0041c00c43d0b28401c116900641140d0380c003000020f90010b030000f5054502c2c003486d40528421900004040d81986004003410140e806045803a03000405100c003050400080d550400440c0d00d0100c0c2036074589035101d28000d01c541e25501c0c00e41c41c01c82c0c000303100d0000d030404130b00b42d03948010800700301c43d500c0c0704210100c101035a04000e00d4008008031000900c00400c004800f002c00c041ea6401c2130b208030001412a0011a4280c1d810400002004101988041d40c01e40c04600034104028617006440b01101030305000302a6683e147c400110b15502c18082c2080d00c0d400f0034060300522150f1122020440503090400c412506442080e02c4240750201e14080c0d24411a013844080400280c003011081c3c1c5000c0a0001e105010741084802c004685a8064194941040115283e00705 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 655852895 1250 655851645 655851659
    0xd0203103605100612030503060409141c05042417070c150c09031403040905130506071b08090d0b04210e0906120f1f0b0103020c030703120f09050304 66
    0x141c0a9410000c042c606002401551035446682c01c80c146c0604e80b840d05d03581c0342d01c0814020445400060000c00d1100c962142000380091030907001800041c5801075458200e800750754034000c600600c4000041c002c4040c0e031b404404848010800a2441d100400b2001c035100780b54143e00a0b182200000c000c501c51100740702d00024446071200801e00100072548218200a10424590000904000381d00d2101c0d9074014040059070043c0c2402d000401c00d5040c12130800c08214540d4004803854010a00002c0b1018001e1482d0058050f551a20203541c01c0d841d600c1114540c455034285600000780006140030544070700507a171050340301d420b030b400c0642c07482c184c0203611000320f0201c442017200340c44600d5510340721101003a40000060f1414018004250452410102c5009000001d032080707410614208070440b00002414819050400200f40003900440992040e0880c0b840310f0343c010014080020300c201500711a240403041c0c0000c44105070700b10a000d440320500155000d40c0041014801c503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 655854145 1250 655852895 655852903
    0x122523040317030709052d0619021506181810020307020f10020c0d0e0d0f030c110306060907050a21020d05010b03011a0d060e07090e060d0203103605 66
    0x42c0c0000c64201210354032192440742003510400c403200b0441e00004801c47c2a442e14025600800c030480d075214122560940003c0d5116620b0504086012942c00441c0890608442c9858080030100c0d1512096075408125403403d50810300003002403040481c9030703580d1059032002d54019100c9034007614405030b4104a46142c2182c50f0441d00035a44100800c065152001458030800c6066042c08088140600c0005511083c0640301400c0c100d218412102090752003a843d080743d034880d04110b140461000c0c10f140c5c0d5040b04a42540d0002103000100766070034002c401400110443c0d24001d102c00316180f41d5007a003d051445540080381e00840c146070007001c203000346409440246440c509540c948414006407000803c01440c00401c00a524501c800c0e15030001070160a4095a640c1c00d4100200002c11000440c4140c0e0b041c041000041500740c58503900358000590020000c003240415940144014915000060545201490007151241c520b5048590044150004a0542115040281c20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 655855395 1250 655854145 655854149
    0x60a060b2d2b05010e010513020903061e01090501030c0b09030f0a0b190b0a0b450d020907051305030a0503030a050c0c1917122523040317030709 64
    0x641ca0403d0018008904c41c901400e04440c0c049403590102d0507848046c000912454010750b405009243c1002160908641030070b007041c1010340e4003a100c0c0e90355948031046607028040200041d446503400c206244800014040100d8003c00741c0300e03c070010602592404100c01001c549403001441008054104015400485404120180442c3c5100030000e0420000d9008611100b64045008412120711001600130010010018031a00300c5802c2950841881c0041c21680c040d01c8110000c0e0074103010002894665001c0c05440440e00d03100b4003a51250821400d291800c401f11a00280e0b0b80d604014200d8854006d01c003540d41d03820135298080640e14010060094142c3c10400c520803007138001100c00551006030f0b103069002280e89082100350b002007150000801b0081008100480b0141040c0d004164060303080003080000c01c401128060703240324407008951250068024844081242c259070000700c2c0c601071520303460780c3c0da80b4206a2502d140c203520110201c1005559070b006006800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 655856645 1250 655855395 655855477
    0x3080a200109170414061e0429070210030902040b060f030405070632040909080c0c0405010f1404180308070201060f0f0314100608030a02060a060b2d 66
    0x880c0505006031551746111040540740150400950141c4075400f00c0a120002405220982e549955070801c3d0006221220f23035529000204c40c003000f65008080084414595000e00344000c40c8050203002c0d0700401d01078800381d070043d442cbc10406a40c0d80d1400018a400b004601d0f15036140d00702801c2c400d03c2d101540e0000c1c014071038040110070f0b0002000030454003008a83e84894401d410103c4400d00c0750065a104201650610329041d0070040045c0c040d0000304204000c6030744104280b400c0005503003003031181040c0500140e4003444000e55281000750315003000341000c21104034070642070101c411112803e50026181c003040c00310391503080c05a4001403918100000c4001c1c140400c030301c5c0b2030801c1d1200606440d0124259201c0d4102030003a06026003140604000031652103444640741c0d0b110f41420001401140002070541c14076215000030f50b075600e1902401c024000070894441d0078403268034044826008550040c89500e00001c01e903010000c01d900720a0300025090140c1484120811a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 655857895 1250 655856645 655856647
    0xc1107080601030206130e1006120516110a081210080a15020c0f0f07080f0303130803100e1609060201090302060f060607020613051903080403080a20010917 69
    0x1015840005600b81500c0c4c04942c8113941c0c05103450b1840507140030f41d101c44c41c140b41ca0410820000c540c03002d00403c4440d282c031034510380007481000b5021a5011500c01c010302c0c51082c501c0b0350340c42c850402141f4505524017150b0b08801c0c0307915041075541201946071481140701c020480440f44c520340700300040130200002e0100882556a40c03400340700e00c28200b003000d5808985130346604030402c480c040150200f802d0300c540510451000d0345510a80c0102d01c102d225201042e480c00000004483c0f21f1000c4074000790728608195540225944060311010b0a840b00c071001107580305040c2c1d803040c01410355440000f6110041c11025240e40c0322a80801c0039a4501500380740032a13004210310358400542d502100d0555641000500c6a01808401941044001c1070869103100c0c01c1042c841550b80480c0d019a543c0c0140e40191040445404005c000140500c41000020080d9020300001c50076800e14640c1c65501070b00301c80105456000e40f5445079111a80c1105104c40615448491030040c20742d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 655859145 1250 655857895 655857899
    0x9120d0c11060705121302040e060901060f0302090c07060b0306010906050108071b0b0613020f0904050906090a06050709090e0c010914060a05070f0b04030f08060916050903070801050a0c1107 84
    0x743c0103000f601c01102d03c01c11801c00240c41c0321188142114500d0340140100f25a641d6110052b41e203100c1140c014943c3e41c40c3c40c0010075581c0d40420004110f0380d0040406196941d01d000e140340c0c40c1c010990498245440b090544131a64003406494007819880200041c0203247c08001448030201a201c00107021104a2802d5403d80802a50324143e4002d43d410b01240c850402044860080c440c460750394501c0440e92030030110b41540140700344003040ba4180540d80342c10100ca0380320241a10303005915030020030924001a0540c00299004842c0c1c01c0c00d104c05a51400c1c0c640c04d03280100040c0d034040d00700034000005036801090140c094039820710307000480f49080c004185c0c3c5126403a940c4052010104d840c00c1045000c04e10740748010340c0301070703141e0003400c0c103240151507a40c40d00b01c000081000c0d40000341a074100600c002d4440c41000410b4090520746400c16280c0740d0050b0070403505801505008907880009002d81800382d00403190003e01c0c1d561030a0020040c02c411403600119070404813007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 655860395 1250 655859145 655859147
    0x140903070e0f070f09270c0c111804032003030a0501090e0d14070606210c090504050c010c02130504080301140105040e040215130311010f05090904080309120d0c110607 74
    0x40d03030b001c0c6c0d0180611610b07003586421002d440e0344440d20034407000030f080010300c8110342e80c000c029403009485006080e20300c030b070520100300d0800e2005140402e041101c50015020070300c900c3c40182004070402e440a00080416925410742e40101c503c1a400c6803517500400401c000c0c0d11514804444c0c40c806802101e20a10000b000010a10000444281c022842d14148038059000c2c0c0b0040c182c446060400341280001565481c100e40c005071900c5440910005100005010b074901c100d80c4103001d00070168098005450a0b50401c4050342c00c0702400e81801074944032849018061401076074003a4607580f4000050303080110a075101030401900f480200003040440b10400d0704641d044421810502c0074049000f16400ba0900d03030f100b0074000500010a204a00d2030346480a6801e99502801145646060380c0c0351207560b00054000044a000a001c541c404003d9030b0015409829182c2c60b09800004180f1900300c40385640a003544c559400700390940041c02c46180c0c802243c090241441c1102c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 655861645 1250 655860395 655860407
    0x40f14190b0912070614090d08010b0f0c0d0c060507090506030a05060409170408190206030f0a021c1a04050702120a03021314040506190501140903070e0f070f 70
    0xe401082005003a010400e105002e201010a407980071811a4460140307042c11405032516030361900340c030940070011401c1c0c01008a4500d410301001d40ba40c1010381d10380040b407021a4403000c1201e400e10018411961416405c5c402c07001c03c1c00c400e43c0c0e0000001880d04080c0222600581100c080c4181401c2c10041d0383c6416090325800b4054800000b000c0e60b8480100e4043c2c042500018850042c0c01c1c0b0300b0305100f1480000e802614045421142403000481c101c4040e01d0a01101a50201003840040d0f240b0400302c010543c0712488080c09400c003c031601c0c400f0554954113880c07008884e203840030540c0a01e0300081c1c203135101100315824002e40c202100045e40720201c0710400c01c104400040c1130b5404500940480740030940c0511144050790f030781c400e0700e214002c80200d007522542c1000007080b11072801c8840d036801ea1051280180000d46818010346104000c4c202e0a01113801c107004401003582c05200c044010024050854030310300c0d0030000803c481c1c4c002007040c42444101c05031100502d502c06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 655862895 1250 655861645 655861693
    0x60204091a1e131d031312030c060c120e0a0501180c050114130e070206070f1b02010e09070512162f060a06061103030c0a032003040f14 60
    0x2640540f005080e410503d0302030240080b900140c48030740d80210340002d4002005140210b0b084010000d00d43c0c90310b0f844014000c480901a0001d207901001d0300109400c0d502480b4081450709114100c41e13859a0440282e441030780316100705130080101c40303082c0942805a8030011f0381195440b80000c0d03855031044400411030290604010a800783c1d00320005a55040b035031041c01c544022981030b90f64403c00342200b101101e16a0041c091040410601801180480d000c0c52076519a05460b80c81c054082d81039246070701081c0d041014003840c0744402e8031102d0303115004050554805030fa42440205034291104080c0854141090524903072801580c051607528441007101d62945181c103190340174111070403103030030803446038015081030200f420700d035501c8802200c3e110b071129006414030104103610b0340012130b0201499101000000a4144030f54030254240089400c024400544c4a40c1d0784103641088a0440d08210640d2020040c848070035101000c10303180e1002022951034002000101050f00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 655864145 1250 655862895 655862899
    0x15060a0306050601020f060c0a0914010915030f09110a121a04061415030f12030117071e050f060403050a0b061f120e120421060204091a1e 61
    0x402c0032810340c0c4c5c428032030b1408034240d002c21030301c080c1000c4e11110b10304c0e400740078400003146100d400001c8002d9038480b121a540c1050715046000c0b450310a02c1900740c03081d14a01400c059441c0036003080c22615204842070305d0700410312040c02203c0f4070180034005190740c2003d150000c2500c1d810001624412103070f40c40740102008850107440d01c0c6004400392601c005030021240c1414104101c03030017045101e0440311802c2302200c0441100d0b044968540b920803204203400281080140500c44a1800c1c1030b03045c007200421145d20382e1390b4181000384d8010842211040150b00c440420480ca0411014600c4090446e0214a03003851591101e03a1924070840c01404002c0b0a00002d0340e035942d003001c3c030002250300c0e03141d00e5214032030840040200540c1c21005c02c00350b280c07a03191104004002002001188404119882c160802030481c1042100e9190244140405040b60000800e1400540024250088041450a01c504010300c0105d0140308503801080001d110100f4134004403070a0a00d4102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 655865395 1250 655864145 655864151
    0x5070c120302031201080a12140a03050402030a02031f0c03060e040213110a0306032907120912050403140f101109040204080a021306080601090e15010f0815060a0306 73
    0x4030300c1c00780c0c2540149510328080c02490000012415400300703036204041d106028011003100340c000c0545041c6000f02d101d201d9800305200640009000360b00042d00940024119440c02c1c5896000920b00140429031642502031003180c1c18055070741c0d000301401e5140904060101c103060013040e80d0b40d5080200041d106020100010114078520b41c0308401e51540000b0f22a03540450036000b40180203c3c0c40f0854400345601542d01451680510a030440ca2840680100759140d82e82c00f10383c8003a210160040c016960040032001a10010108084090030703100d65448926608250344030b1030704883d000b40340b5003100c410f0341016100400d6040b4401600c000003d0000d0740d9940ca8401c9004810566070072500c001000300e600c50300007400c032a4140c8225102209082c41100d0b100a41300280326481482d4441401030081d00001e0300118542100340007243c0d002d0610700d6003590b03040c8080e400900b091814950610121070709000207400601d01c50b007460b496040c0000031685801d030038800a0100d590b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 655866645 1250 655865395 655865429
    0x80406020d02130f06021009111002150a06060e0d0c051207080109080d06051f0e04180318080309030303010314161d0105090705090904060b0312041505070c 69
    0x1a6041c0d6062040983d01e000c078190304d9034180343c90143d40f4054440176120781b480c60041001d013030240311415a44220120303114910315013402803285642511105501501403041c040305e01c265a03591003420101008207440e890100e020306501c5400010f43d010310660000310303000c01e000c490ba270741c22254241c905e00d1010480401c00c40c103201c043e802020055013800010342c14004040c0141c805403603c113908011899642041040840795110b002409500900907005214000d0900c05001c0c100540701148000c407002c0620140104200b0450115030380c4440d0001d84540301c040b107005465001d0095150900d0180040d9032400705100c01445d60b2683c06003404112010301142d000912502f51507000f00d40c541c0101d01400304001d0307100040d04840381c000102840e003141c099000d400c40340c54440c90041030509100a20360010302c15584580c503014091010f40b0b0822583c1c0c42c00712180502511a130604501c0900081c0280402d410003100b40400030104840041d00022074034a881c480309004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 655867895 1250 655866645 655866667
    0x6030221090f03120609071b0611191205060f0312071412190504060c02130b090a140a090308010611070510030902090a0515060c0f0d230a08040602 65
    0x60804201c0d0245804041213240f4003010308101d0038059882101c45400ea960303042c600300c96400000709034000701da050041c01d40102e42e0660140c083c41300410300203880c0480c0b00071140100c035180d20400000900070780c04030107031220074402c3d6074000301d040300d0080403c00c2e6000041c0d0b8411280d400c98100711400a9140100060040741c2281c041307038142524100344166118014540240c0e40c240700c2c004c0070104000c540c40c0316100700c9060f120b0940366180c4400107a02030100303025210007110129940c83c0301109040e40c1c0d0034040c5200390701c0e101b80820303050340c00c00d805129104003925055003181010110000250400b9a0a064541c0c51911960f81640b01c1034041c5408901d40c002504071080901085025615401ca408031500039a01e8545540b00c8070280c404548007250561075a1401c00c81d2203503603192903401402c080c40201d00706e2362540b94404490f410700350f003ca801e00104524068001d500c0302d5241540040001c020f941d24105180d000c000740a44400400040080ba0700081002501d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 655869145 1250 655867895 655867903
    0x110f0f06160b010603240b030726010e07140f03060d08040f1409071805060f0f040f03050c01410706090611040803190201021210050a0603022109 64
    0x750001c0c040c0d240c83d65190409401410341c0f000e641000340c0b9104294070003044c01040b030012a07001d158503d1560b034442004070750209080000040c1d15184000751102110070006442c003030542d00903802c0344c40c1803401d405801c07990704030341400e410842484044102c41041c42601e5014800390f070ba00c5402941440c100d03109115603000380392800030758a008a04072036002e80900100384151207d2a0341e0722401d106542d00d281c840519031407042d40b40741c24002c6040c06000791401380c1a01c04100e02301080031440030407541141e00001d49500c250802081402010054509041401e00380301d03490008140010b5140c0041c2e1240b205400d8002540b246560015080c0006078922803c1460f21542645440070291564103400e07140c95040401e4102e0602020301140c08032850b5200a500d40341c0040d0325240c0745800b001081c025554240141514080001d40c6140b080006110440e001401e090030401c1a045940100c020944180305042c0e607404941004210303541e440307220404580da108582490 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 655870395 1250 655869145 655869187
    0xa031209080c16031203020c0607110304090c0e0301230103060203061903030305060a1703070b0a020904020f131a0d0b0d1202010213080c03030714011b0c110f0f06 72
    0x71441021801c1c0c210507240342d1942c0a0324482e11000c202074400c100101c6c16405418810086600404045a0803501410090f2103d80200003660304081c1d503401c4020413210700d48600b44c00b088607401a446207150030b00c10b40c802000811121180e404c241c41200380400c00501005006545c0040440d440d81d41d445010b5403240d0300ba0701a411295240e2400401510058035000d015440444010682c140504428100707103506030000c50800d000e80d2a15600d0b281c02070070200c4a568201310a02e0710740c980740010f240303060300c610307485690f202500810026500680d0042d810314215a11500310380750070908072342802c8034032200843c1c020401400180003001214000b0846494403500407840c039019006071284000703a132000301c0312580c1c0764102901c800008030960b0341600700300604400220f85a06400c600c807003207000010581100f081d100d0300d800185498101180140000004124203410f088800c0502070f55002d80350740071400450640618400f5152103541e011516140c038803038105007814 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 655871645 1250 655870395 655870417
    0x9040804091503061a0102060a090212070e070f02060f1303020c041a0f010e030a1b0f03030503010e0c0c0c060f090d0b0906010e0403050304030c020d1202100e0a03120908 75
    0x1144031818031032210306a42c43e01c0202e0740c8506100b401000c81c0c0c0c2c8015801d101d19010380180807079070b8510040314000d10310b00c0403c0764481c08420381180c144c01e003042160050b00d0754031420516420b00c0e80300501039140f9980c00f8001c42d484407082024440d8016240c9820082000d081c403400d40c400e240584c189a03e00c0c022a4201e03282400a005181a0b404d001d41000000d4a800600c800c0d800011141d030340055071881e400d5400815444000aca2808400c18522201c4101c41081c82c0c40d9401d404400381980e000790005880880140256000c2c000301d10f42000480410615107215110903607241c441054090f441000003040e840c0e000c074112021681c08110040541d90000701616000c4a880010303505081540b0500e400800d0700c0295110785805581c05854050555880b603030100d40134900030344101e8005d11007403c1003002414400504209113180d03005080303100d4094080d04101c03503801403030071940c0d800039501c200440c4d0458148075140c5220a0301260307464440c20b081201d8840c80000e50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 655872895 1250 655871645 655871651
    0x117090c01051c050a091106070b01120c081b0a0608010617090c03010c1d1008040602030615030a1a0907051b030c0d020703030e061c1d0607030902030c041a0904080409 74
    0x811704603502d6114055451048005c0c001641201c4d081c41071500580c80b00804107c4514014003d44011a1040c0d500781e05c54403141c050103441349031043c10104051034030070311441c2c02041d958491525640000181010b8a00840e20398508400100640100c80240502d042e0803400f01f0004d00c0e0904c1040c007600340190080c0304825a01c0c1c0020071540c41050742e405800b107140000340c0980707441c03440c07515400301c0d41d41c5901080d1600d441d08402075202415079a44001200c85080310a90000b01a42c1701d240e40c64800100ca81e80700390b5104041ca40c59041c1840350750a4001c001c030503070b044019030b502001c2c507412501c3c91010540380140307188900b1070300d020b01d4401c0c1020f820115074006445005e4038402e5071408081d0700504280b0086000b995400e001c880040e250780030f0030203415440078041d00621030100441c0442fa189a40c14141c0949d400000262121048401d5090402c00c2511001007642c0410101c0e21050b0003001056030101c05e548907a2140c4045028484810705480146c00001010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 655874145 1250 655872895 655872901
    0x909011b0509030f0105070503011e09060308091905060a03020c0a080c030406020d031a100512010905010501090617060d0c03050601090f05010b090906090a060e150117090c01051c05 80
    0x3810740d4001d11510382c030a04c00c1c20721206552206001d19409903040e51101c501f56403e090100301e4282e662400b4010040c4490400a41d121041c06000c00450050103800d5858100506025413134064805024145010200030480c40c1c44010458850020625005031140301c405040c80c10500c180390003501ca4070020900d170b24803032030100041c42100c0b01c5400301c031403800d600881034054461941c1d58940b038a00d602ca01000d1800c00c2d110480c1241c02030314001d840c0001520100007824420b07001203400503901c02c010702103544c1111501d0050645800d11401440031707801c450403240d200500107406124211610010003840c0041c040c0a598404165030301982c45000380d10081c445980182146400d081c000103284e1084401c036400014060000769150780c40c00280179100c0b40c090810308038996900703000212450840072040c000d140007019000d140c003c100006040181080007041d80740705250034015182c000140c0c004040100303003401520ba85020350074010b62070085002034581400c210070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 655875395 1250 655874145 655874147
    0xf03150c0325021f2c0c030613030f03060b18030c01020106050a090e0a0221011803050712020c030d030506132a14040602010b1503010609060311071b170307020a050909011b 76
    0x11400b070010064040310305225821081654a001c203589c055140140500c0c1200420b20480e90743c1d01390105c6040215030681da82055100030b60012420314944160b204007200e6518050001c04070180c42407000740400e0f420000050f01c003421030303c501e100c020307a90b696010100c01c4c01e00c04640c0d02070b001012414220700c0c42c400c030800c01080304003904581d441c2c01301d2116600500109882d103540c1551381c1a00b0b21125a940026026103100700d402984039180010f02250740402940d9081d070790f80c1e5808501810024207000a1006c440715400465040040d0881503260016010310f104030700c2203150303e00980720032080c1c0b03001d06150400c21604200244c082071480d0150451441c610056800745542c5001c8000c100240c0000c3c02500001180c00302d0400c88039110340c10001c654030044010074580b040c542d580e10360100c015402c552103a03841810800a02e500e180010706800c003804083c610702541d560002d42c00009078010b036803240407e00041a00c6003025480070f00c0100c001040e10300003009101c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 655876645 1250 655875395 655875461
    0x1106130e0c07080a110f10090b1302010203220e040b01080d0212032d15030f010e030a031814030d0b0a03020d020f03150c0325021f 58
    0x40e901000c0c00c0900868241c00c1030000b1a00701a4000e0040b500782090700404036a1410541d2004d0828441d458590030055010302817402c040e0044200040d05080c039150001a580c0300a01c0e11a80200b030112020150341c000c8101c5841200c0010424000114458140b12031a03064200d1442450392104210030420700c110309030f058443d0302d41240d90901e41240100d076205072442e01054107550a001154030180c510300c1080d0925010091042462208102d4020b400000c81c1c8640d4001340c041c42000280c20103020310303c0c2d020202c0b00240003104040301d40940c2d1b445110003484c101a554a500440e0000f038160806015078810007101c104000c900c01b19560382c0040100c0c140452525603842140c0c5403003a0302508a80d40079003401140c0c00503801300120714000524654240c003842c003140e00c440381000d01641c0300700a400240e580701c0c03d100022200b2208401049110141c0740054140a83e40000c2ca455054004516003400c806030540d524014003207840111000800c0d000c100d5504c0301c4200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 655877895 1250 655876645 655876649
    0x1a090f07090b150304260409020f0d1407050415050d0c0309060f0e10020706021c0e060606040305060a1d0d0207171c0e03190f05010606030510050d110613 68
    0xa424070102e001e2411a002c0f83e2000380d800030150300311040b0034440d120500036108902901c841c806401c0682e9030380500240c2e030100b41054854000051071a044090500c116101452a0368096a8900c0c050301d02030f2091040d8000c5880c4060703032100d5008414132880c200c80d4a00700300e00052144148540d4041c0107801c51000031680681403444049040880b88141e5840c040c0c1200102410340d0f004041d5802944148402d0310015000c120311900f002076a422040c2c4074000c03100028032180e001c103e280c100000a0041361051504010410128070005111034104201400004091040d180c6183d29104c80615064680c02041420f000b41600032a600b021914a500980c03401c24a09850030344403480c2000410700b01008600303018071640308100e51a00c41c4d9015003100c105010001441041183d241c4085980240446d402030802000b8050300c001002726081c1804030341001031409030401c070745000f40740c0620110b00084091100810042d03800031409044542d40d03102030403051103d44424 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 655879145 1250 655877895 655877899
    0x904062d080303100303112503030914130c020715050909150d081e03010e0a0c0329031006090207021f050a050906120f060a080601031a090f07090b 65
    0x465400241200003000302d83c41512500030030361341142580c1d029110002004040110351144007111035844409410035040403d050040070321041c50b5250090108032140c000c032a10700c0041441c13a01a03141c100760510900390001003c1803003001280c0803450800386a0141340d1207851034060040007500f00008250001d4151800040c0382e9a070580e5060202c002c22405811440789031803c1c0108200801405c2814000b00001505203091124494103820a8100680c8a00c1ca00e0038480dc2c001d6500c60260720010504051041c070580085007081c28280281408980310220121901035400b0f020761040790010010400406880c0d80d181c0000b900308901c200c3c0120610814070740702c04500007421207084000d80d600752425046440494841e0801002541c2080050212107135400074130b82410f00c500e400065030302c207514084040100116a035400402141c00010050010401101400c4a4041e100c096102c0d6500c69503c45450120454003051740e50050030340125032038905400106d814841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 655880395 1250 655879145 655879229
    0x80a0507060504261315020307050f030d1d07030b0702010b0307080a02010e01091404020918161206031a13050d0203121602030d0e0106090f0f050f06030d05090406 72
    0xc03541030000c55204041d585d41c41d0240c0c1d00b0040244080100c00c40305d001c0c00c10b1041e41e0900280d40d0b0380c0380c03501003621443e084582001c54207411140451060019280385031219180035100668070a460701034901000d001030302043d0002d540c0c04e000b50401c011042020b000c5640c075540d940ca41648030b5030b4188040380001c0c11580442c0c010f606c2020402c1c1070b564004e0f11444041d40c6042040f00039440180c07081d401c08117407101802e4250011441030720444803204404075030800f2540c000e2120f9841150b9031605490a24180041a00d11002d10480d0440b907164007955118204000d6101c65000c8006215100f0b4074025201c0b243c1c0880a030850400e094200c0d50700d5120070540a080030a020704020040c7c1c404c0c400600d07640e1194100980c0350700100e000041c41c83d1907020341000c1d107507000d1068446a03221007996015142c1842800c0d030025000301700700c11605103000002d8440800e0f5201004200d408038000f001c0f079a85901800041021880108030f4200c600302e40303103850384200415a54512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 655881645 1250 655880395 655880453
    0x51c02040e0f190f0b01091a03030a0c03080c090a080718140f04150c0302090117070c0305030c040f030b0402240306060d0e0106060203190c0807080a0507060504 71
    0x4000644000300c0b11100c1c01501000c1c40c01c0303c228031010b600002c2550481c0406007458007250706000306034064444004080703030410f43d0001c44100359010340d1000c0e01940c81040642038281d0b22009510340b45915150002c42600d030503a880240340503d0238010392010a17031000181e01840018044203d4400884e07509201d40e007800b061040390092400405d26100110000307859517605c9141300c2e8000e00c02c0d01d81200390034502c0070007821500341c440802d011030350004000c0243e6030022070400200410b030b100040c448c0b5003090001c241040b082c0c07000381406808008145640491402d48000e400b042c3c24081c491640c1b0b042c03201c3d4841040d03a003680100010ac0308a011075a00400072541c0d1081000ca0525545614087c42801d80c00344290400c02030762040320080c00715083c041c003401840315600031a120700b480403c2c180f040c0d500d114050705008240002400040d229010b03501002c0d0007003401c64841c8007e000c00d496500c0761040c000c01e100e20307001c100400c0100307401440c1d0140c000b000e07540780110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 655882895 1250 655881645 655881671
    0xd02121003050601060e12060108160909080a0804030c0b0c0403020411090d03120b0d0c080d021c12060305060f0907080d0507060c180b0316080103080909040507051c0204 75
    0x303111400003900c55000307400140061401408201079503500038000020084140300c030b4a041050071b80001c0c981d600000c0c1040a081940c80c0c81d13030003501c4404410804401581d6501c0c645204200300703d002c0c041400000740a060003204540d00054000895550524002d60f03504000e40c854002240b0035072900d12254110071118050341c010754005031041c2e0280354117031010fa9540c60015401c2c0d4041d611102c0721501d035115102440a202e01c10591400250308141c000c5060a00c0c01241e0411540700e091200384544070100400084400b038104000200c03021400640507000c9600050007921a40041c0040304580360350341c1e481a1854001e44440702d0f01d80540030380701c1101d40340b01400601c040c060311000c152240d218030f15059a07801c101d44042d0380c4444000d08402940e00c4980c04900100412010100f03451002030740d000b9911b4414019819030b51854254081c041820740200100300c006400c11030100204c0f8007130000102141b00d8079103c0d003060f0900b0f07501a64202d002c1c5050a039030301110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 655884145 1250 655882895 655882921
    0x40305030c0f06161209140106140f0414010b0702210c010f03020a090522140708010608060108010312110f010617150112060b1c1b0612020c030408030d0212 69
    0x36041c031703981c1c070a04d1403c01c501e00c400b03804016410703a07481c0c42d21080190720040c24850140148000705040241c646204208a0303d64198400307a4003071030a00709005000c8062241080c19540104561501c4d8107543c00484c290751041c1c20b0081999000701c201003450003001603644103200c026030703d1007041c4c040501c0071401e07030041c9400000030031402170b4148403d14007944440b580e40249500300402c00f140e01c100304207589041617020021250701c4188003025a02c0080035001d442e903420f20500c0781c24440d000902d6034034144405054211514071058115108003044d4805580a030100d07090030702321001180c001c2070320b440781c9241503200c50348243e007901c8003060188602100003081c10b070582c039041a100c041c400310743e012140295181c1c0c4c48815699880d0800c01d01000780700c0e00d017201010900d445c1200400380c0c1144080005548000c0126541c0660312500380642c1050160300c5101920b0b10342c1c5107000b51340003501f89010204042e0404039240e405081c60b4000d00d8079045141c0c130307618000300d10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 655885395 1250 655884145 655884181
    0x41e03020706030e032701140304050a030c030507050105180106080601210c090c05070b06010302070b070f0e0307031a06010903030f2307050a03020c012d05040305030c0f06 76
    0x5a00070000c20026203002c1c0c1e0103000e450f0011826645401ea824020f000c0c80d0035411820038801c00d000384e02000950703000200c110881e4102c01c0e11071075820142c46569660890380d100408002c1444030080805200b0800c0d204101e80c420000d00c01401d0000300c0d1941c5043c28074050405620300400025040c600141d180e0407211840040c02c44942400c10010190070348910640d074039201e00c4d00010301e0610038425911002c8060766510b4540d001803400000181b001350403181007500620854001c144940c40f041d4000809041c05401c0031420031048c0c034000f8400c408150325000301d80c00041070148400a45c01d60819000001d94290f13518030044d01d00c103001340070160001d01e801801300c1c030b128003400301c1859020602c1d0007800201501550b81c000ca5001000864030740e045500c0f003800301601006550300744502407c041050400050303403050490351a6440c00c441c0e8000401a41e4007a009408542c040c5801c00e06981c3c0d6490b0b00c481d00c55680207003080d030901070300c503040004000342013007145400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 655886645 1250 655885395 655885397
    0x506120103021c0b162607090b0304030e0d06061d250f081504050a14070201021c0f020c030a0c0302061b07061d0d09031a0402210a0515041e03 63
    0x156455020403043c801403c042185c0921114091420102003902e0300480da5104a02500c1178901c0c00030702c0205022459480707014070500034001d02c00001d030003801e9000d082909a030038580354105814294003400c11070784115018260341c02000c1202131102003d0b840780f21840c01503141d2074050b122003d228980c0d02282c1002031070525804034018450041290400950707814400b41c040008001021200c050707580d070900581d21480c0f01c0000c42050007150380000980000c5040c20710708100340d281c010803280104110b0303954400100301c3c00d2550341519400c001c0c4004403500c42136410070140a0140c000003d84c0944101d80010b500002074076000c2e503c00380c48c00030040c00c1901542d141409803040d05d4911005108110300030007040c00c20041c0c02520446541c804c10f44034594144070003281509000100d6100c0110104030242c4c6621120203240030b50361802c05c0c40d0b00100c1541c6410a01c116600070b203280100c50440d0b110201e107090321030086000d0a4403003803600c0c84000c01d60a890745608010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 655887895 1250 655886645 655886663
    0xa23041e0f080d110a1a0613050702060112031412010e010b0f07020603070c1a16021c0807210209090a0504020a15140f0309010615080a11040506120103021c 69
    0x70015910446044525613007900c210343c05140156501141c01c100424070301e9010b61503400308a032034a0b1180312540f02080c050401c01603801e00761402500c0b20014010303880da0f9400f07201c007001014481c00808092010049035152030320070072485800d00610a1054618440c1e0400c00170902041000032203440302e94a41d4242e180c62043d03800d01556800043c001c07000c7c40020010b10001c198091900000d8100381008a000f40ca08882c942d035610200c6a00a02150304c0340d0a0b5218820203040b01420724800c03400d0096596840302c40c2110f641d4180c50010304100740aa45c4800e22100b00d8000c4d18543c0c804407900c1c08940e940d1403032201225000c8401940c0450420300800403031911520400e0140c3c200e00c0c00f10105a50401c98210701d0b0700412000c1d501120001c10805c40650a00c00c01c005498070b040d909014211482004154950140c140b00d607031036403a525400075120a0301110004e01d0301034401070700d80e0302c1503c0342036580d1000d21060780a55442c8044210000080c0b13a10203200b54040341d05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 655889145 1250 655887895 655887913
    0x9081c0c0204020408010c0e0916020316050c1504050109050105030f0f071e121107080a030f020421060b01030618051314060714030103080a23041e0f08 67
    0x3258440400c22090360007507420000498414005e001d030034105481d0392150005c8520150070700452a100500480480e030400b00015400b56000c002c0b150000712005200204814500b005424200c900c280c0c41d03885016a103c054620080902800c2114070980314103440342d40e50401990607100c2101e04154000d5800c0c0000d0207803020f040565004481032404405c500380b42503044003150300000c225008140c0603400c0c00340251407401000381001c405041142080c00642d1801c0c658002c03000110203040c0c440d00441510000b48d41078800030a20160700e00280d1041c0c00004520610810050718443d0401c03108144a5000c2e01840086503d908a9404458044907104000b0000901081400d5284090203c00329913504c1005100c0c0c0700e924041c1c00c65060401c00604004a10580c0d0032090300144010008104114180c81180d0014203001071411045a24003001202404054807a520003007404100d90205480c402502c80b1001ca45143d800d46030700d00076984207940d11a1001583c007060b14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 655890395 1250 655889145 655889147
    0x7060201060e060f0d050c190e09010207031e020a151a0d1e050309090c2508090904020609090c091203040f0504090f05010906020a1403060307060516080d05040309081c 74
    0x54996918002c06c29981034a0b2940b00003001070040500e8003021480320001480b00c44101c0d801c8a8011135004006c40c54400309a43c05400c02203d0404134000c031002041501d2464002c0c0258006940c2c01814a8410340d120043c12000f81000c1c1458a694a00310064500b0b03424108900c020301a040540c0212002110031805840c000c00d074011111408280007240c010b440b184441405030b00c14980f40341d1a0301e50b45020210b0b8a10030b643e02d83c03490508680002c00b01c0c021000b01c0d0045c003400e40b00c40d07900d55214004281c2c03505c00c050030789401c80c4c103c8040090800c025005861500c82c101d80e00b84c14442010750071556801540150555918440801c00c820f1415901600a15204001c4880780802c952155402c440004006682e05500080c00801c25588500784c1d18000e01000e201d5810350811a0201c2d0741c488890083c1e070144032000036804020f2200c47d802404548e030241d00203030384101420500c005028152412800300700b0a24010401d044046100d10004032400f0081079001d481400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 655891645 1250 655890395 655890409
    0xe01090b0c070b03090703020301051303080c091518030d0e01080c1b0a08040504050708010e040b04050c0a171005040302061303030605040c081e100b0d020c06010807060201060e060f 80
    0x11001c00148200400000e41d00154000b441c402c3c01c0c418080c1083c949940189401d440c801810301c1010709840394290002a0450000e607003000240d01c2030340e1a01e0305000880c050405c000c034049280031001c685508404961a041043c0910603001e40f0050020701009403a02c0c003200000602040c0100300141c0020303680c202401101c0c0282c0310030100203900010b814200100e803403051301d54080019051009042a001d85138000b0f140d0315094142d5803405d80342d440107100103400140540520b00c0820103108040252607113052000742100201562042c0c0d0041034a04086090458041c1070568400c2011034400c0c80c1c0701396010340243c1000e90321408150030006194500302e0501d90340d200e0210302600c4509c10740c0762030107442e2141241030a140703140448480c1441c02042105460302c042000c60b200c1100c06000316030058540c25247c1d4030841c0e214000e80259500e0441324401c4600009101e0740c000740703178412550345070001c211041d00d9030309141240c0b000712403041d00020340503441006400d2071a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 655892895 1250 655891645 655891657
    0x31903030f060e1e011a070807020a050a0b0c010f0c092c010e0a150510030902010507020603040f0308090a030c02060304020d0c17010b01030e1002070c2705070e01090b 74
    0x7803000200340780c0752003a40d410700c541034404240705a905001c00d658503006242c598050a00c1300c260b9070859842c030f010003d0a12803400020b01406000ca442421500c4144c1180d0207814000c096102c0d19032541e01090303140d00800e0300d04040b903082c0030400c0351240c100d1003010a440d00d25501d01d44010304103c00e081d0059241542c0c84107240c110b01c0b5014021040a080d68042c00ca407256903003107400c100c403046054601a003204048250700000030400c513036868003512a20041401d021400400500050311540110a006901b0020010401c8200030b114040042c50610035100c1d450355031201943d055662201210090100320003000340d80262030a00080c5500c40c0c401890ba03100000c5c06d5a4082403040c49502261003100d8540300c94000306c0c0280a5092141400e1800b00300900c2486800356480d8144580810400d0b40000c8007400c0c0661111110090058204600d50b2112220031050024095242d0410f04d1481d05000c00c4580e803240107403c841c40b10594990b00e80c80e00741000d0600300c2d8045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 655894145 1250 655892895 655892921
    0x409020304081e0d0606260a0605181617070302030a0f180210020102070c1406070b0106081504020906030402100917060105030609030903030403030e060405061c0b03190303 76
    0x611203038100c207104040380b0783c0c00004846019200c0b010042e00b6025101c8035000f902c180b01e0740c0101c1c80c5514541c1e80300400e0480d01c0801011080d01c42044500041400d90020b03500011504024002072070303048440c50081510000e142c3d11184260400c03682d078141c0000c000e0b04000d074000894002c1c1e110341c02035074105488045c00100744600355608000c03600601d01344a1003031301900c0c0340c009515000da100700a00a0b0b07030009502d0607c2550343c18a00c10f03518004e04050f0b00482c410000c06403140d0f41a103111a50000005540703585a0001401c0c260b0304443c000c4d5890004490b550782400c0c0360003501c0c41500060012400c5803140c1d420041550361811451080005654000a0400b110b4018032500b0300044080e1905504080c103250070000001c00e4540160310800024016031400403c450880e501450504a00260000000c5441c1b2960380280da000e400461a50016003400d9403051540c000340700d0402615014178103250300d0340b424007001010318a485401c480440e00a400c41540e1140b2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 655895395 1250 655894145 655894147
    0x70f06050403120f0b03011b0c02090c0d02030c03010806010f060507031b060c270501081612050a0204142d0d0203060f090f0601030c061d040603081c090206040902030408 75
    0x9080c1003d401c50b603818103d0503503580c03140d688403000c0c01c0c20700c20100302d50104001111400e0803408080c100c0d2040b854001e010309640d20010b030900c1450302c2512103d20200c03600355601d08000c0000030342504280a045a940141000044c1050014a20000300d0300942c860300c1c02c143c40c0340c0701610b5121001a9030340314800c04030600000905a4803c46400c109aa10f44600f00103074803d203c40c44000f446c0d14400350300d40072081844660b0704062040c0e1300c0a04440203000300e800400341103d08032031010b0500f519034205030920603001d419801610a591614030b100d4110100c0b00e00700b2280340b95038103425450008030f0310540c5440c06002244880038001400c0c10048403920740c0802d183c008100c0d076807140e02a500040c451400710a000d400000c502060042116504580b03130b400b90b8207070758031524003480500040c188101c00620172401c2484001081000000d5a90130201071030741c04880c0380052000050406001c942241c4140240d103600500070609040c20b112022000350300c064401c0c1d88204d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 655896645 1250 655895395 655895417
    0x70f0315090f060f0f05010b0711011407120e0102030a08060103050606120103060204030c15090e041103060f060307062c1804060207061404020f131b091703070f06050403 75
    0x9240b8001e1040a01c81c0c03000203849111458100221000b0740c0b80e40003410304100040000d0185007041c0d60105811200078401c462100300142c425400316a100803802c138002c035441e0240800c40c0380641c41e00b0b42d9920350062408800c8012622841000d4034000454003030001700341c0325442075104035401310000c2c2081d4030b85504d07550405490b550980c000c40c0e659400050900401081007070000003880078041040118504090190a19680740602c030b0365441342100040c20f000ca80a48003400e108040e0903100c0c103040028000c00044001c0f1411b5000703110342c0c1000154584a814401000000b1201c01903680c5552000e103a01c0d9188a00d450ba80102a40e144d540207002c45900790340594464032005960f00510310b001c80603500440e11b8100340c19080010400562aa10816010404211b5035280c1c050201c9070130b00001c0000d1101c20480c03182605000d554a0341200c03400040d00c10700f41c00d005241c034002541a54900c5454401400e0070039440b00c000001d06240c1015130842c8c42400c019204030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 655897895 1250 655896645 655896653
    0x201050a11120705061b13090b0a03020d05030c0c03281a10140904081c060807080a2a0302130b060a0c4101020f130f0602070f031509 59
    0x1401c0b444044e20a0740020301448103911440365002c0f500350199840c10f041001181c54072404160314401c200c250340e10795075a01100e07503401010b403001d507a0040500030300e00c1c4981041a40ca030450301e19040300d841440c501b10300914000a02d902c0b444101140d03201c00d0031034103007a15028045100304239400400f440d0b00c0b40c004d40d04070106a20030341c41903036428401460700300c00e90101d2010b0204540104000c405110211700030300112080c02428103001541809900c8034103006140c0d66103d403005001d8800081480c0c0c1002c100012800e000b01d0104160011080c3e03030f4031030038807042d43d0303901c03e068180380400050070021842c60915032652800210803c098003c50b0042d03200240060004008031004010003410115098104210440307a0420103810360781d2201c40c680e080f00c2d40014941c121000340c0d4a2a00350103c0307101d41c0304142c1403911800d51007019110102d00707006031542c500c051180031405600c0003810004803015500034002c01440c42e141c10007400842004801203e032500d60460102e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 655899145 1250 655897895 655897897
    0x7020a0914070302040e18032107030b0a080303040303090804120305031b1318090f0b0405060f16260f09010b011d040c050912030a0909090201050a1112 67
    0x61014900c08202a01c4540720552903900c001c0c488400d140c8103100a1158802405055511a0f00c1c603440e141690301d51148107256000c2c0502140030001d000f04200b0700d84c00c0c0002458044c0034261070070700152016004003c0c1e040301074011605907a1044c00040c01107442500100451402141154941500d400c034683da100040802503011401c000148041c0ca010b0706039100c1482c400000301420b0102607600310301103020a1182d440c035105610352070303022008180d000e4400c3e01c2d881049120712424a16120041113400c65056503907005540010b094800316060081c810712085200101d0484000b074103071138000c0d03e08801a00350700e0200b4060207040400c05490700031403180c841154940b4210101c5401d5400301c140315410403012161f2281030a206128107044248110b8012900e100c4020044840340140e4a500d41d00004444105085100200003031070045495a100d1a00c103440d03103900403e807000100000d0000d0003c0250001c024499002010110740c40c100742c40701d0900c0030700754141e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 655900395 1250 655899145 655899149
    0x90405220501050f0a180b040c090c09090e0d02071823190c0e060c0f0a1202010501050108071b05010624030e070509040b13080f04050f2409040207020a 67
    0x4030781d980c0080c819142c00342000694480851042400503680e543c24407000006c0102004089604103000700e01008003400b00f41014200705034040040c0e400b81070000302801114414004218900595010306603008149031280c62465001040200d00d80294050451940d03a55107003040c1d40d40c0ca0130035030ba481c0f184103600b00d100d4143e0300100a0600711010001c094440c21810b0101d071401211162081d0041c0444000303480c200c0342c1c0c6441e000b00440c03103070410300c1110319091300b8060507070b1060400251074580e00b011034180d8000c01003a80c0fa8030040d074046030241e89a0010504002c210107004c0d03c40c600d10b4922511407400410001d56070708107142d00d400c5045200c0241c40022901400b9540e152091840c40360400005211403481c0c40082010004094405400d103441100003ca0307803041003804408456101c403140e0f41e940c14000e0b2541c0c1542290003041e22070040d011420115150040c2640142000c031400398614030300301c07005410b8031351040125607042074007448684090b9840c03002d5400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 655901645 1250 655900395 655900403
    0x4060905120a0b070c06090623010b0406020705041802030703031d030303010b0a08040525030b010e150f040b04090c09112502010e1002151003020609040522 69
    0x400a400c1600300719a10050280c544400d0b4403504880010815030241c0769040840750519005007002810070002078004031390701410b40b9040011040c509a640010000d01c030310032920940103643c860241c401244100d114050050b1b010f40b1040c0000d11303041d4481003c0130b0f8502c2c410310450005038042401c100d41d60b4000d8011500c1d0480501d141440030921a0710244d040b40510320715030510a00720280d000786000380c4100f060302400a010400d04000c0d2000303a9418082c280081e180e14410b8101c21801e80c002240c1e40e41c0c0312000065414514144180110010365035100b480c08002c050001420344100042d911944403c03841500c0d1310b451140309030050140904091144c1880505000c2c0c4692400208102500b08840c42c1e01e03010302d200800c01340028401c6054001d00303600040b41d880c180c0b03c00f03255210fa000700c1000b0780941c0004803101003064007405041c0c00d83e41d18800703000d803d10910001c0d401502c20132004550349840d81c40b00d68003240ea280c01c114081109401b181d10b0000e1010115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 655902895 1250 655901645 655901657
    0x8091219030306090603020a090f0e0a06020c070e040b0a0504110a03050114100e19020d0203090f070501050f18060408012d0513030507060b040c0e0a0b0301030c0b0c0703080406 78
    0x15091607410700076070300134096a40c0244540c03451540032420040062041c0d03444079a0b00c1a1005004009401805000306485d003105c3c40030419040c43c0c0c0003584060071841d00381c4141003002403102000c1c8689441660800414001039851003104000b038070300200101e40070404055101541e0740d5025250001d113006000010705003219031054481004081c100c1d142142810604210a000401200d40d209540d981f41048207070722072404201a0082d2405c61030142c0c00031040100d60000010002c402d030040000b14ae41d031607500c00054405128105075a15101010071074038480d8840300450075003680c8043d005c5031800b680c41c90102d0031034103c400c004103030884508202c0c1c5a02069401c1000d03041d02010b04011609020f03580817126400c585c3e004050080110341a024800c2a80c0703c0444100d02800034031480b00305450003070846805c1031800b8801c1c600440041030604c031110540341600c0e441480d17059000d040000c40d030100c0d0400c0014001a00c165000400041e04100241c0014940340d1144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 655904145 1250 655902895 655902943
    0xc0c0f0f03060e0c031f0e030a030203041101230c12030c12100612111b0c040e0a0206030604110f04030c0609061107030209070e040212040203010c1b080912 69
    0x900f519000303074640ca610380c813907541240d0650f40811544c41c940c00301003c8040e0b08101091450251500000354041804042282c4010a81507001144210700c6140c1002c0200315680040d00c481208800c041648004035080032002c010a02c01003484202540c1101c425a0703004000500c2980b040b520350080ea0303804034110481340d00c401049508011034944040056042880040491074034000c48201c0944800c14040345a86a01c110344082400c20710510ba081c2c0116110750b90b802c021100980102d2070080800400c060100f0b800c201960300910007461503c0d00010000038041d4079076800f40e617a400300041e40c0a045144c0003003000710720540160000d10301e424005400131020b0b07030002081c0405d181164599190200d860300c1643c4c0d04940d205000e86601d0b1040b103200691b0035000f40c10a200081480d03112040b46d800a1146100310020b021940d11b0003030850301210910840d1003c04480700b5004001000d01c00030b0000c004025245000085014040d10310b8540f0007240030707260040c0d40c608 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 655905395 1250 655904145 655904153
    0x300d23040b0a1a091e0105090411040207030311030403030b190f0b03270d0314040b1f091406030d050c190609060203011706060303040b0a050d02070c1d0a05040f030c0c0f0f03 77
    0x1317a50042c1405c42e40700c03159203016190b4600c4000f10668161265500141d41030801d1301a074001a601c1c0510014180c50385441d1501800030407000c2a007510414030b20f140080f0b103105009040040c0c03801340b010740010904d003c60704101c541018000c4403508181014500d180a02c8807800c0d00444082e02c000c0c41d81b190030803005821655880c2154016452541c1000003083d08203080c1034000c40b4003e290140910034890341600e02030a40c0206100e20700b04441140200c00402e6140c1c00f4801c110145c884001031311038140d43c41c0c4900c03000d400b0f46400401440030070004541600c131001d802104003041c04542e030313036409089900c240c1040314402089030350024010000c000e107641c03200c415001180fa203810001401e0707a9000d00a8880104000003030910f40c0c031009034042c1d50710542d016140c5034005072102c1c0b2070605624914a50385050f80c89000184894405020341802143c12106d56901c2c0051910116000003c640d415104c100b1060030009401d44000c441c20010020b4426108103035085140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 655906645 1250 655905395 655905451
    0x16030e0f0c0d11041425140904090b01170105010e060d0308100b0d05010e13110f240a0f0201020915160b07020c190503300d23040b0a1a09 61
    0x140c6c0c001c1942c4461101d175000d50400d002032098500c090590361101c3c0000001000381400c2c010061009030084000108440a881c2500306c2511103030003881280c1e240d0001409010302141d80c075901104041c4c0c80c0c00828000d0203001e40247c600104203005540310b090203081740c4c1c0718408103e241030b0b4400040122030a031022203a00f107545410040480039240c0c0710a0014a00e0b0808540304901150f400d40300c5980b21602d0380080e0341c2d002803a10140180b42ca03001241e80140e000394010406180400c0001c0f0310610807600d070048020b02e09012104c9412402c0c50703941200d04601c0010300350303044500105001d5800315118440c207070300130140203048030140311002030702c00c1340646419080007003404141c3c1c020609a92000154a00f85a41d84118031440c2071041105074110452a00160007102a00e01d904206855209142c0d040c075000c0041061900b40c280480300034000b00d4a9001080c215420b5800424100c0582d40c0c071810386440f00307030004681e42c000380c9040c0c0d0400a102c2420421404c034103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 655907895 1250 655906645 655906681
    0x120303060504140a0e070305010f06060201150602150a1113140105070209010b0306060f04033210051522060905090d0c030507060516030e0f0c0d110414 67
    0xa14248182d0545000300d030f04222003d030500c0c2e8010f032164007030780300079404000503002035802000a000030030448508100400007402104015400e00303900f80c018ad00d442050804440c1e09032300400903a24810f403901890b01d0081c00d1442100d1704c61060494501091000d00400c0d10380c807026100c8207103040011100c0758a0400303014140b040c02e01603400960368128800703044a180c10003450b5260703540d100055551141480c40d007246000404c011050003e9020494800014810070819620000004000514000c00c1116095200d03400f914003045481d00036076000100d1000d0148204000b10024101480c44502090942c03030005400035686842c1c06040000c088910b020000e03030502131007007622801d803905d080742401181204c05e01050310910881d03000c0e0341c11600403c5035003408143c2e00c915014001000000a0510342c2e14030261001266014000e8034040041072640c1c1054140200408101410390360308160003aa5281c64441e401000b00c1e13042d42d03040340b0b00e65140003840b13090a02488 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 655909145 1250 655907895 655907899
    0x1e140a1e1103040603050a0906110301030b220212160b130b0c0a020618090103061e0b011d0604180c1202090a450c02120d150b03011203030605 63
    0x14200a60918000700840b81a544c091501040da0360718800010701a1104242c0200010700d000746000014451602540c143d9114003144031030ba0321030107144148a580c0d00d562003103205d46440104010300e481240b0365110314240e17051b02da1070341020400a5690407a50300034800a0400101800758072000904400030b410380305a80b50811506683e02030b076511800c4802801002d000038032200c00300011080600303d1100030502070056849240406c0a800e0088031206c6044100e15405400351540c05107400e00e4406940b5aa180d15180f403040c000326248461700d6801c4001004007241045890219440d610074201001c80c80c541c8000d0300411070240401d034003180d9807040c0403000c95507842c0c00990007202c03c041c0d0f102111181d1156035680e90f039200380c00c02c8140100c62000c11902001440e401011042900d002c01c076001e5122810398071035520004000451004100060101c002607004010541035804410406522102d0600c1c1560080e0004c0c0b104149080d00e81c01010303494014140a0081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 655910395 1250 655909145 655909157
    0x305030a0c0207080a140708071d06120606010818060f061206150f0402040b0c0a02010809030703020c0402070f0203060103050f1c020a0f05030d0903120b0d02011e140a1e 75
    0x9401200c45d114040c86500818200c6103181015002004104000c05010914169042c45680303803545c00346070300b0f0440034840d01c111101c002000303131600180b841c44400f030540207032000703540b10401180c20180040410501481c40c1d600ca080036402004024491500d070f05000040b402c11008110700490380c2140102d26922800400c011603401d40c0c0030720180b40c001e48006040840e01d400281c040d004c1c8d1b402000d264000404c2c0d80103079840000f2010305141c000c1c2c9460400f40c030741144081d200d100d180005009a030000510100b2401e00781d00030610f99028291484480c021036002a040684c2a841560103910501c49802c2201c014801148410031052503000d212500320070203501c0b03001c5580060a00443d5484280078080d00380b08880c80d20600c61070401080040c3d2402030003240080040c4040145020b1001090381481c000400a240e0140c403480c2c180d04100e00c50420100c015548d80c0108080d9044240032045048040c02c6050719640320382450b5403030070440c0341e5280e101400c85030400c1a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 655911645 1250 655910395 655910399
    0x22401030c0b07150c17150a08030408030906070f081902010c021603030e03010e03130810060506120c0903060a0f0b030105061c031106011202010906020c010512041e0305030a0c0207 80
    0x51407071134660440c400b03040c0110b40e072484c01e10240d501800c403051002d8412540c0e0208041d41c031218800c0b01074444100d8042c03103c070703856a2880345d52340218094904da5520800a043c3c1520341080502445841042142c0c880c01880d5102296600700b6a02c00d0700030701094801a40540d02802400031b06e0486200401c5000104032465681651a01c8080e052110403011404152804e402c4620f91031038200440303540e13480940da442407000715032007440d401c1d00070300042e0000b40703415002d03503400c95000074421810aa0a902444c001d10f4000d845842050802c02c00480c90f03840074040d940c850315036068000750034201c41614809449079040c0803031281e40340c8001c201d040d9036900c051640300001d000399068603980034a4140c2e03020215145140d5a441120000030b05c032014450a111520b1003a03807200383c0d071503891b82e050703a07107107a501c80940c00f28109002040202c00d010840729803090050008803941250344040c1451107440510960010f0390020412021915500445000f1025171008002c124 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 655912895 1250 655911645 655911653
    0x60c03040608071b03050f210603190c0e060105040305061317030403120c0c02040e070602010e1902100e06030f0405070501020c03060a051003020a080703110f030c0907022401030c0b07 81
    0x4c400d410040c18450302154825100030100c044c0c502d03d89000c14020b140145810000a5030314007162210700c6480307003040e45018801120304d206100d0707900901c400005030600d42d4015400000030072542c1002001c1c000000822810010f050203101c03c0e40c82000110340b1400c041c0300c07558035501c80300d408540400c00d12001035808081d0b24610070b0003000c0050780070350400e0115070046200d41d0182d4443d0a00c00840d0031510f0104800c421108290001c101820b080203443d500c50a801481e03450798500090300c10054141605071900416030742c6031803c0c0c070780f0b440400139159400031384500c03d0061400c8200020444104048405464240010880b280da00750010350780340001400c218107581c032880460810220200c603140515401040c41105a0b1944207681e43c40d409440256203451600f80300c010981054040402d81e080040c003d0301080c0d11030300510450140c0507009008503c190002ca60f14a00039050302c3c1700f0030700c049445d40d0165146042c90103a03014103401400818104001000000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 655914145 1250 655912895 655912937
    0xa150c2003090d110301090308060f10090b0913020f03091204051302071109160305060906060304030c051002040f240801150c0203120a0f0206190f0209060c0304060807 74
    0x810b084546a808802d01d141c40360b000e00d07030030750469019824000001c04164001e40403038403e10382611418044140e000030004124619003008006c282e1030030040c082c00f800c0c4c0c00101004e000241808040902c8000e0b0f0008036840a079200c0741101c00841030000c03100c01400111500c03941e8580a5080504000000f03002001c003981c4d281d600d6500090b00000c0040c3c141e4010b403513500041c02c010441c038000034155120245c103202c00c2c00107840d102c00102c00385040007980c1d0092801403c0179065640300e550660b00c41c800d103002541e10348940c415110242c50300740000e2007e44010403240140c03c0ca82140c25100b581a0f0600342d180c0030810b5800c4000b0303503002c2c0c1c000741140c206500064100401d41e20503910311204000194142c0141403004031400c2161005103a48516641d0700316403078496980803038581005440c110714a644108481140c2e58603900300100c50640c642006181401074030009400d607001040b44085c64001080030090250000c0f44141d002c038840c1030141064901040440c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 655915395 1250 655914145 655914157
    0xb19051506070606121101170103030e060a0201200d0f020c030f1318050411030102180118080a050709050903070c09051005280b1c0506030a150c2003 66
    0x15120110b140700500007290084002011880d4189080e401c0700c1c2080445801c204a002d030120f50b011a034810303002d201c02c0324181203a0f05641c541840c050410200702c10740c1c0c40044401c04540d00c070151600154903804600c2c0102000c9120b860340d43d0000c14019055840d86541c0602c01031052002030202e842c0132040b030b10520020503103180c0d510401c048840c0740503410703044070024034a0070194120820241d405540118096800140c0c1d0440c0d28040500340e1054003410140701d100e1010f50742cbc203540034054011340c2c0c5402000000ca01130312113000310320f4030b40c50703002c19261175003c0307101081504498403540c0d400c0b90321007024610b0464036444102c0031056500c40c15000a641d8000a01403800ca400d51a01030310006209103002c41d0f80d0044040c09854003041010003c0312030900249102042c02180d10541843c100c100700e280c0024050402480001e0815405020b02c0d09440001001031030f03d030303920310801c4100061103400b544005010000004003544550315005a5000c0310b4800019646 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 655916645 1250 655915395 655915399
    0xe060a06020606120102040e0106090317040503031209011107030305180d081303031503030c110109050d080705030f0f0d0e060c040e07030e010c020d0e0409080319090506040b190515 80
    0x140d04c1c04118141c0d0300a200d150b0102d060076054500200d13855500c449050100c03401464504410500c01030310080700e01ca280f01c0e0355459031040203050054112504441d030300c43c040307200003d401842404003402503444a641100007a55603010000c1810840c894015900102070003064000141d0b200074114100213000c0c00b1a1800d082070541c1010311130303000610006400a648440e60b544c83c58081c0ca50f00ca11042140c0e0060400c034034144c01d511446040b000c0f00c0f402001900299000c0e00c800400da407080c1d00036211800100091005031a030784e4002c04074420303900380d02e960312603042c00700c00c040b81c0300c0341c0c4107141580120050000c40c078609001d0360240c071640c0d02c0d000400e4880c1142940107111848181d1695420f01000500007a001314842c405146951a1185d0507a4180d0400c402c03030300c0140004012001c1030011424001e0300400040c110b4182e207200003481141500c60520700324007154100c0d1800c08010410403031081c03d007600c0481228250301407150341403002c0c0303290350b1948040a01f8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 655917895 1250 655916645 655916659
    0xc2c0d140703020a2c0907061107051009030c06030203070f030b041d01050a06140d0803040503070c0810061d0f07020a061a0f100c0602030402061207090e060a06020606 74
    0x140309544140641c6004660080c020001d856580e0f1888842c280d990580992080e5070022001c0b175004801d00480c4a84092400743c0b08060800314181d074142810182c00e0040d02c00d402d40030036151110910151055003540701c42d1050b034950310304141c1c000c606401c80030402d0300510034401020380001c6807111100300ca04011415113041070200d0028200b51155081105c010201081c1e109819406140221000d0b0341c180103498681c86100c2c40e0403080c2c0c00480c2c00013142b400d070b0b002091500707001e190006e12800c1602d140c02182e0300d42c402000728641105990b40c0003443c182445119621030080140401a0400c0c03054244440546021500502017040b221620000400f13403407090160000729a801a0b04020110584a00050020500b4003080c0100180100f121151400403480400803e9a41c1c0e80f40641d8100ea5401c0081d41028004a0b0004014040107240d890502152842423100350303518a001e83c070380318800401c82400342c00d031400303500714101c24001c2c90f0340461043d90000041e1000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 655919145 1250 655917895 655917923
    0x81206040e24180a060903030606020f100e03040f0f141804170d0213210213200415021203150d11030102031f050a15030b01030e010c2c0d 61
    0x181c03106a801c60740c070428078020404c0c0c0c00d0030004a5440310740414001d68003040403e8458106903035603890030900181d0350f8468104c00800c441c040d000034007100c00070700035a0b05040d0b44404192007042d440d08030300034540d180035003401103050030a05640300c490203d440fa4208465011250131240c0042c101400c500381410415100001d1801121108040d01000b15a20240c05180420619843c021b5540303110110a10380d2640c010b00951010040d0014041300e0f00d010480c03440e80044c004e604588034040300c0003c00268403019440540300601540200004441840c04c0090070104035079a01c0000580900500c03824000c12a180014403106a8804419070315500740360074500e14a402c11341d490b40c00042005880340c100c0f800200a80118a0180000c545400811501e60100d00a4001651520320320000c2c00b0301c80c1d007000a02078810b040000c0c080d038260000a00351f805c0c0c0303081c084c04541c10041d105041c1c0c0c4a0683c0800111196440e940b9900e045400107034410003050000e8541805068a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 655920395 1250 655919145 655919161
    0xc050406032d0b041103010506031801060b07060f0b01020d0504050f0d080c07060908060603100c0c15022d03040308190c02100c02060906041b03081206040e24 70
    0x40c0d00c03803180710451104005003440071604043c041d01084540594104142c64040720282810b9034141c0c0c0000340081c0c00d42d5202056420307650351205042e005592940341c001105604e0a00501d08035005280201d540200d4090f480243d4003c0c0034942c2c1150f01421103040100c1c0d02c81c0c26141540c1049500070f44c03800280c40003a40301442008042c090140000320300000020000f420b400302c42c4103407100300c0c002c0da4030036000d034a03808116076050f0142c1040f40c561100c885a41d03c5405e002203517003403480d58040320342c480c404075012075000800129400a4124480170f900303503100a12560840400d00c82450000f00c03c1d10310300001d40003c09015214000c2100c01300240324051004540203410006203044200003076989901e025109902441c08203560320b80c40c07000c80d0300b61088110200034906a25035030354171081c11020a103030350081e5440140110002d08007000070080700c6040b85103425242440400c200403908010085078040e482090b161b101d9805403d182044042222642025644c070000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 655921645 1250 655920395 655920431
    0x13051f060804170d110c0109020a05032803050c030a080417090a17010e030703050d060e010308070201080604150f03050c0a030b0a0e12040b0304030314100e04050102090a270c05040603 81
    0x619485d84004621040941415070100a90b81d00031110724103400c0da20701c1030584030030b00884120702a95102e4000c0710880000704003215420702c60b140c40d91034120f00c0081c0318159000f480c1d402c00043e44200070700040c00b11600c1e04c00f8520307a99861a9281040490016603070b1640d501c1030360f840141c606141080090700f07503c4840e20054800c203481e55a802450000c00c15840340000b0131040d480c2c244003080b03100c0601001c1d4103895200c141c1ea46051041d070010355070694010f01e00c035441078488084428020702511030400400e03c107010090740170f09518025041001b02c03040b880c010310b1070810130804036030942c102d10b400c600380b00400900c8511792418a400c02c42503004500014000082c00216805290002c6209500a60701000140c0c50080c010090b020203554000d5015044401408400c0d5a41116071700310344505c00042c64900f048001c24050205644600c0e030700210100040411841c850448141d0a03a04000f0007414800c1348024020740100c1c01408101940e071200d1807070301c2e07081034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 655922895 1250 655921645 655921661
    0x515043605070b03090a0b01080115050d020a0906080d02010f090809150702060712180320180f0106120603050622050f01020d0b010305010f050f13051f060804170d 72
    0x50010358070b1a082c240717180d541072068000c4680791094030001451560601c1040000c0c402d007500c8a061300c0c580802c01642c440540000e90340f20031090300010f50700000740b00b11402081c5800250841158030310f4042d003144c0440c0c150100c1a820040e4280008030403104131a2213000890700d203401045240c1d00140107000385d0500941002000078440c05001c4021401618400d00340e54503c03c0c00080f02c0c1d589034420b1644002060026450481c0407420354829000e232848070060002400f590150b20718a441e054142c8003001c00312895401882070950143e541c08007410070240134400d040c034580c0d803603507075080c01045000d51210386000101001d0b07000090741422904039040318210f84202004500030b42c4580d02d0040d185103000c00034985035000f40242c42c100c45840764100c030705038640740030300c08164000b00c12154048810358844034058168800c1c075006008004460344c0610300c070116000d83d590581c00503020304c9a0101008000707002c0340c842030492070034000b00e182c440d11000c40724000380c4012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 655924145 1250 655922895 655922909
    0xa0f05090d1b0f0b18031c05071814060d090f02010212040e0121060e06011e0b04090b0102070e07051815180418080306030607050a230d051504360507 66
    0x1506541c0d841190419918011f206500b007065448000e402c0d03560181c003418803d11103003100c1d820007090784090044d0b403084002403c0c903440c03d07601400340001ca5448500c100c900b40390500310b00341035580c10842042c07420201c0308010b260509101c190440c500051141c010800112110307600b54143c4a80c03800403607903210f00240003410182c00c0c460780340d0000b4040c0c0c06682d8011030910340c1140b904280b080841e203000342030034a80303070424070040040d00c404c08419040d48030705600007a96001c4200c0702da10030303070790340d80c880f5224807400c01c01429264059500c40d10640c0340407414140d6041030720407245807505140c4001003100b500008034014026100009101d4558a4085014002400011882a14104d003aa1915996002e00303a80c0c030b010710003407040002e015068003040200c8074404581c58402c1885101d081441400170b01d01035a0084030321a16078001d61303040140c1c0f030516001d591a450556010180c83c0e5180c0c6080c0703009008166020846804450152800d000c010710501002c0e04c42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 655925395 1250 655924145 655924147
    0x7060915140c0a060507021f27050d0201060f050a0b07020d050619050f0f0412030f020f04174201080f0601060906020d080a0f05090d1b0f0b1803 64
    0x30b54030115243c0c0c115a034140c80c41c90034480000c021510214a04034417502603882d81100c030b000e40301d05a0040100b803580003114545c0f0004d05e00c09404440300441d00a214034010804802c0000c4000d081d81c81c03030740c040315007a9040c00c0f06002d00c1e50b0700400401552110440c8580301c02c1e6a000051407190460b40141203406443c0500a114000c05060342c00340c0200c55003482a510f401200949081d421106408021401400f043c002020b03025a03591a04442c07a000c07482c00a24107182c422680040d2021405207000207003001410130282800050507500d001400a070042e50b42890200115488646244680d00341c3c440812403000c0d0314041c52840c0e4141d034018a40c0c40d91982c59a44440303410314241d0340300b081f0001480d50b11480d0100306079003869000d01505149901c003030b0341106024080d854042d44802c1c061001c612140f264074400c9490768006e08403c07032010340141c0035000d114081c02d510380e0390703102000206000061001c580c1e40e01001c0181d1035581c209112144058103200e250141c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 655926645 1250 655925395 655925407
    0xd0c0203030105151303110112020c01140906190209040216060609151805040c0503010912030501060e011418090a05100e07020a03031d070803040e090706091514 71
    0x980000039505030340c4291000008856031500034086800307155049a4000300c0d8490910014840f10300010000b607040c14541c0320717840c00c10000c0003660007110b0344041d030384c0d5a004840b03580a2540100368005041901814860800c82c2c441c4c80c0e0340384034501310300c600798000a0665003900c50707504550890341915084a420f0b081403600101906107803254405203420301c42c4038581d45804030000f0b000c8404d04281c00180580d0400d1301c034040c040040085d200c50003d02c8000415031420300a10250501c03440584121140f072800c003800315041038114801300075842c40f1904003660000907c5043c020040c0303c060300c1c7d9105401a0801c00100b06980f904680fa0009100c400d603107540203a806a084514420b007a680c40c0c2e00021480d4100b11103050041c0d102c40d00c00400729001e44e00c4840c2020700c082900d000391020341d6540b8a0301590740d0050046600010b4100031070a079058480b5041200400507040c114541b4a0040c05801d0900881410107401c2e9016080d0380d015960003d0850b6420662503181c00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 655927895 1250 655926645 655926647
    0x607031e02070c0f1d1321050c0d05040f05151312060b010f0c020d050a140d11010b1f02150106050a021005040312110403050109050327010801090b0301020d0c 70
    0xd51500c07801c0013010b015903020440150f09103080554021010078441c8030303034500c0407410044458010540c0c24444244d500c00c0c2d0203d503559580c40402aa80390740765100d1042c4000c0d40360a40d1094450b0411074148010b1000e101c07030b8840c101c01c4840c2104d40e9078040c9403180d4a026180300b040b00700b881000c0c0c000c0313000402d9006080c00b0701c00c0f64003031941001000400401500c105030910f50642c001028829207030b0051920507100c01c100c034060411948002081d40e1071038552441c9004084455202c4008250b146901c10428982402000000d0103940c55045c00b14000c2c040900c400c1e000c98500082c51031141d40300b00151002c44120000d0000d0300d50396600090a40d500007030319070006010f0404417404252050042034001c42d4103a44c0c0d10b4101200780c0c1d00000806000c3e00780301008c40b00b0000000454002d001c2d0000d0940120055559031144001d400b5070369107030180810300d000415419010680c1c1003885103045501d00200032440724601b4000071700a10440780b201014600e0485090129 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 655929145 1250 655927895 655927913
    0xe010e09131712041202070f092a030b0a08010b180402010512010f05010f03022b1103010f08060f0903071211030a1d03010e070b070203190807030311030601020607031e0207 76
    0x13640c010f0f000f007106126501012a1207551501400881c0100e0300020440707400554000103800002958100c0303c402500d500c1d4010842c0d60b410314002070303104c40c0004a280303080c0e030020008180300002004000c603450003044c24403049804814946110340001819079014200300c80688d4800001d000f55507840c3c50390350103248818080c2500056a071499001442c0c024030032505032071810504219046004403021690121a4050700410342e16510404680141500514003070201c51400e200d4180c04c1078021890404010200c44011540300103010030710710048101c41125400c42645050b5900c1c0c00c00c20784942c030030030541000a00c40068081d50442d0b0210303001182c5d10140080304442c054001c101400d94121007003100f019001039000b040640c025500800c0c0c080c1c806401d0760f070764060040380d5059000e000c501c00c0c0d41900d00092044201981072040c40614890640f95500314100400002c0d0307220802400c150074560741e911021344000304000b080b41890081c83c01555078241d540b4101d40d43e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 655930395 1250 655929145 655929151
    0x150a2d0f110301030f2301020d0b1009050934030e01061a161b080718140105131b020f010501120b160c0f120e010e09131712 55
    0x624035080c0c0d001e01400380d03141164126900034031401e601070300344d4071482170f00060002024041c80038000b9007201080c2c03e001510790000382007000500c8991b800140300da00c0c00d00c510550100500418280820b99031000d1858000c08000300781c181070b00f820f000d030f0400c0b0380c201840454102c1000744030304501607040c3c114040a5042d04002d0081941d40c41000f840c0c2d2007078624100c1040c02c1407058504c60302018014003105405050100940d40040307244801c1c640458201050b076070000d40e41884581e03039900347c4e00514003404a0402030660f07815a081c14052040c01803d11681c0000c4000360081a2078221180605110380e0079141b140100201940d501040c1d1803035207003035080c240000381075180c0050000060b508580b02100c1d95842003a0600100c656003c0300040c00500010280030440100070152514032500c0c2489042c0030568010303103025101300d101d504110042c0821038050b11100c485a405c803844001d008400c044502e4107010071565040d11000300040840c500719920291400140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 655931645 1250 655930395 655930421
    0xb250809040b0904050c010309051e0601030515100b09011e05090f0607050d03020a021623030a03090b09060405090f2703030103030e0622140102150a2d 67
    0xa2030808005001d020007046078040e01c0750700001b0104140d540603401c90101e9920600c180c5000c04c10010355914480e110101d83d0000e82d1003c0014420803800300314034628281c5502a580c00e0346071080319500005064014119a05808106192640d0040210380a0881245060036500715038900042180c0c024031946442a892028000c40505040c401ca0344c074660048041c08110f24600c03002d601950291044d5811803241e01d465811892030750184201522801807010343c102e81c0d0020000d5640f0007034414a200303070031407004440082c1d04032009070200d40700d0b00961501d4200c40c01c0003039017a000e02e0740820b401005250820003a183c003141c682d0b101d011040c0b9030000500b40d5401d03400200303001c00c0c0f0003a4664410401070011070b00408210303018200050003a0301d40f42d801480140c211401022895125042d1a0309000015542c4900003410000b84014111454800300b69021010040c3c42540429618407551040c0c0c00d400c1c044054031a20f00d030f2200886a400c03448040180514003000c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 655932895 1250 655931645 655931651
    0xd050a020d0227060f0d05060604090c0506040803070b0a050f0f04050f031305040e0a15020d0617210c0d0e0d120908060c18010e01030f15080c0303130b25080904 71
    0x17170858034000d8041b0448540090040c20640d40340c03000e02c0020f203a80c850075103000311419400101607a5040040000d01903400146d1f440c1c510603c0c1412a0701000b03030228100c1410320b0704100180007032856031540180c10f50b07004103940c1c903542081800c14490603c14004d6010000c1c817400c01100b10400b01048034800c0d0303000c001c01c800c20281d00b5211300300e41d07400416098100c0c084c03a8082e10540c0240c01100341e038180001754581c1d00c1800c0f8034200081d0581003020740100c2c41440d03005404506441c2210199102140b03040481d8100c6626a070404160805001004484181507101c2c4000756048075444143c0800e01404030340054002500c6200701c1d000351017000001070010a10000303860020400100b07070540f4010807001900d92250019442e410141da40840c0840d1041c240900300754030030700d2004130007103a00b0701110900302111003c03040e000341d10411100b000b8044640c021000c941d503101005d62503850000100082036402208601e05032080602d00703090106031402020702c0c02040b1020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 655934145 1250 655932895 655932919
    0x708031c060e1b09031e0c04050412120608070905251d0f04062301033608190306091a060f0405190e060d050a020d022706 54
    0x200d05640440c0101211008400d0100301d0703003004446030100242d1280c0c40309080c4850800030920345a501e039150b901c20036040c10f0200e02c4100a000d90b4003810700686092005103043e486100e92003040b40d03010803c0103c84821031001150560208003d400d0300410764442569800c0c2100245c1000d0301d0125105001700460406018103a0f0b003c041521541c8490f400c07101c010107441143c100d040078860700008100b440841c50b1781c582c40b600000c0c10081c2120328101511001048000b140e403900c6c00d051624202c4141004000c041440103140c0d0404c150112100041041c0c080140000900030720400c001700c0c0506c0140c110b080b0004041c40c5558040058581d40d40384c8505441e41c0c05011f02e02808080f42c3c040031410f10b00c0081c4031491040711035610300360ba6600440c141d00199051040400e8400c50f081c086010040c0f01541c0109045405a0100245456103901e8012144c00284280400c60f024003c54445a8403000e07078500c2c0c18071100415064400f103441030401102c40c54810080b4006d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 655935251 1106 655934145 655934197
    0x50903031309050601051204080702030a150c0e0906011706210102030f0c0f16021306090c0e031c180506040f0608100303050d1805070803 61
    0xd660252800030070b00300300e03000a480607040000800445032440d8a01c88810341068000e522150307240304038800603103454001e20300106515502c07620440c00b0049507001c001080300584a622500c990302c001c004801c242115054007007802d08082c00f50003003150101a81c040005000960700d0070001e4941181c003410a14490749580d000010480f40e0165516483c2e040400d1605490420004440300441c5006007140c0e4400c03000000703080d209655a90314903401c47c070305680782004882d33180d41c019806040a642a44041002c0100f140360905001038540b1801c4221001007940b00004803003114210701790305150120001d2070b60080b940740c1e80c02e40200300070044180d40b01d9525141c80b801400c1150006c20b40c503400b8541000403c08070741c00900b16550320010110003d10b8681080054900411880f00540580b20350b00020600501c0000181401f0001a501003401650415 = true := by decide +kernel

theorem cover : BRFrame.Cov 655755395 655935251 := by
  have h0 := BRFrame.cov_init 655755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 655755395 ≤ n) (h2 : n < 655935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
