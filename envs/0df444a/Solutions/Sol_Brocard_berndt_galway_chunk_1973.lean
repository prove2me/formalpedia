-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1973
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:21:10.954985+00:00
-- url     : https://prove2.me/submissions/44b94820-b045-4282-be4d-d6ac268c4f82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 354676258 ≤ n < 354856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 354677508 1250 354676258 354676271
    0x310090b06220f02130602010b030d0507110909160f0e0703090503130308090a0902090d021c0203010906020315060a020a17070210030c031a0a180207080c060103030f0302041404 78
    0x1240c903824104402030440442c80d22903900f6114801d940204086407080c0000811140d0b00c80080b400ea5410700b581d6030f01a0000300039180d100f40035074090701009100300441890a14180007251010604540803403880c0d1107031101c070340b540700501503800140c415003020580245c10540c510302403071405001c00c010155111284014080188181c2c0d02c2c035128100840c106a07928240031005412044410344613183c01d60000400281d10710886070f000c200586412042c0f04642c00700250701c400d8080c140b10b08000103c410b00160390a10906101a02c151001030320303130070241041c0304045180a80c1c907010383d0081200340300c290b400042c20510726034040300c00c40c1781583d5020224164015101c000350403c1034200310705061609a04001c0071103490396020485144000110303910350481011082e004841c1c0d01040c0500030090208a071102280e42000d4908010344d50f07582416440a8203050041c0c00c00301c014010140d009810002d101307545c0c030702503080c00d0400c8150503800c030682a481d40304964034231 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 354678758 1250 354677508 354677539
    0x3040b0322050a0c05130b0f04110409020f120109110d0902031f0203070305070315050f06090619080106080402130c02100e03041a0a0918111303020310090b06 70
    0x254491003890b8014141e9440300e0b028513118210030034500071207100703020100782d42055164503c21904030000041c180d01284240d001840001c0c401c0e0b001407514280200004580b960b950b0009014800c415136050b551461080300302d032003624040c3c215003c014100b00d10b04103a12044400e90709000d1048070005059031943c40024540054040c03440c5600b03850210803c804c1c9090381c0078520684261720148903540d10901d0450868010010042e0103050320003007400302e400c0268160758180409081a4901114100022140c0d00700510f901003001ca80340244240c9507010348068014007480c1000383c03403414240d00041c0390f800c2c0c29501408070355644040030711061013040140c0e8900f0000004018501d0101d0a04d41c6a51107809058a0500c0d4021200060a100c604481440d50540c0d03800c14043d080c01688040c0382c03034483d1010580354540c0014400fa59402c8010411800b44e010b620400342d143d4410b16003480d8101184000e2545007140360004280d1260816502c408120f68150381c0000030b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 354680008 1250 354678758 354678811
    0x10b0a11100501060f030b0d0201020d050d1508010207031206031e0602160305040911040f0b22060305010e180d05030a150909030801080601061209020a0e040609030e0303040b03 78
    0x2580440706150400000042458000091105143e42c03650240602e06080c402d001c2c41d140380070002801a800550107610b0319100314080c0034201c502c10b40114210210042520302c24415411000c0640d50010300c050816410000c5640301654084003800418a90b4036260001c071400301c5502c0500e070b203130441d070720410980d5412a0a41240e507102401f0305a5107080003010b035000383c015103050624040b440f10884103004203450032030308504e0450166034200492061590000c035180500c04182c20310a030740c3c42140c031600ba8042e0186580000b104e624001c0c21142200c4081c0107008080400303040e011040601080340104015141003084c0d0701d4583e000614010201d1814014003162300a001140140d0240c1150035428025507600c2d000d030b600d40070400e84070482881002d0209903003008074102c0d081650004c01c3e01c180000d180000c15a615107080c6c2d9006003c5600712591a0344002075010150401040c215580c0190015400e0a0400e4a403d0941c4800b9100d04a415800300e103107848142c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 354681258 1250 354680008 354680023
    0x212070c0509040b0103060b15030a020a0c050d110c270702250305060609100306200f09030105100f1a0f13030303050a02190503040f200f0603010b0a11 67
    0x26182c801c0518003810b000301c061a007800f04803021b901300804001a4071b01406d80c4201110f9060348035245458050720f0800030340c042c0401c2030620100f1488000031560520000c031030348120752986a11034a549000c80d0400481c0c02c83c051048100c0d0045036548010225100030f00505440007030425241c0520680c6441c0c4810b403054a6503464a0f0310710f00a90002448600301c0703124804075001601c0356800c100342c1000498014070600400034080010034515000154611645044102001800603122000c1d40c0440941c607900d07070000801e0511410301b40301c0c0a9000142010040c000340c107107040c285000e8598070a031030728044043c16403080c4c0d00000c01114020040c00620076580c11080851040c011134520040c0c021900c2e0a00240300c0300198001c6603400e203000350103107900b1040502c0650344c0c2d03000030300240c0b012100d03c581500003c0c4080122280030860079860105601c10008124501da5011070060013140248010881d92411505441c2110343c80e050041c1288605400c10b480c200d003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 354682508 1250 354681258 354681269
    0x50d08030c2a0c13050106080c160203011406010e0a06021e1006030b0103021c02130908070b1f08010e0c042d050613021608090406050a080d031b0212070c 68
    0x1140c95000d095400000f0005071044059a0700386030701c040c4441500844409214210105607414006450b0850800080c007160080724200b2101318225000300f0700f194180b10b1a40c0c03094000c0740600c81c00e507800114101c1320b418100d41c2140300c00c0c24184000e44564400f110b48041040c13250350849500e000380051510303c104003804110396684c034241594000d80c01c2c40242e0040b51094404250003400b07810075082d5640150003005d10382088070401303000300074000b41622200828000c03200001e0b80c0c400417a000704141c290095800e01014030001800c01540d00c43c1e04583c0c500b0440842000000c6106040039a007154000f03142d5800317848174012880c8840754600d401d50040e1103904000d090f0b40c4524003070300099404051424180551104034810002450b425041240580d000941081c0c01800c0c810400f50021903800ea840340800c0c8281c0c50b9404c1054203402c00e182c41845c0940c94030503484c2c642415140d04150848820010751542c070b03901000c0104100002d40314081c0500d000c43d4a00921 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 354683758 1250 354682508 354682567
    0xa031202090d1a150a0803091e1801030501050c3907090e0d0903030203071205040801092901030b1303030204180b0a14030d1809020c1501050d08030c 66
    0x40119101243e0b441c42210840c442880200d90002a8203005a082059905c154000c5203001a07413010800c01125a06041d043d488440c0400c0c103e9481d801e43c03000200103a0f00a0054a5045190090039100000c01c0d050890105209850710071054481c0100306070706204a182c40c890600004144810101030000043c0c400c8000002e2166250340c0a07580c0c404091050341c0400134200002c942c100e15030b03c409030041e4810b0008101280c41c020a19000e00c0e4030f405c1c480c0c0b402e40c0da406a0303030a680074044152074100d40300c02c1c0c04162221103aa604080014101700024540c1141c1d2030074615074002d0807030180340c01c011407100d04041c001d604803170262004141c022004c12043d0105409081782c005e00a001e074005020010306810501d21482114100501030011140400000c68a800c0c2890200454090f61180010245e0071440180103691200003e0b00f5000035040301041c00c010182c1c407242c0a42013120200011500c0401a80e40050b9101102c3e50356003404849404a044064011408031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 354685008 1250 354683758 354683783
    0x30406020d0c0f0306210b090a0210030606081e070c080c07240c080a0f14040603021314090606031503070b0915090d1b091107140a031202090d 63
    0x1d541141e82e641c8143c0e8181d07000d20030b160303d81500da85819403016803c2c1011100f028800d000500d06040309600014880c100d4400b0303042c81d00000d200d0343d50402c41001180e5240d1341403007070300d81c000122075000c559181d82204010420542c51500d1000604d201d082041e401035079000c002c1d031b82084428008100c2d00701d0320b0305a1120900340b940c1951110940d1600030290080203110f025900d10529103400a80050401050800a0310146031001e010703410070046c10a080024910103010300b01401c0290740c0180c4038140c0c1a0300380b074100d070703160801103903140c05980c9101150354110805030301c848140c41c602c0c0c481e15101c4c903100c4030307084543e40c0c80d5050144840100c0c6400c0041c1c054607035501c080301c486100314104000e280543c400c1408498204000c0141310001c1a00d240040408070002d8010004250f07450034840c0c2261403904084901440000b146018040101d00300100085c03401c0241c00c0266503940c02504010681c04418146174003c26034014a44c0d8048044c000c4942020b00840346 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 354686258 1250 354685008 354685031
    0x5060403141f0c09050405071e120203010905090c01170705071104050411011803020f190b040b0301060e040b0d02011d1012060807080a20040f020a02010b0102010209060d02030406020d 81
    0x3910f01240c8480000c0da024500045510b4180600b501440380c40d2648907450035403404092601e920b041403001402164829158819018802180200008180081c85081c451402401d2518401740f4604100003a081d8048010721000305680020407810000c4c0d0b82e50503841d0441c54101c0400101d64031528200801040c0803644c07803070007004075099844a0901036541c0422030209810700000c0e40020525500620781e0410b0000804508a042d0031070400c25616a0b52407040c0d03000c0d400110f03840d0404001080107541141100c44401401c890900c500c400f0540030030003070003525001a0400c00b08601b0307409441c800c111000414480603180042031208404090280300b00a001003404515012000032003001c049030450035121036002501c01c0000a481d0700d100b03074012060141c1d4550307401c84100e400b41e5840c807a00c88640d500f000d0258981c00003c00190842d090341a20714156401080225015034503c0101c45a07a5001d40700141c481d241c1d03080040c000d00071314108003c1c0c140b805030118613 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 354687508 1250 354686258 354686261
    0x30a08070f050706261e010f0303020c010807080f310b060a0b1b0f1902011e27030501090b0402091005010c08210f011d0105060403141f 60
    0x60007400b070021a005507540740ca00f192080840d0b040c0d20b040d0303c410384a01480c044041001900a107100040c46640e0380c001c4207940a41c542a442140b0080300300d04100304041d01800300802c650824202665507140c155809000100010300406419092000140300e030003403244000c20000410152900c1960b07411140142d0741d012000a464400e141c500041c15407a005824106980c5c0406540341025000d03541c11446a0344580c031054a40a8400c009440031000c0200e0098156410701c0700d84c180400d0300014124100c968090403c3c240c0041b00c0c0404140c12400ca00c980c5491309101c1e1030101c5c205042c91026401c503420090095007000031041c1440b4621080302d0280c5d0080300c108820740c84410a101105800c0d1040030302040c0030107168008540041e0242c0300b52607032442400c2603444024030040040c1411100110300041a50061001c451080491058448403010707100e00c5e5410040000c219001d680700c0101515003100e0440c4d8031a00a1007d40004200040150607261607851002c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 354688758 1250 354687508 354687533
    0x180d050a110307050a06090f050109060f0f05070f08060301110408010b120a11061327050a0902060702130618020405030c0d02130c03020f07060f0509120315030a0807 73
    0x1400100e000c1c5800303040040c080215410254050300402c01035101e942d03804051310901c0000e65000343c00045001c0403420a02480c110300d8402d07100056a9601082101c04840f80701c044815040d00d08010404041d4100c94058000070042c10156071550764040043e0142451414034812000c1c042400144620305402400710900200e17141001203400348000e5545544052000d040402d40300c401e040710b400c00000800301003c48501508280340c40c0d110b40400e8041d0b003002056030586842448041d00058070940e0b4000f96404401d1100031103540014080b4012042d020303111741509011500d4040c1c507075001400170720000307800b00082546444203034001c0d0800d01c035260090080300362074038a83c94001ea03805901a801008080c1c80300c4c0105c450802090124100030a041e800c01c1031a84801810000d0011079102d0040450002e88160b02d61041c0c4030007500806d40d991004008503140d00a000540c0e03400040c0c0c0507104824075507000020b14141c07000700003034411000010884184645441c414 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 354690008 1250 354688758 354688777
    0x2150a08060a060206071b02012307021212071106040e0112050d050310090f090209011e080604020303120403020a02130603120c080f070627031403040c0608180d05 72
    0x2402c60580e902c40590b280c29040700c40c1e20000d0011100c1c10321814404070f00103c542d0045c5004008000c2202a11480880002d040b203402e06020546104514104000034100c0c40b03100c0c09406142105248030300103000300b41c402015032000b03440102290b02d6010586000340301c1130300400c0281d40d440208001d10001004295403d0080c41031101400380200c085901906c10900c19020003803030024000b0041090800c030850303581d04c5000c8900581c0d10b0034a524044c007059510300119028815501890340ea01c1d40c001100b036004802004056a004002d5a038405005240c0040d40e680320b10742207003003c4850200030352040031131001d0b82c12810294440340569100c1c000301c51120040c1d40c0140c43e41140c001000702000d0080000b211542c0703501c2c1c0030304100c43c410007012406100380b85041c13005100d5561300201941d4651250418150721005445551085068440c40c6040030f40300c0c0120365481c0d001e5482444900004120b03207403182540b040300300804405840400f152408003c00c141e00803880d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 354691258 1250 354690008 354690019
    0x6020a0801081005070e06030405031e1317071e08191104140403030e070509090c011806080a0c09081603020307080f0a11010302090a08150a0b0d0b0402150a0806 71
    0x6035101070ba100d00c00c480c01040c41b600e4a00300031403030fa02042190340c8020400c59550205000b8903602060075030355400c0074a18440903036100c040d800c0c032020b503d6009500000c00005240c03103107120301c0c00c0410100151000701000c4400662440c03100741c500c80f181c0e844a40a0301c0340030b14060130b5108490346040c0717991050202012400741c0e00100001c1d2031043c1480310000c2401c101040010b80207070f0040081e1840402618289a80e620004d442054105d4079480c00e90002c0008551940c0c2c003400999040038030b4200c41d800341c1d040c85001404041c1c000c08858015503070b6254100464080d003044401017034010100e6003440840c41c0c082d00d901c100f52004034020301c00d00030041800030020460034205243e450043c202007196858501e43c06000c00c07a01810306034200400b000984582c49510302900c0c99070001c01141040c0300c0b1520000d08000c10340314015143c901150301b036540c0d0202c50709449410411111443c2c480c1c0c000143c00500528108416807400a0b8040409802030401440340100b03d81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 354692508 1250 354691258 354691273
    0x20703091a03070e0f15030f010801050108030d0e01090206030103030309050c041e15080321131101030c03111606140408092b0602040e100609061b06020a080108 71
    0x1d40480c490150a40c800c0100d01032000078a0341d840369081c0c2c00c2c02000101503c10310701001c000304503140c010000c042c804050000c02c12a401007440155801003109000800846d0300d02a0190340340d00818503079402c143e45807118500c8102e400d401001c101c2d90010710455a075652840d01034020009207804450074081d01c0340040b56440c0c00d201301c5003d900c0c410707140885000e0340741740c80c030080000941c02020003004c1d02c2e010541517400c0016101c1e29403201488a0319490500c0040500d403002032000150390800360900000030803840c1000300143e0300703080101d4608020030054016020141d280b20001d0f1000c240f2250380d44075108950300c1c0070b001e5441002420311140004050150485000c1d0024804001ea6005410300c03022202c0c40d503ca03910491000a040800e03100c0e1601043c0d020791304107401003400d1040c6d81c034090038160480c142c1c03642403640d80e1410002130004c90280c0725034003c0c461a01c002c000000c1c01c41d000202041c1c3c0c0b05804540c2c55480c0c0c04090105142801448039034400c080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 354693758 1250 354692508 354692519
    0x207090507210e030a0c05010608030a17160207060c261b070b070f0201050d110a0908031309050c1b0609010b151606020f0c070302010f020d05030c07020a030506070302070309 77
    0x2007500080030000f0040c5140c12602c1d18181c0d00144010000c0b01c030f0759a20440020142d900b4001b41c00b1050643c0d503914540c4080c42d1440001040207030040001d040346041e500481c03500003c01030f08503206406c0003130b40c02c0c04a060400d19101c00c0700c1203080e5a0880350b03d20460b510100c002b00302c49540c01081340f14482010100541e80c0040b4010051400820407440d804502c40d4000751401d103205242961511107030364840020313500395140b01d04031f821010428580441d040750000d8050505580110300380080720010240341d080d2803141000c01551080403842207800341c1d046401845141507110790004e01807001d02c1d5520400c65002c0c015510300540056240380c40151a0003044000d01401d09280f0503401c50000f0001d40401110030317a50030070160300390b452903e010700b200795550009041c50f01d1940c00003614400f08800d1005c2190000d035041d250039500310080e00c0e00204c856064549500d12840400c000c6401da8102402d94800c2800300200141d140e00180245840303540c40b01e03403550742c46 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 354695008 1250 354693758 354693761
    0x6040611090109030807080c120306040b040b0d06050405010e15100902040f0603180b04050c01080708060109120213060b0c0c01020714090a14070c0203061510050307020709050721 79
    0x8581c95400145141c07400c001045902c805030100310301840e115441d101c40d5001c514609000c02d8030903001300e0300200030080030b443c051181d240580c05c182c1d400c0c8650b1100a00180290308042c4000b004150b480d40410140079095200080300781880003111442035402d807100440d61012201c0c181c0d0b00c81500000704800d030a50090b40e04031100d04081c00c80640c00d0907002d9000d09101080a6600d40e51904080c02082c9481d20300d03400765019002070014411508001004c0c241c0c001c2c122024410100144202a40d1203c205003c542003030b444010310405070b10010b0b00395141214996060f40c24180e0210720f414851005101c02c0c0903100c04c46142c040b600005a07115010f03441290100c404116a5a64900b01030321100d03407140d03101d0070004d100d030003004004903840d40c2900c0110014a00d040c0f0202181000c1000e540c01a11505800401000c000000340c03204550410f20010060048007150f417840c002c01009010303090284040c016031803c8200102640c0101c000742d102d8004032070401100c580107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 354696258 1250 354695008 354695017
    0x207140d020c01051b1e06100b0919090c26090607080c09040e1b0a0e01151b110913050705040519050a050106110601080d08180a0506040611 62
    0x40e005460406606001943c883e040701c2500b81460040191404c908401885104031440c4440c064550086c19107103600c0c5410001410003050002c0d40301c0511181401100b981c03100e1500312000790260341e03401403402c15280b55901041e0311a0070260110900c44c1c00000c80c0d04110454010b000c620300c62003482040340071003a10f0400070303600a840401c2815100b4a00c45601801400b2602e2030b043c103500108d0102c440610f1500200c1d080900514907141081c24141d40001d401c40d030b00c103510303424400500e01020041c841c65400c4c01da56201d1000d20303801101c00700c10f03004208802d60400b0050342041c03840c0c0c62141c0300c0507119401c4200001d19554044907071200715178200004081843c00d0a040c00b0080070050800b000510a05580c0040328206004944c03142410a80c00728080d451f04e1000f40001904641825003074001d100103000201c40041e21000003481864880200d488241d010442c0100040110029014480c040404d20400242c8507000300c2c807400e0100120b0760340c1d000901c006c0c040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 354697508 1250 354696258 354696283
    0x302060a03020d1d210904020306150c0a120c2d0c090212010b0c1506130903030b15040515070f021e1206060a0e0406020c0105010f080106050303030408070212011d01020714 76
    0x40603c0b07901c1b82410a9405140d0041014000392152082110302803038503081340142003034a0f84a042c040c0c0800103c0c1a25941d02002c5003000c0d41c90195503940e0081200d8400c03182c0c4c0010001100481280c136155a0090049400070700d6184815180c80341301c8046d6124905101506400e080002034a03807251040714074002c9814090100c6c01c0d500e1100100c0042c02600456000030906038802040748288503038488288039031400100e9660480038070800700c460300441500300d00b041c40b01b0406500c40a03942c200403042018140c0d039039079040c41c03c1c20000b9694000030750030903d5210047c000d51880028050740d900c2c100c501c1000c6c102c9041219035210130480d4401c0d0807e041c0141000b19171501880d00f030f00144201c00c0035042180d02c0c00000e0171120264403007400c050000d10108100d41013072107a6005800164003642c030f50b240c00d48550080780f003418402401841d80803034549120710203600c0500d00180344027070007208011011006010f50440c100c2a90b07604100d030604022014001941d00361140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 354698758 1250 354697508 354697573
    0x6010f090903030605060a0f0806060304050607081b07031d09062209140105010509010e0f0601110f0a08090f09011a161a0f1e010302060a03020d1d 65
    0x203003006484406000901011018551a034002003405d42e1002d01512080c0050fa0f54819260a2200b0040040c10b021f0020b50040008005103c0803903008510f083c0d1080b03a41c00c1c4044507407130703400da411300307100c0905025450769402144100815a00c803046110b00034180a100203804823010410200c1017040d9945540640340e208010a8504d20050400717009512500015a003981c2e92510400d444490200d0a21655114010b00aa1400d00c030900d015000102e4102d01070725206c6000607400070302400490510090003c1e643c01e01000300002c00302d2a49070000da0360307008030a18124419400c1503100c24800e80030b0b00d801c1012420100c100c030741241d0107411f0b40203d0000c1ea902e4017685900403111000c003075030102105000b04481342e01400003101702e04103110040c03030700302459118644090701000c10140707209808070701c109290b112941500e030121b60243c2d40301c6442c1c1081c1d0003841000d40100500d4240503c141d0340b40c00e401e001d46400451034003a500b100c8600240d035000000c405c08400b90b0708 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 354700008 1250 354698758 354698789
    0x10501020c21070306020c0303040210020a03121505041b03060b070b060f0607051b040507110a0212010e07090906140702031b030f0c0109030f210203041a070513080601 74
    0x1489039800c410b400242200903659160f4881e02c1e20426680a248850385c1540000244000c60038000e40701c1c54200e1540c8050300da5041d459030024181100c15003108042e94071403c10580300310b2803002c5040141001801040038040c00c503500e03c01c0c5444004180c0c0441d14041000494400e210100c804065002259800c43d60740c10080090301003d000d01c01c2e070881014410300b4002181000b0101a400c81c02d030310000c90b21002001c10040d514010040130030048004200c000c2c40c400043d10b47c105581c1103820304030b000c00703252a150050003001d80d0202c66101d030070000100244140e01041055000d400c09020407080003000c20000c0c00203507107450060740100a80b68160720401000b4908400407015a464050145c1d90150940c111007610a20b607552380c4000020150800068000542c81d8200448980b88084e00b1000d201c005090894a0036000000142009441c0c414440912400d050f46c03007039403d0140700102160000d0a41c0201074082c4d50f0b0100d103802000542d0b03412281da40c010303200e00e0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 354701258 1250 354700008 354700039
    0x5030a0303021c020403080c0615090a0207020d29010b130608040303020c06040b18010b06030601051b1b010f050c190609020907030f1805030909042306040b010501020c 74
    0x1e622008010718031010f040d0342c051078421280002c2005500600d20310703803282e554481803070a0400c050b21a01d107008040e066498640c0711440255440415001d006803544000d0022840c3e4031154400200021500c030000c0e0a001314049544600155038150b0600d240e81300d1045240c10b01c00c0c6510f00d00c195002e00300400c0042c7c41040c2540d4043e1207464090f0400d240c48545515016054074100c660704202030800040d100030340140002816680024015005920701041182c807010348054100000001c00c00700c4038507507400382a00304000304121042c208010904038074103030700001c00b2400105098011000300303102e14283c43c12050f03920040d2112405048005001e00c8060b10b0443c0c50a44502ca014050b95500c0515849400140c074081401006499008101c604918021070400f08091500011520000944100040607200d2061a458500b0f04e0b9860200c4245602000b181e0104c110061100c00300c0c0749401288617031a0500c459132a2001a0b0325802110705040d000040002113440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 354702508 1250 354701258 354701261
    0x60e0d0f020613060518040b010c02060912030c0601050f01020303010305070b07022206050f0a290c1c0306050405040302100c18090e0f0114040602030a0623100905030a0303 76
    0x1a55200038440e52030300c82c85100308110400b1a501c00c8000c05d102003425036100b90720700b5103810114001c0303a0410540246800280c00d02c4031009000e801640d02054138603254443c650303079480d40d10f101802c4070b484550a40750f10741c2d298400d02880d40962404d10729070501e5400042517a042e6a440400b419000f803c14190503c030f074208500590b4001c40c03c10310300c200300f2350b21602110050751800c0007003601800c000c00c1c0071302c1554000b403580c0283c1031401c00700320014050a01c031840c10040300d002540788c2e40d02e421f0410b550242d0107040000e4091001c0c08182c840c0d1a081031540310019032424010320381d6136402c0000301c4808a6000d00942c204a803841a16095980003080038043d900300031907802600c1d01c00d030308001459000105c607207030340c2c91910303900000401c20511a02800030082c00707d0081001404000d05026200812894010020039000c1e50140c0010000e805c4100180d03000707c403665240c0344c021600018640c00790f416600c0b844440c51280b455001030f5075001e002081c4c94205540d0490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 354703758 1250 354702508 354702533
    0x3020a020a02040c17070203040b0919080111070605010f0311101107080d0216060219080c100501031a22030e060f1c02040503100c0e09100906060e0d 66
    0x45019030380001d0016600c1d07100740c40c0c00780441c1c0d0340c22000f8140801018810440504284103661041c0410400803995000300c0c1c0200790b00f500d0860035071003a50fa181000e001d0070342000c29603509015940c42400d80203c003074604140905014402a40e075044081c0071010a80030140085081088650b084d00b04000b40b0490742025241ca2011320000c2020a030810440c0d400c10800e41d00100000002568104845204107200a60300d07080140b4220001e51740e04400c10000703601d40c01204a610a200083c0309580c008480071301a106240d4030f000039080108424081140c1c1c0c9280c1200201410340e136040f98a01c5644031419184400103045410702800c102008200c0c101b0040010504607912035601410075188500b00d010b459071030080c0058801c0c1c680385040044030f841400f08004903900040c01ca41c286008080009803c02403081c200c0b44d035050b81104035005020107052281303410141e1140021122481810009691103d0303007200c2c6201110b03140781d4807545088490300400c01e0507200d003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 354705008 1250 354703758 354703777
    0x1103060111033a0e03251709030d03140403111507020d0f022103060a0801110705010506011806031e0c021501060509090c0a021903020307051605091b0c03130311041b0302 75
    0x106e11001a90324030113540d482c034260248800010801e01001e003001c00c451041c41a1a0806201a04445a6010f0300e01802000030381009000000c4054410b4103000101c00d40e29940d60551a901c1d01d2074000c2d541e1104038462200080b1501c010a8803d0700c089901e82070b0b8035410380801c03644c000c20f030064240b5400c00740c00701d03512010801c000108414240b05148681c03503a2040c9a4030740300203040080c2100d400a05050511121509000b84480442400ea050701c51600b00041c402c012101c0b02400390710454401d500b96480c00f41030002c0c20303400040d0f4200300f010070301e1100070a0b84c03252001c4580f07024035015640c21043c400c010440d14189038024062034000d0348100c4440030030754220242c4003002d03c0c0050700540c00000720b80c001d01c14140412005804a4906241418900b202041e50300400a21006d4044a4500704d02c400d4212801204e40301074107175003201c1d201c0b101d58007078112600c0288412540c0d10341029584071942498054040c00d8580d040c00252000c006102c107502940c01041032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 354706258 1250 354705008 354705067
    0x2030921090a0303080a0b0301050708040b040302031207051209070b0f09030f060c0301230f010c0215030717090c18041506030c03060e011103060111033a0e03 70
    0x1071250758903882e4100300190701940d40d03035805003060b03070f4064102e503100c2000c14000e0341050204100301c4d4020484075001940012070b0b074901d60b80d90600324214081d40e803000503068121070030301501c01e034000e018200f201540c0c0c641680300e46503600c8035030ba01e00c4c0340e20800c018030b0030138019000b11041c02130207042c03180e801406072030485034100f0105003000c5040f200040d000070080014071080a0950750110b4900700c0c0300303003d11651008400500500004444981040b850501d140d045444584010089210b020b08082d140c0c02c03c00b0000e0218001034103442810009000001c0ea4041c000a9550441201600c00315000990307100d04030800c000140150b503904540d00386403025280d1403142c80c009500500000c0d034130508514242c0c080d10072000c540443d607814580e02d500421100e9048941111003402d10070441d01c6002001401e501400241e4001201070840c40a981c004001041c0380c1c40d00c0720498680e101004001d03000c12542400b000701201d030f00504c40481d00ca03130b82941408240041424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 354707508 1250 354706258 354706267
    0xd0204030615080d02060c0f03370b0d0f030302131a0406031a0f0f01171006030b03061006030f1b17010b07020303090603071419080a02030921 63
    0x8030281600d0380d035581c450b22001141010404410140405855545103101610030b0f4205050710041c9405050121018600300002240a1030b85a024901803404000d2007007946030010264080060340e0001003a561605102050489150030840844c43c554800060a0020401e40b002c5009421000044000c90300c01c0801046949034800e03960192002420400c2d5a1130030700500500780c0391180c8001541148100c0c1081141e81c51245408142400344c9403210040281c171300403680341e201c1011010083d80315109101442400000b43c1c02500c0140d101404400d510f101450754541c8200c2d10044260014031040c0a4140300e6048800ca46e00350900129007004021041300c060314080c0701c01c50204010b81d24100d140ba0b070208a440c01400701c0c07591682851b0154001c0b03520b900c600307002d07a0312610300040054180da01402c915410901b19008a58a400c10207054070322000035440010f011400d100d00103a9411544d0080707901c21002c483c09007020202c52100500a18070001d46070111403010300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 354708758 1250 354707508 354707513
    0x306010905120c03160e040312150b0408010e15070813140114010602070b070204020c07031b03060f09080415090b0d0605040f0c0e010c1104050109020d0e010e0705060d020403 77
    0xb941c0950000b20034000d000c20380c4800782058900411000c1407840e2140408080115500d070341c0580341d00c0350305420b1819901451025510040003001d01e142c1c000300d0b01c000045400b81440010f003054519180007046400c7e25041c19a40d01c0c030605007c140317021484400140e005100b944419000308022030800814039a5548107410300500960310241c5a554010541c8079041d0502914010442400030781411420007101e2800e038031a140c8081c0c0180e8000814852501042140000444d00030f40140d00d480c003504038488226219202c10b0310114204040d4019251862041c0010f10b580440e11503d05840c3c4195001c0380c500d0350000c0c00034804000c5000a5021100d8020034001c0005000000c200d41040c1c10841102c4421900b264440d2803d500449503a8000d920300c05240002d0070241d10398030302c0e454102c140c0d1241c540d01980240c10680005000c00054020300144d01c501e200600c40006480b18980c01c8a41401000500ba4080d0070b08000d030f400c0100080030358040001c005031400352281c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 354710008 1250 354708758 354708769
    0x60f0c07082703010b0a0609060c2a060206091914031e0309011805033106080a0c0c0c0302151b0c0102070f03030806100504031e150c050706020306010905 68
    0xc0c0701d0b0381c81d1000710b0a05015034942031040654041d4101d40c043e00103414020f0042c40400c9502400e005d10a8050201d024030454000e85e01084001e00011070f840104020700180c1046103105002c0544201c50109805000225001c1090380c031504241c0e000d21990717201c22908407910302100310180400c04c044252003100020501c15001d90f511a01c0c1d8038204011103500f1110a04640c401941d1b915100710000303400031048072141d507903071003642001050170040c481407804005080546c082d802c0900291041c2c11482461040441c007104000c00040301c2c00c195076011850034000c00201240350180010b103001000c6003030020044000710b0820b4030080d45114441510318040d420382d80300682c1c3c07422039a410001034001d41450300d0501c0d840c07495560090041e100c05803440780305004c083c5140740c04a1040d0161801907801010443d4020041d56904420419200701540d000c80c0500506c070708016580200d502c2520566103583c6450400d0312410025080500414104500010001426582c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 354711258 1250 354710008 354710047
    0x71202100e0303071406070f170402010e0a0f03030e0a0305100e070b131503020a08073f05240613090c050c010507030504110d140d02070512060f0c0708 67
    0x165402402c000e00000e0b002c0d06d8030300300030301003410415840448100e196001000f44a00005408007801030744682c40166400c0c840b00004680000740702e800091152010025141268021b440c0e04c1c0542c9100c1d400d04c08140014000544164440001441c400350036600ca050009000c1d81507a641035180c13429030380c550f0f006200201c440000b81c103040c001444042d8458007100c145080451030301c0c5240c0005070240400a00f890207120340d1420609042c6505c01d5003a0034280c04056481c0401000f404100c3c3d120804010014001d291a0000308100e0742040c50950501e05219500c0c125042a0100161640300086560f81446000c0000902c030226004074a11038101e52901612054030344000c03421144020300c810b0815040c5010301020a525070802075440b5030903108000042101e09040c0c1044201c0b10b002c400e2813003001d00780465207901241c4441070741c40071661005e0b6100006061590b400d002d503003081902104002080c48010400d0040c05090320901589082c20322400c10540e8542c03c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 354712508 1250 354711258 354711263
    0x327170102070b010e100e090307020904210c0503270d060c14040f0504020a031407180503010e19150906021206060a020615040e1e0609071202100e030307 68
    0x40109802c4208903941c150580940110312003191586041d0b00c920504171002d1050b01510a54a0f01007000e40c08140120340d0342e01d402410030000e83c20036162900400c0680b034022410040b4130302c94000118410010340d42c5407074011005500784618134140821040055142c0348000c0c030400b1a924880c0c866516038034607940a48400114a03620305805003420a981c86800840c8404200c00d00c205130041400206980702a41c0040e01d8240c5002c0540050a0004d08040c0e0041008200b04400350b00c201c017440707000d0690342d84000190fa102c00307050a988030010b80c1021030300000c065481c070040480f00805158080c0c081c0300c00040c00780044100b00c0d003041800351095a000291611491802c1081d190400003e40d5583d20340b010104c8025210403014041a406032a10314070400741e50f031150489102c00b040d01c0140d03208507229030016074009902c0945000c4038041c10340011584a80450044129001100d14100303801059080200d80e6459040280c14004c16181b4201e06031401c00150a1961 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 354713758 1250 354712508 354712511
    0xa090f0e1608130b18070b04030f110a121209060216141c0b0603060114010c030c11150c0d05040f120302100c02010c021501060c0311030c0d08040c050a0303271701 72
    0x10245c0c1901c0b41800340325044008900c200700f000f007002500f00c2d2a183c02d11500140c810728080c084000156850700300c0e40c020030304140303142c1c0210306010045400a40b00300c4541c6414030034950390f5500f80c1e1920348029400541003a1550200162a101c14400c0c0090b400200038600f851004641c0711286100b02c4010b5038488420000c01c541d900301000203230701601e6050b001201900d01c10780001c1101d2512940101005920203611003001059402c0e200b000000418a840590004031b103003005070484140801540714002035820170b00c0c091000c136010b803401d822040c003a0f14281410030a0a9030004c0003281107100d01c146d03501790410248a203020a003c5940045200040c2d03210082c9401608905090301c2e190300341c0104030f0345402c8071103092600d5060920078001c40800c0c420343c0c150302030440d4840c80c5010303d0703081062541d03100d44414443c6200f01c11020615440300c0504c0302041c03c2c3c1c00000e001c504101d802c601c249800f000c0d200b07406000d00e180c0106260710b50b4000d01e01c2045410202c3c050703a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 354715008 1250 354713758 354713791
    0x3040801050f0441100605041401260115060e01030615030e0a08040b03010303171e06030c030109050c040e01020c070b0f0d020a090f0e1608130b 64
    0xa040a0007000c0c0c22440d040c01c006000d0510303440b01e120440c0c010104a500300940c9403540004640782ca5640040311020710000c600e049070f0b01000751118190742201c1c117024508040400c0c507160500c28902125403040360300348145e00b07210507058091003000398410030040140a2030307281d2509018600c000c0e40d200c1c10480d00d0b1890900302410030380b91005081c2c180f5040c400203020a500740340c1c0600b0080410310f40410b002600d400100c0c00c20485803009414854000f601003640c94082000711f048038401d69a21791000141e12400c03c4003142a51b0107603074140442c2030681e05140101c082900b18a00800396a007000c45000001c0c00c41e030000e5021030300740d00401280c0ca500c0c82c007441003a201000400081d482c101e0b134804450f8641d03416001e0324488400c0032502c141400c908200b030b114545824201103644d00c0100d4005400b00406204000d0040000540031688481d1248454000c120328000d000b200901d1400c2659642c0c8010603c0c1e494000703e0304010701049551a101c2c0c010240c100254180c0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 354716258 1250 354715008 354715019
    0x30c030201080108010b100807050405270121080a11060a14181246030204030308040b06040f0c0c0212012d02040905010602012f12060f0d050304 64
    0x1e04005030300030010303a49004070100d050b40361f4240c14000030074203140080c1c00b9500c01c0c0c4203941c0e0b80180d401003038101003c500340c180754800340c0c04940396826403600701214a0b030360303044000f000018034a0b4108c9a000802031403070005d810300c0090115a00d01d800c04084030310900c1c403410f00c0c01d130303080324105c801c2c036250903c19500020f64131040380c00c16040c03151214070501c1da442075581d440301076002c0820340c0c60006100303060101d801700301c074409044403080500700505c3c41040c070726000d40030090707400556503240c40040c094028400c40d01101d070b05403244955683c1c0d0f40c0701d0310301c2e11000600f4950095181c1c003600541d40814030482c08244c480d510307485012186401072100c00200017201186607850001711501400900031070318403500031440003413800780300d040e052806401283c1c44104901e04060002c555182c040d082aa550100800361109817440400018811032140150003408d103403c0004001e6101e8440400740d0060003e0f2100c001d80b02d0b00c0012403006040214192459000810709106 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 354717508 1250 354716258 354716267
    0xa050310022b020304060522150207080c07031b1a030403020c040608031b010c021222150807030c09050111030702090103062705030d0f2d18050a030309080f0301030c030201 76
    0x1044049005230f81c090004211000224554130300700a050550310f03110101142a068040321420b942c0811040c0e1075100c51040c1c2c50307840c441404100da0740c041021a14040940342e01443d0100c0303084102a5054420b061842e07105940080c1c0141c08600686051495540340d5000c0e04004080c000003c696888000c08404030700612005208000d90400c8600034182d07500040305040c400d0085203032b5070341c0c002400e03450b0fa0303111404540b001c807000d0440740080c0c14800a440d6415a640c01d855841c001e82e02c0700c200324111040c4c0c01c0648040380d61007109001c507510441c004511161a4000c4074640091a00068a1100f007684221155a15030400c2034060391216420b41102e0b294040220f252550b50b500e25880c0e0041407220100f0765501c440100420f140794006104620000c082080150390518505800000280c101c6030340c1410015205060b80c003030041450130ba5001809800071481641d400c40c05000c9a902c15245036009200c607a01e806441002180258803501d007403d00e50b1f01d91b100141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 354718758 1250 354717508 354717511
    0x10050c1b0601052409011812060b040c2d030905030f03060a0b0a0804110604120b060118080705040f0b06031503010b060307120e0709020d0603110a050310022b0203040605 75
    0x89010b1019040149200e00e40d800385d0750445800d080c0844000028039003410000c80d00da002e5481000b00c44a51004c0c07220a5001b10200d20058600380400126401c094801c40121000300078091031020494803210241d412103018280c051801080d040519141e05145030080b03042d49030110000000e2016910b003140c02c00e4014400099801e0402d1404180038284080041020701441e01c90101d1150560303c050465002e803150ba6401049800300341801010b03030604450142c0815146a020030079101820b444e8400c1300c0010004085d01802c1605000152402100800f0040c0c5c8a0301c03405195540c0e800503500c244100301c01e0044400c20002090700790f844003602503019407400c0042c044420340c88440304100004110000c507519240f1004a490102c0c4e03a40a90202031010a40d00a240704541058013120701452950001e4002e10701004008040d038800c80303034568003010104000449a8029142404030a0580154050950040000b183c1400110441e0690000401040003004d200e82c3e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 354720008 1250 354718758 354718789
    0x10b130b090f1012030203070606120b1b090d0602071415010b030f010b1c1802041406033310170c010e241b07120510050c1b060105 58
    0xb5034607802c1028140c506010240600f036181e001c0410010300b894001c02c00c465903113901100400039107a90b1054500895a081ca00f02c80d51310020b0003140703c840501043d8140810036420952070400f6283c10080b00d0f071014042103817103a8091000c280414030800e01c80b490f441c1075401a00b080046102034222040050b04600541c13a070500501907801c8000c05185c1c15900f226985540d1441c03540399030540420300c00d2203803803113a083c0108031010818580f1070310107051003600c0c00d010f030061809609414001c11151941c250703102c404d40907054202416a0807c0c2403805000744588500341003440600f45085030703540300c0841070010410405c000c00e1140c001c800b14002c040e10b03140f402580000c11244501c4555845001007030307216141000240c50a41c9200c510181ca03507541c482c014840d0404164003c0c4450407401182000540a0201034612200c19803082c040c00407800c0e2030220034000c24000d004c81d018500700b40301010411030064480c268120300b401c0100415072400c820000b8450300441c82 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 354721258 1250 354720008 354720031
    0xb0a0f030501032103020c060901020c0f070311012a0515090105101e08070f0f050a0b030c03100302030f0c1203070b1816031505010501080108030d0c02010b130b09 72
    0x400100c0c021012403403c0d080b214104c1c030110104950100c0103801564481d4040e0701420301031000000c0154010169003512a00b5940c844e00c0d59488035454000600c409801500400c160005643c46144a20700b8840e101004c0c107501d2080090750b0015031070004089500364401c00c54807941e8000b40d20403a6001e96260020b2109141014421039211400d02c65009100310980c4028010040b4a007036101819a58080f0340e0340303c3ea15160304110100c1403007030802c001027101000c90b1300d092152140d8195071040140903d19114000b503080d01c2c0e0700050160030340c048410740100042c0e500740705d014080d40044c0010160b24144208000b101040904a10125072042000c0310000781485020303640300c8101b42c980384965648104550403d01032440440c20140d60510100030450501d00000e030040b445401000036a0303c031300054454080a0141005941c0180060310203010b05401194450442d840040b0301c00c03c034100456480820070a43c2c603141034450b0b08a00050400d13928650b805950100f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 354722508 1250 354721258 354721261
    0x105060108060d02010c2315010509150904120e1503090601060e0d08030a0e06010b1c090201050403080a0e0406121a0c0a0f0e03071409060f01020d0c020a03020303040b0a0f0305 78
    0x46c00050800000070806001280195450415410010240d544e500c1c26151000c50080806850030001d0141034490003140740880e00c40d080c0803840074840e200c0078210700066140c0c0e4483d040c2d000030001c021030030400c2404003010300b174441c42070b1581480c0007c2e44107512801c094450505010b0142c0080301040710003c40340c0160380c0c40304014018250000602d0b503503030f103400d105a0080c00c4a142d100314036116010000031804d0115005101d0500c00351080300c0001200c051440c1a60140d09010b40000c809003c14000b2801072001000481846c1c10706510080d6140040340c04e88a40d0341c80550303c030101c4007101e020722040c01101c0e1000c24035000e11150a140c40d01032120320f4040e01c0008000c020500060900c9103024811b0080000d40c01411079403003550713503059032a80400801205015800502c0402d01904080b01e8000c807007a01600500032941c4401ea00329400044010140c0c0c0c045032110b030000c0940c509000910240441491156581212000182c160340d0b000140302c0800d841c050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 354723758 1250 354722508 354722513
    0x50304240e011b060609060308130807060e2101060807050f06070f08090a08030d0603021804030801140a12050616080903030a052e0305101415040e030c0105060108060d 74
    0xc43c0000902c0031000b1054500d2460304055005001c9508001506850321a011080c85081006040703207003c040058181d0f10b46a21440b921004148034110110748040d18850302460701c8000701203525070401d0114030303490b250808031342919119401080c25410050050010381026090401c91000988100b864010f1541c2c41406124000c034018114082c040b50a0845030364001c1c0c0640240580800c4030b03145c0c4410710743e1100911803071100324440e03250031031440e00d40440341e401c0c1031041d90103444d4100b190b8605610800e190034207010840e440404078a0200d4000707480443c1e0fa50050188004026500c4c0c031b40032030720314000c0c602c00d2402072200400411442c11000812290f00010070040821940c4683c03824400000005d980c58890703000003034031445089076003213125017201d0003102194a0522021840b0f002c5940380c0d40b5170300200c00f071100000c5c0620342c00366041d401c100300030b40001030480c1c0482c140390564010840d11031860b5180c0061003110340e8041c0d0f43c107070071032000c03148501602c5c8640d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 354725008 1250 354723758 354723767
    0x5040e0604020705010623040b04050f0402010f030b120105090c0301050402030307061503140c0f010302030907140d022205010b0a1b1b0f060201110309061b07050304240e01 76
    0x80206125a4001800404102080d0010001400c0783c2401040940b074095120a124900076400d40c0580c9c60324111902d1403919000340c90250000004400c020b440f15001102c83e0310300c1469001c00c0c9519094800c00350307210b001581040c4c203411400019a801d109060034140044480c1c0c15102e0786c141401c0c0009660080101c4850036880710000030380845c01c10420706034442c0c075070015280300030451104108000c08590500c0c1000110b4641c1c010304003000040d401c0b40015105240d00e54482442801026450a040440b5400c000e184200042041e400141210301c2c044088260080d41d2048021004003405814054014903001c14201036105a0003428001c15001a190383c20b0b88860031410b021141010b551060181d6805813500c0b516404054001038242c0300ea400150b181980620314038030440280e9010b016001c028000c9912002074620303103800903821140072030b8410814200000c00800c001e00040c07040c42212054260b0700c1d11021303a000c10f01c14965051001c2c16071400c046030303480b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 354726258 1250 354725008 354725011
    0x90b012d0602250f060e0310060f12050f03180a060f0804120c1203020903070f1202061c020304060507120504170d09050303010e100803070506070c060b0301181205040e 74
    0x25030380e0f03003555140e07181c950001c005195402141603503811030020810507400020204e054009508031400c1c40c0003100900c04640d1144035030100c031038400c007051000c4034000b145100c501703014400f10f0705201100840c1c1c50031540282e02c4408801c0110020202e00e0400e08400d500800103801e05012070302e0207035400f81c10840c00520051004a14018910304680510f480d100443e030840c801a004916501e0050000c0d0f2005551a22030301c201c0d000020820548940d4a0075524086005241010300e94240442c13030b00034002d44901519840e030747c00c0b5040c0c1240b016501c541e000e600d01145c1424007080241201c0d0039020420141410001000042118201000d1444114600755079841040800722030040c4428000140329000010002607a140001ea546000d02082c0155981055070b88101594031b214180d0024555000703000081c01c4540215402021140519000f0480002440010b03003194855041c40e8282544c1c0d40c0c1c49400e01c03000242c01c0701c6418031401e1480c80c042c1040c904034141c2c0c20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 354727508 1250 354726258 354726283
    0x7020904020114030709030c090606090b0a02010204051c03031803020615031e030d05090312070f0e060a0503070e0402131710140108240604020d090b012d0602 70
    0x25220042011a4841c014400d90740b40c0b06078a640c0c9030306020800600b8049a03100035903207058400130114081a0911400084640b162110754a03146804c2032242250130841460b025075600303100008854031815030092000c0c03c8401d420b0040c0c580c0745000780484d140494030120150b403a07903003080081d0300005d64942003458154186840c19507500001d185c142400c607054600710a280080c2c41000002000d8450940b4203841400b00b0b60310203038103039641e00583c046070804407407400104510038024104140406042c0c41c140132591014800300c2c0036584030551001c00501c3c00005c101c0340729889400d80c600c4440c00c480540c40d000b580c11950110800313038041c1130f0800e100c40c24201000d840410081a0b920b61003402801410610440301010325000d1243c44054050031030060b010111007846800340d1046040b00b00060f03101c0f242804025008580f00307c001035951480c3c007005c1142044a00d000f4001201400c4840110400502c030503142803034141d048400c0c29209100c1c054000c54200c0d000710 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 354728758 1250 354727508 354727519
    0x708060c09040f110c0304030215161401090c0b0403060b0d2d0209072105070503011206091401060915140405060105270103060602060609180c0603180c0909030702 72
    0x31a100c100c000600a400e00b28000403400148800702c17103408800707481203074006c48400b500e21000009000040c0b0401600a50080078030841d04001241440001c0f01d030054903000146180c003584c0e031070300302c041160001d2079500c201040400c00c11000b4041c00c04842010303143d0740301d5410280d070340d0702d0040c1040c0c241140d0380400d441181d8000c0c11641e0440a5103800400701c80300750800c158054140d003180381d210010080d044070402000c0c0b85500aa5028103810303030700d25145038600f0306004141d8140202c11a203181e2500111001700b44016483c10b1018507031000000c04d54070f0404210101d83d80e078919004800004201042030711709555010061080607a0041950350750030004031141d102e440550101204480964180c0200e20115100110401e803800c208554850340240d82c2c503c401c0380c0e0b0369402100d0340c000034001800140b100441080e00400c4a40340c4101d00005100c036001100d400419548003000580008020880b6210704c1c80207035039190761418080c07141601ca02c2090300107030062 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 354730008 1250 354728758 354728771
    0x302072d0b0f0702060304080a030606020d051905040b030403030606110c0a09110c030c011a0f0d020f060f221401020a1e021e01030e0705010e040504060b0a080f0708060c0904 77
    0x42c400404441003158000e200644c1c900d824600b80909400c00c0e6002d200091519101043c02c40c000a403024a00549841341030a204d08001d40c000e8101400c0c044100700a4140000525034400340023a40c080da1094801080043c01d00000400da41510305032841c10b17910240e2401c1c2075417541581c4e0300a03100c5900011580a24040c003e48161150814194440c8000034550310038600c103500580f0b100100c1c02d11450950700030300402071701040d4408943e500040724240740f8014900345090035030301d6501506007401e01d480368000e8041604041c844a0a00481350b400741c40b07501d4005070003000f420f903001400b00c1402d2042c0000b5a980d44c1142c004004025401c10b04440f8000d04c034010490b154014182d12124050800c180502c641c010143d030f0100707040c00c0c41e050801c040410040c05450b8184e47d43c1c00030035450820400038080142c8242c41d6143d42d40302e801040c0c4c403411452800b410907600100785190f05002a64a0710b0340960042e405600460305111200c1e11b8001101c0d180c00c800c03180860708 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 354731258 1250 354730008 354730027
    0x6061803010b060a0804030f0e10050903011401090603170703021f060506030a061e0e0c0a030b0d080304021305010f05060f13030b060f01030e1e190302072d0b 70
    0x4002122030164001c0c0d0214400c1c0fa400d901c40201c0e481b4034480c0d9038051150301118401c0c3d482405a484143e480182c0800044856120b00040d2107100002000440d9170925500422101c0c13400303801a00751951294003e105001e800300b50f0120b555021031643e4588082500c0094682c80c00c044c5140402c0f0358804500420f00f240d402400283c02d0041c411607070703410000b050400034103051040c51500480e41030040500000c000054085890b60103002c01d40e5912642d502089a220588500070b155071b0b035031a1400c545409080415107403085000c2d9a60f410035004011110b5540002c108a960910005100f00c07402d600f05c0e101154026180c40344c68050f50700d0100100d00511000340ea4911038a9400024030541f0345000340030300c4040d1031001103c0074641c01101964022034ad82c0302642e108da42d07000d800600e10451800250840e90036101e4010343c218200c90b603070042850950050b440307001d0038408a07007451070082004074a445410700012440440e014149103c0c4119000590003245030700c0d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 354732508 1250 354731258 354731261
    0xc1518010c051306020a0b0a0c12020f090117011202010c080c0f07030c09090512070606030203120c070e06030c0d060204090207061a0415140102010b0402030a0e0c090606180301 78
    0x21a004000090042000c0d940c001403658110b10700080e900c0050100000310303940082454a40d15400c1000c2a002d42c0d910b810744c00140c50b991000d441000b90401404140741e146e44040c0010780302c05840303135a8405440000401241081c010140c4007158617004019070500e5040410b4520750a00340303480401c21508046c11103001c0c1c2c40c24031245005588116820036004607482056030f2050a91a1516803540982000c58128550003045580050b00000f6162802d40180a03520712079140440c0e4941c40e6400301c2e081106002e254400c0400200300b40551000521501e00600b200300208101e038585000000d03560f1001e50552405516440f114101707210380c40c1c040b500074260001007559200ca0500e0b00e40000e003008811641003091949002a0615190060400780e4031401c0140390850b003000f4041d001d41e81c1403d006030656580e1425411543c41d0360015510031031010f07600140d56141c046085007020f0a210a6900c03c1c241c000c104004c940d18001a2020b9030bc2491660b0310702c1d903a60000c01d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 354733758 1250 354732508 354732541
    0x5120a05041a01080d11030a050901030f02160b2a04060810030605100314060609160207050312070209070906080c0d180b0916051f12060320060c15 65
    0xe071400201c1001148030580005d411041070500d030394030030320566080d8000b0340340d0040040703040010b042001060841e40c440e400500d070f8180001e0005140045005e483c0724480c032004821110034443d8000c02030600c204041490032001c41009145c0075030f480d0b4082d41c00c60301c03884c06200c040c0050140494403100c55a43e00801465028200b00b2440c1002070746402240f08900c411a6000003000c0d0048901d800828110701810014042c00241e031203c030a54000011502803000840c0700c0c10f0720002d5181e400b0420f0110b0310345802c410756610001401031209602d4020440d00c01d02050880070081298483d0780ac42e844000d80340080d8407900c120f036043c4080d2204074515582403035040302c0c840c2403002000b419402290988110742c3c4c051030380048105105c10521596600210911044090003151804840301c20f20741d01e8240740c500c40f41c0c02e0300402c0b0344060b08107554140c04200d0f04800380d401c540791014001070031902c980c245000c103000c0c640e852004004010540d054540400c00d070310341079107850 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 354735008 1250 354733758 354733793
    0xa0902030105190b0307051005090117010e0115020f0d05090d02040207121b050c090709080303070e030601050109051c0501021b060a0513030f0305090c0d06050105090705120a0504 79
    0x81c0400c0c200440d100004600b620302410f21580342c100b810046150005d46030b402c990b000f602d1000c1d0041001020f442c2900042100350610100c2044614510301d009a400d0183c1001910b0110075414911803107544c1d142e200400c420355028076000082c0103070005014903415407600e0410707500d81161001c02c8101c0440c0600a401c24004111402008147e010301c031000a051f90f50003a0070a10070b000c604ea80c0508440143c203640010f5800380060610075001d961003075030350400c01c5074542d840c4800c5103940d204459100c0003510080428400345424001c8500603c030901c2c0402c441030901001406a00d0192840c54100b0401d48100c400c009081d01510703043e05811a00340d00c42803060421030f0b120401202d040d0303840ca11b00800140307140001080d800e83e0a4050f59221703110343d03101409400400020340820018401c040b110420795855130310160f04540305140c0030419515050501c0240e0380041d01c0320090203c01d100b02d51702d44801001d03040c1d224090400200f11a240e5040c1458270490701c10700d2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 354736258 1250 354735008 354735011
    0x3010f06030506061206010302060706090f0b13021302130504151517010e16180e010906090b040c020a08070305130f15022a0f030d080f13020310050a09020301 70
    0x800d02c600400d019200398820303541e44610303100d0309940d40c1c0c603503109001c0207600420030b1080d6008202140d00100d640c0d8403ca800c1d055074040790721440843c8404032121f52009a03d201503904505080c1105584610588025414038902490705018001030b401510700490340c035401d0407486032100001c02c2c0109940b41c803042c505008008014101d040ba8603c600e6080d40080c00003e0103045002c2080c440c00307465036078242c50444c3e10300459418450b6045030050078803104010640c10000007015000708006c400024500d1b1400700d224090b00c1c85c00065610441c6051568501e541d008910110820707030003221340388d65180900d07065a1030b001f0039001202d0f200c40303d0004111a41080c0e80001900d002d8071101a0b107402e50001281e42c0c490803400400241e41d001c06600b4440301c3c541a503080c400b4001c0101c42e42c0d0001d070021030301d4103030070340000000160000705001948486442a0f60030068400305c0e0010741e412900800c2e620310001d41c07114480c5079648001500c900059100042c15a4001d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 354737508 1250 354736258 354736271
    0x70201110624130e010617030307050d0b061c020a0f082a04090509070f0506130b0d0920010801210b07050408012307030e070b030a020c0a03020f1e0c09040203010f 72
    0x31154000c280c6c0e4007418840394130914504446a2000094904c117444660f0f9607451b160591015031b002d40f60035400f682d00074070180305801040200c1c510014114072071000051300d48510580003440700010f43e42c07010510600c40b0030303c0824022004881c880440c0c620000301510200b041201881c400da84c80b0803009840c19042c00b02c045408100001103a031200302c042c03030750340e250002c0217034510411107a451038031503200c000c014012281018040301004503c0001d00980d45840301c600c0c800c504005428065500b04010200f0740c0c2000103240501409011a6940c0100b041d2214100000c2d00014002d80e81c04e100191055204504a40180c02410000c1c445260f4840220160403104100302203654080c200007040d05100b4401e0a8204020800914480b031801e004070a50b41d002411021401d40c08001000108004100903800d40c0c1c07086d8005c1203d12898126982801c0400500030402c40740e2485101c443d110000c1e4890000408072003183c0300351036520019004000032108d1000e847e05008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 354738758 1250 354737508 354737531
    0x12071e050a02010606050405060d0b010210020a05090301150605030408160c17150603100b13110c06060603130b10090507030c080c070308160e1507020111062413 71
    0x14060305000c90719030000c0c0140d5842c1c1009448078011401030075041310051140d8219654160420003007140180140c0d007241c1c0011b07036074100743ea00060006000c0386d0000342003201410244180840d05a4010701007030524201940205140310151001d00030600229100c00ba49a08558050845030700c0449454134a540319204000c90f044a00c218125004104034110440d6020344c0041c402e41001f000391803000800060b0030003c0610ba01d03440d42050110866030751180f000e1282d81020300801883c191909003000c8520b2500800030030050044405101380260004d50281d2415410341c06200d054050342c8809050515642c10746c44842040c1c14842800b41c9203400d5885081204141da9a10f0000d039200c1000c002c0c03922030302d00f0090025000c240001d5041c40c060028100c0007203146080c10240c010600050300b0f00b00072070403048003403200203801411907801c03a00d003404082072100600a140740842e0742041080581c00320788401003940f1504041c581e81c00c00100e601942401c020003000c0e0011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 354740008 1250 354738758 354738767
    0x302091506070605180a051f060801180c08011a131404060507180b040b0a02190b310311030c0615180c030a0207030309080a030f110a020312071e 64
    0x81c3d91034011700000600c400c25019020411906098000c0300400c01c0c203003900b5005501d0f41e074501c0c00d155a1a504e07000464025400c2c0121501400b070906041c00d8000311b81441c0d41181000d43c0004d8070380c0c0c50020038091041c120600840c0d862022a1804559880482c0000180c110004411807140040c000c00c020000070341d01c50340c011511950340d1594908140c2c164900d51480340030784641c2d80000d1000300f0030f4082d008014803100d6850f205a0303945060703900102320b5418116100301c80d444602c2c0e04024440c84c4289d260a2409102400c248000c1303400f6000003a0303401c02e0403001e4204507002c0c440e10038103441081110000341001c0101c2e52603142902200408400e1074528900c00d030410083c2c12003081d071070590207010309072523010545543c1303e003440341c00294031046045003859120032003003002c9801c0c034000c1e0000c12065200801c0034001c0540e44403c03154514641004800144007030b1141950000503a949500303809178900841e1602d6400344d45c0480700070389048090140041c640e40c2181d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 354741258 1250 354740008 354740011
    0x7210207050a0c09050a0603021503090109020d05030c0c0a03120e0a1206021207050a0504060c0c03080f0903060603030c121b0304170c010c030c0b041401050705070c090c08010302091506070605 85
    0x40008000d02c0c0ca4031280d01041d11554031010754000c0c0762b40541707030300480c00c1802950800351a01c00010320306615408104100085441683c058201207240540c0c1d900c140318141141d40c0444902074401d0440ea2540d280c034525481c070500b00071002805891507201e4000f004003802c0d1080b000d800804182c41c0000103507010901181211180382c000c20074a90103901501d1030760201c0c1d1503017810703d414494201c410442040054981c002144030010108036443d00800d0107034000010565520200301c1810316000303014149500036070041005107103590b4085810203505480e49442d503910b0320000e45d010031100c2c510422450500000800203801e0340040b0403058084a038000341d941130010540107565500808030701801040c2107001410008420102c41603000c0e1245448036685091508005d0848408452100229000103035072803c0c8541a82c00c2c00042820380e806102d403081000b0010701c0d4101c1840001e0040c50503138045988200c036122070010744440900195142c0d03440b41425006450f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 354742508 1250 354741258 354741269
    0x908100e071202061c020d1107030f0c05031909090213080d030e1e16090b0102070b13060f021504151a0a050f040e060103050703060e0607210207050a0c 67
    0xa4081c00080d1480c04a40c2d660201d600140b42505040000144644907080310030901c1510754204080c0c051203541d0b10846600766905034006485040500c1d024081d8100300b0000070500c054080da400020304004125107031284850038003440917411440075a406060350300030103101e40c000324080c140c090724000d864089600040c11104008811002901141c14494248940e600511691900c100107104208400302020084402500b58122031209682107500580d200319100c124000456034108104401742c25076140300d9180c90303d607480244201d100340c8036000910132014031900b403550081c4403d4011501c050780c00c0380646800c2c58115800c1609840c0d072642d181c07810608800341c031100b9514160b41100039041d8990a400e1a00308002c441844885075800f40d26038001c0c1c2c030042c0050141074021841400200394160461504001b0f03038601080e4800c030b5502c450204401c641c1d1214204006460340b8151050208002c01c1c51000b0340f1402c10007a10f20310900d05c03d00100408034a0001c00c841 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 354743758 1250 354742508 354742513
    0x3060901020c01060f120f02010e06031f0b1201052407060213060507110f150406020f010e03071208040302030403121806140702060309100905060a0e070b030a09030908100e 76
    0x145c03654540b21304045940075002c491251441c0880c005102d00d590703007180a005041410441d40700b80d000030441d0f070048a25401c4815003418200000c00c2103080440942007030741c020307401c0101080700e001c608581403090750700ca0360002c01c140285110071069030080e180100b103000c1d03a5400341c3c10b02e800654004030204011104003c1f00092051003141503455896001c0ca89a4030b004071542006070203110b0301c48035076115104114100c104140c0c900180001e0501d03401501c1c50300390010340345086078000302c07001c1040d401c1000800f001030007000100010b1540da041c18842900da90600b00c0c990b00503600000c2a40301405441841c1a82001050401e0040741c12620100d035140c1c44200c88030302000d00d41260f030b807106210540062038440c0155502501d00411645100b1060600740145c80c6c5240080e186a003000d014407400d10054005c0c074003039141c5540103041c020700c0c10607201d1044c40020403e40141c1c4d5603010210405204406103801090355000311401104103520070350040406d03c80050051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 354745008 1250 354743758 354743771
    0x20f12060d020a14031006060f02070509011203080a0f0c0e092a18040c0c02120703020603040b190c020327100f0908060f0402090601020a02030c060d0b03060901020c01 74
    0x1d00d0200711600040c0c1d406420f200e003903840c2c156414070b41da0080b5019585801130344080403031529684145402002c04e640c500280052012000c1c0c00c0c03072071640019000e1201803005002c0c02000d0120540c610303603d45040296596081c1c0e4903c01440c0b105a01c0342c2443c10440b4a40f00c680e8401850012410101c0c2ca0450584509520002c0c11940c40342c04010759004208590009400402804880c041c1c103c24422003640d01300014110f50a80c80044003040200f1040070560400c0100c41c0d001d421a60001c003050f86c1035400040a40c00024001000c410600c000a2000c1403000c009260161000c03030240308036402c030503010303440760810000c00c1550015001c59480f014603c103410201c102020b042c82c848040b0120044a10490b1010b5150a1045442000444281c00c0040920400c6610308099160a2a00c100b2402c000c01410b05070445d88480010310150b6000b00c0c0307201c5405001c4034419a83c2d61034881d0340f0003404419000a505000b002c0c204119844190014443d1020205c002c0220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 354746258 1250 354745008 354745021
    0x30506040b010e0f04170702060f191b020415120c0302030d02161a0f0f0c0c06031611010e19020301050a0c0903060c050409050103080a0f05030c0d09080904020f12 72
    0x5180f03084410004640c8a44080345c0816211026006191040b80405d860318016801152081c0d10441c15000c0e0744100240760900c0074590361090700c084a071864801c940040451600d80c42d85101d50000c4e200369a03a210b0f800e40a0140c888010051015007602c100300656824009416012440168041c1c000d0241e4244d031b8520202c0c2400303500d941000201c20725802c0407155006030031107034250b00c0e542e0000c0000b021f00000382c8018004003ca840441e40e6548001e141e940d08090410540c41c0c00f41c0342c24402c3c00300c4500700103e14030b28a552843c0561b900b1403601c420300e000d4842d54112038041d00803901244618003201c14480032880c000d400911968880220b08030450780c40e0790180000880421082c00000c0302504100d110000c946009410300391580303280800c6503002c2c0c3c411542c844001070780214060b009400088112424280b4a055140805070b0110920070980c4815115688a954000704445130054075100c90020b08110344030002c0e10b00e203043c55440704000c420000b0144000425 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 354747508 1250 354746258 354746279
    0x602220b0703110307081210050a15080a09080d1d12040b03090c1011250b0f0c01020f13080304060e010503090a140601060909020702150901050d06030506040b01 71
    0x22112428486850001c0340d44048a8403c6083c00f884000c0c0410020301d00400c48070b5019101c0710703034185050b0100e4100035000f01070181c801da008901442c2150010032144601407035211481c500723402c02c0440b40c0d440200c0700c1e00820307070700724000d02c2d00c2c80120b21030409010701e50000307d59a039400701300e07800203030350800c0d969641c404500e1031070b40040200130030b20425030310710003558110006c1c00490300034081c0c900016040d240c03100c0c0310400107055800602c9184000304041d8004036840100308207988040a041c501e444807a00410802d120001400e44e0888020001c594801820724021504c41d4074080042030319038884110402c086000385008222503030003004650440e409a1111035402180350015100c5420043c031241581c003841d040e04d004504000d80d54003440ea442d2018100fa981000d201512002c0c81ea0800003c3c9481070040c500140c4541c0308041104004e8920303c5d49880c02000102d540f8422148601c121070f003021400000c0081c006a400d004030321424002c051a03807078154458 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 354748758 1250 354747508 354747577
    0x8190f0324090b130204030f020f10020c060309031b010b01140307050301050915030a0b060111070e0c03180a080a080a05150909010b061803060603070b180a120602 72
    0x1089411403030007004610050341c40705002e140c0140c010f01a00c09031080000c101d0308190301c20340c2c040b011070b29238204515201180a07071800c1c04480c0c1039170030b1421240082d500c08215845a004250010100e80440f00402c01d440500e10510868084039010000351800381852250b050301180141048980f0401d80c01c0c01c0e42d05c282c4a42d92000d045030b29100410210000c00b404044024501700171104082e207040c04425102e03401042d40030040d0500000040c1200d003401d410b102103030003211080c00140804008030780c02c040c2500c03006440b52200d80030400074603550b0071358822600ca000740703200421000711b0103082002803680b1203030702d5a80c80c024040181d9001302c403004030030003030150703c00d05524102a0154000030714000006403e480000403c40d40e6101502e002000c00282560840900e010040c00382d1103070302a03028100d001d14041502d0759601400c00e81c68032025001c41903074095101c5418007001080e128100480301d00450824030001d501140e07500c0f11100324414070360701400242c084403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 354750008 1250 354748758 354748811
    0x30c08160305060a020f070605040b04200a171c09081501061b1109100f0504090b040305071a130302010c09060915051209010b030f010e0601060c08190f03 68
    0x148000d584d1141400025440b85541e42d20328202030201030003007441d62180e188514441c0584d1503140c1000c1c1400c0015030701e9000d280000c2005262460300f00d440d9503d0392000c503500200c500c08480340c5103034821b0801503036280034481c1d81074044c0c0720116290f201e507142044500001c285c0d0403000101840d081c07851802d02440c408201c0d880c0904c08544038181020800e00d0040141c030b25000007020005424441c02e03105500c8859503010700b0b00c01d803000c4c8045880140310856042000070751a5a40d9294100c0040c4041e0501c07a011805000340310f18040c0c4480c0f030035928446038490b468000a00d0703001d401c0f0000103400541c83d1120290195004010743c00540700303180c554030032991404041d20b0382c601141e0094810494280b03d481c40c4209282c2090b80503107220800820b0707a030111003d00d45071900400080030725078142040c00685204c04103841d07054030340d6494002e01c0c0030701d5810106c04600c201c005003000c00d2140800c3d203480d01c1e4061440051042259070900c4426000040b003402d030f84421262 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 354751258 1250 354750008 354750013
    0x510020c0f0603070c121e03150501030506150304030201151d0610050d06171501060c020603060a180b03120903120d0e0a030f020c01090311091807030c08160305 71
    0x6000c807407900c42c0c00b03181d008850345800c050506090740d0b40141c5605510710800851540031001001c885442c0707501070309074070314903081028001500161f071510b07500e44140f81c18155150003107074203a240c0c0045022804800106981d50b401c0c1454001d00070500145c09a078800920344020802040b402000c4519500380078030100705855000c1003240c0502108103407001e1010410040c069000f941c000c00c001040c0f12040d050035402604200c074100540881042001010200180100d03508031a0303056026406445050f00c1c0d5070707030300301042080c4001c4e0440130390305282410340d00d4449000d400641c86484d06505644030b2030f04030380c40c42007903018080c9201d901d038000d4102c89d21100034031409051700d90001400451403100c9030049608100d8180700581c00140c3d0303203c420b00c540d901004495040b140070f2a021130750610719125810b00300556081c9038880c4252801084400340141c1c0b0ba030600305250f005032040242d9a01e0280d58491040c440ca00441c01201030392041411000c07880c00849030000003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 354752508 1250 354751258 354751279
    0x903030601110c04150f060806060a121104090213060221031302060f121f091503081b07052b08070c0f06081605040b071e0501060510020c 61
    0x541d00c03802c500e41c84039610720604030010381c0c40e6a980210488551900700400041e400c0604918008000e07400480500144000f03211450b203404c000c41e4410703880b524145034112240700400000d0943e41c040002c40400c0030401144c816510f03070040111084c000310789200d05680300d00a0f40c88001221500c001102c0580d0419205600c503001580c0c409251040c80003c040300764000b51590b00070110095045502142c40021340c1c480c03030107240c2c0200e42c81c5141e8603880708801c090300862050f4003e0392881a21000680429000596040080c3d039000070b06a0300e17104040301007046443c4081ca046450b1044801c0010207051001c078603208004c205050030102c0f02904400b44c034a03410f000d0100c8814904110b180085400803521a01800c0e02c0f04050350000d1130074000420084010700503260600e500214107001c00d4100003220115001c0440064844545081000ca0710303890340c50b00c12034200b503500c000c0e04120065011909403801200c05070170882844c0000c03170303a445880c40d4258001d0286603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 354753758 1250 354752508 354752521
    0xe01060303050a03020f0405120c03060f04050a06020708091302091003090c09020f070b1e090c010f030f0204051c0605010b07080406140d0c0c030806190e07020102090910061403090303 81
    0x400610046c805441c403207141c1030750b0750007145c40d042901e615072086030403840204040b85003c1c0b007603d4201c18600080c030a141000d845e01038031a81c0d102402403c8a9000900ea01042611001c2c1c0d0600d0f000181003035400540d842c0c90101035400098000e20a1700c0c2c00360341c8401c2d503002c0d00c10a0740b45900250000c0002d0f003801d15901c001d501441d0704240080c0140f1000300040e142c181c410340300c1d00c44075000c0700c4002c0c001620881e413000042c00500554001444c20020b59a200200d0908000c880c80d011030700c01da02056217070091107107420654102e40f0044020315034410740c24655050a1181c602007000faa81c0c0e81301041e142c00303580e000610300e4808100c10060f2611600004058040c001c0c0c0603807034000c2514000301150b4144080001195044807004141904484203130703030128040d1030402186852611400c80d07074100c0d00680100c00919000304034024400d40c180c8801d0200074180000d03038100b508030b44208505511500340060328000d8103240f0181490151b070700503c6a900210305645600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 354755008 1250 354753758 354753761
    0x90a1107020d080f0a030e0601051e13061503020c070f0803071523060a050108130308040c1d011703090f0d02041506050c010e0c010c0f0303140f06040e01060303050a03 74
    0x400b020740d14690240013100c5855041d000038104100c00c0c2d1800100700c61903010740c901f040c005a01c00d900c26034031010703203000c4c40c030349061041030108003180c1c90b00f168107503605000010300040d003011074901429a07038542d200380c05031f0041144200800881322540d0b950100701c000d0300c036280a01401a00b003132100c000025440c90000c99104854140850940d65031641900010040c54076003c0c50030501007032012a0800d0300341c22020f49402c0c40c14012600d0f0503000c20300b003c888507000900308010303c1e0015007440080c1c42400042c1c6440c1415200000e12400c1818160200380107207005001d15640f440705480001046405c0304901400800a46007000c3c20000c400a9039002640c1054445401d001e01c0e044c03100a100c0a020301e501c074591505c2040fa00c01d4215030451140402e80d07403010000c941c2c3ca03a003096280500540c01410b00d0703014445403400320050b00007401000c0200d90714100380305034440c01032960b074484c5800344c6041042c0d12407010b40c58240c40d20b610024005c580d041000540c2c1c40d00c40d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 354756258 1250 354755008 354755029
    0x6010507033006030201030513030e271006140309070605031f0b03090d110a080906070b040b01181a30070e06030a0809010810090504030806090a110702 67
    0x4801006a4108202409461102d4102e0141c0030b0300343e5440f030034421507806108081c0c0040c0c1442041005e0211036802400340100e0840d203030311810030358150101c200814521056507000300c10080180342000300400c82000a1170107082c0100c0d81c50360398010301e0b280010543e44280703214802400c14924021041d50542e20142c54407044c840f9000440c84444021031142004141d14031080307559240501401c0d040601580c40b01007042410341001070b5091002803c8201b031500000c0103035032251500000342e275500c15601c3c003c0020400700100000d2241001c1103d0480316542000200068103408401c05c540c40302c04007110b01e96881241c07122500f0b244003e402c0d00e00304462484d100b1441009510040c282e40c0700ca0800c82c0c0d203c00401d005403020747d00c00340d8104d2410347c0182107900d101c0d52400b945002e05e20b0102d04006844000035100204141124001c0200b200e0822032400d290500625007003040b108503014522601c0442d01003001d601c5a004140101c12131725041c0341d800c1e03080014880e074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 354757508 1250 354756258 354756287
    0x30a0e0d110303071202101e0c090317070210170703050402030f070f0f061e14040e0703050a0506030714010e0301060b1b070801060e040807020301090816020f090601050703 76
    0x500d4641c2090741d0700c0c100b0041101c0707030046400b221100407018000745801e04840400081500b04a40c800065000343d00f600c0c0381c1c04100c035001c0383c07030194000e0032284404154006418080703804071894503042800700401680f402550840c036110100002501d6030242494020350301c0320181d001a0703071184a98801c0390014070040c241c88141350002c801d01c0c038044641d00800504a00404100300c0c40500890200044c03009003450648030811103c0b050074038440030000e20a010300c0e90b40c1804a26140e00844015003807102c030341c41150070301c010004c1c01480204c4400080c43c1c60705011035140d141c00590841201c1d02c489480c1441c0c0307660001101c2d0012070350981c41c0c140d921a80c02140f0342d180000030307000d01030f00c00e0b280c55008040700300c40a18000700ca611416003a454080d0038002801050310341c81e4002d404c814040c1e501d45140c80400e00401003108094484e43c804602c0c0c020540d410380440e80c5081c002c07562450541c1c0c3d901e0800c00c4064050710170a01041c0200070480000e03003d01c0101c1806076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 354758758 1250 354757508 354757523
    0x20a0903140d0e0a05060708032a0a020606010c020a0b0a020f030a0c05060703061a070201020321150f0a05010c02010c0b0c04061e080c090a1a030f09030a0e0d 70
    0x595a07a280090450070101155903900407001406880e41d0200105146440c11100618075524100200d81c80d0300c20101d000d0011100040011103480001d035481451b0404c400800b00402e07880624442c007900000022401800780c000826150742c489c200a1302801d40040040c0c1100f480d124114450390300a00c0082e055000d030000c0c00e1403140b01880506100f110139240c051150020380380043c1016002041c0300213041c900038050040701004500c03030342d115820741d810079a20030807400182d10318040e5a0048020f460a080d09a141e001e1002000c1d014030301c04141042ca01c035240c000c002c1c004900310b0040350031008d01d104c200301c030f58459486034415900604044103840c0c60354440072032100f02201c0c541e10110001504101e504d60141004001800d660f00d01c100000004d40b00501002020308090440d102c081200031103669107c90b4003004202c0c030001d0300c0c07412040040c55000c03a00100c90414041c01c206001030380540b0007008481011035070390740c2c040c1d10328103a00800903030b0f03055228140c4425 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 354760008 1250 354758758 354758777
    0x6060509130203070c0c0b0a030b1c0f020105040e18010b030f030304020d0611040e0610090323010f0623011e030e0309040c0804022803061a03070f08010e06070909020a 74
    0x2401ba5450b40000d0110340400543d40c03d4030050280a40719400709aa0291125440728401d158a00700d40c503201c158010f0303000780580041d00048583d4040c0c0c0d000324001080150038030030400581d403505584841098000d010000802c4101502ea240300d034943c41150f0002c000280c014079100d41d0b1030300d085106800c0000d011000c885002e405411a400032100e0f001c00b40e0603c0003504d0500413a003039031130f01c510b01444a00e00b1070740d40040600d01002210350020491341e81d1100c0001c02e4000d407460803000102009115035811001492584041c01d00306000030748540c1d880c0c0ca500c5004190289028a08049030082c1c00324811002020340000c454954001481000701d1583c442c0100024070503d17554150f110b0429004200040182d80c0310181041300d642009000110803820318805c40313401903070010707000621011030440c4e0480034a150798140162170020601c036034019a50000d80307090a00800800700403880003543d8140550b0f000740800e074802c100700046452500240001324851601d001c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 354761258 1250 354760008 354760013
    0x606070318090207120201051f150c140703021f05040506030a0204080601060e04051608160903050106030503040e1005030a110d061e0b060304020904261201030606060509130203070c 80
    0x102d070000101216090000a41c450189509000e040c1c0c000010027041c06210500100d0703018003040c2445200c41c11002d41c0c00701c1d0803007400b5161044080d5004041c0000502000e1022a224955400100e00c600106000c0740e070140350313040709240d640344292129403403e4201420041030b5003000344160b41c415020400401c08450074855140200f030b082e200c009155960604110544074001d000d11201040030034698003142d44510ba41e60440c2644440b2081c0d456101c174215802d0f41c0721380000d0581c0d820110004100540000200300312004008c8511719920740026034442c1078007521540c0c0e4164400e0380100c02103a460b959041d420301008000c285001c1450361040207481d82a0512242c91205034254426820140a4807030105400c035003440c6140381550010342140d401902c00780c0300d1611420350fa28444580004400c0c82c1110036041170f201e10300184030714403640e0300b40003c4840d035003003840000342a401a815102e0220740141084121204609014000e4100401070001c110359280103502 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 354762508 1250 354761258 354761261
    0x1501030914030a0f03180512031008061e0601090305150c0715061707030201021209060f040314070e06090a050408220305190215090310020309010e011103060607031809 74
    0x50550407a04d64044104001070302404840c11203c10080c440d507a884260006031002c52141031030070340d84610680ba51100c40c1c128100c5100c0e80c000c00c40b144905424000004881090010703100324150701720301c0c1030766203000455440301280300050607a4007011404407442d0743c0000040e808900c8040503400c2580617120301c0842c0700c1d48000c85131000d54420040c480c00d169603101903118580d42c4000c0c0107140c83c40d80002d540b154003e600c51007020000c14446441c0c0d840300200d0b01c00144404c1d81c00d44403030b00d03420811001040e83c1580100d03032240d68000240f1044600005c3d100700d500030454000c594440c6c481d070028040003802291121010003007581458103800b4024041ca19001a441d0300324158908030b46050056582c20500c0c40c0b031245900c0040c0e03a420080c120440e480000c0360341300c07241140401d02d4100b80c54501d03040c480c004020031000300e0056200a48040c83c0e1002031000c03000c40440303480d6a204c15103403da0041030400245000c039028140c4254084d0090b5075000815944081580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 354763758 1250 354762508 354762517
    0x1c0b040f02180907030501140628020321071b02031c02070503010e06060a0302010f09080703030e09060a0315200a0206041b0f210212010b1206150103091403 69
    0x102d038015015010321031814261070160344107507141070420040d410400d505010344c5c410084248102c0d40011112070b9008945140041c0e034640c108481c885081544019403a500a00300b0860001021046141186c030b4965480380107180c0341d10395840000c0f0410f0741106462040f2020303a0944030307020349a044e0080d02480803000010a130701070070450307040400b0503003914880c0c20b0742e1001e41d0040040c000366590301c10216080380c2d82400c12401500001d04140c0d41180282d000c0c107010b01034030354000141908102640d4003650b048030442041d985000411064600c0c03804060010b851154070240c01d00c019501410741c0120075003504c41c031205003128440743c03940000610760041c0c209205200c100420f0039003c007e606e011030740881c0c4890038209010291035036480b56265142d0307018001c154a102e485d000070f14070741c0c0103444000314288052040740603005a1000034050f24558668a40c921000300700786000301d81c10070801103e0481d407401140035000406043c3c0d2448098280c04580010810040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 354765008 1250 354763758 354763777
    0x240f280e1e091018060e011401021005090c040f0507080604051305060112030e03060c0a080a060e1611030a05090d171c5702160b1c0b040f02 62
    0xb00340942002c042e13803849040c0c0044002c0c2c650500005010340c400d0301c60b00c40d0568450f182d20041815030400101d140201455100b09418940414450302401c04940c2d01040302090310309003d4400300d0340000c1e049032801c0b01c88400181c9040040b0304246000d8200b660021803102c040100705510783c813190300f84482a4482001500d48201c59410541c00c5290110301000840140203e841c09913050040ca219109201c000c1010000000e035801c4c41da5400040640030544404d0050b10740001030f10f4194005000380c00121320340c0255000ea0305000003c8524011342a5102d0381000c00d07600c103006503545103100898454501e40e181c07864803c45903010b0203140c8144070406854a840700200d804031040c2908030079200074002d60510100140041c0c00200442c2c201c01d07104000f4104044423103580e1900800c2002042d540f00d481e42440d030010359a50008610a40419400ea6510200d0b40303a12501c0d0384101880b4403490414040ca540360f00c05d46807140081e002003074400c402c004c40400c99021503401d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 354766258 1250 354765008 354765031
    0x1e05030a06080c01080408070203010213030b07120c09140a050411041401140f03040c1a1201050607030c0311150103060204032001020705240f280e1e09 67
    0x4000c80580c20703000c0c580c010320018015110a00c0c000000a0620f0b00051004d40510000200c110454909504441640a00c01000003420b900c2c0d01c0c2c4030a03284400e85410b03000035100000311a906507644280034081d1840e880f040b4210346030607204070f984071255900c5944a4a420800101600d546c060640c00d03400c80080b080d40c4904011140f200f8213150704003c1d040100041e0008070707500190084590042d5488000c03038407179607140b915101070000c1c3d800084400441500240016540001070580161341091959080e0b88610500156009600c005000034401030030f490013080c01800030011910a850940700d604900d10603d42c183c050a070310032606e2580c0041c2c2007060000c2ca010029200c104004009501815903000030764894a034010144110709940b0054100d130440090f4507801078104406546480900007000900e4102900c0e181c07083c0c202d0030340e00c1201c0d42a07200003416203103107850303842c25202424244010b621054001303000c0c02d1054490840595101610706e44654643c400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 354767508 1250 354766258 354766261
    0x2503080301120c060801030302030a140730080c0a111006141002030307080a05060402040512100b060f120a020f070b0a0c0e0307033027080c101e0503 66
    0x905209038510f651202d02081115001480001d07400f01c1103a2035a1079915069014003005005a41a0b07c2040c20042c054603542c014148a000b03880814001d1007480724110764514503845096600d40411207403001c0c01d100400020042c980a83c0407010b0800081c0200c03210b518030610300c032048075442c0d00a0881c4182c6085d891141d4504104010301543c4d0354400f640c194202000050000c01000d491005217a48980c002061303512164166030050800802036801c1c080301c851019290781d501c07800ca1445da4202842005181031440444881c02c3d40b040c102031400094400131003101c1c8001c0d00000e04c4030340030443e11842d0707110b4502400f10fa40c0162050039041c180310502d8000c8800c1e0703090000c00d200c1c0d915420070f415a004035044048030340141d044030400a480e01890208090162124590064000b0b201c003c0ca80c082c0141c05695500550324141d141c0340d8200f9502d0b180b0611036020141c0c01414200301d5810030703160501005203142401c0400303211400c910984400c103031190500244001c070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 354768758 1250 354767508 354767513
    0x1d1203090601140f010e060f0a050919050919090210120c020615150904020c0a110d121b0203030315010801050f03060f0709052e090602250308030112 66
    0x20030b0040c06030740329461007a8054800b140c68400c00940d51030500103c0d02c042c0055845000c115154520044c40c611b0b074030803610708098082e8100c058054014800d1051100d000b000d194100803d5507401441c0e400d0302c2da00e0500950303075500c0840748000d070030b6160303210040181c584001640300c450498481d0b060f0001000c09060413500c45d50380707000031540041c080c03100d101000121606a088290ba038400042041c40070241e5520440c0d1985030864400207901000740d20209160210038816407030113800b040e49404100b6400c01e402c4e009406000d981351281082c500450302c00c444250002118446462550006415500102d840005002e02c40012045540c0d024510710302500d8200d4101d010340c4610008241c0c3d80340010081034079480b805000c501030034003c155100007044000d2024581211031000a41202d6079004112000d114117540c04c5201405118014140c500542c0104440c03086084a01d01c0300034006807040000d000300c0c1c0c01001045004000318042d01354000301120562071131 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 354770008 1250 354768758 354768763
    0x503070f020601030b160e0619020714090f15100207050114120a0e100c020705100c020d0b06040f02160c0803070809010e13050a060f1d01091d120309 66
    0x44440c1021500203200500004001c00c1406070020301c090b8a800c0d1058010320b00740d0f02003e8000b8691340c020000701d00355a4103d03803580307042d03c0e401d182d41c20b5414480d510f4281d030071040b001902407640060910000b4500c0d40025103c1940441903010f51811080c061000c2038008920f1600c0500680040c0018406560407a010042c1b040481c0718903464002d490b0300711403004d24081c0c4080d0312151100c2e101c0e02c40300742c1008200c0221000560401c10321139140f10280d9503040d075200b814041c001c900300958155000341c10441901d03030013605101603180155200f103005000102100c0e840380d6600f0f40b10403003050501c05040e000514800300ca07000030b940c1c141a20031000c290310064090703100f0803c02002545240a442d641c110a007021542080910001643d0b5404000035062052030b103020000645d549421490441d226580310103552078035492440d80d0200300c4c460040843d103820340104000303020f47e8820003164030003040542c40c1e84114092241071801642d40003101e4000031040c41040c807000e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 354771258 1250 354770008 354770027
    0x30f060a06020316060b030a080307020105040b070c03020c01080c0409020705030d0b0d0f030c03020309150d0c1b1104090503030412021b102d0f11010204030f0212120703050307 78
    0xd5000450805041c0015400c0c13405241500400c001d8032946001016142003110208003503100c8000c5480b031403c101c0090003041d00f200d05491540144000c5183c61f8004d946004c220f41e0583d016181608290005450450025111541941c0204000203040e00e0600c081c12100340304002542d03449e01d40c810380328141d0b4808000580b181c15914210b6001545010810401c01c0d1305003415558800340381810390560207856802504081910100c01381a00403200805095800b4002003107140d0940208a5414890030842030541d401c49801d00007051020030b8460081d0310080000c18807030f10550f40e0b03038116007050341d08544411614044040d46d58051049404020741e04210640d88000200001c0001920308000300034402011444110103600340b00c0003209448802d082080c0807003401008040c3c0001c0311004001075421040c0c21200901802100d045a03045080301035002e902c0d400b081040c050040a0003041d100c3e04009840c40308508024052490198a806499107000310380a00712020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 354772508 1250 354771258 354771269
    0x5010c0b0702160b0a0210111204060608030a170708010b0406030e01090602070605221e230c12060910020f0c0d020105180f10240e070207061e180b030f060a 69
    0x3424050501c846e40c0f80e003541c0b1510511209c42132181c03030720f082a10052045401108050200281090303900b03800041c2003009540c00156401e4a598040d41150350305428003500d441c44100704402c0010303521030780020f5418280c0c030000245803210356544800300c0e80462001c450140e101c41c100810084090b03c0038141034484040c856030300701c40c0e0f6140c00d40110a030f80c1d40e004030030030f1003609810f104440d155452902401000d02e0840403460029980d56507500301c5003481070380b01102c144201240441c07a03900403c1524000c0c04d5030122600b814019411110100991440510000d515900704003c080106940764000280d1410001410f40840c8000e45d908c213840d620082055130200e10028101e1600024980c0c00078100c3c403882c042c81c1e030300c0c0e012900c209900b10304040046800c400303c140c800d0041201e9001c039210b55039a80390a403158000c04088046e8140c2d109030044007580035120300000d0030482141c51140684860751031040d81c00550740c11500c903205108002c020304146401f00082c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 354773758 1250 354772508 354772511
    0x60e0f030406050f031504090f11030c0d111903060608010b060708030f0c09030304170105180604030c0206040f09021b010236040e0a03021605010c0b0702160b0a0210 73
    0x900b0144042d061340b00b040211040000004001011240c43e50201102c0c805c00510a100500042c101094801082e100941e1006003450418100b4a000101c5550015018000307045100705515046841c400c540c45040e00076089200c000511003241c10003001544c030400d00014140d00b014030042c01c542c1c040ca02c645c0110810010780010809400582e9441141d841482c4c0c8ea543c0c030304500c04041e004d0004038036014071011a02184428031041154142d808807802004140d0f0b5844805515407054500480182c2218022a0209110785810000383c0c1c00034040a2925588030135a04640714640d100844403680072500f11951604801602d4003103421000139801c0445030307005400310318401124450098010741c10034140c0091b40e00a8916880b004000700402ca48006a90b919520380314001c030014040c2c041c1c1410405100e0541600b5140e060b5100b20282509a0f181c1d0289040540988294403d264000c0103545101c9100030140c04200c1aa1351106400c220103413411041403c4542020b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 354775008 1250 354773758 354773767
    0xf0917011b0804060c0807080a05150a0b0a030b0a030206071707080301060f230a0309050a0209040c050112020f0301090f02070606080708100b0303030a11040305030403230105090c1905030307060e0f03 88
    0x40d0f00440f05d5400140889e00040c00c3c0c0c4a9250146501c0201d01b641600001c0413640000c80c21588806014090f2264806200c03284c0180c040041041c0e56000095200005000e2103000ca40500280502d1203a0100e83d245000c50503121a4281d401c264440000103803100320890409912103542c0034000241405106419420841c03c499406191a11000c15580e0043c44090007010000908904e801805e000e40905103030500d941d841c107080c0112400701e01d10000c54642d032a414803c85411200d01040c650031341c1d013800103080103010301c1c3c0200240580c0920032040801c171680b082d18000e0800c072004000c2907180290706070910201117044203001e4903003804d1114030b49000c13080700d910174240300000500a6031400b03600303518021500064814400480c000c410043d01c00c21045000d815042040d0028003680d00c20740c00d0f11021902c40010741c10102c7c0c12001810400d04a02c88074a12000b00d0a1042c0c840d80801e14541240070187c0d0b14030b40342d0f1040c07141d2400034021101c00c000d02001540ca030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 354776258 1250 354775008 354775021
    0xf0c0803120103030305071202070c15020a08030a11071e0b0a02090d11120609031315021b0a05060706090c051203070b070e040509031305010f0917011b0804060c08 72
    0x201d000510010301455101c0700001d092030300c81d600c1c00d0603c0000d180115220403040c2000a070310703141da02a0002114603000041b55041c000100303e21050342c0410304074950381d64506107202404a031003036500000818000030300025884841500f03240e00402980000b8050303420311844900015000b0321045104116002c1140c45201d4003981140d040241800340f2090342c0c000c5101034980c1d0305007106500484083c807010b600080010b01c183c2c0b90f036980110a440d25050300d90407600d01c603040c110251340403c04ca20008500840d503403a058600425100081c4d5440c00440c0340d9602c0520101c4d002c42e912010441000002c143c101c0141c2010303111181049203108010b40c0d2841208005002c2c126088001943d052040f110000302c1d103c0070f401031080c0d003020b10710a552a0010031450700050f800001c040f030075502c610500701d1381800da40c2c1c1c3e81c1e4502d0719044030342d00b410f460720322640d01135502d80c40301d60130f080c90303c079913601921040b50340c2c2a6080c0b40030300303016013100d0011040908000c039036014800b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 354777508 1250 354776258 354776287
    0x20c071809020109051e0409140304171002031501210f02121e06090a0e1c08150a12020a1a13060807051803150f070f0206010302060a0e0604120f0c0803 67
    0x801d001071f10005031404090603d071036012002c668140303141c44002004030711519114804120742c0081d508031904d07400e48240c3d01e000da00045540d4402001789850b400100d41c030804803a200050366006540708120b45411a500782e03485030517240386150300007070311800c00c42a081400d40e10941c0701308107401141e91090015a40314002c0e040c0c0e03115001c80c01c0803e18a804582c040c401984e00740084801d0f100d112000e042201d804080c05c00301290440001a140c0d074050120725074407110007088030784118140703402c8540e050320b03d140980e080006080c000c500060360941c144e000c04128100c55848a820503811540340f64950001020080080248a17156070030800780ca10380c0e41d42c802c603003c04401a001007840c1c09400c005030006c4605070400d102c261008800301d140951240c0d510603041110929040e642c0c1d41d03081c40001d40000080120207000d511411070306100481c010034a43c40c00355a200783c00c050a0480c0d00c00d0f24048181c564810801030140c0702d0074000c201c000b0165042c801c02500500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 354778758 1250 354777508 354777559
    0x803030c0a1b030905041a030606130e01110d0c0f09140d051c02061005030307060e0c030d030b03010507030612111f0512011a0706020c07180902010905 67
    0x8840502151581c501405240c0340708600c034541c01000da1844107400d004211340c00e40c1c410035000740e1a140918a2040e280241d04081c40009001890315403a80030074031070b480301d0a8100d205080d9a41b9003088081401703000b0710148404405100c1e4a891050314890121000100401c050220040d4120398943e0456200000c840e40310903c2d068604000c004120b07403105a1070010300602544c05c046001034003000100d21419103a600f115469600d10000c0303040ca68030303070180c182c0c03540c410701444e80005c21580002030000020800e503206a09414040703840c1c5000c00044c10003190b258039601c4030074242441001e5100443d80b6040c041c2c0d500d011788070b040d1543c07442000382c41d000808402901549559402c0048000368507412510030543d4400200b103074020160044030440036000001e4002e07000d24000305406202d0903041d1414003140d80345c030001c1d0320803182d4140728001c81c54000b40040382c0813000703040d411400c03101041d00390b914400100707266815004103115584e41c4200c00908086c450320724 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 354780008 1250 354778758 354778771
    0x180702060112050a081c06081902060c07031e0b090c15130e0717250507030309080f0c160807060f0306030c030f02130b032802040920010504080303 65
    0x481041260341801410026500005045481c0018103401e0fa03840f8031042d40d12100004204007d49520b8100d02c80e2071f00380e40907090301c1e0491081d0000025180102c0208400c4d50319000f100d60090b540c0c3e0b44c2070090028000000b0441c407800c6072000c2484100c1700c10300d9000e0860000751500001d04000900f000201104001f44c600c000f01d441d042c80000c4464500140261458030001842c00701e600038101095140800310040c090780120348002c01a04a041003e50140d1a401402030386410440707060300580015801c043d102c08070000803540302c030028041d4031280c8546550399400e10044034079040c0410305102c0203500d0f80310204020400420240144c5102d07107448183c150181c50b084002e003047d60405010390b0620180042044400c5480c0c40c4458802d4a070348005844d100c0303058040301c085051440e0150045805806030000799242c400421090392a001450300300b603000305003200c45d49082104e04451010039a44444101c07000100031010902c1c02d40d262a08081e21941c880c00045c025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 354781258 1250 354780008 354780029
    0x11209050f06180d0c030c0b09060108010f09080417030f030109090b011202030c0105180a0b07030216030314030403051207030c0e10122d06060822030e0f18061807020601 75
    0x117420144154408082185c220841d0001c1d401c0595420352101805e00c900311141d1b2909100c2d0022038828054034001c5500414200d003018036010019a103039000c281d098015000402c01200c00d00900c1f4065030180000c2c03200040c9041c018581b00821402c10b0300110a0311442040c07240060380d0005184013140c0c02841c185496080310044007048451501042d0350104444a0100300315807050060030440d03001e54200c94403003440c40340c0d400101c051400040c0000d8000d60350307469100c0c0864000d540080c03003854070740e1422030202d12250607070200313852040021307860350b9201042540c08610407690300002c0f00c00070103849a22002a08146040740c20646654407400c2075003256001d150880202900c4060f1600c503041c196070280003e0441340103400101c1c140030017049161b01031707100c1810385034248040090b0030389454405880000030021050b60042d4a0085110707152160b140382018050300e103a040707040741003800401011044040e034071645030100c0e0081100c4990300060342d60445514644 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 354782508 1250 354781258 354781277
    0x280213060b0d0b0a1a0903010c0905060a140f0301060503060a060e060702040906060b07050304060f1e230f0409050a02030f040b10080a030e1315090b011209050f06180d 74
    0x22a110b50300c603511048900485017114290b115801d40100843c1d00c00301e000700254115009c00b0f94000b001030160a400039800e000010302c20f4080d8070181010074084080e00d0801c9003d2440c10104d40c0309801200000300d001c420f014030f900b0100810400341105042c0002524080008a045406980c0000e40b24a446071003480c10f11100740e0100010f4040b20014903030740d10007410207c1d52544584541d1700002c1d450160031400d0391148106011621100082c84003128a07000200c81e042e01c40f03d0000f03500c0d850900d0203082c0d02410002000a581e484c00317003a4a55140610440c100c2d072000b0b102c2c0c50b0060040003000300c1c00100c48045544507a22402c106c241d42c4a055050b1450798154000c800c00348a030301d0155091503000021911013090440e058152544050242c02c00d07601d0611864264140514041c02041055000103004c2c43c01858200c1004c440795610005440c20361100f668550850241040413079014400c0550042840481c080c002c0c920000a5036601c001c45054010007800e940e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 354783758 1250 354782508 354782531
    0x3120603150b06070b01080c01080708090316050115080c01020c03210a09031208160c0201020706031e140a05070914040921090f060c0302030306060309280213060b0d 73
    0x1421380f400c458000b04950400e43c0c54070161656480c0b40038181d80801c0c2408002030b803040c410321201d4440c02e0b41c030020b18106a504010412522003440c0c2c120f429540321007038208008032220b03440780180907080007480c43c2d44081c40060300b8540500d400901070741090700c40110701e03a00030301d80c1c1c00540096448075907500005030341103c4c00e18180c0c000411354010b500d11100390036488412280200301d000040202c1e03030001c0c181641c241400000080c0582c104540030410310b03010b03038840c89002003403004003241d10240d0303450b210840340b00307402c110000c09801e03080c400000090712038983c0c041e00d5802d0400410341800900c1c0c00d02415442c0040c446c9485001d000204041c4000b0010700c4681040e038030141e943c101030050704031800c0f4080c2c0c20000d2aa510000f44043c450b0140b000301c3c0c0d4051b0040d51030360700d411007032080c5580000c000c1c00e075034801c80790400b00380811240c0c40d0580d0480008064961940d80c41009214070640126960490600788280f2220306007604503015403410074800242d10a466 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 354785008 1250 354783758 354783769
    0x40f030206090a03050a080405130615081807090906050106020102031e040213020d020c0f0105480d0507020a1a1302060a050406030e0a031b0507080304090903120603150b 75
    0x282c10040060040d846d800040185580160060b99002ca5610101c800c400d1414811034090384070f0181100c044000e8100c5042c09120399a41050a4001001402c202034041030718008140e4040c2190fa0744e00c0005500748603283c45000d000d40f010303100a61450400754210301e250a0f00d91194090590448081401c658515100c4400405c05000541d2500504840b010007504007800710500c500880b055021100700c1842103500c203244001020b0404641103c414507000c080145006a1207a25145203003c0c403000000310f400e03c940b04052540d81d00c6c0c03141c15801503960140c0081c041d0b512680c0f081000840848900385140d10f103041d1000c2a903581480d4006010108130007a4012200003400c3c2c1071903a00c0002841558000c0d201030140f00c3c45527601c26038401c946500900040e6410310329000d0701011130051440c950086088421007905c2d502e106040d81c5c045e0340086030503682d445c0d4800c105500040e4400e031020f40f21000700030452540e12a0310f040940f213410596034550781d640c00401507459 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 354786258 1250 354785008 354785029
    0x60115110a12020d09030201120216021201290a0605162001090f03080703050306030a0b01080105071b050606010f021005010e0103141b15040518060411040f03020609 73
    0x1500310703416211035080c40c5440e5851510000c006000301d01403109100d02440d5183c04495043e51205049401081c401000350010509039090384a040303411005a07440c4114040c406500da00000b4250005000700340d18105640510040c0400f1441d9140c440d0365150380c14011034400e0b007403455035103028021942c00c08030103410003803031802c501200c044040300c0c0302c0d4602c02000080e200c06000c5500c46c0301090141a0170310006102802c2000820b001910034030185400c01b10207030450741d100007a65103000c4003038401d0300100035a80d0f455042203070040d4819081d1000c2d0300481510344402c2c031107840e982d4880c00000d19640c14414894410040c4510030041421003c0e200a0100015616516113801d020801e10003503030494900d44848801e01c4007c6001a282400205521400c4d0880014080740105410003000311b600240800030700e9031540f05506100d407010400c040610300e4420204801c0303401c40e648005410301c1c01d02c814807071000400c40c03002c103407030301116103035190340142c000106900c4a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 354787508 1250 354786258 354786287
    0x12060b0d140607080108160b22080f010507030203151e1e100924120507260702070b0304050321090d03020a05041e09230a060602060115 60
    0x1075400d500250301d00c00700b001c0740502015961204d050741e8600c48943d583d05c1c0243d5056000c8802c00c0c04200001041005182c4d08003200700c0c10f044060141c01e0500e10401075441680250444000f85c56032170420b2003200d920681500f411400d60400e4003060070030f00464000b0300c1c05002081d6a81c13450b40d007054240b815124000700f401c14581c600e0064a0305085c1082641c900070b03c011007803101c00394080c1c8140c0080e21803038a4440d40d01088a0041d400560107508548280292090545480707500d41c000e25219080686400b0a49030703840046c0201002c0c40700c0303c403030781da0000c1d010700180940c017040700780031141491100c540f82c1d00c8500b405800c510807c5503d1a01000e9540a0300310000c0000806101e041076000741c80465401c100e00f582a4840d04900000044042200f48611007440701d0000031000100c0310024455100c66455040740d08682801210000000c0e20103103000111803500d030300041148082c0680c81c0340c08000703960303000c1c18060040030100d0342110040c490b2017510542004d61 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 354788758 1250 354787508 354787523
    0x120703090b0c070302010e3004180207030221041404020f04030501060303110607090e040302030c0a06020d06170c010f170f0f0121122709140112060b0d 67
    0x1080b20000600da4844101100554241034440c140301d0004641c00c3e515a002c0b07280300103004444100601d010210221440039441b050201044400c482d185500c13a540096070010ba442c01e0714100a440c095500750207521800688101440380105041581c0c03c41d41f80c40000310300d01e0785400000b0f010340602d07040300e460701d0408034002003480015000101202e009441d040c0c181c510343c460441c3c0700d580031100000480e08000c020801644402440390b800b50082c41a05e0070580700c000e1181c1081d0b030440303040d28080e4021034503030340060031842104020165a0300c0c50343c000744022130440e00c9190b6100040d0500030041a11001c81c0c0c041ca200c04e59000c0002c0107405689000e040c0c011524005480d841c5040c2ca081c1d002050081824044a81c440d50000209501c05042d5503425980700591301e00000700609602c480150003201081d00711803030000b400705c40000d0b0400401c5c0044900b07107182070f0b14004425004009d07145040d03e41e03a80c901c2c0c00070008660b00b58100f000c03c041004140c4002c0111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 354790008 1250 354788758 354788761
    0x33020c10090320120307030801050d1505240a1a070309030803010608070e2b05030d18112704110a081507080106270806090703030e04020f120703090b 66
    0x9080d81d2100300559201200c4e5605040b0010680913564054031500401103070000700103120626050b803c0c1c425251190507000c2c004514140700000392442550400440200b4090038020211800b0f8140c0d5041e1083e26400c009521340046100303d03e124202851314002d00264900078103110704100b03409581c02444840ea2940c0d544401003252104550780000520103901c8280c603441c0001c1c00700d050b14544180b01614401940c00844170214030300d0115894402003040c554560030034092000f406400e01d552180d418418200440108415040940704d540c5c4400107515621415007070130303c00c01c42034070503044a640f10301c1c00925616551000e1070380182025400034188400050105146c0c1440f04c15082e940c0740c081d01a254841d0a0144034046071350680e2101d00d4800001c442e141248184401c502801d81c0d502c03407141461829182030303e15401804040c000d0540009181004110070340301149050600c2007850541d009041548400b5a41c240214401d00d1084e0080c410842c5c06c2400200503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 354791258 1250 354790008 354790043
    0x5030607090b1803070308030406051b0405011209120309021305090712030504081609140c16051c020307021009080307060c020f060a02041806050f120a0b0133020c100903 75
    0x8507041103270100c60540c00c141c0011901d0301415403142d4000e0700c81c243c06040c141064015100004541f0b11030940780e03500c200c14400b0511404201e196003003c0c7c4c400040c100c40e01c0c01400b000030400c041103001c00b410030080c0910031400141c43d00448180d0136410241d02420714044926100e19840241644142c4c00014201500d141c1030004961035201d003000b078107036903046585141c00210303050b040114040c04203194090350f226400241502c11000e41e2201030200c10801840300c8000c0062005074004122903045090110001c4440450350400241551405242654a1240e00f5000b044591500040b01c0014003c210300c00c003080340e9600380c9070380e4075001c3c0c07140d0001c1d000b0744070310082c16821001642d20880d0a01c1170009580015000c4040e2266510500440d442810090900d030311800400790041050306161901030035460420b034480d543c414402a448058181e0044107144404900f01005900000c4030400c3c00ca05940c801602102e9480654041e2081d50000c0c0600002102d180c44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 354792508 1250 354791258 354791273
    0x6010f051c050f090a0308040b1503120c010b010216050d0213020c010f150506040905040f08040e0f0f2502010b041509050106091809060b042405030607090b18030703 73
    0x403451182400c14030310351301c0e54007242e41c48800d000c0140c0492002c1c1c02140c00303e403084029580c0501403541e40034690b6140c402103860402291444070b83c44001003403a9040036401c0c003403401446424802410149a0704440c00640155441424419540d0003400c00454a40f1000d14106203078003d0119100e80602e06183e010b40014409800280d1800850241040034076a6502c140c4030b01420180c201030031300c074828004250103081900c1883d99508020001210003004001034484110740209a08040101444012015203401c8103a81031208001c180c41c0440212880c010900c802456290301e085001c1c0d0040c003440c3c001940103800d192016240d5003404510030110380c1d06070010041c5a0307854208031141291401011040c00200501854076015a000711419501a8200140b5226800e0001e8100e803118501003412543c0c0b4503c04107a8001112101d00501064014180034a00244005c0c4030101601608205503008a1010655844007a640609500203012200368507104d040000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 354793758 1250 354792508 354792511
    0x10906061403210f090307030b0106050a0801080a080708070c05090106021e030a140a0e040c09090c08091207030c050604051608030c0c010f020307020a030602130503120306010f051c05 81
    0x28001c0c455442c440700c07600791003002c44001c40f10400c40d80c3e083c40803002c0c02100c40d43c40204001d9141c40b6180011010a8600302d515000342180c0d120301e031780ca5000a001503c6088140d01c044030300d400454010002c030300178204a400090b446179007260360b46040d1420f0b4400720502e402c500d411110a400100303d00344c0009501d002d50000516280c29440000ca440781d0ba0320a10107820700250300401c001e00120134581c0036044503074007414180841000d910200d01101c02000d0100001900403a040003c1c4c0d00c144181408441540340406261910241c540d035284414040c200b032210300003501c4401d2502c40d1014000d140e17800002c2d41c001c0e08160904c65682e00e900c40d504800d0f40c0c0f410030001000c0e4800022520b89803a18000390484204c3c950040d601d0060102d100030550108110303c400603a901807040020307503c030b2100161038009030126020202059000580641d0007400c5107030b5541c032620150b07a130004091a00c000110394603032048606014034180c400030030050405140420312180c0065 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 354795008 1250 354793758 354793799
    0x2010f0e030c0706050c120a03020a0e0906010f051605010905031801020601060f031a04090f03020607050a1d0a1205060403021b06120601050f0a031505090402180901090606 76
    0x1802600c203154280303a12031059404000390350380700807020001d460240001d4003144000105841c80300c04a181480341076882910383c80c00295000035101e08554124005141001e0103445144582c5007640001e01150007140d1200c00744840460f03400d43c0d8203142d410400c80c00307a110000303000d0000c2c01c0c500103a0301d030000c8640b11942d890700c2c49c142031f05510001ea96812200301c2c1d82c440075048090304041e4001c020001840d02216203800726041192258094220150b104241d00680d400250400038101030010b0054000c01c5420040e806603103a1002c07010b03108400056030b5003510881000003500a6030765a10200300c0c7c0700d5030600d2200344807002ca2198032403402502030f2140500d1020307401079114084020319601c25014448071203008609111603600c1401810010b2400c00164403403552604500c00320340010341c0321501c0c25220503102e4032050081000f40e07032441507402c05030700080c054162100308034400c0c404100080d10280c2c003500f0013003010350490702c00c01c58240c0320004840c400206043c0e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 354796258 1250 354795008 354795011
    0x9020f07140a0506071d090f25021f020c160312020105040b0a0c03150f081005280216210c110d03020a0227100518190501030302010f 59
    0x1c0c4400d8050100310b401d0081e92000140207295580441644c4415941050304510440307280050f180703490f10041c05001d007410200a82041c617020035580c01c161200f0f0070100000d041d00000020040c1c0016001207081c4150754104180e6102817088030003401401c0d80300300300780319041031011260341070401c20082d2805005580d07031340c8161381c2d001d07170a17140c080d50020004550040002c00450040e402a44218594580414540c0ca038a00c8070110840e90b801500c5402030030003082000040412103809085ca01030b9042c00340303140c54044000720640d8403640c1e445058440d40ca07640780c0e801c40c0c1d048445c3d801081800c500510300c14100141c0000c18603940c01030007001d0401035460180a02c213451940e6a000e040c140301c05c8044d80600401035841d240880070351280e18140c20040e074481c013a80c5c0c050000c01c0420b403500714900300303d003100000c09407001500130f4011201780903c1e10350344c00b5285822030400c03034404a42c07525001600301180c030040045169142c00c001000f01036043d04038182070402d1400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 354797508 1250 354796258 354796283
    0x1434030903170105090a0b130c030e070603091a04210e090717010b160215130b0f030c0f0408011d0c041103010e07050702030d21090321020409020f07 66
    0x1c160304900001e000d0917a201d410540020402d501e1508492a400b034050b0055034000d03040c46000307065034200384140e008243c0395801c03600c80d403204115540040c2a40d03d0b0a01043c44aa202c811825407405841d2000310501070014003801180c10740c00030f060700020050340300c040340c02c2d038020b103060720048900c2d1040c130380e25011840c854400c1000d03000c000012119151145d00e086100c0250b0351000c441e010030800000700744005a074400e405849100c11280b401c07690b50a0406582800c0b031030941180101c0102885043c1180c4494010307203034040d6846d82000d0b0f85001c000c0d4030b81c0c05405a0740c040c0501f5800c0c00d0001c00c0c110720403240700c0459a20038044410159181d03007040113403562030350010480ea40600c01002174407150807426800482c6400e08514105150700424245955400501c000c036003940341d03040c001c9001881e08810304001001c2000078803540c1e41d0080c2002c2000b03400801c0f100f6440200d013403820720741d4115402050a00e00c215599030041c00480080c0d0450030041c1c0c0c500c2c4403460f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 354798758 1250 354797508 354797537
    0x20306040f03021b010e0f280801140f16021504050f060109050c0703050d0204091407020d0503070503040b040507090614010e031603030c0f0206030a021206041434030903 75
    0x100781c0c1c0340340016150a49108408410300c1804c22803e2403460780701c42e5160314000c0c1080340c0c103c010744841c59640442d0308d15081044060a50700d45082d40f150007041d90701004a2000c81903d090303000520703110281141c0d11000400ca15040d0950903100350300c81f0490511040040000b0300e07000d45030741c050030380f01c1503a40d642a00080319000c80e00b200c490385041007981d00282c450001402c1e03c0065200c01802e06803211340d03440442e40080c2181002000700001d1200c060380400941c071038020107181080c914a081c0500600e507001c040c000a01c101e04400102e410810240504009030183c00700400c540c1e503480c0b6101803070700011088140030812040010049050108d1049190455a03c052039854030b50380c2d084410003050841580c00b00d415040302001a5201c00045d0b0180c24800d02c01750301c1d00c981d014100802d5002a1640e8072481c0303031441c0074083c0503512105a0707000c04000050841c20149981e030b0101070a99807001c1c0383c0301008070b5842e940c0da03416074820005a40603903a41d551100c1041d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 354800008 1250 354798758 354798793
    0x6120405030c0102121801110904020d020c070311090109050103021f0c12030522050a121e0801052e11100513050606030303010803040e070311180103231302010507020306040f0302 79
    0x11392307503a000c94000708552009400d142e00202605900c024006181c0321251081e1030514825400031144d0003208030a44000d4a00300c0740b054050728210008009551542e80001e40050503490601c2740e9000e01c0554510b40c0b4062426400c1c0503030490440301c02111403040060003040b007115451080500036640415222005403c0130149521000174164601c903622400c070010340304000e05080084120040700d080003500d0b15034500c0c0c51592100783d0b01e941004100000d40052607254407241400080d18003410250b0110030f4010401800d014644040b005a880e040c003e8680c0d894001508100c02d00c2040b1280d0714004403000c1c0541e043c1c807095200d010805460388402e200b455000d91007030000f4408045008404c503000403507070600207100386408480c51941d030402c02c080c07243c40c0ba00c0d801c0405596054001c402416100081540d0314110309400c0c2200b59034040c000200d00142007803060f0859000d0303402c0714003454000f0101d401c03500d86031400c0f50b80080303140b00880050040020801501d008c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 354801258 1250 354800008 354800021
    0xf0903080a0b0d050a0606150c0807030305060a120804090c0507151503060504032102040609060813050f06090c090403090b0313151d0c06120405030c0102121801 71
    0x19a904842515030240101c09400c20650165005040440c24030002e402080b220010302d10814010403071616040d80401860124181d071410f01590401c110002050f8070300310b618441d41400c0014403602c66402107009003e1980064480600100c1e840c0f0074011818045d000b1500110700500c40441c0c920000c485600a9140c028802a8a030302c5010640d50b294202c007800041e16045050340320341c2c0c1d4450300181e41007554183c1c0440c04000d04c044401002c0e580e2080d0708006600d055182c50701e80600100300701e00e284152020040d0300c40200700b0b42007c028802000740d400c00201c1d080488035421840d21030710160385007009441018502c003901d04182540e18492605622180d405030b2034040e0603002c1e540000d0402d451200b406c80840009011041304060040d5442c2001801c001c00040341c612548011702d40310f84503406001c3c9445ca0356a0401104c4002c208001440241c4e00c8034604240b0f140100428814154004504840d2001d0311403082ca00c00d8006980e00220340e541c4400180c2250134 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 354802508 1250 354801258 354801263
    0x100e1203090f100c06110703020c010f050a030e12190f0908060c07021c0b0601021218010e060f0d0b010e0405040b150a0f03050a050f06070e1314070903060f09 70
    0x110104191801d15040000f100d440200c0d08180800c1d105541e02c080031a1407120b50003066140c0482d50106141c1c0c104061a4030541c02e0030010049032290201a0060003070310049030400da02c908130120b015030b0910902c00d1100712080402d40f01c28140c034580750f6400c2c21805503130005202d41280489288100100011205403002401460300c0e1000c4c0b082c1c0503400800b050307810034aa0300744110107142a45041000c540580480c007081c2c10160002410104541c2d20300d00720540038041000c0c9104c000c01c4000c1500e41c2400c00c0018518030b500800c130130b4000d4171000c0b0300d210303404903041e8034014094012002c00c60090f83c1d0980c1d60342e80402040b00303c0d00255805803442c0d0041001448040c001d0120290844005001e02d855555900602d5642c8d1580d4104441d5a0030451710181003040400110803266040f00c0544418034042500400207403140315840c1c41881c0341001e00403014181d900980d007002588094089a00c0d101d2009418000741e4401110010325003d84401c004846105644880740e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 354803758 1250 354802508 354802519
    0x106090e070f05011805090f190e0c040b1903080d110c19030306090e07140108091b060403060f0b01021006050d0b04081213030f0e0109060815100e120309 68
    0x2400d03d401103c558503c51148542c4984205022807039a407004d00d240c5c450b03d00040c11000620380001181d00c1030f405203440003d02c40c11300c1d00c080b5001002050485021406540000381080380d60002000e100381004d400d203e400084e034002c0144000c1800030030706460102803e100c07048107031a666031140300f40100c010300e580001d040e4481e00312442201580c4c09000b8580401e5150b204e01802080750940f04034090740d07500c0400204070b8441105002011400c0900740240c0c540b415405954582c0c04000b0300e00002009110030100070358480e425940a9034200c90104840b002c90b41c0128010f1504a0301c00c2d015110b2400605007208940c0208001d80b84040c00c141c81c000801e075101d200012014104072a00b120038086240840c60241813a4410401850714960740b24090401500301e54240c60702c44104001c030302740d40d03000c0d03600700f16001d003100d00b04e02e02862a66542119454400410888203074000300d5030007091070180d4054403412603040c04450030b050320305008001c181d507440382c000710f244c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 354805008 1250 354803758 354803789
    0xe03031618031b0602011a09010608070c050703120219081b0307050105040501060e01090203130b06040924110c0a02120a050d1205060616080d060e090106090e07 71
    0x101d2007020549000e031203851080070116226a642c2244010070300c0c6504080301e1080c4200700c0c203542401281e41914580c0c005031100400c0602151070360105005113014000d4080c0801c1034903104007034103d84941c01105482105460740342c1240dc0080301480c000040c03240600c581d80246078905000d0345568410003640c5043c07030015101000016082c0303622070a02080c031904000c50800c1c042e441c4181e2040700001001c1d4184409030f089a0f4041c0c004441191061082140c0309540070310482440d070f00083c1000443d540c41d00010042d181550b401404550401108148005a034815400e00c9070702c01400d00650801c001c0710074550064514202096200103034500c05410498080f9020152203c245d50900300203403070300c078a00441c4145074000101110001e1000046078454160440c6d0202c0d11586803c03003038030443c8201d001d8058081c1500f81c0024200340c44c0d500766400040202008506454039107804502c0600800c500e05c00c007510300b4206039805000010124503041a28060009002903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 354806258 1250 354805008 354805051
    0x101d0702102705060a110708070602030a0f0c09050f010c02010903080a030e120301080114071d1c03031505041e0905010b150904060501020111270909030408010e0303 73
    0x240000520480c02510b440070071294042c1800c102d580440d00540040c0703900d0501051000880700c0194403203030384020030300080c0002030f03100c01110a010340001c005a200c0d1521018180146242c40201a80c01c0c5800c2e40d031401241c0101085003140c00403184c2000a15155006442e901d000c00d00c003c1c00941c2c2d08205000141040d00607052039040c928000440601310300c1314601d00140342d09410403980012004000c8a442400340c51091600300640704100c2c14003140c06480b04000342da005900380240382202240340c44a01507810242c008224241d003801d035a05016000302100d03c5050410a40e060021401e81028000c0c41d800003c108117151003040300781f280070001d10840e5001c03601c554864010600341d9480084108030005090b101c0e695540300d11082004480d02c0340d000b40d041da410718101c1c0c1403030103115003554640e4180805040d09000200c0480a400c1294002e03517a101c01110244111414000060401d44005c200200b0044452900b02a0f4034041124040030240740643c54615 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 354807508 1250 354806258 354806261
    0xb06120c061c05010e0912040308030f071413030b0603010203070f1103071a01091406060f0c07030501150f0b040302090406181703070f0e0a03030e0109030605101d070210 75
    0x690001030b03122075919948010080c1550403c0e4840350342e0071400c40604c402da43c01400190b15030720410701c4942c0b40c140303550707506a154000106482c071001210f50014914a01482c4001d50008515200381d980e0480401e1132600c0d500c241c003040d58500ca01500042090030144200c070f00070b014503200c14403414011041140e074003204100b201003078007090040500003650381059034100c1d00c070b8014810076513040240720030032660320348115600708149405108854541d82d080f160324081200c2c0c0a0f079252150003e5510700081940700400300d40c6400d0340030021207442c42114050310082c1141905842c0d803448010981d014a01020354083d0b00c69000c42d00081c05075000c520011410804c0d650084034545810102401e2400c85280c011000010008015030010481d00c4001c0242040c40015170705501080307941005001c0201480101542080241e00600040c002540c0c00a4180328a24001d0404030300210980f14010000c0407010100940c101e2020030075104401c5540140320b5070034241101d50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 354808758 1250 354807508 354807517
    0x5120f04081b060421090e0606120f04021c0b0c13031203140a09050304230a0f0e010b0307080f100b0d0e2404030f2001090b06120c06 59
    0x1140303140200305080320094040380c00020900b25402408507850700381000116000b4400b8211064000ca034584015550084110300982d1040544548a80c0e03940011543e00c0c400c420048000007050001c001707182c40c1d036403030040c4994403d46140700c2c0031044080075403900c0c0010000801d2100d0701e000040d100242c0c0c002500304007a030694075000316030b641c0e11080200c140d10101e40d400a0b8407481402744c1e0b1102420b15907081006050100001c1e14580c607280e440c0e0142e800380c035418401d40c044409841c04c80c810040b04ea01c0c0010611020a50344800144010010744540e20803091030900000d1039030441810740f072040030307652540c0310703996501c0340c500d10405e500030503080b10107080e000c0104801281c0c6002d8400100c0d031035000120600090a4103141030b06e18054400074002c010003406204240c00341240d0001c0d41820000752003440302d0b00a9a0f03401043c1d1140011400d40c660b030305c940e00e505400c24003a8030300852507018070b900e48000380030210360303851109841c940c883d40d0184a2810104d0091 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 354810008 1250 354808758 354808763
    0x2011514010513090f1104290403020a0f03050714060f130305010507051b0102070503190e09250f1b0215040e0402010801080a02010903140f0114070e0105120f04 71
    0x40d1030141c808240f804040d2058111020090399581249102012071003240d02a1114014040c21305141c010740809400c040624951102d11040803803500f401040140e03406107500800f01401a5111642c001c505d50b241d00c0141c51034440c208000403000e0000c1049000d8401c050191884d00b03c03412880340c0d03e40d004503074428035003881d0302e80080403800a11856011b03503000e9407001c0d81d40d0a17075019200f01c201c04072006822648100000c01c0000c20000881c0c040ca200c420030103442c402c0387c4401b40c071b8a491050074680c11a04070000c0001689440c0f00505941802480c060395007204c1c044204c91904044c0300c01000324410b0180c4800f8111a54403020f04a440245032070b0289001034000a8a60410b41c40301c24070b000d040092200f19a040206140500301c044000d11045520b600000c00b2202d41d840b0103000408100c040f0038a041c400c1c0049040c0002c1e401c0280110707140d0165080c07154800301c4000f0005480031850b04025072069044420202120b210383e8566110050012820310029204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 354811258 1250 354810008 354810017
    0x80103050a0b360d0206060303090418060504150c030c020d051c09122616090902180f0102030a0914040e0d02030a0e0a120b09191b060201151401 64
    0x11510341c402c0151518520b40010f1400d0b241154403801e90b91501c18002c0c20441990441420009075440c004161400020300b145c000c9501034215501101c8113440034005031002d4241010841401004640c015284400c201c00300007030701e14500110110342005440b4001a04008049929140700320b01400100d42e120030003c040c564881b03400011107180c0d00d41158154051420311850716009011258081080740062000d00b10315140c0c002406402044000305c6030307031086180c0c2c4c42d43c401c4a501020f428402c0045507120743c0299005080600340c620284109080010402e00d5417000c426100c0501458903841e07401c90900206103030114138980c100f03801c6540c9052203005c4900400040c000c030800c907005980d850007044001882e203059014594007421300910100102440c40404c0480c03190443e0300200651200548141400007014645a410190300d01d0391003400481c8040072603280d0015100c2010594030304c0203a0a07180c564400d8242c0c3c44c920441000700f511001034650b13041c0c405140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 354812508 1250 354811258 354811291
    0xc030103120c0312140f100605270405010311040f020a170a090c0609060f09030f0821010b090a081b010c03021006090e0d091809021908011b080103050a0b 68
    0x51504c203c4004000d410b0181d400d40381400503c045402d0016000329402d0001200241001006001c1d48103030400280b8480303404118400011f2600c1e800e50942c2030003481403119507564145030762014083d542c5140700d80c0c9010700c5080ca01a842c421541201c8250b1030350840a80009040e001d0b512005080c82c16650f240c40f0b0540000d46003003d160041d20302500e40060450910b50000c200a541040c1e48050028810b002d00220b00c010722000c8181c0c0e400300d542d583e580801d6905000400c41e003411a0103143c0c40c0400454070881110251a03171074002c0d2540500345654100c40c5e503540382c020092011142030404981015445400c64150183c081e0040703951221401003408100d4145a00c1542e01580e40c0200d0035203440c3c140a804003007030f2075147c07131504141840f4041c80303040f585225091310075071344d04445011901c4050342c00400c506410102a2060b079503d03a403501a10514020035502c820f40c140444095014801850603250004020503c4004030f07521000010005080981d07064440303032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 354813758 1250 354812508 354812537
    0x90c03060507031401090501050312030702030c0d02030406020c1c060b03030408030a09090606260a0908070804030615080c0121090609050607020304031a0a0b0d11090c030103120c03 80
    0x80e403400b981c4981e42c00034074605075064120350018181c02401d662400c150041200303542c0010030905c84840d401c074040c0d51380c451000c217070701e544681440e00b000c1b0701a1440703400e420703a00400600100c4007540c003a643c0ca81b03814010810381c907400450640c51b5200c00202a0003240541c2e00c00c1380c2104005d01143d1806444844007440e54000c03040840000e10b401100740b08000060050707000811480c03c141200e5240208021501c652120f40034150281180004402c5030b400c1c1c018103410b94000d144160340d40c609003000308140d442400300b0b549081c204001700c040c2a91090043c0c1c1200c01c42c0c0c010701000c51070500115041d1401040c149000703d046600600c51094503c02c3d01b10403071103001c00048000341c1d8a4090b0600900408400c00d42d04140020030102d4403003a440071008213900d110b4070081d91208a040020240828241c3d0408241d07904c42c410003251046203080760381c00f1a83c0c1c0c045541d0b680e03440746591109001c001c1013038440350318a4981a001d1084124040e04c01d003403400710b800303150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 354815008 1250 354813758 354813761
    0xa062106201206040f0506010c030c06062601050f06030307080901120501080a02180915040c030f080d20090906131802040b0a0f260d08090c010c020a050103090c0306 73
    0xc5250b105076508500030300510345024801c1d102d480e80ca401d402d204a1030040300190440e58401005000e010250307601208000c4d00c0d40c000d401800c445040401d078035145410180b200452180e0841c5550303c3e002c007203030b02c0b00000d801a510410004000f1850541e031982c0c0c0b440d080c8c2200051605010a00d24003001c080d940f4083c15008c1c3c082d180c0108040002401000441d034800c5840c03501e10040c150510100da038022500054205140242070301648a520b00400e41c606503500141c03c07040c1c1070210004004059004060450401c0400d0200c0c20304c14103440d8185404400045000c003040188000380c1c10060516a03024800a10400c0a0700d101810607041e1a01c4072410385001c0c00702da040740110301e000c2c820519040801d494061f02d450805240f030311550340c41e01800b00504194007003081c403500b4440004240c0c200e100151502c000a0240141c4800019207660000c3e0103000e02c10500c40d4801c0358110905900140384201030343c5000015001071150920903500114103080c08030124005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 354816258 1250 354815008 354815017
    0x14010b0604060e011d061912020d05181504140313060806030d05070506010b0903100216030905031b011b0602070c031e1a060a050d0b0a06210620 64
    0x4986515543c51002e00006080780320b56649540314520703440400c1c5a030703282c160503a44038114005410504118181c0180d40c000850041038416600000307641d1a00141d542010340540d01e0107000c202c3c2a02000b00071501c87e510380f50040308030140040080c012803c4414040f0303201c2071503400ea80c0740131914100d001e400c40c029000480410001814009030b0f0800b00242181e8a007246051402d056407955010741780c91040c454080c682001052145455400740407607038080b03003207603011955040024a02651070076100b0b4246c011030302505000843c2d041c04a48900320410503055022400b4410005480800607a012003c04803040b40785200000d0862000704003003400340e244404007501d10310b0014610f0300d1480480e0b041c1d80780c03c04160000745002484c44c6e2446000c1807c40081d0f918070021a01400e010303032100341d000c2c4189244c1400c0c0641c5080d42c0c0d000b2214218180941c50700c03015011031056440540280d011440140b86000c0b402c5070b400084001d442545070006c00c140c401000c00320741c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 354817508 1250 354816258 354816269
    0xb13111002011431050c130c140702030c0d1b06020f1006050102070e0403030209090412082a09240307030f0c0e0402030402180901020c1506030a14010b0604 69
    0x56030408401105150000741e9840510440002d00c000700010604d070014290502d104100a44910070381d04109051021154908020701200144070409075032002501411b1090303004101c00d0b2004840300e0402c0021200e5880d0040d00404060b682042882018080e2007000c1e58031042da901c0c3d021003204500720840c000c2c4003950051103038021107114035080401c24644030701d48900d80700703080040d40d1300400c400c422990f5207080c072061a074560034140c0282c0f2500c9480c03039203c009030080000304141840f526656001d0b07540c2d45111580c50f00e400c0e04c0e088880752502074201d000c1a036614042c070b45600042501e401d003e010400501415241090f21041401030002c110b140030041268080c3e06104468001185074810b00a00d800c0e0600a00701b4001000e01c9402507030004006001d640700c1501c1187e81c101c1410f880d04852401c04070041c001c3d0841400903105015405640120100315203840340103107001005810000110b1b80da100140066412a406a548812860f0712590b1035001402c014217 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 354818758 1250 354817508 354817511
    0x70212010902030f0a170403030f052512170f270604030c1506060e04020304030c0507060905010e03060408030f040c0801091a091506151c09021005070b1311100201 72
    0x1910346051940906004004801c1b010140320400201e83d10a5001a0804003424840d0b50780b4a05040c10502906561401c1c018500c484603c6081108001c1c1c41c0045110301e43c1d4001844a008012071030081042d5a00010045440f0204903517a001130042d0303510b603c0305a00400c90550308444a410104121402d902103000c8000c1c400074000d1840b52400700d001c2c540d408101e0141403400c090080310340c06003400d0003258080001000c00d030081c1c0394600030603003181c110743c84d5699911740100200368034080d40b4001080090b03114802e00b400a04607018a41c420140b40c00d669030b901800041000003842900c10200c61200010600d2080c81103015450044030000901000307110305d000101405451450950b001f00d0900000a8041d88000d4016004440d0309a1442c1c0740060b200d2a4001d100d00700480750b4044220f0289243d0a901084540c7e10944014107000c6940b40d00f5a80e90040000203800b8036241030010740400c2c886103c0d14115482181c2002c04c0d003a040f4082481c41d03049002200150307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 354820008 1250 354818758 354818773
    0xd0606030b01060c03090620030c010c02010e011e05060a0f08070e060d0302150924190c090303230a021506121002030a0222170c0105070212010902030f 67
    0x82090701e0703680e0142001d414400f500c9802550000d00704001441035a0400c59009690a1031041c6c484820b20554910803c0325200d110b40d501c3e5a00821040f030f1a000590720f0030384c40c3d860a8806010b015444184d100078229045200b01c0c100d00a4600140342d42d07480000d4103008039404580a80d9440501064402890794500b0514a00490100908043d03c03c40c609601c041c0040d80c0001c1000c0400c0c80031121802c191150380300586090280744d26086c01440c0d0149183c506a080309801e07200f4040341d1109084800342c8503c2c88120b42c01d032007480c400120451818004280035207002d902e000c09842546424000d5139041d581660800340c107000043c2c1050398162030b0014440180d0303802150446075082c16400014003190759102007034003da041500400019401036042d4107030750040d11b101d106940c52055941442814502e6805082c650081e60740c016580c12000150b01311100806854281c9171540a408010b9800b50005200003150740301d248440c0141c03024001c28040402000080240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 354821258 1250 354820008 354820013
    0x1b0c06130603060501051204110d080307030c091d130c0306090f0615050a050d0203010609090f0c06020c060304060908191d060f0d0504020a0b03070f0801050105180f010302090d060603 81
    0x1a00c0c0240e1181741000790501040320224004500d040e00168170110800d40c81d0600008503070f02400005005d8020f03800402000388103600340d003111102a060383e482ca140c2a40351900404003c0d50312200405900c06000001c82030280790b0300b150f0640b0b000d8101111840d40d030355543d009880b505241154204800710180040202501890080d00e8110344000c5d820350502c808101051070b14450f0b03d03c40c009218100096441c01e50110003d02030008040c003003051241401202120541401c4981142e5128001952880802e06c4903041d44011702907803464455407944d4025003111302c800d4800f0007040081c4402034001c1485206019070980b117012075480d000c0807180c1031001074900140142c0e810098885403031001c0f021901d011210903c0001c1544442c0003242981b812504642402c0c0c0c400000e10103a030381c004090040010450f65060700d030780c0c1c98200444860042c0c0b07030844070101211098200a2601c51211f9403511010715005003444211400520710310002070b01075804a83d00c0d1000d109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 354822508 1250 354821258 354821261
    0x10c05090f030d020607030c09030623060907020a02090402130219090807051507060603080a0e031c0e0d031b03051c060e180a0209042f061b0c06130603 67
    0xd481c030101c0c042d012840c038480c40607443e40c5000b45108105a40c0b8000da140701c038000c2e2039160181da0058410013641c0c210a4600745039802c1c07400c0301c081401d6428002100d030b1034800300d03140c80383d03141d035020380700c94402603081c00a5884043c0040740c2c004100c0a806410303103100e01c0584240f0104108001700803c00f600003500e4011075800c0301107076820114041c006a1110007802080401c00c080c125076402050400038014200c1c0d8000501c0c0c2140082c0b083c460660200542c1d1040d00c0440564044103e14003810102c00703d0045164041580c408038441d00b071802040c02c1c00c00c24003d040901d0030803802e0b072000812128071881140422408501558070001c0a10b4400140380e0f1882c0400c00d103814020180e140400c02007545107600040030b032610b05c0c00020700c01d0700b10550380506440328905151510880030260040030103082007200e2510340050700c00d440c801d05000c030098410b5181014104000b440c20003102e541c001c0501c1202180045a15140e000341181c07014044481a45410154000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 354823758 1250 354822508 354822529
    0x50706231608240402190804060e0706080a0c0c0b010b04062a080a020c0a0b030a0b0904032c03071203020f010603050d0509031005010806070306051507020120010c0509 74
    0x60401c042002003205a420005100070028007900f444860600c580e4000340182c86040e460030310001040c2001030751103401c805a1401184a40c00030b0048080c0043c8040e0f89800c0749c89500009040e190201e01040f001c0e5101300d0554036180fa0600c500780072511380d4621200c0c20b91180da52108005001c1010541c02040c44007130f2000041303450701c80f0b521041d00e0300000ca10364100ad82822400601200300134003c03c03445807124009071088068036601c0503a1484d03604229181e80311203003031003e10503440c03500108040c416941a22042c01005a20100f4820300744a041024a40b100e040181c01c015642084640018015036103000c6001c851031400a0401700400c00002d034581c1040b10910021b01c002c07460f020200d0072841e003c0d40b16028140082c0c03a0110821000303c544d86007000115024030003140092041d1140e841c24812281d9400a02401180e030b200210056403091103220010340c45041224910400410f00c2d00f0070000700001582120390b1605400c0114000103903001d0181818250310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 354825008 1250 354823758 354823801
    0x6180102030103021e010210150f060519110307020307080d180f090903050f0a17060a05090c0c031903020d060605040501021548090a030305070623 65
    0xe506551566000c56108881c035401c0d01c0d413510b0360b0b02c0d0840c000d07407081000100d84e40e941d003400d004030940c2d0702008030808801c0c05002030741c0c201010301148803805581214862064004e42c00c602c44144601100c425140c01500e0b5103600003013200401583d02000000c01600d02c0e41e0242621000c1524081c0298400245100380c12026220800107882d400204004540f10340381c011501240503c0d0031145845000f0210100c0240842e001c003415908c07902c1502c00c5405912480c0309510381c04100215501c0318841c456000540c040000d190308015070260240840300c0040380c0c202410043d11502c0401a000700c00300080c2e000c2060081e480d0705019860007414141070007880d150405000035201e031100003100b0394144000d0041050400200180445c00446401030004c6000712142020026081035503c280b800d0822a1042007d1564040b01da41d00c0e001018814054610b0f07406540c00e0300494010f542040e5039188959006200c20b941102000900401c0f20081c680141c02150264803400740 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 354826258 1250 354825008 354825011
    0xb0d08091f05300c072a0b160f0b100504060e07031505060f0c100507390b09061305071e0503030c010203060307230105160b09061801 59
    0x4110201c2e400804503211401e259503e42c869090b0b400007403040c2c1440c0c100c0610381d04030f01d01c104418560751002800710b180c802ca1a07024071300a0340c0c52003a0401004002d400c03503000d05003003c00c4800e042400418202c1d091502544ca260f419440d01d0351402c1c0da243d8162600d039040740420585100f80020000501411101001024205012904503d80042041d018159240300800b0305c4810740300c0d05070041400a200340d9840c51082002c0b21207400c050305030070540c8910f0914a2404100e80100d9200c6c00385644c60621380515101e0a00c030252051226840c540481110200c400814100307400540d80a8140413995003001d650380c40c98003000414545001c084003c8200c0010008103245003101c40c07031041c1a00003291809900000300f0b40741c5c041ca905120026040c0f41c0202e0640103584118022400c0d1140e0700d64451454480b800380400110030407030559194001580564013500d401080c04038640a1241c0c59a546101001c09403010031103603112104008242d00480d4080000c48041c100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 354827508 1250 354826258 354826309
    0x7060e1011060a020304020612070e0a050306150907050c010203040c03120206060d0605191503050115030c060f050f0a0206040605061c0210021504060902010e040203070e040b03010b0d0809 83
    0x144240c4030100070f808000703420340002c00314003550345060941e9404070540c0c100c1c00c2e003401e280101a01c45241444094001d0000d40d42c0000c00386008a000d9115591503244d03495022805401c10801c054002c040b00d05008051018140c101024406181b00c0d910030001c8040d400c5c00d40c10003440413422a50194115400507040100300e0302c070050100341640e03000d41301150070746540e242c210a038455454404010303072801d100c441000d403c0c2c84106c0212400f4034000c20480620214180141c04640405001050100ea08215a0788207a0300020005810714045007000b0a141c20014154003c400000c0168044400e11003480042d1054036000078041395440802d80465035071019490307203440041d200e03003a80165034007a01d000388003040e0a02101d180d01001840d00d840d1400080400610a9002030703c601d0b514006030a141c401c4074044c2c0c9460b2104484401d81804110260440b40201d94040d501c07980b8440d0389031500030101c0030341449038a43d240c40e01c541e007040c0000d603901400795050b130100c0040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 354828758 1250 354827508 354827537
    0x30c081002090f100207080a26030c07110a050d05011d03090a060c02030c061b010609050c03010905041a1e1308071b050a06030f05060f150d060807060e10 68
    0x34008030203c074090703880c3c0500040c040b8061703003001d00740d41c41407045000f804480410841c14814200c00c00c800c03105610200564000071001a002c11113010303030039803801c09c484404900c036107101141812008240030009501c40021030a1101c034500201ca40b691a00c5036010a041015985401c1401002c000c604100803040043d2106096220f60b20501407060403a00540d00e040c04001051070740070300142d50751007000d011100c1a02d00b917002402e0765407030890082505c107210300030300c1e0140400500c0281564201141c0748000c1c400a40200e03003a5400e400070078007008907c1c05091007440d81c101c2d4003004445040b850410580014515110b80c0d108004000c0058400700c2641c3c041078001500501072500304913038a441a0303031501312075801422034500041c40c07949a00910301640382c18a0910258849106000400110684241e4081d0400407032201008211029001004c042500400d074190380784803150414040e07800c064001414503506d109541030040c40304002c0070151030304100300d11545 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 354830008 1250 354828758 354828769
    0x80a0e06060a0b0d0b0a1d160c11010c12030209030c12030316020f010908090a0e040506150102030d050412080717060105031b0315010908030406021002030c1201030c08100209 77
    0x6010303e0701e070b214000c210280788800540c810268144040d101861094840215001036401d81550381103902c00c071030004601c581c0c1d001c0311080039941d54407024080c0c40296034114544c5640340c0d072141042000744880300440c10002c4411400d40d055100141da6000344000d140c00c14135000d410300c0c0202c41e01d0780c9181400d43c0000c21039601c40760b000501c000c50250f030107049040c83c1e400b00c0e80040c1ca40c205041c903020b00030150000e203c0080101c40101c80155144410401d449007214090301d44e030032420000d2103012400d50b0007016810140f05880c41c048140d0b00000031110182c50644600d0301c202c3d140541c054108070041c5e0841c5403410006107220081c800400c004d00300030655410050f000c404903038030b40c040e0300400c041800407041d55074803032030907410f030070b28440007102400d001408030040002c135103074003004030b90540d80300d40e025142004204142e00040d50000d040058129401c2014101e081e0141c100c5501840c840e4451712206442c15141502d481d101100c0e00c5584e620401c100c54003903545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 354831258 1250 354830008 354830029
    0x60509010b04081b1f0815041a01110c04022704090f060b0a0b0d0e120405010207060e060c06010803070512031302100207170a060609020307140c1606080a0e0606 71
    0x50798074000c60300e083c03a0040385c1c0300301000c10f0b00c10200c0d8058001d03d141ca500101b44500c40d000360004c2c0c1c5a44641c00e420803098524900700340005010700c40c03a440a40d4414241c00e12240b0030034049890404111000c90120707404010f1689038010140707440c2c6580008100540044441181c0a105503135054031041100703110020f00600f104c2c0e43e001e40d4516611810700440c01000c3c209603a5464040d04038003400945042c03507503001707640151400c0c01c00c1e200b81c40040c0d409495040c3e00800d605400c0c0070b41a00d036000390b0425541d00400c00d01084180c00000c200d003502078075007a0003554503002c0500d02245042e00310103031564851001c0c030400c0901081200011280744d0111460135030b524141c07200340d041c54043e421441c04400d02d0445100f40c16800105400310700e220304800c00420313a64400100482c0000d480c0000050409155502072000c03080151031003804540944541c00e0308080c3c1041c0d07045e0a035002d1004903e8039010405030001c1c034030600014207007000c00fa041c00d1821400181d5074843c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 354832508 1250 354831258 354831283
    0x150f1205010b0f030a0b030a03030b100207030b18010b03010606090513020304120e0f0306010e2e09020705070b1606050f091f06080f030c0601240509010e040f060509010b0408 77
    0xf40030001513080c413050340080c2000700b809801e41d01c1020003030230000d010344118210705000f4940701910a10940c03001481030203c80e04032100c0600d58803000c041103a00c2030942134504440d9252501414a5502031142000500058560040c080c0c50007050001a10710440201d4981c0c0c4180100000b064064860b10000c4d41c1d40e160401d00d241e10700c80011100301c0c82485558051041030f0020513490100c10384540507040b1070755100304c00101d031200c070300a240f01c0780e6224412803844942001927262603000362160721f10a00584841344d440c0c0c1603481d8103421000280422090014190007400031520803282c1080d42d11403d15841e181841c0080c1c0e0b00d00300f0310281038441310458103036058843c095200e034001d8011503064820200845038a941d50f40c100722594040c500902000064401a03030715540590a01c41e4290f00400c4040c0c0d600b59500d40003a0b003154144001003240b4041c640c1c0f24480c0c10803041e441e480c0041c0e0582801c0a110340440144c105601c84501008180f0105000040c00e070450003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 354833758 1250 354832508 354832537
    0xf060506011b06050906060402090d170403200f100e0f040621110306060307030b0703090c06270605041e0503070314210301051306150f1205010b 64
    0xc8641004031402029581d88890710000038402d50704000fa19004103005103212401c03941c01da21201d04000417031042d51102c0b07a00c04206e404400010302c00c541040d150100c0d041480341000e640b0385a207180c1c0d0201002c2981040401084c03d0f01d1440c108027204200002501c1113101916404400390130f020302002d00c0e601c81c2034080b00d4624240d465810400141c1003600040300c00050351386500c4410080c5620807207030200035808d8541e0600b000656644034640080091441c14959215400040c0c0090500d40c1007640300c41040b4081500800020002e00f000c1c1c0c0d46000c5d1107a0144c412031041c501180400991020f038108000740c0d64024103907026030f00c0116106040c0f00ca032040400c8050300c5030341324a8060150000010911070b02d403506865940c07405090b00c01d640820a4002c1407045103000d80c40c03000d003007400184440d0802010043c1e20b00f01c4c0c8074002900750b448000207902c0d200d840603204000340540700e25070744155010914842190848805210755418100440078602610f000b00d000c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 354835008 1250 354833758 354833761
    0x105091c0315090213050f1c120e030303070c030e090c0a18050d0c061218150f050c0405040c0e1003020c030708040f09050c0a17070e03031b0106060c0f0605 69
    0x40920084a800600310f054085682e58901090708600e02194840c084c031a03030100c0490503041c24500d81ca01040359981c00120409031895603500c14056206405404208100c913214400361410801103014017425251018040c003949402454501e4860b542d42c012042c0030107104800000e402a0781a10790359003001f100b07028001d0f440340e980400c590b103c25400001521048180801d40208505585403540c3d9012000c00390f05840055404078806001000e950302000e0700030071807a4820815802c0d10b100081440c1e0b0f4210015029500195080440a0800501000185043e10039422080214104010181140000281c01c6104071f441c4c0d5080c144c00041c2d05d0b150001c103104903070003954429260b07920b0310f4650414085825460040c0c00c5070354036080c04111448228800d0350910170580d503842003140f0302444805017122000d002e000601c1031084009005ea5000c2c006021056446400400d4400345000160b0940300590300810502400780c14031004030b00440c1c940100310b5044400421103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 354836258 1250 354835008 354835031
    0x207120e0f0301110c06090d050d05040201050702040e07090f0905121b03030702070306110408060601270b1305040507020604031d040c020d0f02161806090504050a050105091c03 78
    0xd144401d001d6415482c01601c0c4c404d91024101400c02252043c0407242940d4920402e035075507102d401c802402090051113000000220350304000e502034410f01d0181d040c10182d90116040c4d039129140820980c00c004020b200c2c2d21403601c10110000054001404000c01035242e5a803660100c4030391809400c0000380b107465000c15800900b0894661001312640c92034010b90094031101c60340001c850b114240b07880e132141c0310341e600286e9081c4d804102c050000740e01c40da001134031042182c030800c0008410041c00701c5150303041403111100510a49210b15600c4454290328405000c140d04031920644c0b03840c0c14803503031960004041b0f500580c1402c0c001500d004a4829540c283c5081110580c414101220281c1159000c200909a480c1c0380e102c6200d104056041a61078081800454002c07800b00001088245440c0951f02080b0b08104c2000a44c0743d26115240144c540482d000d83d001d60202d6100010002d0074402d0680c04805440507029241041300900b41e0003010344080f40401d500c80142c0d884 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 354837508 1250 354836258 354836269
    0x80603030702060c25030b0c21070306050103110a05041a090406030c06110714010302091c0803040b010602070308090f030f0607260c0703080c07201002010207120e 72
    0x14540040009413140c503a890542d58518004210406000c0d44030b8411001c100c4103160b14050740c0c1d100034031416590310200266025002003161061a1000200030300302013001c0f542c1c05000d00b1582d40c4c003042880c1014005001d45a10114085007001e04000c42c0440300e600200740d0b0240d5003000034403225603100c40008203590003204003285d07201b0b1074150000b0802c504144003100301c8070661143d580b50300758044829104d0100388900012800640920292503219038020151084010000345d14801d00b58243d5000e001046011a0b40000000c1808248540100040e004005500c010b101490640e61070703110701d000c2c01385100d02600d08135842c4e80c4e1541c1c0622241c40000808011111140380c44040103204626806c4014040032802c425046d40402e80e5606521400582100a1802a4942c0c040301e01440040c13010001800074400702001620701c420f440b44240c07002c248400c601060004000e013603042c546c0e041c029a1b10410401000489549115403910b10508040401382c03c00300225a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 354838758 1250 354837508 354837517
    0x30b0402120d0503072a02060c010f0f0f0b0603011a160b0910051308030610020102040b1321030e0d060b030a0804080105010b1c0f090609080715050105060a08060303 73
    0x510500840e052840d14943c8100070758450b0304240e40d000703002e2219024500c141500b80500d02200850302007001d01506020006000c4006184c0000801c03044000034001224071051078280d004c1d07202c0060054588003801440300b0b46400712a0640355500d01041741d811001c41080c20032001c680410304403080c404400c20002c18030b411510340d041c40d1510520342912403010b01a20401c3c549405c001c5841e4402114084d0b0a040d80a4511465601c403001045008450442804d0441d9020000403c90b00e18441c050410061810900c0000d50f041034261045a0aa03d0345000317080e042074807110100394418204244039805540c1c8800700a224104070010302541108540c051250420080421211800030803c80b44448020050f42e62140182980c500c6a20743c0020389010b202c074111902605640103203c0b0640200c000075080d07040e83d032500155945000151121310001c94020b0520521902c00d00e00080080c804005543c140b800044060181070403d40400c4080000980c458a0030011107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 354840008 1250 354838758 354838789
    0x60e0708060f1005030a050a0c0c021905030f0f07140a0302061804020414030114061f03150b0d142505070807060203160c080915190324030c030b0402 66
    0x45500035002d06028049500685500340300915102c00a845d148c000e03c18580c0d6405d00d5500d03c50345603000d80030881082107d44190b00842a5550001455581080441c01c454404d0001d041d42d880400c04050408440c3e43c003c03e07010002041c602d03543e0341c80600c5030041daa030449040b511a84c0d035440320880468040c40003a04544006070100781c0364100c03110010183c10481c02440509501d4200c2002003501b52840c680042e800307129000c40f20000000001c0b0761400740360000d1205c405594184569202da031004524450010704060307000214002c08031042c3e004040e00f031440c01d041001000080c0c020381d60f03070904401e003104c00f010a4451022600c56a8000316110340303560540c1440c0f402076205640d03902d0700e90501a86120303941e003c1e00c1c072000840e030040c1020341451941010300602548814400e01507280c1008034080c00d8003407120f143c120359144d1303400040c1032a0b845151441c080840c14503489540c520181040000e50035a00d1000b44c075403100d114039a5807034034404240356201c240d81c83c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 354841258 1250 354840008 354840019
    0xc1407261b16050411040905040f0f03050904050a1a0118120602090102010b1e0d11090405010b040c0c02090412090b0a030903080106080903090d14070303180504060e0708060f 77
    0x4410300c40010300e1080d40025242c041d410965540e081008486861080c0650760209000400003034056070700c22541305000304284610b6649070380c3d907036070175000307842080f40866000324541e20541010700c583c030350113581d042003009054a00e142000001c520075080504028441030f40e080c0c18010034078008002e01e401e0100701c044500c54a0294065048822158010362030201841603078030700f460307940c40c0f801c00c040d01d100652850f00081c07081d079021000066912007422100c000f125150040300500c56802040001940180c0c481003206940c0c803d1010000c20010700c01d0f510150b92480798a50300164000c5010f82503140e2100151104080c0d42e100c2110214003065804240d41c042c1c00c0601023921076600c142440c0e8a5600c00d07610908169200016644280801c03002c0c0d091504040703c215000701184690b13072000d02e1005240c85840c0c4c1086000552401c60740d01c180301882070f50805040308131014405207042c0140c03840500f900510400800c0a000081202c40c1c890065104464002415 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 354842508 1250 354841258 354841297
    0x206180c120304240f0e03010902131b051801181e0905012106020c0a020a08160b0901020616120204091406010207060909021b060a0c140726 62
    0x1c1a500c0c0e41092040e1100440c10014034840868410618000c0f0000c9407508031298000c00e1003110b5802c08078042c90342565075a03800d05e000d40d03115104a50700c1610700c5000314651400d16025404100783d905100c0600c10705010a1400c40c02c984e14250445a003841c03d0142c0d00c48450007104a80c00f40e60050043c03280d01600111154005801041a1044c24005001503665002010013500420b00801d6a8000c440046400100142c000344030090010044845c1c41020707800140e0001c199601c1040264060f410f000b00000c2041c4461008000641c81d031030174440c1b01c400107500c512005205101c00b11440210307a030060b020354525480c40d507e1203021074480d0748944400c0300600070740303a2944a58030404001001503200256181c01c2c1c48190b81c550680300c0c5895541c001035003040303540d45290b5460250035904010100083e9200d65044d01d0046281d0020450103801117070809400d452030801080f00c071021942103018682c503c000c20b4140c102c600f40401810801740512158034a10b1071038540d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 354843758 1250 354842508 354842539
    0x306083708070b0f090706051c1109040e37080f0a080f070207150309140703300503130602130e09010603210203040513050a060f05010206180c 63
    0x7030000b2078411a910441c60302c415004040c2040101d0340030401d9440302009002c098071540240003001d2042060546c6e2500d803000340d0b8291150700215240340000130039070320b0207885c0901981e82c407901d568000c1d09109000fa03001d1460380c0310340340c01d40303e440108400e1812403004052401141640142c84948c8900ca5070020030032b030341d002018201c0010b62603000700318400400d0303a00c2030089038a03400801160340f91140781107160800208000a040e0b43e8029a0086104440311200c460f0702e01c1701420511741580303403280b50f030200e03040142080b00e032000d030b000100c0742c5410500015030b4113030500744d8480e600c20f00700b0940450304c004010201030010559003d0125492000010307207a0403131100b5003681c0c4401c581ca00f00e503200d1102608802c132400d5003054050101c0c0d60391300c1c2c184003417041c0c170b241030348450104a5050544a0510030b456907070080101900003480742c4030250003e02c0d880100c0703602d0a070000b943c0d0240501600310a541160703101c10185801c01c24118080005424185001c0f00c40c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 354845008 1250 354843758 354843773
    0x1015120228050a0608070f0c1e0b04060e0703080a08041b0801050702070509270f0a080c0d050a0f05090406090501060c0501050903040302090127060f140103060837 72
    0x24070400d400740c84015004140301780100f6010b440b44956513542c0f00c185403201021600010181416108003134038020340103415480000080416000d452040309600341440d00e5000c403401e500501300941c11007400cd10002d12420112000c030a0b05181140b42ca450343c1c10701d61304404215803910006900404001000b00c0c042d0421407041250350280c51030700d65107006110f070202e02220340e40300075004100c1e80b9580d442e500410010000850044a03218a81110301c54a000c0b000281520b800c0004500e01e9511101008016803100340c61400c1402c00d03190075030240007032031000c0780760060120100340c040305503c6546c0030350000c3c10175040600155944030740107000d14549050039140c9500340030008644c0c4000108450440b940a00042916803030180054503820712140718001034254920318038000c6c103d50180c3c0000d00f2481e90045034440c07801080402d18151200100e0500d0b003017010030480d07808042001031a00034140d060311030044e40d0403e04080320f02441002024404002103040a101a5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 354846258 1250 354845008 354845089
    0x2d06060715111c050a111c09080c15090a051f0e010f06090c050304020d0602030c0c010c09141017060111070305061803180415050315040510151202 65
    0x70f0350300030049521122600070540b80444a1440b00e460208641c01340085507010349103414060280010365000155140b030490307403210541d0400c6a010300f030118191a0018425a004500b490003000381d072200780e4925803035081d010340080d4007510007040300210740c200c0c2d00b01031003001e04880200000d592580401c4001c00d8280284101585010040c035451070184049a004d540c0042a080451486980e580040e600041c20010000d106002030070219800b40105040681682c560216450a0054644543c2844a04a48280d07200b50314080a2034100c5000000070302c1504004203660344040068503683c0c0c83c0382c1841c41030310421000100b40140441c1f2a8003600310200c40c04450b4045c040310a0341ea0003a00504403684010001d010b509281c17a902100c4000000c0344402c031229556000a81000310100d0400c0d824410b0300704100070030000703212040d549035041100b000b00018184801c47d001000c0d00441801181c9880c0402c00d554864030481a80c0790365801c040c41c0e08050940070544100c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 354847508 1250 354846258 354846307
    0xc0609041b0201052502150406020f0d0e150408030f250306050307120512030703090b07030b210c2202040f03060c05030601080f041a2d0606071511 65
    0x51800b12884400c00c4d02c001081e4150b460703801449081c10b447c0d903164000802420442e01c05500304051010000340c0f601800400c0c000c50400070700c0c0140c0c405d610703040840040070301ca002c0c810300040000140143d000c2d00e4100b01c1201030741e0302c20394a1605074070341094543c620303981000d130a10120894550581006e01524400e0381900d681644d2180c4c100f848242500c0000c0c100e0300074180b484000e11480700a55403104141c540818078480c142c4425a03a54000e9450300b0010b0744404c0f9914031800d15a03811412800d84803801c82030000c1d10302c030094a035040d200102d8030079041c03280c0380308620841400e03940300481c480c00219601c075030b10714034401d9034401c3d0310080322043d04101c400c0050f40d024800352845504180c654150360b0346c584030384161030305d4014401c49e1200c1000400d0101220080400c038490310345014081002807101054010303041d40e25034205e020740183d404014040d01e8460503191410f40c0215009102d12111812102500700e09640d054882d0780811890302d000080c1e140b1020860 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 354848758 1250 354847508 354847531
    0x10f020d0911030c100503070912080a300207111008010503150114060c01150305100f020f2a061005090a020a08180115030602090906030f0c0609041b020105 69
    0x50300c0314241915490b501d04d0842e0300c9100c901c480140f080c0508019030344402c182c50080061030302c1c0c4441c910280c0010205403104580803590b403101c10b80001c10b61217001e00306450654001c502d00344546000b01e010b860840803640211b80c2d0801c100344d0681c0b410102000601100244041d401c009141da002481114800d208004920303180e40d5258142038144c0306a041510022000803060100d5580085141d0300a5943d490300300c03502c240c4440012002c0c42c03298014081300314030042004251840440c00710b401c10f10400c001c01e043c0815104172603940c11204032007080d01080140790088911499101c40c100c4c020740c4100301014019035050030907203c04451070b071296200c0c28141400c9009044c890004100240041030108905074000e021f140c180a0021500a41912034406824066803049803503640104001c0b00300d203800c649081d40824250014a00d0203410400302c0d41d9041404440740c01050002400780311605caa81006100000099451459210040000f03008003000c03151200f850 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 354850008 1250 354848758 354848783
    0x403020c06030c1206011b060f06050f01020a11010c15090302010c030902100c0c080f010905100b060714070f0605090108010503011107080d02041e030c060212071202010f020d09 78
    0x2071922109072800303496000303040c030700301603100e6103044d00304102038212414881500c1110002c00042c40200c80505d20410010507035003403084469007500ca060700168481c0d83d85030601c1c80306076070005041900540003511b20f04011000c40c0140c0306040080c0f4090f00301e0012400c0142e52814503002105233a100f40c0c000c0040115451088044a24042009502c08030755005481e007580304600d617441d00c41c01980c110744800d954036107807480c10b071400d028038025035120007450040c0982800850440c0900c20418070a400c1741100140c0184103414004181558100c0d0030360032031000700081400340c441001c4502200e622003001800c2500041d10300f60015400700c002084508040c050007a80a55004810341840c915640b080d45941003004c001c2005a800d00000484001550006480d081c49103100d40b81c90382113051820b06107100b81c102500303541c40005030441c40420b04084a00d091307002300c4c40b071a11003002d50b0101c0c00f620480c0c50307003100c1500200718500340d161644d200300d64551040100c9040d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 354851258 1250 354850008 354850033
    0xd0807031506080711030301061115040c06080709080304090f1a0105090d0503070203060412080f010b040b18030a03180905090a02060912030706020a0905090603071e0e0f040302 78
    0x81d07039240c0700340d42078404440c40c00300103031070103050000d8000a25050035141000001e401e2440c5070001d900c00c2002030040c0f140f00e0f00c00c8405203c0380c04120904241c080e01441c058803440405030784d62107040108400c44d000520507511038050311015240c40015079941e00d90b0b030b03014000a021195044085a454a03017460340341c800a0b060f01a401c10181c484500b4085d00c3d004201041c070a0303c10584813800104825401603806100b414800e51040c3d4400102c408123a0307000f0980792005044100c0740d00040014040455a42c0030740f4210340c0c0318200c06a807035480311100c2048030b001100c500e4141c490703494011b08260b003002c01f001e124030240045d81007865907046e04c0000d4901c00e56080a50360000c543e02005070400c0d00040150043c09000c9a8907414400740b00d0b491a4010b5900f9a00207501155030740b0200d034403069513002408201da0004042c105000081d0f1030b14200c0c410112100320041d0071810044103120b078400100f00d01501882c02d440c2c8103003451310008c0c0c02c444c00c40c014000c0c0b4500b0200c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 354852508 1250 354851258 354851261
    0x2d0e0601090b07151d010f1b020a17030612100f0b030c0d020918030301090b0a1202061611030d050c010b010504030c0b0304080721080f071202030a060b04080d080703 73
    0xb81540145129080c80d48480401c0020140c404021405c0511145c490007180703801d008015862564030382c0040e81c8000c00d40c1d0343c81d810414504050071500030022101c04602c0803541c5407403403821904116903e0b1510400200c2c06101d11100742e100340038404000f108481180d110710f0115188000900c00c5c001d0300350425071248401e043c4660310200100602000d818514031a550115004908010300400c00642c1441c5400981c020136805454207003c0507241014802c6800515260800700e0074603101d5030000b1080c1c0185029803602049144005050080d1825606003211000e82a01c1c001e5141a100400c0f0354051160b40392507609000c5c0c0c00040794030070030071281142c0e0040e4207610320300c0c113001c1c014055a05c040c0c02515010300c140001004104070001841c04e100700c1c0201c5c1c031001d40b01001c010348401001031960004030141c4041144803a00701d060704003a0f50303040c4001641d903603500c1c1c1c41c000249540c1d0040c07403000c00c0118012455010020307030102038101c181c482c910169142c42e070450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 354853758 1250 354852508 354852517
    0x1c0c0e030f0d02070e0a060801110a09050f0d0f02012a0209010e060607030c03030213061214060603160908060c1e1606050408070605041104060614042d0e0601090b 72
    0x40044e404040e0811a20048406243d08660900d80c08168076549264050a40d03088a2219440d03070000201c807026590070075906002482d080d56088114039805000441445003050090700c0104107010350400c5a110b03458410a141520110b1008429283c008003071010b02050128011030150001150301a65a503005204010007000d4625100707096408440703c092401e012801c1c103400b4001200b0500314200c0c408054402c07541d0b09200c00b0a50303800740b0103540a44000d660b0640001040c00066182d8508032030340011200340e0300c0e40c5011a114121044125580190704d280030f90014425031000020007060050001e101c8088080303140b0040e0700c80307480f610754611942c0d20b060076094006a101d0700015403060080c0c403142e0411b0860f898490560780212400c480741184040000010320302031141001801d41480d20000d00c12600358514014899406046a4400f00491111140030034000300c9904052880b9143c400c0c0740d560192a107110000d45140d40454446003001c00c0c001c1c101010f03903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 354855008 1250 354853758 354853783
    0xe030306031203040f0212070905010608071b05070303110a170a081b0d09030e040903030902150412020609030f03070803100605030c0a08060a1d06030706050705030f1c0c0e030f 78
    0x8502081c00d070b600300f0042400c7c51340382c0e0016008200001801d10500c0c402c450017094076071036084051415031801415110407203a45c500c00110380031004003240700015140240d030303031608021910785a034262481c07800c8102c00f8000c1c403181400c5d150480d2020450b003e400c41f9455034407000ca6a46034041ea0100403030881c1c0b89491030035000d00140c640e0754441d0300318006c80c0d4064140000992010004103040d15801e1741c1c2074021945511100e0114141f8208801c0c6400e040c6a5090a01e0f0805d180c0010840b02c00d03101138890f800c0440d440000395800d00c00c0e40440c0301e1040032a035944859107020541900100d5010384040102d6000082c100d0044003120321640182c0c960302d1801c3d1903210199840b407405080303603400c012a0709001c1400440218a04840c01d80026a02d08604d050b0302014a001c40390b4205108000d030034041c0b103000401c00026118001c08985005494017103182d01c8644080700c001a030748520341020b588a00032130b046541c0c181e55013030070340c1503540492402c806246c0e208082c00d60f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 354856115 1107 354855008 354855023
    0xa021b0f0d05090109060c0204022b05010602071a030717100f050307120803090a0c12060b0d03081609050402041707060318080f0903010e03030603120304 68
    0x1008501d0092070942e03c1d092031100020036405c498407038802402001c42c00041113666940607100c80c400300441d0071101c0701c01c540c110b420080d8042150307030b84281b0300000458814804100c001c207650059440c0c40c030007030815924000c0c40d48014034510420040480c0c20b00c034050064211030003007441908180074030703080c8450003c8050703a50703028074880c1c3d0250200f0880003040305040c01641d904441c07603940325a11544210705103407a100c1c00030000446030a0108096414442d10069103018840810100030950148000981c424801602040d441c0d00021a103520b048000030f1075072614030700301200756603801c00b00b016a0071a4003c82d41c0446c20b59100d003901c06040007400000d089074503041c40b900c03201c040c5120344800d4286010384850000641a60a042c84408550b1203800c050f008003e4491040301e41503c0c0d401c20398509119003d69104642d1250301e060581340102d412649 = true := by decide +kernel

theorem cover : BRFrame.Cov 354676258 354856115 := by
  have h0 := BRFrame.cov_init 354676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 354676258 ≤ n) (h2 : n < 354856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
