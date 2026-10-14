-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1955
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:17:13.736558+00:00
-- url     : https://prove2.me/submissions/0f80af66-064d-4b1b-842c-bc9ae53202ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 351438848 ≤ n < 351618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 351440098 1250 351438848 351438859
    0x40e0a0213060c02030613021f23191404031202160b1806031b0403030809100506101809020309071a040509180102071502031509010510110c 62
    0x4101080089400a10390001c81c21041052103448030016101140f08540103501a40040001020204482c00c0c881c25103000420810105c68041100c40d84d031500c0519040008100003481d8500f00c0d030084900346440c050b00081406c02c2e4900284001c1e2190481040041003030b045403001c00d041144c0215805580c12a030050040c2040d924082d42d6020040d44460214003940030014560390360318150341140381d41c030321300e000e1510040c001c00095801c00b4040a00040d600c207826190650035000404c02144241c850405601e82070321103c0c200044020480c0c03030f89007000c0800c0310a41d50725115400d051f0b81418540c5071140602000d64000f1029002151590b1000050006560740003c04408841840c00c16013070120a04500441a00952082300e40020f64200400d10b40c402181544180b001098001810300903241c84a00d42d89045001104003e58004180442d4050f03000801080b00d0040d64a200154076003008030ba407042c2201a03190400c01d120190030090340c814801c400340c41034020725 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 351441348 1250 351440098 351440101
    0x50307120213050907020a0b0126011404020a080c0a0509070509040501080309100e0a090e03120403120509010b0f010e19090c030b030a050d0c060605120d080a1512030203040e 77
    0x10782d20054101805081d1003080d024000540c03e80c030018248800030b070301140320050760741307440c0b10621a66500380c0c00030301102c50300d803507620040700034031604050340700001480c401c0342480d005014400d62140c2200889800c010b2a007809074544c2072150b070882c0c4d002d4960341096504e401048a07140110706406911034201000002e10740c20000103490781010895001c0260340c1c0c00d50741919041d0148e6030054200400d502d040060103500d600c85004809503000f940d2401800302c0311040340810849040300071aa205454903014402c9200345503211124800820955036403c00045c01d84001d001c01c80d04003d595041c620440d00c40240c0441911900f410707131441e0303585650a02c0b020f408018010390002c1e140804034041da22f000a00803413081d82003805011001092602141c1c546041c24050300e1031078582a0000d900d4480440c0f04400611090240903a010190002409108080c1000d1089802c0c84481401c0402d400504e07001c07200c5040c54102c3c4502540307400c1c1c0c114007403a40003004a400403030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 351442598 1250 351441348 351441367
    0x2010c060f0e060108010f0b010921140f0d030e0c0d081303030c14010516180b0318060603030414040209150f340605070309060e030c01050f010b09010503071202 71
    0x5030f07681a036100030000d202c0d080811744060225110080010300042c82000200100202c844411000e66405025500e5072480c03a00d40800000c0001c06141090b4002ca00c0075107010030510a54a0000c8145804e1000820b42c0d004a0b6031105210b0406204984601c41c0c0410031050204440220000c107800440789592410043d01119804105440141c0a200750001304041889500d04c40c10500404045a5a0342d540888005150f507400c40010b40da5501c000c80d401503030310051403007010203004403210303510000c8a05040441c007919031070190340103010900107451400d01c00d0510f00c4041c0c90050b1205048000290071115501100403980300028034004100f495200400c2580541c0c00315410007041c12014800ba0742401000c42a90800c80002e000040d031681c010b00e07002002c5e45008240b065803911610708072980d00d03064490640c00000e01d42400324080c014154080811800072103150b1428001000c6c42c03082c441120f040000000004540d41e0145480b1030032041c2c0280115214000c90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 351443848 1250 351442598 351442603
    0x50d1e05130b0105040606170703060317030129040b180901290f07030c050a02090a0e0706020309061204020a0f0e0a06080102190e0a05090a0614010c0308010302010c060f0e 76
    0xc001502c04150642c001304440c10103000c0e04c0c080325030565448d007281d240d203402c1e0881d1035000f4040c01f04042e00e0b060004049612010030411018178600415640c0d4035101c0000c9458a0898001c810036051a0791f07529171034084026541201c6000c50a0380ea1941c80d03006401002d0700c9902195803010304500041041004156140c8050004610742600b022103003040e280c1c2d07801941089141d03210100b00c2d140000b8491001502c03182d1085080780c6003c0d82c1ca40c002040b2441c101e43d02801250350303000545200000304036060040480f800550315041c2c00b034001c0381d01c0d0301c600341d0604000c11101d0041011901c0e449100d2005102d00c24800304104e4603420b40103042641602c400324041d0400c08041914141031085034405180042800200c0800300c0e41507405121030b1301c3c0168800418a070000d5582c03188005984188013181e130024201d81400303100341803400010740319410010701044050000390400b80b401e0649409091060040040d4500700c1c010b000f80310840224141000064007820100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 351445098 1250 351443848 351443881
    0x409060b0d061d01060c0212150610091a0c0c09190f0203060f240d02071a010501050f0d020f0406020307050c01030e1902040e0601080a1b06050d1e05 66
    0x710028040c4540e22200201d00c03603c080000501c1d8039241004220362801090312845491019201d26101040072540b10308012420520300c1c02c0024480400c10a464002c440f401104e51905110031100d04100308003418004510400941e00130000b83c0c0441034070200000c6c100041e00400c50b400e20b181c14035803802c0c81c1d00c0340380c0c0b6115114280740c00d03516880198002d03a8031444e0060586103041851038100042690444100c501c1d00340c14105645c880030402d0020300040c2c0c503550015981d000549029151160445c406900c00c0310b00b00f00521040c0c5c0d20100b2078200c43c28190782c03a5110b10520400e20300900c128118444200400503002401d180c0100c05080098018010748841503e4000194203480151200580940000303032400d04080c5202c2d0051465400540002180d48a42880d00d02e810400c0c1c00c481c10329405505401c080042080056140c142e500003000ba03110329000c0054400e004800d2036079034890b1955520315020414542c845d00310081e05030280310904081c620f22405119 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 351446348 1250 351445098 351445117
    0x120f1204090c08060f040236030f0309010f050703020c0a0e070e03010e190515040f0b07030e060726040c150924050c0f01060e1509061201020409060b 66
    0x2880c840100325400f5240c0d20f40700341c202a04e0f52030211034800400c0300a521181c4055080c6403081c4440c540e108402101c110319a21802c4031283d414440c0d400c062400305005100340490b8010041c100c0c3c0c60340d2001c00c000e00040c0c00c0c200a80c0302c500f01e00e8140d0601144034100d5802c60034181d40018580701080700d403070099400ba200c101408030f5000c145400d072402c950700c0e10308031f0740000340c404040e1070041d020740341d1315020702d00b69076a146800800c8038902c80203440558010f504071510005100c0114000f54011900341401c000741800483c4490706ea107002803121052080148400070408920f0078200000e1442e00780341c140600d80340c6403201d42112a80941e003100740181d059109042d000d0803070701c4161585811102650304007954082915070345161202d080001c140400c41140c0f10803c800c108101508001046c0e660a01c05564400ba0008010b0951107040b0102008651501d1840e1a04400150341194410400740c101d035000e4491681701251032803404c04001001c00c1c908003d001c2841 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 351447598 1250 351446348 351446351
    0x170c010207080318010b030a14150a061e0f05150c060f01092409020c0c06070503071b0b07030807031e050108070909080a1b170a0908030f0405120f120409 68
    0x90504d0001d080320b508104a58150b40b01c03416400105425416142110102104842e482040701415050880050303420307030850342e15090144803010b244801e54490308040320664807501c1c60320304078004034501031007018042d02c00b145685584046407011500c0300805c040403504103040440c0b2254945200741b00d42020a490f06158107107a441b03580401c40001307100e5181000ac1828500008020340c8100031038490741c070584044600940b2420040c0c10b1440c002c0b40650b4a403169802c0a01240a110600503043c0607080303400d210810b00c0c0340640e503400b074141c07030440c0107540e640409170000c00400103580200007118102c80303566030342d030f420260589121900740d4001c03aa0b6110804240d03400c508000313140c2e401c20311100002503c030741c03441e400c8a05849076204008105466040b40b0000d100314511134414001050840207401a201c0001005139100843c034000f903200b00c0554900440c00351911a182e924402c80300d14200b08001507440786d5482c1a209481c1c248003440c202d82d0710032f105003400d89 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 351448848 1250 351447598 351447631
    0x40e0117060a0e1518060702031905031303030903020109080c01150e0402010e100912030815010905090a0c05090411090102151608040503130e060a21170c0102070803 73
    0x50b452400b4907850b40c00c180c00104081200102d951a0002e4001d0078000020140f0b04010f65408040105e580503400940196582e40114644201c0700a0040c0c0300b2030911404100b0b201549034034400002841e5054540000d12011038030f02240035010820006e03042440c007161485100c041940b00d83d80c980c80d40110080420303a120841102c5d03000861b40a030101d841c200841983d13052218001c0c50036901403810944044d00c500d60303412a07004105044d40043c69600030007072040a007c1d44080c2c3d22400342080c1603010728200016880070401048410343c55201c83c5030406041c0036a003941d11050000b041031092511454180301103411241c0b041e401449112141c002c2900c50400047c01078115019150206025000a40e02d4901c080c0085481d80b208016045003580140301c0c58000d0490b1804454060801800300449004241c2000c0c0110240484128400c6460f80e049909140e2021b041c2030125009040e10107035000e2040001000e50000610b00c00b00100c48004600c0341c1003041c450100d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 351450098 1250 351448848 351448861
    0x405030d02061e07110d03050a05092a010e040e030c0114150120030c010b09070306140d0503040f09020706050c04140d1e08070b1f170102040e011706 66
    0x241c4000741c40920074400382e14941124919850f03000c507448035040c01d00f8480c0040d180c4007140780401c01c20701500000da80c1c03410700a00d86414001d50390006402c00041c0003240514581c03c02402809140c607010220711810a907a50340526400211100700030010450702d070030329080c02c0e2254444141412594a041381c210380e0b1303082c640ca1750781c00742170608001c543d8046840015540000d03216545c0151300c0c060800d9030180785042000705142c00303801e0008201307000d0120500486403c06030029042c107082c00e00c10710002102c100083d103014800c40310f03d11f0541d80c82c01c242d400e502c1150804040c820100c080072403c204280c005020041c4290301c1004140d60701e408a822601a42c001d48070140300d20003c01030580b4082c0c2001d55494001c0c0083c0b40140360342c49800b080b100b1081c008841004002c20650140022a098180d0080e69040d950703200f0022030103400130203100341c014100c20380110602101845000d6050303030098200b04c0301d078140c0740d40c407202080d01c2d00d8005040303501c1c40c0c0b188100041c3c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 351451348 1250 351450098 351450103
    0xe01110c07080c030109080d0207020d06050a1b0e0d060b0f030105180d030c0e0f040f02160201120504051e0304080105151905031b06130e180105090601121a0c0405030d02 75
    0x181c01c03c440504023241404200069031001d18140c1c1c1c00780e409001030001c5070840c4120303400765441100004502000c0344140154039007c100000c1801051940a80306441d81c400701c09103240e000c440021452902c07400500c503596840d0000d41c041d882c0008111a0240d0802c06081250740c6104584458641441c12003c0d180c0b00e840c6540000c0030040d01050604140c5040601e261700200007054000b56a41001c040b030304800078890301265280866019540c00a006190324441c1d0101031120340f403d512060b80d50079072083c1c1540042c0305241e4407100d1580a10a4030b0282070040300a000e1411b142c80b50300312030b4a0f1803244911034400c01d0010b48960041d01001c03400c42d0300143c040c1c1a5140c9454028170007051010b070141c1c001c0740030403500310702e04007502290001e00150494030000b8200017010800d0340c890048010a981c0c94001842810800012040d04440c441d440070307218040f107858141400707140c2c03641e20000c0354081d605109018480070050016180260110784540501c00d000f283d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 351452598 1250 351451348 351451361
    0x70602160303140c0a09060813050d03020a09050420070305070c03051501050603040506070f02070b1903181e06060312020a0b0703020f030103020d0201030603021012060501090b09040e01110c07080c0301 89
    0x7000c1040c0c6801041a507015159860384003104c048009d5500c60a5120300d82403110351040c503c0004c1d4005000b1030384942012041c00a03000913102041480030701d0007440d07071500420501d01042d200105440c0c04061080c41202c11540c0c1c4040e03010066a503078609661390741030040003c41061842c01c00494142000c80560b80700d0358000c002407000d81c4a0710750170703a06100030881c00803c6000e2070300003080d00785607080140228031505d4143c01001c0000c000080883e0040f080c400c51052003101c8400110f03030300241c62061a4001d00b282c8240765118540100100802d5200030500320070302420303d2446801007010031410307000d425040d400342d8806004900300d1081070341011403020140010300140c00c0541c9071145152060400066003500da80020710039030f84200d1510000313640021000041c0115002e1078005004c00e08194124a080803070724007041c00384c2545a8002d03966131086881000094102a082c07407024800599a405403441c015100c414900600c0c03050700c6503e142018a0405103d0903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 351453848 1250 351452598 351452617
    0x206040e0a0b06070f020d3206071814010e0406090504020102250b0c210307110111030105010c061508010903030b030a0c0303080c090319030e010e15070602160303140c 74
    0xe00b0403810340c02c0050000012106031141c00c0c41c400b00c81c0398182600b502200c07230318900005000307103852181c002d80780c5800200350b1340400884525542100b294400c01c0410344207500302d14400c0058201c0101c60800540c0b080342d40c031038142074000604050300d90099001c0e9000b0703400d440da03170b05845540d42041c00650011020a202da8402085814111006860304891000a07a4441440e01504502c244200c0880401d01840001406441364022030700e0b20002003010003c0c80427444c2400024180d01051252a042c00744040d1820300f0403242d42d2122030140b00589200c1c400c1d60301c50341c0300c0d8024900c403d001c402013441c0c6551001c071480c0024070980400ea01641454559084d5030382140c0c40d41015144880d01070003408a000195030038020413400c504d04842c4a0300a034403908000f03100482030741d261130600140c040002c0c0740b82c5403011480070340001e495500d540c52146103001c1000b441071065100210140b44408810903515422100c031314401400f45515503202c1c48070300a0380f0310412590 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 351455098 1250 351453848 351453863
    0x11515030207030c050102042601050906070309060e010524040207050c010e030a0b0702060a0f0c0207050f01020c0d0c0e0108060906191107061b051c09050a0206040e0a0b0607 77
    0x42210a2198005001c95486840e007021100341641d110f40c01e80e0003903005511b03459050040000420010114030320040d01c0340009000c50b00b410341c400b42e11900050465010952103440030818030440750030a044d1003100364000c115500c0e1543c11405140e5114540c2010084000713040c5a5910346402554043d0b50000050300b08416410019650004038042c41034050040f10781850114100c064001d1150402d0b030060201803404621001c22520000e83e01c1582c3c514002603040780c194005410404d40b801680c800081904201c01030380703000c1819030340b10350041d0300c4841481004402c40c0003100300e03501e501a400090740c840320b0f43d64071194112192140780e844180090005d240000e691410880100f0000651400d8104d1810041d400b109080c1c44250f2243c07480d4516680e10050b07440d00d000c841c680b05003802c1c6800c020b400f244036804800f8000907203d001140130700c042449003400c481d030300070f1840350ba450b510180b0054000c021121069a141740401881444c02c001048840300d41c0d00c0440d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 351456348 1250 351455098 351455129
    0xb06040504021e0c06040b13050c090601110d030207021002070303080a0f0b0a0e1005090112030c230f01110405010c08031003050f1515030303010b031b0a110115 71
    0x510009400c106459440703030103030f0790f002082c400140009002d8440c8000c0075141515003800c000c49071402c094500360400800c5074680000c6000400d540b180340700112620300c0c581e00d4540040352030107401d080c4011f0500a607140503050725011350041203920f1084c0c0311000302808040081e6182d40541c0300280c045000788001030010170655201c03000c2c85100308030000342144140003040046580703410a40000040740d06000e100000035449400401e0f04940e056910360420703002c1c1b4450303500480c0080a10141466680c00c121058002c0003107504000808440480e4000019682e111081c44100c00c075460802c03003400303c07115034080703d05464042e1141034018240317a48c4c07010300350302c02002c04501c45800c42001c0001b030303010320060780500a441c0040c88070181681d07000c901d040c400382c098a881c0c2c4010300114065100841074a04668105180c40d403240d456194000e8900c102c5015540345200001d01d006400e41c100d240d07100d40c0082d0b41c0080008013406071400344404101c0c094040b440b0444e01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 351457598 1250 351456348 351456359
    0x2130f230c1e0c030d06240f0e01090306110306100203090319080903010f020306120303010e040204091e0501020406080906040c03110f0a030c080c03061e04033f0b0604 74
    0xd20a01195100500c181d14010300101901d06641003185d001e080c254031044108490440042c580c7c5d0f65a054220000301c4248803c0b018002403188282032003481400c040d0242503078000c030350079402035400000500116a0f9078050a0b070950088820f0b80c03041d0000c4600d48220307031001065401501000c1c004200360030402c80c04c4c2c8072280c0c503010308880a42c020030402c0799980302802440410341c0c144c2800740e00c0e82090b0f41003001e001480d44d41010590f00a02c0100442080700ea0800e4006c0d805031800074110303846040280d0081074299229007200d15010f104020424158014001c85109613140c0000340c075080f0f000c540700c50b070aa40c0a80707095000002800401c0c2c11102c41c4960030f200409616001d51040086100350540d03a005441480401f00c0400100d1000e2040d0314803004201c0251581e880d1003d80711170780c42080c1c440f00701624400390000701003500460620341845050ba0080d1403507400380085821048a080c0042e03585061495118114141390140c51031400c0003d115078102030409 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 351458848 1250 351457598 351457627
    0x9020307031b1b2d030909020f12100b04170c0108010b031801021b0c0a0b1201171203180106050609180c07060c0207080106050f06031302130f230c 65
    0x340d00b41c0f20035903010030194072559500c04c800710300004030300900321407202c0d801c001c0c1804100f40c1c80948400e004100d940310744a0100100c0d076004801c00040030940d110381102d184107518a0704001500900002c004c501404c0e03070803419100c51200c104403800b0082e914011600c008080c482c640128400b8804100524034901d8071141104a1000060074100303d406003203500e000d07000c6c9e12012900b00e0003010045080500020000d40b01d1001c2e0289411114034010304140710501c10305021b1000344807550a40340c014061800c020705400e9842e0f0300ea040000400d24100d44042802c1e081e0b610301480041c1a003450f0065600d03c803802040c10000d00400a600c3c0710b18200104a501080001c1002d4400521984107541000651b980144042810001442d0845255802040c4241d003d200c150346581d41d12000c50354011011820000c86100f82e01c0800c00c1a50b036844408410350a018805685245a03841000600484920300c0060307a005082d0803d40388060f5100400c03900c0403c80207080c80040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 351460098 1250 351458848 351458897
    0x90102070c0e1f0b0405040b0d06061401031505030d110a08030a0b040c0c03080c1b060f04121107140301022b0c08060d020418060507020303010e0c09010903020118030c09020307031b 80
    0x9e008119041c050b070f07880c407044403001e402604551100c200318210030b5a0500c43c070840ea0070054081c000540c149400607582c0c5040900c46030420500340c00b0085020010301905030240e5000180c5512030911002c07010107044010401c9014615200640300400d109000d152480d54154643c3c0045460ba0284c03120705600400f049046070341600041d07561004200507042c8125002c003120903850425151244420740076000c1380c0108201041152400314011454400b110f170303803203071410610001c040801e004e4007818510f45a9031056544881c108415070a2a806468032120200b10401d0f40306029500c1050907201540c225a00f40000401800d1680c4200d145c0d40c0500101444040550745000560703a08880b10001a0000f0004100c40c00c904000c40d81c02040301082d940c1084548800240399400c10310000c2e04000f156000c46190343d42c51091803000d0354014004a0445440f140144040e44c005e83d02200000d150106917421a010f8003201c52044069903505a00303c000041c03001080c040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 351461348 1250 351460098 351460121
    0x6051305060c1206030f07060c0606052707030c0509040b031f06061407080a030506120106060c02031509070e04060f020c0105040c08160509090102070c0e1f0b040504 73
    0x2154500000c2502000201d108192404240d80d8800f1203042c1d4200101001d0034060091b80403440701045814041404c406450591605001229071410b00001510030740c1c4c00103820503c1150000c602c4009003a04a60406502440c07844646407110124220703610581100c0c0084c0c030a2222850901d070a42100c0c80082004040701c02480e0001c0c0040300c2e48509814420500c0d58030401007211580001500e981c0c164200764a82c00c00c24070b0784590106100c1c2d941604c04150707480000881555035101d2180124028200070040389843d050003600c10036103403005030b12070f20825002600311040c4160b198440c88000000d41201442e04166050700308000c0c02c01c80700c00352501d03035100c0c0d446800e10103030010b40c3c010000400c1d142041d09101c8815210340d00848986d401c19080c4111101184000901300c580c02d94000c0340d96a2003e00340c500900800740020140001e01400003001c1d075009168501034040c52070031110111254203a030f0201007440c0b244007000b020501c402c210914059011002490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 351462598 1250 351461348 351461371
    0x90a030f0611160c06050301140d06110c010608012a0503150d0b01031109090303070c0503041e0501110a0209010312050c0601080f0c010201050f01150903050d031b0c0209040605 78
    0x200c04034000c403841d400c403005500e48018007840c0700d414051203a006000034181424038501d194104100d03145001c211162080c0211112b0341904200b00c0a940409003501c40380d010691103143c20305805010b411584500d817580d41c01c0625003080110040700e0000d51140110032318540f10a6041e00740c0386500020031a0b0703809101c40040e0002500c075410038501e001d20807424080c2070341c194544900ca008008900701c1c0220001070030414002d0000084036002491810044074032140c07883c2003465807050790130013041c0011440004100c14002e000500903141d090300c41c1c0724105240d401890b40d904016001a500849c80801003022a0586c9001c42e10301d0387d246030451515290010032803a091007a4890a1a0740c0f2007803000441d050148280705c242e20f0240300a10540c1852000f441050170180503606c0c0103140d0402d2400d14500403040030000316404026200134484108015000303296640d880d0040e2400b6903171320410759200c0c00000360346c1507004002140c1600d960303d40c2c10051000a000c443c400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 351463848 1250 351462598 351462611
    0xb031e0114090714070c15050a080c032a04080c150f03060d02040e070303080c0702030303040605060105070c06030e0606010c120c05010e07030809180f0c07031704050c040c05090a030f06 82
    0x3010b0304c000814016000361140d4284a28060540900481c9240301c101000310610102140a901884e055007044411a100d91251210b0340b826107600003252055a09414807145075480d4544031f8043d01c1220030800a46076080760140c20312007901190300c4040036540042020a9840c2403030000395401290281210022140d030f540440e0490350018103c41c0350350b00489040041585c00000c142c1e01402d203009880c1815155400300b036490002420040501c1c0d101d00c005142c42c1d10034812380e080a600841c400f80322558030040a030080c80079500154250080c440001c049500444103402d1040d8000000300811030080c10071680c40b41401d0782161380d9503c49145400c40241004020041c600071100e0941e50041e83c000c10884072010300f1a9540d400358a405c01243c0802c0003403450b80310b554002c99503560341311071604841c0380058068050000905000384800e100c000a01d00b800d12100759402c005442500d84141c415011f070100c42d075840070302d485080c000200c981c184c85803201c0c8985004102c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 351465098 1250 351463848 351463877
    0x60403051c03090b13050601050a05060703110a021f090b0306090a0e07150e040515030706120e06010e0a050604150b0a11060c07030207210b04110a0b031e01140907 72
    0x1031303003401d0f0b0300302c20584100b03d0040180b110a200250050004603a400002450107000c200345008080c0701900380440c42107c000040420700140c1d00c0d55500030041c00000850380d40c00310b14021b031401c50500141c039008010610120b0101181d005d01401020f84555035034030301007030000d00345542c08400b40d8003c003e40015107075401a45410340d405561503a0118007010024002201d60040110b2901c5480911000950304d012959000703176a1640b0300160340c2d81030148004040e210a1046810074407903032000080f40001401814007640714080140b09039141e1038204010380b0201d088020801043c0d410030400b12003214010a80d501d0741d0308003d00b8402a00c03500d607050800c11150f07840c1509002078003100300750781402140702609035403491170b1219064140d41d64a000c0700c401d008140d00700340d00c085403e11070141c1c0c090301c01003c028603041055403141c2c809111070300182c40710350445c000e6000000700358450a4210381601c024407545143c50900c41c1c1000081c14002d40342c0c4082c017029034140f030b42 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 351466348 1250 351465098 351465113
    0x1502030403210f180c0b130f0e040b130b36010c02070b030106080703020f04050931050a1112150403090b0f0d09020303090a23060403051c0309 63
    0x2042000c100c2e000a01104200a010a4840d200d10558801c81450528000038808020f0a01500e801c480c90701d4850078031811500d000302064009048007090100300050318180d280b81c0e5841075120b400400003940340c5000a00d40d01101c200024905040c5800051040c842006c11015217000184003140c492050810300c8041e4868070380201807a51500c4640030783e6901040458020901280d10340d280d5890980000d2095002074450010150001a850015854401a075001e0040103004006505110b020300c41e2003820002d50741107403c4404501540503003841d80f082c4010b904a005400b01126654a1551510807243c03904da029010340030001504108106000c0e0410300c0c04000b1085040504024180c059640e2056111000810402c0507200d640c01c00d86075500000c25010880c0185440042d0a50044400c55034000c01c0d0a1000140f03007900000ba0800c5080d0804101040150741081c4a124802c80c00081d00710350100d0b214410a0701d04821080301100549000101c2d00560380d64600b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 351467598 1250 351466348 351466397
    0x30403021504020102011d01021b06040c0306110f0c0105060108091906022d03090f0601060c1415070c020a051c02210307030f08060f013c170708041502030403 70
    0x147ea07a5001c295609071000c0000d1500440704240c00510040c41c5c00e0362444460703040f60000904150b02d0701c06c1c0001070085c00081d01e072120041c28107151981021214a0300900e01224180c0c0001c5040b8085001200e020440c1d40381d1452072954900070100d43d49070140694403c5a101c90301816090803c43c0c009000c01c5071a9960000041403503a0341818180540b40000b400d01c209041d030002ca004012641d00a0b0540ba115548403070b50211aa5440c1074590410442c04602501d081960003000104c50784100f5810020380700311034400d1084d8540052000b500f490030080032110442e02400409454155000c80d030035011164405003030101400c4d400c1c21a0410001140410b4a10800d81da07015000104103501140560726030080301c1c02100000c2c02e40d540c2c003209200c80709003d014207004c3d40e00c00c000080d00c00040000c00d5108100361b0801403581a120007412603000b01c200100b030707e452080445900440d000b007030f861050140508154025480a001202803048809141c600704015a0200c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 351468848 1250 351467598 351467651
    0x80d02092815030203010f1a160c051306080c010818010204080705010305090c03071e05091509011a03010513020c010c090509090a051203041b230603040302150402010201 75
    0x107149161401c60904000e100c81c0c0760b420305006000500000d50304074000800c494645202c00c0c90301d010301100808610504602042e03600c1144030b200c0901c03040c1101c003000c1399400e5035480d0302d42425154400440761280501c0d9000d03040440c0d02080b540c420b40040360071246820024240540e00303000c07142240e0003580203003400e80000c0401c1140f580c05201d600c0d44501044045d010004002e00042c1d11400c040c0142401d42643d40300c8031043c01c0c03804801402030007024042d00e0007410064803030b03000205070003031540c42005910008100c3e031f90101244d8454200e1041e015045900344401c2150b9503000c4540071403603c0d030034440400010b00134016110102c5a540724111418245002d002c01c0c0c00c0000c0c60510b20381c0c4020b0b1101c0026400080c2120607010404420b5103030b03107031031400580212289240c01c01c2c8004007000491440d81d0ba40c04c0101c405c1407504205007040004050100e1800120790242c0907802c60011722100c10703514011240c4c050300c140700000c0c1d843d00c00d444141c00c0c10643d1002d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 351470098 1250 351468848 351468919
    0x41b0b040303170604140f180109240603030c2603012310170a061a0c01140402220b060c1b060414060705030409090f1b03080d0209 58
    0x1e58003d03041040f11604101c00356400e00a02448411039802e016014011207980e50603200002ca04040014440508440c01c10092007040d62501b406009800c0e203401c1440300100e0f0b02140032007101688141c07011250301d61a0645070403c40e031074014035105410203910007001001d86508403148000025406000b40601d503110402600c080b00c0e010028411001d401055461141c44809820610410300c0b00e01940d04101580e80c2c0ca003a560240c407041e07102c485c0000303582c6901d1700749a881d04040d00b403592050008000581210115081c0e2040907980603421000e189450041c07084c80c0c0583c07410541d444100070412040c84d50205146510402e00c642a0781c03c410360b005081c02c0003180d0441415000c9440728145410f00c2070300c031100304020105034400d00001850741c0c1000b0b801e00554005207100c020400607401c003810f00c2d1517410740085003180c44901501c1c01030464420b5004090589400032422400c141c0503400e03c000960080c5c0d5404d500254800c5070040c038540700c83c01d084440401c0301d40d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 351471348 1250 351470098 351470117
    0x5060d0b030618060907080c10110102030108012a0906080903190206010f08120d15031e2108070e18090a0606080a1104020d180b160c020108041b0b040303 68
    0x1c0f038509012000e400c0019a8101c5841006805400125a130003a01c044a4010081d40c0c8014180e80805100c60074000e1540007100000381c001c41981704038842903160b1300c4220810103000c3ca003040c8403034200341040422009681440690311440e4484d6000c03404404503481d00302c90608034106000e1890000005a0008006014405410500100408119000309104146d00d4812284ca028085446c142035954810641071007608060364001581c005080540611340c1044042d58800d01030000c0e503a0720341c0240c1c5001725165000444111035680d9680f134155441e0400700b220f03038004920b80150702004000300f00c490916182d030807034014202c500040400003035503e068800ea4007140d225421503041321304e148010a00048800003420401c031401603894046848000c010000311541c20481000c0b001201d00300a042a0f40d140143c0400303111060312016082d0840d002100d56030000e0004038041c0214000507040600c14642c860200b080c0c81350140c50f0040d560403500258030a0340050550203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 351472598 1250 351471348 351471391
    0x4060b120304050901150c12050403031409010827030a0302030a051803030a020d1e0f05090106260c0916030b010216140a03050304060302120c1305060d0b0306 70
    0x100900c0c010306200051810a07280c4070000f010080c0510401801c100032581c020395251203400c0c0c0d10000c0c1ea1200d078003940710300c480c035006040750081c1c0021000f040000c0c04141d844600d0005503000403405a5070a81c140c2d40e01c0c420450200c011442085004054071000388401c0d00500103401c0c0c400702c0e80d900580340c1c5860944442503600103007034002d4440b80300d151205e056401004a075070048400c0000743c0c1e40c00030040748000a1022520a60031044000446d0b00d011135942c012120418908000b400f464039803034040c50894265215a0700e417004400804c0c1e56204d402c91007005180200401d907440024194040740d012001284ca0643d441000440e610f090f60b0035104429080b0005c1c40208607403072039100d1460403511076004a8605034405611804d82d69a51030444002c0d5600c00c040e00d807199502c0c100900070b50005076007000343c0500c03800010000e0040e4410780b00011031100444990328a8035040c00450380c0308820042c48240c07260314004503074a080084c14014424114500c1c3d0b100080d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 351473848 1250 351472598 351472609
    0x15050c161419050d12050c070f0302030d030b010504050f0103090525090e1209040b030a12091a0f0a1209110f030303040201090510020a0501050915090a17031e04060b 73
    0x150594100c000c01d50310a00898030303004942c10035103502a468405e618120803094415006034400d10309580315040c030200d065400d1a801408a0b8400d500301e0703007001c49002041c1d00f41c400740144c082c0003802c140020031452410344004003d601041c100010426101d403a41800c103100c442c803628420140c0f9141c28449039007100070000410201604104a03000104802e03221100c2010303010381e941d802b2039005540d595560180c001c0e03c80c01421208400118a014111040001e0700400445c030030441c00214400705440c0c00e038081c03441c18181e5140c40f642400803000c0381c200700700c40d208204510b1016040c080c40f074070030140c52a00503c210301d4400c040d00100712014401e500b60318001d420500c140401070b41c0100016080e01d000310342074002207415280807440c100110202514035803c100a1240641c0042450902d07801d0175452003038269280301c0015030b502c51100004080301c1c83d440c08001c00998075805035801c415002480728944d02c0b20300803641c0460742542d081d20210380d0764200214a00d0301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 351475098 1250 351473848 351473869
    0x90a0902040b0a090807140d11040c02101b0905090a1107110a050409150b0310110d0e0303010303080a05072c090a0e0c1e061306021615050c1614 64
    0x208024071460f800c7c400a40c42c80c94580007005d0080c040c01940404000c000640c6210707807000504104244c1007041130003503441044034084604035140005910507a0b1203800422070224254a85600740c80c5041c003400403c50b001024400001d40d80d10803114807812100041c0a25401100d4035038484195000304800409243e1103544601e10302284d581c0041c2c01036040790300030382c14000005040c2d80b00c900401d0a0220050301801120b01e00035590403040011030190000b200002400c11028014965055492100303001c09800308107100009401040a5000907900035103900d407501c82c0c00740f2064400034001001513207003035003055641082068141800366039400904004140420038004540e280c981101d0b051480c050310030780002000c040540c4881c2200343c10081c2020b07075074003a44000508540d940c1c0c011007005000742c1b40b541c0207142c1800202c0c41543c500c088041ca49000e40901032321590b000000c61a414018294090780510800501100410114083c0104000c0400c00c000c9040340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 351476348 1250 351475098 351475109
    0x30f041a130806010911090d060216290c070803060d0615060903050c0a0501050901030b030316060905060703050405060708071b1110090b071e080d0603030f0e15090a0902040b0a09 79
    0x1000d0151001c6503850070700d01003208d80c2000c3c1c016501c510503000d0309064044102d0290514210076030701c040350101c1602d40c1541e428440300c8000343e42c40350f000219070307841074640207480388030300b4030104445180480d01c1c2180680701e0580029128030000000f07130846015440b14010131200f00c03003041030050030311030204070750400c580d8122a5400c060020303201c1c1c0a0f464080d810550744400c00303482030b1002c0080710381407601400f03004104100d070b16012000d4030020303404550074000c1201142400d07001e8090708e40600e500101414040d41c42c00c000f1101d260001740b18800f00b0440420784041101880d4034400350b0390003241d084c1003908000c801d000001100b822a0320410030541001c100e214030407400d4420701c070351003144140e03241182900b0025040b00a0000740c00000002040c642030000c0358402402c9a00c00c1d1148880c00000c11001d8540d5840340c0003481d00310021544a101c016003100045c00c006500802c140111034907410f41070300301d8204d5000100c5050001a14000c1e058202408070024813 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 351477598 1250 351476348 351476381
    0x2010b010c15020d060b0a1b0c15090306020309010b03010501060c08031f080d02060601030c03050f0f041b03061a0301061d060409020d0302030d0e030f041a1308060109 74
    0x1460000028140c580180c405005505000011111036425030116030070400240b0042c04180e0300c07030401101c01d50040e0550008200c160000907550860442100d03017181c1c008458010451504001c02801121100c94a0402c942c6481c040009107035807010b94000d01201b4000503007150301c0d0040c14212003045c1c00981c14081002a60300000e0500b004695000c101c2108192105103010104506038001e034000c90521701455043c80109a800914140700c0d0100340e030140921900d03100103400300c3c1e600b80c0d44414034000c1003000070118500c403840280c000384070340c0c03003402c9202c815003205895544c560001c4a6854681c081941c442c05800c60400303038501e084008100b0540380107402c0e01c064181d450001c03000f6151400003500c039907031a1300c00941e50782c0140c40003a5628540c5002500c07940722001c51030a2901c2c0803101c550080000059560f0309020a02480c03a280c103140c5522843c008091184041000400c00c03000742041c000305800080420000410155041ca00301600303850304086016071300e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 351478848 1250 351477598 351477611
    0x603010b010e0d030c05120724150603200408070602010b060309060f040f020402070602030703050a0920040b03011802031905120c0a0c0b1b03030f0622090b07030501060201 76
    0x95a0b40000d40f883c00e98181005078801020345021824425103c01d4070800190119021082c40400c0751400f0058100789440001d08441c24190412168107941c40029041400c506100a038041e51160700a00c9121044603c400d84000010f032559005421504d07040e0844041000340980901036007460001c00c03a17a4600718540105915a04d0800403d42d02034541003501081c180218040345502041e0050002c1d503035a101810884041d60050f2241000203244c0800608c2e455410302ca003620442c0c0c045052810301e1005c84c205080008030140b000e5010b55070b8400d01c880769500b40b10b041c1003130350152603269441131a030040500304aa159204c0041e400c01c0c55244001880202d4040403032410b0b8106ca40e1200b2060072040c0c6048690b040050012480c400d002c105941c0d014084d00485014400b080071860400c6005512030105807858866808e0b4140405c480e89010f050b0207040c004000448141c050071583c0e4402501e034010400d4071040c04400a1182da00d0345401781c180034000d14002031006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 351480098 1250 351478848 351478877
    0x6010618060c0b0609130503030c180916050a092c0c031302010518040e0a051c020715020a0b0a05010608060d05030313060b12070f0e010806070509030c06120603010b01 74
    0x6140c0061166110b02010700c0081d0400740d0b04031401800a403c4800c0723a40b40c1c5080c4010342c50a50080000980d003580e42645001d0314a0710300c1a044c4641780007418424107050305a015a02900a00201820311a0764000450382c6180300540d18080621685255040604d040c940c94101d4006854800050010020000f81801280b81d00e10415420710b8015034805181c1624030f1a0750070b98003a29442401c0020610030150000740e480f1105004400782c0325541c150b40c42242d002302e5200400c00140e00185d8081003d080b41c0030180b41030401c54010317100d070b0a0350b9559000c400d881c202c5180794503a41e14401440b40c0d5510003442944910261750324004d801450321000d03a6030200401886084123122800c0d0200800c0c0c0c0c01070a0700d154003424130280c0d2040c4600d45522809140035042d03010b400ca02c0001107026010102504860400d401f4015075200d805080b5a642c0c01180c040b0380522030380009042d5921124001c10426400300ca0074000c6040207410103096869142d50340e8100b100c3c81410405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 351481348 1250 351480098 351480113
    0xa050316180903270504050114090c0a02072c040b090709060609050d020d020301110c12090d14150109020c0d09050f0f030a02031207020901061b0602180306010618060c 74
    0x3003181c5400948000d040d001d00181300c0c4581150441d0790881d080c5000041d00788488626505241c0084440380590743d40c074407002d00303e40582000308006a002600800c41e8403c1c1028070a1040003500c034030f00308001d1648150581c150107840c102c0d000b9044104200c02c13001e003440010050481080c00340640303450110014140d44c0d10b801020f1141820151400842d0b4440680a61903a800b400078069042e86990500d40c64000001c4814a800307010b1000d8196060340040783d504020041011000e0509500c0d0007a0425115841194500c51040320b03459015406080340c0c0200002000581d90310003020031a828000c050701d5150078094402e00512a45d0307200c02801403506819100302050400500010b468400b400384040c0d00740c00b40c142160b400c40d00700703002406118002c7d1017000099aa40800f200e64441d5000340e50707440065401c0c0100087c02c5600200210208800030aa0201403000003c0c01c0c000281e000802040014000700b54103114060280001c00d801e05154400c410213845280 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 351482598 1250 351481348 351481367
    0x60303040b0d180b06010306141507021c1b050103020304030f080703020f1c0b060309070303080c0c0d020a031d0d11040e07060302040801060902030705090409020a050316180903 78
    0x201c426001242c1c10301010410b512202018002c3c4401425003000b81c10300c40c80640c0240c441c2800603080180c0400c540c20b001141701d110b40350140c01006207160151b10004140c103e004202c0c0e101c03d0228a041401441c0c1103809040c5004644511300c550b45c1c42c416030400005540005c1c1818014410000804c1e00204110b00e414042d040103584bd42d04c520007240244504410102100c0d408100d500010342c0160004102c91811035040215142c00b804201a500046400101c0359004d200140300007071080341c00d25081028241b8890400c02c100a00d00e00782945081040010f910071942c42d800c2c03651090008000c01054855840981805c0020030640540000050110825125565000c1c0c85580c4610710607090b0b06d083e1507143d500c950707008000e03600034420b1506641c04d200d004550b4041c00c1c803c49002c0c5649460341d81c0742011000070300002d03180107007040e640081041800201618280300702d11000311140e00009601d802d046603121a001100100400c0341d182c4100080060f41160412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 351483848 1250 351482598 351482609
    0x2060a0506130903030501150201150b071a0414010b0906010c0b060a08151509060904060906090b070f1115060d0c15120f110313050a060c020307020307060806030304 73
    0x49001d5484078042400500301030b4044201501c0c0c5011a400d141d450f85c069410386000304081ca01800303403901d080342628001e0101700d8005002100400c0304175040c00c0182901881340198020000c0d0180e00c04921750700c1140c040d0b5409400102103d03080b02c0a00c200441d0800c2144c0110040c113005c1c0009080320398001c0024000d00305031003c140140e50741c0340d0000c0100003e400325441040228087d980201054611854011207100522018500305824500c00d010103404801c0565450b06c440d0b024023195042070b01c0d020361ba070f2040800310760381d138103917030f104441035103030500780141d8800001e00340c031259010001030350040502088070380001c00b003580d000002100d09100401d06810022800a15036008441c0710f01110300c0b140f01c0ca0303049000c0c4044200c06d14010400480c40e800039005480703910b03107030500b9003404000150350000c4c14480b502e146030040003140c18400066640d9411603030180501e2003d0307071000c20f0303c0702107180821005018080524040d0040e003403141c0030076540d00950050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 351485098 1250 351483848 351483851
    0x1140f07050312010306140906150d230105101a0703080c0d150320011e021006030b0636070c02060a23040b1602190e0703060603090302060a 62
    0x110038070004000792a101245044600001e580d01d251140090408100110311050b00100040360311001298181c03080c54038000e50215601d07100100b06a03000401c004035012203111803141c0f0b03004001d42500300c000c26928000540da08142013041444641ca0742706528a98400081d814080c1d000010b59a215034181401040385d01e803e014180903018104140c490b2919000701e0134243c6442441741e9045a0041e072181090b6426070300580e80354246003102d9404102d903601d5814010441c91800012240907106580b42007102400280130b8412070303881518440c0c1503605110a42c58030045a45403102441c00c120340c04108018854508030180c1c4212180c1611100040e001c0c6015949002000703900819407643c1d10901200901003e465008946110203030a006000924691044500340d802007010316042802d0001c0d03c50b40f01018210807038110480c3c0c20420740162110745104090318400000086d20324144d00c0083c1183c41c10f80c804410181010725080100781c0111b070701a000400d4090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 351486348 1250 351485098 351485107
    0xb1c06150302100905040b01080f162705030c030613030c020307050a030305030f090c010c150b030a0804080f030703090902030403030e30070209011710110c010b01140f 74
    0x2a44548000d1503002940200c031a40390a03103540e9100c04400107581c0304075010050b50014000444098004840141d1a043c5120204d0011607007980040300e2001c240c6080c0c034800c0360180030b00e40c0d460004541525040d40b58201440307103240078011402103413402d600521940c5040ca504200c880c4480030050180805919118103645040c00034002030880600345a445d2560b920f0005c0c4a0740c42150018a080368500210301e00683c08641401210030503551185030207030540354808166500c0081b1040956a00c28200c510746080c040901a00c3c01115002d40302e92030112040d00301200148a6100b40d0801c10880001981042411040e0b44801c40016100d690754a003d900030a02e10320803825501c1103202e00c440c0c48212004100120002590034041c1700c4d080c040380e80351402070b00c81c020741c0604003000502201036408401c90b10040a20101c2c1d00e075819948001c1c0840d8512441c1030f9007280c0000362046262024007907120003000c02c0ca8886116141c108003503440340219841508103120008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 351487598 1250 351486348 351486371
    0x1211030601080703110f0928140a0806040507080f0601060206011203020139090812070f15020307090e070c0201050c07051c030201050c130e070c0605190b1c06 70
    0xe105c840b0b0044908160f65030340000d00140078887e00301e545076a201d5101c01c5040790102190000300e007542c903100d03942c80311124141044061602c110244072604070706803210004050a04200840c080ca0003a4007030222241444062418840b000c2d82c0d05007940c0c44100100201c41c4d00181c4941103a4841ca40c2543d00c000600d022405018900c04000c0310a010610000b100f0020000c603014016413400129245500440181c80c0340745280b06000b950307000114040281c443c0400200941072040c051a80300720708941c1c4007130881c0345418400090907408801c200129400001c40c03006441071104014842c0303407280c4000c1540c40c84c0c03c0001e04010021600d2201d40e0700809c40b0502a000042c83c440d40c030003058080c003806080400c1c00b03800560030b02002c1140078001c10215500c0d01414801d01c0803850400181d4020040054a4071040060042c00c6c04041000da20a403070103a4021505400c072407003e1010301c0150340811001d14070800b003503030710300442c21485911400c20390341c0040049034004c900c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 351488848 1250 351487598 351487601
    0x6120c0901030e1005090f160b07020a080601060215071706010c0813140a050a05090103080c03071401090b090708030406030506030703050321250324060e011211030601080703 77
    0xe40702603c0c6104800c0c3e02c007101005901326600c81d00c0d182c4100c440c14404106055036a407440b642003407460b01200000d20840001000174415180040d0034428155a0380e0074031441c00400341d01240040c0c02c00000180403400c5920103a4121a0500d00542820a8030208000400780644035078140400711001e074040080300816a00400c01c03080d12605c00681d111240c03000c05188144607440b845194201060a14118620101741c4d40050000318103a821075448020640c00140340050300d2000f03004c21000114210035080d0b508a000e03002169001e40352900c40c50042020b4003108490f0070186040c40301c0d0720000103403011502203140c04111900e6400129007000c8050300003800030300000607044020001600000c2400c8501800c2031300503540d50030460003031240d00a01d03150301360f200b08130780d05964800d03041076240382c0d100c0010710385a01c8105010342070110107602c100082100822000b10541e0850f002c2d0020f2101070784c003400710301e1300104000c0151200408090500c2040004101014800d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 351490098 1250 351488848 351488861
    0x13020f01030b12010c0f231b030c1e100522020111030304030c03080c0a020a2406090510090b030309010c08120108010b0a06110d050904230403080606120c090103 71
    0x344402003081d44030401c00109031b8a903003200307074000c1040c5854900599035040c04600303941d42030f03890460400840502035039450f50501c804454a00c828054000c1a084c20300a8241312800c50001e02c4684c00420981810034030b9400c0044403051614003040449010740018107910244001121240c1c003146c4016100c40b000705100540f6031001004200c20141c200c406001c015002c1d1300d600c40c440e610003c1c481050302c14401440010b030000548030300020010000707a03a003050b01c182600ca01c1c00c01001c5600c100c075041e0f0700c004840f80d125024040309008026015001d040c55403028800754810001103981da00c00c0421003410020700031b440400303004c1400142c4805000420400c402540c0d503e01d464003070603104088034032072150040001101e500032030383c000100c0742542c00b0b407485e0001140d064803c0d8004400140d0080e03101c044102c4000b000e0071500c01c02d201c1d500125800781c100340c00c00400c902002801c04e8040d50003040001000340c00748070300d40c2d0301011444110366204016401200a4050b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 351491348 1250 351490098 351490129
    0xe07030605090f01150b0703050724090c080a03050909060a050d0c1d0f16030f02160b01090203010515030c1b1f060609140a0b1201060813020f01030b 66
    0x16080c20301841c80004209180000b42d40e800900045e541c040301c80804901d184100511030380308101c03000001c2d015070090700c041c2d0301681c0c054081c801071207640c0000c0f9a11013415410780c0e0741c903a0050100f02c1c008129201a0502c40010300c0550f205990280040c4542340700c45114018180000301d0701ea482c1c0301030002914000c0d040e20510303006850000280303415030103003012a02500480000c04506034180910580d00c0c1072000c2c403036850710b0790494000803803c0c0d5404100341d02c9520440040c3c1d0507000825030002010701103000708070b960408a42d0204c3c181c1201d10668010001000ac640e00c001228002c1c91070004001d42eaa116800303500041d1103121000680701501d1149829103403004114881800d580300940c0381080300c180190030481d607840c0298804a40d103040c090124100400c0075000c0c51401502d05070380c00e0b03140d40950030300303400030080e49030b5a44801d001849159800040c0580202c00a1400e030504002da50008071064245010b0904141e650b020f040c0b1190346010f02d80c0000f04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 351492598 1250 351491348 351491351
    0x9030a02060d090f0321020f03040f050a05072312120307170a02120604050402030d0c0c051f120c020a0201031e0608010506012006011403030c1006090b1905040e070306 74
    0x1401890080e0042c0046d007007a8108001c3c005844084035000d000700c60040c0c20103804185180e460f0380d610703c07407151100c0060319203201c1c164074880007034002c00c488805000d11240c20321034500701d000c0010003403586514440c0201c94001c072022441000040c1000d000016440080d00c941e2419011102c0103400007148802150080920015001590040850554840c0c41c000307581d40c1c500038441a500d06030b5000790958004690394000d40c1c8142c43c000354045c461003030000006e0742e860000e1002c05000032000788a40c05103141ca040c141d08241c4804a59103190410300201e408440c019444039885007010781415150310000c0380c803c128044038181000b481c40c041000c0d940b2100c0360350081000312541ca0214080c071003054410401c21411452406112000340004d0b0300b0403920030158601f01c50125010300c8140070005107080140305030031180c07400c9000002c0340c0c0c0c642f000210030b89001900c1103008000b40e6110141c402c0c48c2407504016034400392404500f50408444991501c209648040c0406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 351493848 1250 351492598 351492623
    0x12120f050c031c0b09040308040212120c010c111218010e030313090f0b0a03061d100e120a081308091518100903030309030207050a260309030a02060d09 67
    0x160500ba060425070103142d0020413841011a052142042090310058082001603001400501d002d541d00c004106c1c003141661640c00508515140b40d030041e240000c45a5114007a40b0031103070b80f041c5200040c42e000401480f210b9035194907054030381705500700030103640105100c0152a900926003104000405000ca90780c48207903101d00064a500c600480356107504100c40000442c080d4007402400410044c070041e841451a9500b47c01000802c030100305d4421980b2680c07000c40401e1150440d0920101c10115540b10b0608403241440c3c43c2c10b541200184051002c401000d41c410b070036a0b071014910440e01e00318451400c0249a070300810f10110b42c80803035800c00c000070b0110180904215005008034105030403903001003004002024129000082a4070820404603100e60031440065007c0c0c0107590b160b9403540085095802c130360300300d40c0c9452400807803841c66010072002246403d038050040c504010181000035154452444080e20030f8001040740124908103a00c4030034925441034006081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 351495098 1250 351493848 351493867
    0x912030108030d050106081b070c030204050412020706050327210d06150c0803071b11100e1507051606020d090909030e09190908090a12120f050c03 65
    0x40703902084010420710700b130000000b45140182c8146000741614501011013a4121803000c0240c2c025a00690315403803018400030250311648211401a80035141e40d081d045400c03440a4903196032a840f000c1000710400403c0304032598444c80107078248180001c15594004110b44614168101e502e10341f1085600c2c00d041c8800c2c1d41a402803041c03a5200d9818032100355500c102001e000505000c03040414000102203001422017402154810503500380245046600d120760403a452240d50100d40d00841c0e5049054a4580b070034082a95000900c0c06145117109100850782260903a80c03000c115000c0441c0840410205004103840c40940542400e0781a40d6802d001395188410201d640c0400d15046021807400803030300900800e25050303114030050429007018494401c4004028810608d020701ca030480e1080c0c0d42c001c1c0350040e40614000b40e16074035a54200030300540603901c020003115210500e140090306080c00a81c0f985918205260110b52010050310705104101480e11070703010002d01c0c000c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 351496348 1250 351495098 351495103
    0x11d040b1e0f01090510050f13090b0a14130f02071b03231213090f05010501110d35040807050714030c0f1f0c1a0c0a080912030108 58
    0x140c0401103450300c081d6182d030300042d00c0070425401129005070b20b1144604200b40914001c0030740d00c82c800f507003a1414034021240c2220002c550000780d85c4a8460408000e64603010500001030189810b81d04a414190350000e4060b0040c3c20558034045d4590403452841e20095041d242c20035007119517030100d5a0f00c00a4070740281080d00044071030310941c0c010a5202d4950181032003003141c0d45001041314402c40756801035030b0380228403100d4440d84104000309950081c2d00500d072031680140d4000c5007550500c4000350051501c1000d0107001d03805801031403a2198801081032340b80d92182985411b0b007070000d801e50041751400c0c484142d02d0603000107200801a01200409226000d10151180703540c070340032080110000b03503008551560266007901454035001c043c40c03003c95401000316801c0c4113101e41a80c0e42140c201c40780404030780c40c1d0441c407041c406200701c0d03100e058000c00c01c0d0800314540700c910b00d441c0b805030000320001c020b034a400080500c00e0030002c1c00b07030065402c5c0c039240d21781d039440c00c400e079 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 351497598 1250 351496348 351496399
    0x711030f030405010609110d0e12210903070807110a03060e010e011d0a030309020604030204140403020f34150e0102160f030f06230402030f010b060d090c050405150108100302011d040b 81
    0xc201c6542f080015500360f804000c1d1241a5481380c419450031403561124001c52000c911241e9000d05642d00c0000015214440d034003000c685d180c000304032104050390190031140403908160942510503007145c01d50300f011804070b40856060400091260311400070411601a41d00001c1d001071401e40c1101544001103120780c4518413903802c40b010380058942907501e8040607200c801d9040c0e500740104400091000c90b240803403084428044040780c0e80c024816084003001e03900804100c0100010000356410b0100103003e0101070318150380c01d440c04010f14050101840b0140c12400404000010007507903410105500240381c1440600c0020590039504852040ea4107d220f4454500104803d00d8107005140102d070000b86400e00300703617000c10154003030644100200c4000d0009100490780d41c0d50f5100303541c001d03c1c18407070720600c40758020300241c100c40c4060b02e44120061603180c1040140e038004194901d8600250001c200c03144610081400b81451905039507200303801c2c00032103001c40d0001c403458 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 351498848 1250 351497598 351497647
    0x708010f05060a061b02010c11130519020310050d02010203070b01060503010e010801050f0c0322111002070e01150c050a060b040f0b06030c030711030f030405010609110d0e12 77
    0xc21451303586041c19a010740080c0f9241650030940000d4001640c040c80a07482d8090041006150f0002580d0000742c440e500180018002d41d914018440ca410a800710b240010203420303421440c50400540c000c090218601c0b91f18401c1d0407110528086902c05d100f554070a945c06040e015080d40c60b8240901160001d019142001c1200c1000141c64481401100d0246500c0c200e440801d80307410f40da014043c0e00c01031038034039440c0c0010403620140d000303940b105000d54007801c55120b22028034010004040c1c002079542046500c020418400100a503602d641100c107000000c080e45e0030501425920406d81b003102400c2401007003040340038480f507a004591007003000c8900b00800d40020300b500c01141e0b01d0001e41303908113106000240c0c02042401c000d5400ca2500e080020070340d0034100b030b606e2a40e071040c0c40030031600740040140802c0000c2401014060b02107500f05004d20b0780c0201955106010b80090403428030744a60303134603162101c10301015003840c3c0c500c1c241c1565440918900020800c0a6626 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 351500098 1250 351498848 351498859
    0x70809090c070f030e01051e090415150807031b020607021c0504030f050106030501091506270c18080a030e040c0c0b04050309040207030306080c0d020a06110708010f0506 75
    0x1684001da81040314010b9501820403240e1001d1902e0480310502d82c001c10a050000412050340d01171503890440c01c0c6074400001c0650750700f54200c00d01c019038030048582d4800800c0300f0401d1110360b28000d44100d2548440c6043d410316a10f20500701c5c0504030041001c0c0016074202c00d20519181d0102d1190701c10812a000c4031a503c0515400a8031718000504100015800707010034000039400102d0f500459000300004650561a9200e00382191951603040ba49034880003000311000c0c6a07170084c40010b1501c0754081000c40000d49241c4124208546903442d81a6545109500e1b5402030107021038074040d4004802819480b6032025546400180040e800700300d4400d54000d50389407a0107505402c0e560390340c420b03c03001150ba4440e8500341c00900210740d24002070255400e591164801b414076680603560200d400c0d890021240d08241c01021014041c0342c40d04408000f584414600300c1c211741d4245004010808100d869608040035500603800d2542002c03c90039242c142074001600540c000c450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 351501348 1250 351500098 351500101
    0x41109040c0329070c0606030b01080601061404060806040905010f05160306080316030c050a060212040c050301021623030c03070b0106110a060b0d080705100b01210c021207080909 79
    0x1800f104910701d4900c4045140800000030401840b450080301c4181c130800010941c140c40c0c2d610217521500036080b151035948480c0040100503840304440c8002002c42c0903d0f03290905003440106496030040542d4012600d46000e2420410250701442c91041100030400103030130981110185000341485031400a402d203240442c0d401e001108a5009107801c09842c01203c180740e9091392000c440b0301b01036a090088184080100d034003030004086d0841b191001062500c2c15241c03100c003945150b089035001e0782c03040c080707680b0000c01e6000441c01150070180e22460703c94625030709503c9501480e07160b150f900002c942e503450a00d0000140000780d2280c0144010b50781c803407604450302c0070004075154241e8440c3e5100c0c03022600c84d40c46104440e80103040b02d40100c05075103402c1d00e203602c200c10071a1140d0241480e06485100d034845e283c0441408d00e000c51543c044151310010f00000d900f42c02c48a580d0383c180204400d40200000151114a50314054507840d8a0a0041c1181c020700d03d03144c01001c50b41b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 351502598 1250 351501348 351501383
    0x309020102011b02060115050c15010f0f060507110a050a0e100e0603150702152505040b2203050d0f030b0603250905060f0a17040506010e041109040c03 67
    0x3c4410041c8280c1e900070101caa191289039160410040305503810b0041c2000581d0007588d0a0004c00c001100034404810194540b0a1272120440c060344610640000c01505011480d40041240c2619410160080d0101c40590014296401543c025035000608640006042d404401e0f0704c0c0c803400039038800b0460305540e80461403114004035103040e81034001c4072001d00307000c1c42c402040c0e03080002441101d03204428498200c03401d00c02940d90000188040c1380010003140d5586002105aa462600904142c13601028060500542d00c0c0e9250600c0341401415040c501c2c607050f00b00651300001201e41803120303600d01501f81c1c07200c030b46000e000a08096103550030303041003400c80e4083e901c3c4818602140c0c018050f058440707c181d500c1c1c1300410000c100d0005c6c075981c98102800040c0c014524032555100c0241002d04075030305a04511030004280ca04100c0844c001044890465012a450000755900c0c2e1030410f070011449800701e80e10105503400e01c41801076200103d000c0d284214500401107a00c070f07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 351503848 1250 351502598 351502631
    0x6020a14060402010530010303110d181208120a0605120601050d11030a051501170a21051608120f0f2202030106030b2a0720060a030902010201 63
    0xb25400380c081401004201313141e401070311290500e240c555400e40600881e41800e200198800e030300c2580000c0e80c1742140780060700180f0100340041d00c0340c00c01003218100e500303400d01508107a205144010402c10350520600c00c000c03080360310720300c89840702850900d002c5c41d00c140200381a000f090b015000e402c21180c1030780c01c0000c1d001c2c169000200b000d04040c0c2c46a0b10880800403104c1c000d42c1501541e040d683c0052820001c42402550281401301158144003485040340d40060741601568811040e000208680e9001c0c4203d103001c48011100c2c00f40d443c5000d49480c880e0042102c4841002c0c5072400500c1350f014090010b6078034403c85840c045d00c80f4080b4442c060010744241108005000101d08072140c0207000c061140350039070b024071703560049400003402c580c0181d00c217950540d02d0004210f07508040d02800030403e6840704080441481c454840a8240100500145004804002403892010150401c924404010b0801d03642c3c000c000c04c01405400e007024128095030078422103255440f00c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 351505098 1250 351503848 351503851
    0xf01051b070305040e0a0b10020a050115060c02121203010803070c0b0a120e0f030c150f090d080604020d180b0129070602120112050d05190309140706020a1406 70
    0x40d078800b1306050501840d040130ba100a041203285035500d0a01c5071041d182c02c42c2094915200e80c0103015094020306129003500d00c14811000202c030a080203120941e040484d4054030b039019a40005400d2602001d80e15101c2c6503000544202e20100000a440600000070903540c0d10540034440610b0b0b075800070700f81c2402285082004181002405000028594030404600602800300d40702518040c80080c116400030078444626007010114045550030041c00c41d8210514440c14400c510b0710302441a01c440c24090300b4001c200c140f0f4080744540d602c41c1c05a410780c00400108000000307042d4420010a0844d0200303c802c0c2c0071001c000100880301000b41884894126206046c289800c56a1806035001c4002100c100e5402d101c111407442c60140583c2c040c2c024469080e041d90001d007096441c25103c002c4510400c034040014024000906080c49140d000604000c1407181d82ea15200c03070300d451554400c0e0024071500d07000107031a0340e000503803100540c0205c424200c1201143c400c95145c440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 351506348 1250 351505098 351505103
    0xb03090d080f040206090d080d02040e0c071703090115060c12030902100e030304170c090f040305041203110109060507030c02010213030f02190b0901120c09030b0c0403050f01051b07 80
    0xb0050020b070250800800a1400c280028105044840503580c0ea03e0190840940d42e0703030059001c05e0034005116065002d40d0444140c980080c02d1801c5590b900d500030303507811026000600701101140e080c031825044561101620450030303000c03584038100140328079011401500e0f40020b19000084440c000e1143d130300000d802800034000b101c2e814000f581c807501840b184075007510041000098120030351700c0e40703094544482d0107000e0400310070003080707030903030014042c40400d240390400e1000083d0404100d404035101018018210b04a07800c01348c035821619040a1059403c2041c02410007400e544140c2c490f8203d91400c104412252404038203d00030100858812000c00d0018004101c410240d48440c6100400c02494080200701d2040d1680481d030040701d8502c1c020491001e55031700908101d02a411441e0304214050b950440241000b01602c0090070700381c031017000300e40700181c94400c40340a15005411a00b0070880090014000d04048510141100202014030003030000c80044a03070042c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 351507598 1250 351506348 351506371
    0x20712030c0906110c030a35040315060e04030305010303110a02060d0b1504170c0f0f010c031101060e09070504062d0321080105040507120e030c070b03090d08 70
    0x14101401614008104c00b00da032034030b2042941e42181507500700301c06540c261050300c0c1c41200d0012034900340074051001001c88030015044901c89100a032081c2510b04036034100d01c0c15443e0301d40000f116801030200f904000e00d0401c0e03c50400043c150103801041c100c0c5c0c400c0e503407071040120345c0c0303100d0fa215030159000070762003102003003546810104c1d41c0041c2c600c020000d2104400418000100e50701d54030681c0281500320316000210208a4240301a0803500001d64201800b06510400580090f800580503818085040003450505220f0900d1580ea564520000c0103142c0c2c407203001a09008046501a43e1403082101c0840d0605042c00344130116406040f51801500304d010400141b600180148440d0300400803000010851081c03242e40c4007404280000742c41d14069030010000f000503045240141c0c02c00040c0014554007001035841c4010480b40007c03100820b640807800c51090000c5809a0300c11401c0102d118842c0100445c01500c0080890b4840e1511200030788000e0022941c80c482d80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 351508848 1250 351507598 351507617
    0x31109010803041a030a140f072c010309060b060f0702030106080f0d0f020309220c0314131406010603020c25030215120903090f0405010b09010c02030a06050a020712030c 75
    0xe048620145420000e00300c00428000b40c1c0c1f030314502100000302d40c44a1400849410b02040303a400c20140f10302000500c9100110007002e0211518a4114101d00790401d5541e01c2e000d02070182c19801001e80030002441140d41c1c010714500545aa00440c070280e219501c2c0110013700102e0014008251b003003181e001d840c601d0060541030359031740d07051601c1300158001084903461907581d21524490544c10850703402030709141001c0e414100c03101414030703d0030305103014080043d11000c1d0040e1035100b509007580884044841c582a08a0b43c080c10030034501344640000421096050340213040c00b948030100720b41d9450030134000083c2e40c02240f039240f105110710807014405800d008030b01065910010103980d04e00302410718401180315045558461680001c610ba14071450300e6108400b8a800032103080c071242d410030342d10101600c60074049605210300c040020f000c5440500c011041990400030070069460f152680c04060751110404660501e401800070180c24000c1c13140b649802c00030303604c1c80c100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 351510098 1250 351508848 351508889
    0x1c0216030c03020d030c06111215090414030d090503090114070b01030623070c11030d020303060603070905090702070f0b0c1504020105090409051006090e0303070c06090c03110901080304 82
    0x104c00310120a030200400d0803c1c441c0810040d010311154070300100c440a648940b8001e040e09480c2003e4429081100e112a24122507520b804210703030483d0b045699055510510003500703185109040a8904490814400d8014060302101514a01100380c8400c404809103180308421807140e610002c090480b40c40052000c078230994000040005041d4102521035003800f0b2821206000712407100c0040c1c0500744070020480800b8082d101c0a500b43d0041503822200b4202a480380401055903001e81004400070f03c803d4460101c00000b080040c0c00d0136100c0c14080740094480d9003d00520395424101c40300016505042c0d000c4900c841004809001403030306030110000c0080028006078100a010f00030b0344260f039694451404002d200c0c000501c165160011518259595075005802e0b40307160607005e40030b94101208aa0380210140360440103000d03189400750041102c010040c00c5218044404000c128044d040c032241e200c07084a8a4006a9849400d1035030781c840c42c0141c1c0062504446500c03c1e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 351511348 1250 351510098 351510109
    0x1002030702010f021828230a0e07020111070308010e100e070c050f1618060e070804030329040209030f011a0109090b0906060a03020c1c0216030c0302 66
    0x2002a414030000c2007402c0501204401c2c1d810150089111040040c41c20225140c40304191156410284002da10303041c0440c06c1075640e4034180301d40101d04901c10700841c81418003907039403041c0700d6000301840740440d1500c414008101c0102d4002001d507107404000c510940d0034005441d10f6503415a5044001d03802c3c442c2004100c013000c0d01100802d0381400b00418001003140340148640001e40d90325150480504015150801074210800c241e00074800198400b819440031130300b940e0b6028240d1005160000708000100402d91218200b003010809100c1d000b54800281c9000c0e6001e5602032203c140341d69940b0b0640c241403040c220b80605020740d080c0c15800c00d40c000c1c02c0c1e1440e0003000d40b1070804010122500b5501c40d2500d02010701c01895841d805980c024154001401800001b0007003c40745901242810308007400a43c801c000101d0b01c01e070041e10980482e60b48a183c48191240100385281c00265142c010410401501404175450441c21142c01000100ca400c100c1c6220541c0c5103400307012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 351512598 1250 351511348 351511351
    0xd08100305030319150803130603020702060409180f030c030e0301021809070309140604031103070b13020d053a0e3f07170a02010e0f0310020301090c0c05100203 71
    0x400d007584440740f00e922000b103140d500d0b001b01170340c00103540d036032041883d661004103094004100b410300c18003050000d62114829a8151508000d00044656896000d03200d0010280c1e40146091051131032001090f07070001c0c2c4696800d200340c903200c96009003482018240e020300c00104158000340680501c00d80703041c807074260b0001000e0034001070004050300c0320100c47c80d0b05140340708140d0050040c4020180c1c440304200340714000001650504040390366030282c081c80503101811121914020704155070380c652104e40b02581c003034110b88000400c840f02041d100c88a002029507500210460681c0400340600a44069181e41d905198840e80710200002c00c858041020f00d2180d180340e210204c2c0714924240c0717402d80c201504055624220103180f41c50b00e0302540101c00c030074018591700c00701444000b8440c14120b80c2401e0041d03900004d0408160075440140203142d00d80b151000c404425200e590042d03050b210116014009034481000c02e64005a2800c4000c0865124030440c0d1880b01190f07004e107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 351513848 1250 351512598 351512641
    0x1080f25090b04030c05030601090603080406050a091706180d0c0f08040e010e09010c051201050108090f060a0207020306160504150e040903030b0f0108011a09060702060307020d081003050303 84
    0x5000640b14100ca9402d5081a00f0496000f850001d081c8070300c1c9001c10100f0f0060640840c01c0c4102d40c107541c2d450041e0b014910410040c48400705181d0441401800458094241d00c040700840c0ca004980540e44ca000c01e0b41d0a4074440c100c6001c00d0104000481c00c503503842c40984407040c8003013a698540c40101c401110a8601032403d01012507007042e402c10041c000c04500c0c1d81082c172070a1442205084826554481013131141c10418a1046d88415000e94115036007405c1c50145a40c9802c002801c182c20805044a103010340c5040140c04121640a031601900a03803c4030364076926608418880c0c1c0c4041c0c0044041541400300b080401e0380301007600d0f281111403070f0a02c0101c40080101e801d4401c8540100c0c040f0b07456a42074881414a0000b10064840c24641171159504d0084c21000c0b0120b80d264003001007000061405003520750300700700c074030f4103038090025680c074608090020340721000c0b00303100700000c0d80d0f0740040741d41112400840415030360008051859620303600300c00100102d810840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 351515098 1250 351513848 351513857
    0x402060415030e0312041e12030b12010c03150b0405030a110120060604051e04060e070b04030804030b06090108030906030726090c1903020f041104030c030201080f25 73
    0x3c0201d014003400640112080015004840c1c10540303071010b0744c1c0c03c41c0300102c1c291400f80c01341d80c0d010a203156105c0080c0c43c818200000d038002c1010104a01a104e568403140035800c2c42589818103515901203003ca61100162142003501c5000c0c2d01304500c41d40c0702d1564540d01000b0030601042e03140203a40034401050400300b01c2400756401a290b040c3d82c60150f0440754000031b04101e103070b00f003a000346030748036080c080c0036200100c2d0400c030284580009000500320a41c3c5804003001c0078820400c16020f0440d90000b41d84865480c41c2000159016000071907418901502088690a1000c920360607200c3c500059818001000c091000d103820081581c41000320110700942c8003035880e03885840711003010b0740d0745d0030a01d04140302d81c1c60700301c400b45058082d040e04205110b554101c10300c04000d603541100c001d812203005100143c050842c80f070808000318800200041080320581049007101e01c00c2c1c07954045503550899044401ca4112904503004203040c81d0810081071a03103018461142c541070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 351516348 1250 351515098 351515111
    0x60b0d0b0405010203060117010e162f0f0a08041e03021302030a1a060904050c0405151308071d07120e0a1b030302030a050a21050717040206041503 65
    0x584064810003501c0036201a5070002c02d00019583c4550902e01d140300030142c01c109545040403480c030740d0740000d00346014200c0700b030490134030f03980300c1c0034000301608401e20303100c0128410982c05d0b01c01082c2c1c1459540b0380d01c9841400c4107950400b00380d00c44940e8101c4000c504292070b21003140080500d1703140824940002000c0400141c0e00ea00c1103404422111b41c00603241d240288818040721418026400700120a070072003201036889030219810140292004501901d8000c001c038054011904419800710700f114001c403e05880c000030348403901443c00102d04460f40d91401e551a81c2ca0b0b03004e194266021882d007207410841030f403441e5800c002140340400c02c0011414441c0c1c1200c076101c002c40f0301504007800150074400c0300e039004403003224540c5141074241d1860754082d50724490403a0001c180301001c5030800c15240504c405912105044030b03507520441c1c03120190001000d0440741300010030200d54003104243e4090b0400c8c0c0c4141c3d40036000a142504081c42c4022502c0300490400c10140c0700c0c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 351517598 1250 351516348 351516353
    0x607060b090c071401091104020904021e07051e0705040b0f0405041112150a0504020307150305041e03090b0c01110c0d0807020a030207140f03061509070e03030403060b0d 75
    0x1c1e014401c4428400c06500d0340214a00070600480a1310100280d80c10320368a20701140c0024031800942004a1300181c1da964110f004c600079001e00050081003422201c0e142c2510302c254801814010302c80c43c103403a030f13400d15445c1c07140740e4102d440003489459204c020148460700b0075a01c41540280000e0401c0c1c10a05000c000800307440d270881c0d003120b180c450801c50315004d051010642d003801c0703a102d01402a020310f500b1962402e603402001054920f0b16000494155202481544080c044110340c06212142f103100c098040c10f4180d60407181100c240113149a11580c0301c41003201035505544920a003440d00c1c0d6600483d070855005140035540e20070719291200b0820005006c1503016901a1103215034009024244140081c1550155084001594006a4017003007040c10703035000b82100c0403502d84010109842000541803250544901810311040220b14440d400b0400b40031a0511480e5607034130001c0341c492040041880d0594000d210034000212950400c02490402800340d110341140da4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 351518848 1250 351517598 351517609
    0x305040b270103020901021005040618080703122a1202040815010621110729010501050a0906230f030403020c010e18042a06081e060607060b 62
    0x4694588a40d10003001e010262210000389015490242401c50400045c840041e466440b42d05c0040349081d40d8800241c01c0003203e611803804214a030003800404031f81480c00c0c1107290302506c0203a001c00c440d0004004643c1c424003600d004400320001210b410090860141540d031580c10340c2005001000508980547c441d1024100a191660003082c02d80d040c405201810300048c1c010343d0410242c42940d40031550300c00003800c04881884400503641501e0303c500303141400303114802410305c00a08420075102c90742a0362480d000803c250030080b542d030f9600054513580314130710903100820300c02c0c0000c0000e82d00840500c1541c014007000c3c5400a030b002105115268415400541070200100c1400306040d0704010004000100b801d00512003560f500000b85000c0119550f180251215800241000500e00d00d2582c04003815400440c01254504003130003038807040c060f110002d0300480004900c001460207040c50410700030034400003a2200000c3c80003c0d4850481550312946905400703c9075240c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 351520098 1250 351518848 351518857
    0x130b1b04061107030b09070515250309030804060e10020606091609050604080604150204030f0b0a140c0301080f0c0f010807020307140c090a02120c0a030b0301020c010f05310305040b 80
    0x3020301840d42c02c20f020450481083d27030740050146414850022056504010030745400c015406404200380f507442e04941e5004107800081c0400d4002c100010141c1e00940000d0444404441203507843c030251008a076554070440e842d035031001140c070201e41600744121420456003980d241000416440c2c0001c61001c1c1d202ea8003049140c0d02820811040c400342004400a01c209e04205600d40351031520b580818025425014100046070b00200e4019005580101c545e59a01104062185000d50910701290800d1045070340f18020b25081d01e07641000412034100042004181070b40c00d03081c0034011240e24800514480035444100441d5011036020b40310207000d400380c140240200b0320f00e0410f002200b0700c0604080245401441030300c089443c049081c507444200038882c1515928011404ca0203071103e1700302c182d00b55200182002c41b400c0190000045490b00311014025a280e410840c0442c040c9403080c502c1124011705079403120301c12441841d501d41e01038680030382416228506984035921 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 351521348 1250 351520098 351520111
    0xd02030c030403080717060103020f1b0c010905030d12110912010c14040b0a1419090509060a050a060e0f0a120201110d0203121e130b1b04061107030b 66
    0x30301104100030507612900c1507070301200d030b0700d042000070b140080d24005560000d440d0303906141c0c02045660080301003400765031007990b9004020703544601c410f02c900d898114601145c0d001500200004c2014200000c07080d2684015a54641c51381a940310010000c090b0120641d020102c10003032124660749031004502000c540700000624248002d9000e0800711003110351130064541400100000e40318038080d59101c1c130250805658510701c0000421b040d210b200340c0e222100c0c120448010b102a0700c412000c01382c4400741c0e000784103034490350100040101c10340310f0107038030030212501800864402d511890b900c02c80540905101540a0001171440c81103400007802044407141d55030640da4400c041c1c00119802d040502088030b403c0030001d4580c032440071000b07200101140440c90a0410186540c9442a040c4000004d82003441d10741c0314019010409a4007510800e010a40100d442c94140390b140500701181c0d45000c2c80d196064880c1030b08221110498000e00e0780c0000460014500e10340704c0c18 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 351522598 1250 351521348 351521371
    0x15031806020310090501050a0e04030e010327050f0304031e03230d1d1b030708030706060810060506071205190e010215160c05160e0103020a050d020109050609060d0203 74
    0x1410301684008030717601680854410080d1042c00c21404401c245a5500660189000d044540107580140d001c0c082028510021a003003c035080300038008600c0e2000c0c401d20400940b4000140c1004082e41d0b8000c0b8000500f42002c40c0c0501a08500705103a0b00800e01c1c8282000c40c40e4486072032a08000c00210448411542030001c0d4441c5491050b22480124031010180340c03584511058010796210700c440c40750030529503000400002a81c080007084010111107003202d0780d4066510303021000d400d543c41104694801c01404901c001c1003409101e003a604060400307804c2c03c0c3d061f10703006040b140c0c40700c03c8c20500104001c0040480c0004400c1c6000541d41d480303200008a42000081c60300c0f41410300a0040c090310802e00c45031404038940e9481210b1245000940e074909800d010b03080c500c6140c0c029078212220440040c0807081c60440c64102c038000c555001c0a10f0f5640148460110f451000031b002a500c0e440a1226151010107081008000340845090584565908081380c0c000c1d41d2100841 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 351523848 1250 351522598 351522631
    0x3010b07030f022a03010b060f041409070c030f0c02031608190203070b0307030b06030112050d08280209031f110a20011b0807090801020301150318060203 68
    0x5034214029074003400b1144014510703d42d049141c248900c40302030798810901d40080e501e4145a600350080c0d0811200103054540c1c1e0818409825010390051003040c00009215a042005291031900c451051200f504c403070007003036643d550403110a4542e20003001800580c0740f0740405030714200050181203007038002240055041021041c81d05c205c41c000030243c52283d1552000584000c0758500032100304503c0300d40c4907100d4603400e4024000c2c112189070440000b000019643e60b5485804480d1030080f0240c5118011020007100c551404685581d89801400c8001c009508078980c0c0b8030504001c1100181403428400000e030401300c050300344240310f40c402144079100d90302d07a1081e4016802e42c42102d80c50425100009481001502c000c45801203504206454100080d040110403420303511a05400c52400d02c4c01420069060314900000703500c0c6000811900b1051088034142d4001d02111061407141c0141103000d4580da0225034000c8800d07051500c000b4400d400076501038980c681007907482 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 351525098 1250 351523848 351523853
    0xe01060b071a091c1101020405090405030a0806010c020901050915040e030a1202090f01180510110c0a032012010c082203080a180f060c1209080d021e03010b07 70
    0x1c409025144180d0f80c0c00c0120304040c241d80403440c00d150310019082c03005002510701c00403802401241c0c030841d00003440c1d1040101300040070004000d40107894841052507254600116200d003032440d402508071425030300501a44c0b510500040d407000002d8409004d41400d0804241510f1010382c001103c1c0e070001c20460100c982202000310510032030302c002c506040800c3c002585010010746085c1c1070028040c401100c40500303002900152101404501400f41d4501c0c0040c80303810080c005581d6406018880b000c2072404814000c101c1c2e070820141c02084002c200701c417000c21003507610f081e8041c1303020700c11403420003007802004134040480c0c42d107140c145408403c1040407402c0e808544000044041c0704800203070031100c1030390040101034001039001c001910f10462581c24013406000e1040811030001046400d40141d40032034056910b400112440322032140c181c5144240c000c0401009100a050342d54040d8090a519224009101d070080780310341c2d0302d0b0701c01c1c2c1c030a8008590040f400540e4006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 351526348 1250 351525098 351525143
    0xa02010606050306090406050907080a20041505040e0102090414090d020604030203180d0206032e0f03020d020301021306020304030308161d010302220510050a02100e01060b07 77
    0x7440e180c02d00e24a035103440c1000841003100208010003103507848000c100841810407004000c1c185c441d0071280381c640c490070510000450070300810460112496140814203040c010700c5e01c00383c40c03460b100c92054241020440a03210541d00001e1543d801e026001250761917004640a0b01440d0766007e005081c28240c0509040e4000719401c1994440780c24000060340c008201c1e40005047d4604050303114100000030f842d0f020b20040030b94031802c00b10512484d5040304c204061203400f00d030000140d4480a100140e9403000c18407403540c481c2e044040810160500c81c5038003100f41e00c001c0005150000d403480c00313005028603401180040c0e201090030710030160441d8050750400440c140001ca19440b1440080640600040c18406040d40c101940d0342ca902a405651480e01c2e406501090541007444c02e440241a070b2050b1351203421201150001d240c042c00465240442a901424020b0002c40c803060103044404500c0d40300d03640c2c8110005d9028412030103094080d1050a9500d266940c0200340344 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 351527598 1250 351526348 351526361
    0x2416060c0c0b010314030d020703020c030606013009060e0a2901050d0309030b072c06031305070810020901020c010f05040527040303021c0507080f13050d02030a0201 73
    0x1090211060741c0074007142d0308001d07060441c1c1d400110080080e00e020b0030344e4214003c6d070f0704400d0414004210713281015004514030000c904140d04036010b035540d800045410010f40404502c0141550a0001500040c070034800c08401d010140071441c000196600012a8204240f0042365002a40b8801c02c05c80b101310b409a030182c000b60410118500f0000900044006100c1c1c14880c50008920004050160142000640e088448001686403417070000d400000111119443c460810108494000400e440711080703403400740c074050940c0d94089222408414400e1309071090300c151800091600d204002d025442ca140c250096142c810040001e4500b4039800320081c184001e2501a03020b00b544441520f048407000c81c0d041d0042000f03094401103541009404400b540c81d820100b1050541580061040201e10002c0451451128408070100c6405407000c43c00200309201242c42050031100146d00510000001d404c11601e035680e00f49061255006d40780540c00204407401010f4082c402c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 351528848 1250 351527598 351527621
    0x50c07030c17150c0d0c1701150f08150607050f0706020705040501171c050912060106080906131b083c0307060c2006091605060702241606 61
    0x1004a00309140c80105900800002500702a9564a40c800b000d111f4200346282c1c54a0401131419961a5100000d4141d1905140e501240700300f0181d11403241b155100314486c41001144000342c4200c44200162680009400d582621903011400e09042050054100a20486d0001e100030303071410b0140820343e841644150391200480080821150300481e070621103030010f15a1805900681000347c80300d00600c0c01481d003040d007501c1d0008030700c2030001c0c045050b0b82c4c0684580c41d00d81e4821200c196111011520a440040100703030740000654405408481c0c7d04405000b058029100e16410b0b1030f089440c02c000e1f604004940c01c1d01d410920340e4228028402244802c0310800c041001010354920030448010100d650360541f03170b8000c900c00c0c0074403105070540c0e0940783c029041c0030510682d03076202a519081f15000b5059101191030541203100c0c1240c1340641000d0905126030208806803a984541d0b50700786c03045040d007030003160804c3d004081d400d5098030340c14103540040c01c100c000c403032440c0c078071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 351530098 1250 351528848 351528883
    0x1051306051e18130e01060e010306050f0601140903071706100504050105010509150d060b0c010501060c0309030b100e09100629030c09060f04050f100f050c07030c17 73
    0x125046100300b0552000425010b486041d113488041d5440402024180301142c0c0701e5107404030200d42495810300c190b04907030203100180704a403500701080e000d0100a454460218811061085043c001040039000254008043c1e8040c20f40e14407136102d40d403141150b14101c940010080110740c40d0400d00c500c016000a035410082981130000180c194030800c507540784104a011940994801030108581060851100078003c450365400708500c1c907040301000b04495405d000010800c544528500540941c042d83c0e0315214034a1900d486800e1280500b030340300c400c902c0340004540c00c241e0f0400b031801a80f031403004102e40c0c0381510001c5d0031075400342c0002845904c0310302483c81b860170000000280c12580c0c4101640c0303803942d00c00504103203d4a003c040d003208000c500c144445009030060300450780e06807000754a14214900304200560b05288401c0410000040340c40303405c1c0703c3e0016220412056040301c2c03103130781c4079101c1c2002c040740c65110300c0b26040c003200c400241c20300030f00070f06071000c041048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 351531348 1250 351530098 351530107
    0x3160e031e060a0c02121317070501080901090302060406020306010302070b0412170105030c060a05040f061809020a02061906170601090c090b0f1c02030f16020309030a06090201051306051e 83
    0x134001e4582001c40c0c840c004061020440590391102c2e090504000c00b03800740252500326401c000191104d4061280038080781e014400510740c0701e418025500c511307505a010305090356032039964070000d41015001c03034101a401c0c02103c0c0090349904166000740e0080e442262002c107907503c0104002400034500c48002c82000041105490000300700d02c140408848260f03c4d031040c25001c03510380c015540301d48880d50039040009102c2d5007104429034003d4080c50744020054460360004141c0c4030360000f19005074420700004480c49810200340151083d07689011500603a1880b80000503020f00d0941c0c0c0042d000900108a1103c10748904007100d406801c000210f42e280230641c004034061030301000f403800c0c0b00060390841d10140c507a060740d4031240c3c5e46d0215283e0800000c00c0c43d82c0710f0201c414544419803000c203034a06900000540b01c402e54028020b01d4105019036916000d000100c2049052120500001c0d1416540c00c0012000d06000d50703a40d52142d07500c2e00e80351105043e800d4400f906210030032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 351532598 1250 351531348 351531371
    0x11a03120405013c0914060901050d0f02090607060f0f0b0607060c0201020f16030906020c0d140102090315041e030f050c07030204181b0b03160e031e060a 68
    0x305500c503080c10500d01d00c004807a034034150314462040e82200c0001400c850f100f001303606401001207001d543ca004040c0c140c8042031401d02800c2c2c824510003e001c508107010320f0302c18040035004550f8140a000c0d0150401c854000800c00d9904412802c40e5078949035040e8444450603841902d00c8079a1400341401a000540003140075841100f5000d8841071316229090302090007501118006204c00c03800303075643e00342403081110400d002d280440c0068032241000030400d10004082c0440d0b500280030004100059032154201950182014a6550203005180e0250340c10b110030f1072543c0040c095009a0701d81468040c405d464480e00d810414808030400d003010907840b44012442c10611b0906640e00d20429034020703d00f0086520003988541000a0806070140032b01121900703d21507800041c0268a0307a19030403020080d0f0003590140901440021f52a1284000589000c1c0306030400218050226000c2400c2c100075483c090202c0007c031070441d03900002003002c0d6512050044003001f4115810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 351533848 1250 351532598 351532607
    0x50a091b0f1a16110414010f050d05010f050c09030f0a050c0105030a0b0a1814010302030c010f2105040b0a0c020706031505030604110406060219170c011a0312040501 73
    0x500404691150310110601080701c000112440c1d114190103854464683c0c4c90030741954200b550b100e070f000d542444000e6038001440c640c0281658410a003090615040c102031140b55100e50034181c034650b40318000b540b090350312445880e0241207401d040310b40e1020054103251410380c0051144a06034400b113000008507001041d0b41198031380902c0c0c00b9a0761746036100c8120182c07000c500c9003070748041e048a0005810b168000055201c019082c0c00344040c40041e4034240d0030002c00d101c0030303415070000c0011890720b620408001e64196414105809a0500602a03001d01c1050905080c419540c800a001c10b0045508440b907010203c0e400501100c01c4200d00251100c0d282d114400034191030300f010a098404c00c01c0100c0240002030304587d0246440d013400c29080c600039089074001c602c1e01901080644c40415098a030083e6400b500c00480c0250381c40e010300300e003070300201c00c080c00080c021100007010070700401c405803080d1855150314402e00410503003041c0400d2101112040104810000d503600b1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 351535098 1250 351533848 351533879
    0x906080f0f160302061b10050a1b050301050909150117100612060b010912030302070b0f010b0307120207060c08310b1b04030c06092c0901060504050a091b 68
    0x1174034001d0b150303029401c030200070fa106003540c114103000d00d400b540c0c458102ea038805840b8240e070b04014451500c20b605041605803c0031021340c0064400c20060045080008503d90008031080469114140c501d115058614007a003025031245044498115180e204010300034103103101040822907545001d0f00e940741c80c1903200f801070446c0c0c0c48050b9040141e0241001d0300040060b0303601c04c000303e081854010001c1d40250400c503040406100426035126401811505903a0f50200320f40c59512220b07070513115043c650b5a03a0b00c516400f00603460000f803d50003100d2100c0125217840480d4144904450a00820124041403502410841041070718010f600c000700117803c03e03401e113029291403041d03140c000941c00c05000103440c0014008104210803501804441c101e5544854240c1c82e0500000c0f150340404812138030800050140070110711250800d03420540c210000111241d0350400308003075990440304100c58941d6441c0120a0015203c15644000c10f076015010280c0c0c00d007012100010407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 351536348 1250 351535098 351535103
    0x806010b070312110307030b090a020406200109020315010305010c020f0d0c080d051003020111010b10080903090d05160f12110d0b041518030f14040906080f0f1603 72
    0x141d2410300c0e0f001d060742e40c048001d440c1d10007180340da82d1400f9000603004e44914a009800780d20742d440000d903030355001e200747c4040c0c80003640c422245440d00d10424189580c65000c90b465550f0766079417000103030f80c10004805d00c900e220703914846640c5582485800c40e4100f044007002c2d5040f03103240c0d4010150101c0c0c510041403803410072019020384d07400c1c80000d80c018000d40382010b51401d0140314909242c1161142242c4c401d9855480031521462428240c3c1c0795903c0d11a0050703080180007400c54080c1c8107541e0300000c2801200e091261100000d40928005038055a040d04030000300f180e000d00d101e840300007418400c1144248541303852000780240b0301d00c0c4030250030070b9643c10284202e0303504c105449110381e8000e041c031000d43c00c180c2056504c210300306156500c5203281400d03107110b034445800020380040d016251400342d07414100060340c25010b4400d2800c2e040e0800c000100c0c6400c024443d08025092240c01060381c1010090401c3c038042004420740300503032100001c2030220003042c580d00c0035683d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 351537598 1250 351536348 351536357
    0xb0a1d0d051b031b01110a0912020409020913050d02030a120c030b030a050303070e0a030213050601030209040905160e1b0f070b0a051b03060105120408090d03050c01060806010b0703 80
    0x40d201c0601541d014540c0c01d64010740c00b00182405603010a600300380318008130380008020802c0c1440300459284113060181c80800c074030340000c11154004c5504840a140094004240b0f0b1046a0000d46d03200002c449030701281250300c5103070062003000c07c80c411041b40c0b0390000390301d0624402009040035003000c600c06421522041421400c40c401d40101424520203000c44664011600c0c0c041c5e03d03a007003220309400017140f15903110002c1c80c00140d18421a138010b85500300c0c181e00c54032800c01074240141701d1410325800b00503904407500d8031b114141c0850f000d03402030b09058041c1c81000680c024540d002c4c41e92401b202080c400e07a04514481042c60b0318080d100907582d202914441031003406281700c06440107810108010354208030380c10540c42884000007003030500d02414204480d6000650390703140010030901604c68a00342407907205030054041c00941341009040c000050708940110002c4000407004545006086401d0003040301400c8081d003c1d01c580e40c1440741074641401145005400c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 351538848 1250 351537598 351537607
    0xb06061e16080a113313240f0b010f08040c031b060305061203040b0d0603120207060f02010b0d030f1106010f050a0504020f030a0905030d06030b0a1d0d05 68
    0x101d0560315076080c0550301c00031194940102c040060b2045281406042150050800204030341d214200b20001d404c02092803042915040619070000c10801030a18051003800303185200825843d155000451000310320102a4809800d450381c150307034082c0403141002e030901da98145160f80040780680e003144185403000d02584c407814280144402e91340007074260044503039030340a40340d501e4a0140c103039602510240700c142c45200078440401d07210700d030300c6c1d00b9034105201c28000b141b0000010501d202500300003140003a03ca031581880c64416800f0100540e2005004210003604403c0e01152642240000c03c103c09202c0042440b101d00100c0c000d08001948025158150080396441882ca0401e02255980c1d80c5034001c0a4040d00b0314040c051040102c1000001c05207018001c4815582012407401e04544501c000e900c00f40c816080e080781e280c00309001e28014600284604030045000c1d980d070103000e0900810001c202c032210959100c442401c0b90011404017400213542d00e1117485e500e03026a03103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 351540098 1250 351538848 351538867
    0x4061b02060d0c051e0405010f020c0a0b09010c1b03050601051807050706020f130807050301020c031c0e0313031104050103030531080f121303060902010e0411070b06061e 75
    0x724840c0380f44030b680701701c0100100da221000030005031066900a8940500da040121010f070b03603034104030194581c0140380000c00d2101003041404cc00202d101814020944440e42c2d030340c1c2319170400300082c0e0b02518101032010001c0c00020000c1c1c0e4010038080d00c0320708582e01102800c2070024001000c40f01032103800241c0e0010061198120f03450030500401c2562600004a2810203981d05486040441c6c803c446002c0b5091030180b007200c9190220000540c54500301540500d06c50310f011069030401607640e000480c1508081c4010319048649501075000b4908601d403825035035010480c2d86001e50b1608005000180e002401c40d80c0381003450300c0120b50745407000710381c102e40301803050060194050000c0000c1c0e0303001c4c00211250344048140075604402c1c2141105940390080e4191400e1014441c070080010941541c0082e110a0041c584068a02c2001d400f0609441010340420510704000845c441840380c582d6400d50414800c5800c5072800a2940c41200300c591005410030214800184440d0f8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 351541348 1250 351540098 351540107
    0x6070323071502031b04090506120316030e0a0306110a090f030312020904091202010c030b030a11191d01030201020f010908031506071e0b220f15050108010204061b02060d0c 76
    0x50007829803c90ba46d11a01c0e40e1060780a0f00301551100e00540316100f061410388404030a032103d580301c280d00001c8810303154078115002483c04408030340001c8814004070114105006c0c404400101c0c01d045a40c03054800801450042990f20000400402c9001840020b80c040100d09540d10808000f68484011200140003000020720007848242c00340c41e400409901904400e85481c03158070100000d201090078181c0f01c2120085c000c0600001d003145010901e00340c003500d840c1b0640468035085c40c684801003012110f81c2c25404481419a03200100115130b410002040100c60110003440f070080c8036911505e0741e001c0074211011154061004041c59180d44040d1071100d6001090105040070780b035411040441040001e8a081000f08002402503101019250040300c11104001140b0313041d80b80c4002160120380100d03055203a12114064040c50b60045034040c1142400050341d4524020000e08444019041c01400345000042c00c0056500d0100307442c0407003080d0701e01081410300d86401700e8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 351542598 1250 351541348 351541381
    0x105010818240a11120a09030c1209150203070c05090903070f0c06030e0a05060105090406180c060207060e0d080a020a08071a010e0f070309060b0607032307150203 72
    0x622001a0a80c402c20307080d10b82000c0b43c01410440010842c891080c81181600d20070310b80101050030316080070580008455100300c41c3d990103840c00e032803090076665030341c21445110b01d40a030000740880c4c0f003480b07101d42c950030404440103035000451420100d07690319014076501c1e20a5611400840b00061828401801160103480d0b200040c3c280001d610320705400d0b101e000b40036810009141022504800100040c81030019030001c0007040103078038190402c218400010400c4806585800c980c00807502c1c4800c5065406100d1100380300084d050810003072078002d1543c072000c01c0103202c5003003030f45075100c060142c41225040480b46d6541d6480d013109920306940440d000b4001400024001c0c01d10111000d1007004420040a18401382d90b00d12000019034800d590300a01d41e01d400001c542c0c69030003680104503042c411000402e40d00003241c00610160090081074000c01c2c900321050000645980c0514409421307242c41a00b48011915030500341c818001c2001c09050307000000c20403d00e030103010003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 351543848 1250 351542598 351542623
    0xd0c03020907080613150f0902040f06090b0d0b21010b090601051905091f020f0c03030910030b192c10060c030306080a030309050c01090513020901030e0a050a1a0105010818 76
    0x41d607c1c44d500d010a400035803103440344091710411004089409071064101504952010540900b4440176010080050003403403030581d40b01c1620400c41e8007400c143d60903c448542100000150640c400703003070006081008001e1030410070108921540001b003003a04500080941c640540c80398071400204e00700c01100681d46c00d00d030b019100d180c036095a002a00400c82c400031019141e500303044a0600d0750301c2c0a928200d552041703580305082c110510a80c03044960480041036100821402104e12540d1581c94200d4001030041194001c01c00c20345803c3c0202c0d1080c40c2d0300c00030092500e88601c0d01064080c0c0269402c000d01c0c40078035010b042c400d0704044050141802030300c0c1d01c140140707000342c020542e01008450900840590300710642c041c44a02c07003210000741002e1407504c031203550000250b000b120340e18141903403180d80c52900329003006080d02c114890401428100602d040c1101e0407a101075200c4101924040140301c82c0e42e001d110940c1001181345140f4180c02403511407401d02407103c100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 351545098 1250 351543848 351543869
    0x507090b03011503111003060b0a050a0210091101031404080f130807080c1e010c17040315061409011421061e07230a0903020d0c0302090708061315 65
    0x441803000560051794806011240c03d285641c04410a4055035035a21411a42c2082403022440a5028400078100032a01e4419103010588a1440d0703001c451002000b590315840602104115580501c03540c040100304152503005403070203981d400510703c110b100b0183c5a032004030f07000e206816120b106a002c0d04500041e181c01d2070325191481da41b291903104c01c9201705440c03400000340c480c003460a28024803041e074a20101840381e4071007805141d10075142c40d100310810880000861906a01442c116451400c0411101e01c0c090740910041030800c001440750f1040401040724010608030f00743c40000c2502c1301c855208501d0450b0b00302881c44010000b19004802c2004066003a010056000300c0342d081004a1940720b0300c84c111a0380c40f62403800a407220304500414402030401c406480385100d2454460b60181e20381d0302080f80350980e0350044030400b00d540400d004600d048000d45500c0b03e4541b5100044c0d203880f07000500706581d410009031820750ba80c060344180f08031100304200a444203804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 351546348 1250 351545098 351545141
    0xc0513030b0f060a06170405030d020f0309010f0501050904061a0409030c02040e2d1908070605090102032205010b040e10060b09060307050318010f0b0118030507090b0301 75
    0x104401c9180d41154524071007001080000c155292500038075003660313001d507101e0504040c1c004501444040c05401590988001e2045c4214600a80010030780079460315440c1d901c030b0510521880c00c3d120540c040502181c288001480070b80c07248d41c2115842074200c000440c40b00300300101810403030150300d40c02d9001420080064145508041e40c1d248691082e00e00b040728031100b440c0c2c20f803664000820084d40114011509a020f03848401400d885460441910004000340385000103482c0642404c41d1928008503c8200703100c0944070b550b5201038008020b40c518a00b05d6149000521078030071b01c041103000c20000406101095104000e01c031805001009040310b070092183d62000c00e84507500301c03117050800224401c800c5600f034400714000500002c0c04c640300d100d404e035815040189002803d8445407071000802100740120a0446410400041c420700346000043c40301c41e0401c1340c0c0761082c034aa9000c100280e80000c4004c11289401c41c0020a500004002405059984c100a0380500d2101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 351547598 1250 351546348 351546353
    0xf1606020310030308100e011505040915030507080303011206110d0c081503030c0d0c050f0a060c0906050c070e090106050901080d0207080f0601050409031707031a060903100c051303 80
    0x540002c10340c2d00035150350b406030f541c030740c051140c040c0d640c016854442080401081500034200e40680c0035202400d1090800342c4420482d402c40d1450402c1921030b1054690800c02d000303003440440050301d03038100514603560600009158580000e00010105581c698800f2010340c202c0060320f03143e80720f103481400354001c0d00c000102002c10030384540004420b80448480140780000441d0740c4c400c0c0c000d000d0302c00226011420380f80e07203882c50310549942c00744079a00c000201c024401300c01024494107000580c45015600248042603039003001c2d080c0b10303040285105000001031140b08641c1255940c0e41d00355129a4102e024084c9a800607800074064400450340d0a0041a101628019507084030303107095940c2401c070f0355094819683d00c40c0e030700711000521043c01c1c9038000c2d0a00900074200501e08040101c02c00d1107121040300d032440001d56450440c1c3d1000e84007805c07850400303001c9a0b61418a550100000c0d120600241c881c400541d4820030012200c0c012004d9802d4080792406101c1c10966a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 351548848 1250 351547598 351547621
    0x90507020c0a050a12020910050603010b07050c010e0f1203040504060b09030f0105010b1b0c220501080607021203100b04080601031106040b160302011d0705010e0a08030f16060203 79
    0x208005031090b2008a004105800c260440604903000d20400d203603615071079001d0011180c1c002d480010004c8103c4400b003106d403180310003180203148038140c456480243c0c0c00c015042600c05000c4038100500000c0101d541c0c1e0324000103050300c030307811607442840050101c04a4070790700c03c540c0400d0704207040c0701001510000d15405001300c181e0aa080c0d8100701da0111619003240d100f40254045a0010f0002c0780001036000441c86442102c20212903038800b081000038450010701181003c00884541908192031803402000d00401d80e1310b000b483c485c20032500103500d90f00100024800414080005003181e0b1524550100908181600a59540c0ca900c5056180c900c00d01051320b01d426418028030700c40c20540100d1303084680694500d0304218403031544a11042d0a900700390110b42d02d51a4145104012004a40b4028403440081092919280000d45003203000c94455205060f000b1003044010000f0003210000d1181c1c501f00c2e5039a618403d804079941d5615a8050851403000c410840c0301d1684c2d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 351550098 1250 351548848 351548863
    0x150c1101020a1b0e09030301081f0e03040321020c150702010e09041b080307080a050d1d010618021303020d03050705070e07031107050c0105030c0d0f140915010608060a09050702 78
    0x4600702c80001e035071786000c10b903601e20003072141c41d2041d805444014030040082c0000300d11442d20748404182207218110481c51038205802c1aa1408012500320401a031000b480c00c150000600280100f521341800142185480d10071754034000000180030021a0310034101300030034a00042400502d42004d080944084031390402d5107108205154000c16040000000d8031840341e0701c11270742032901c0d82e84d800c225002e4000d0754886582c9a2181900300074034041c04c1c3c940c100720800400000d002e80c41c0007410100009440c62a540c00c910401150b41000c2e1844510b80c20b0341e8054810030f140707010a10741207032244100344010303065000742d2a0200b0743e1205a0343e0307940602c0f03181e0b8041c000ca0b542201c400ca1980301c0d21200030302540c8038030301b413400300d50240c2c02455104042000c45410310058001103010f5448030b000c02c120701d6980e061079100c07903245840c455401440c0e4a0003020034521009400640720810b02688040c00f0a00001482c50b036901402c01001d010b076900c0500140c00c0c100e030007030b42c0c5052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 351551348 1250 351550098 351550109
    0x260903210a05010501090825080118030305060409020d020f0a05060a050a030506010e03060f0a0e1b030d03140f0402031c0e09060108070212030402030f0a031701150c1101020a1b 78
    0x10b20000150341d6104402d040255603001c40984000e81007622001d28440c021200c1e00940d0301900070015407158203101d42c06540340320038000400520079250003401c554006000902c550720f0080888007603110610030602c1e403603054a840c00d4120403d0009107640c1c220303034401680040c000400b00744a0740d000780980905107413602d05010f29280c3c8001510b541281d0700c140360709980280000343c21408000022904071100303050000341503105034100f1b820205603444482c01c40046001c503103510304040084001840442c84d0400c4007040110110022440207020790040742c0805022400355982844640b50b0148220310b207400145481c10041c01c03402025000d01d00c036111030b41c0090f0040d401000d41c3c500c2107a45070b020340403150780240c2e4041e142d000580141d8052240032501c00041404002c1c0499281c040d845403d0740e100356008402c0d0400301600400004403603008000400364003d80203c04103584503800d64180703107100300101d1034407030b07401c002400c040300c4031049054401410a030b8509848 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 351552598 1250 351551348 351551351
    0x708040e041a090718051b0f13080105040206040320040216061a1f021204030614070302070c05060d09120809011a031c05071506090606260903210a 65
    0x30360f409081500c0740c00714410400c444d0344046240c80c59540e280d01080d4410f09111096082c12801c484c451800d40280492101d1184009455082400c1d024a440c00802c0000003e1040740362035400320301c0c81d0050344070043c190504c2c0e030541071b00d990b606a000102100050f0086403100b6015441240d00e5145640541d17201e86442e00e9200c080218441c0c02041c68030180c410b044030140c10340c01045000a005800045000b0700140d18801030900c3e000b40001c50045130003280c07031707810252410a200c20140c00b01c000d251040000c91f001a41c2d2540c20003c588048805641754216114408080c0c90100401080c00c40c0048121200e0741d00a0078060050b50200c001f04644803d00b4a100c5040e010615159407551055101a841d2410703195440b403000c1c050720f4294181a00c0b42da0314401c440416200c0c10206840e00307010300114403544110b0300106094544548084280705a00986092000b07982610202c03180018010010070003c5541051601c02148456001e8003400a1801019540b510f18107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 351553848 1250 351552598 351552601
    0x5120706060e0c1e03090f06041103121903021b030a0207080105010b070b0c0d090b0106030b011b0b070e0f190302040b100203040e09070e0f040b0901020a140708040e041a 75
    0x7032101c0e20580b1590f108403d916500454244e81d90300c41604002e1403000140b00d49031451081074020701c80e4a0180303115502e60030000c03050b03108050821181d40d021f506290400d2003000c0041003000b000e5000750f942400d0050741c03000c5180c0000d0450802c8040080e00317100004403107400990000c1d19800300e031101c4000700110303603c40741407071850711a20720080c1843c800000890503a864040082200301c080324000900d003030703803541c030000c401009a0024001c00e50300d803001c070010350304410801c054210103c240b0b1000a038560700c12452940c080d00d030600304180502111003c0d00d40118442403d0301c0204121000c1140090084056105000c120301480c2844105c80712030910368540404400d0350340286050a06000c14011407a40041c61000980305000b8001440d840b138000e03560080b0b42070510080c1d1440c00b41400761220380c001e0058a140ea204220104005601250000d42c0c1e00713241035230994425150034400300034059038110300740000c0c41c80c060201704428800300d06541d401e0a800403172107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 351555098 1250 351553848 351553861
    0x9100b010306061202030a021b06010f0e13030305060f0603090309130b011e0e10030504031b030801150201200316050301050f09180d11010605120a060905120706060e 73
    0x907100580f19200109100c0302c10a100c008040d00a940d001440840060611344450255a1115008001c0400d240c018000621030101410244800380c01d40100940c4582000d00c0a030f5200b000740e030b0000e1702301561540494050b90311344400403103001c0010021600c0f0701302040b010b900ea5000b60061031103544000499240402180580c43d08504140c46460040c07109980f0304010100300b8441500304400c1c0305445045a0301e01d070504243c2c4081d0303500002e042c501841c014003000303405c000c903403036802640e400100001d510161060540d0295044160000c05801c810382c007506804400e0300112142031048208021880040d621170518080ca070b08040c10300312801d8945101c00c0c0a560f030002c0f01160610000d00f040d4024503042010060201c010080354501c03941440702c2c5c2c8014800280c0d101c1c04480100d0310034000c08000d80000c071004111340c00100d1400baa0340c83d5a04001740403903111039104090010900c150010a146c4500032617507144285404030003840305000d4507000d0a4214040303040d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 351556348 1250 351555098 351555101
    0x1507150e030904380d0303111303080a0f051c022104120f08160c020f10020109230c040c02030702090709061205160e030705031f0f201e0309100b0103 66
    0xd20311300503211031110b10303207600d0403000b80032070b010050001c1c901040140e058229100c9100b000f14080c0c005a92141d1400350300601c00419141ca11081010601c010100301a80d4402c80da02d240d4400401a0345070003000180000c400d81008089500615108210500a01d010340c8503a410351346d0b8903020440360003802512042c00580b040b10701c141340c1c0014000154042d42410f1003080c00200325010401c026400980044886000340d40143d46601e075680401040070380b00fa910600c501c01c03290503696100c440540e80c10500d480039102c0c40d240e8081104090007801102e562540150000300503103019403000c2c00100052050400044991043c0046640b0a10030140200101c540c8414034000c1d02104417181e62041c064264103020b04007001410f6901000484440307542000c4090400445c4074040040f207200100280b49981000030341c9010000c4030030703850311201041308419111507259042d43d400d071000f020b4032452241c0010a002003507000145031030b180305101c04140429040c4800440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 351557598 1250 351556348 351556451
    0x13b04060b0903060a0e0303130305040e0a0b0301060506160215070602070803040b090109020d020906011422050a06080c030405012c06100506031303120f0204051507150e030904 78
    0x144642c07c203001250414034960200c070a064080e10b40907003807a440341144d401011069a140c4029680d480081d1228182805500300a2504a4005040c0b01d0801600300702d0801c5190000e21982c418060926200c0380c03003040d58805504050b045490743c20b5454102d21381e40c0142da095510118a03c00500ba2040500402c9202503000c0e2521040740001c0d820300110041c050000c90501c1500d0441c250784006010143c158801840c01902d040e0300b00d1030004ac0c4201c403981146e030141241c0341050040540225410790410300d130050141e52581da6060039801032584607500940a0481c0c036150200c030307402024006200011400761001030322404107442c5000d0940c480c007604030301c1c00d10001d035a400000000084241c0281000074500082c0c181d074404460b52541e51041481d400f050034820740c14401110204100b004841904d006426215904044004882900c01c0ca850b0040100712540a0082d2900088081d209210460101c0c1030b1030102c54084038404140c10080c1d00c84840c0405410140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 351558848 1250 351557598 351557621
    0x302160302030c21060f06150c0706050a110109111302090904030305060103090506040b18030a050301090f09240f14060f0301110d0504050c013b04060b0903060a 71
    0xc24a40940d40c081c0483c0c0d0036005648130700d0708168402c0d84811041448014445c400e4200c40c0115407410341d04110880d00e44070000c41c0072010034020401110000100078040d254141412916032074021400c0b109014650142c2d0340c65403c00610104100301c4810b200c0e48400e04892080320b008039003900404a0042015a95100b10b42e2008100032034084d07400117802907810f14000c43d454107103444039803414006071011609004c41d001048542c00440b54081c10a10441c0095403a14048100081040c0418041c040368141e0340c141d1411400317001c0d402040110b5100a0420046160780c0c0006100b070f03403003d02004003e0070107101c14403480480c41000c409049490360384010f600d80340b0030b10141000c0d00c0c208641640d40c07103085100b104699004ee02894030b03030401c083340fa842c00c0e14006040000d0402e803981802000110b90103400703144885800c5c1d00c00090245225221129075180301c070040948100e40141c500040895601d0003d0018560034806804139550740d15040c841008881c80ca502c07a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 351560098 1250 351558848 351558853
    0x6020901080105061819080f06040615151101090606080a231b03100e0319020105040c030f03021e01060509060d0f0b280b04140103020303040627060804030216030203 73
    0x34241c6916002d580407016250780f15400d46c0d1a5210b156042c80c040c1c100e60b4030030490f880407041004000b01ea000b14090f10304580c654441d19490004031001d45800d0001b80e5017807105661081114880c25409002d5140d000030050004594808045441700c00003081034a018481c502001c064041d800300740041c03640c1180051803881c00f01c81007501005190200303035901d80079034054074408526600071a0901c6640030051941d03105075180114072040440e0700c807002c0da4104030820011802000760f04046a400810000c5001c0051074203e082c441070980c040001e61107028094452041540088203854080c0c0e424215030319054200300d036030540220300415174440c9032040360001d00105002900800a400c5aa40126210f50402e21a0b658030400c266a15034541e00035000d8645030056214410142d44c1e0b541c00c0303504640200b500d9100f54010607085c0a0040e0000d0a050540025200d00b40c80c4d0780d08201d13400b0b4503000002e0034448160f9041d0018454541380c0145241c82c541072904a83c2e00400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 351561348 1250 351560098 351560137
    0xf140d020702060c010906150e060a0e0601110a15110c0616090e01030803062b060e0c12031201080304060c151e0e0601410307030602090108010506 65
    0x4092029602114040703070000403d0001440202c0240110107070140301e124003240d650381010200d440402540c3c09880e480c07488030f040c0700003600d940c0a900e00303840d0140c59100b6259144070051703550000d61143c40115214482c0d1200030301c01841e0390004c4406050005014049021280a10758001d01901030001d8010300041030100c401d080322140003202909100a88a40e0b4580c02c0c0b81c41b0b070007640152882c200001c1002140d29214015a40c03040180c0b0700109810244000703081c444c4100800240031765585c21100d9007001041140d00008000104107800c0030380403c50103500d1f600314811f1310f4051080080082942c010102c10355050b01d295948030306549185458294602501185d12000c140c3e03555044401d10510030101c0e5010034003c9400314200305040300e03951911070140d0200c405940201c0c02c110266110039100d840c0d00c982200040281010320607200804c03102510116414406c1c88000420020582c0150034051026217503685031f41c2e86c0d0f03414007a1510035882c0300e0204640b4001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 351562598 1250 351561348 351561367
    0x2b0c050c071e17010b0414010303020316061503032703030203030a050a02092e0323220c030b0f0610030c0c080a11060a060807261c0f14 60
    0x4208108000e0240002d0000a07554a41e00440c0c24a2141501031651a090102c59038241405200c144450503000c5003c1c56156890087d1640150b42180c03c80442400c051001c0c8403aa42060042c0e10360254001641c0d1743d6464040c01c212903074100c40003030a048030b406000e5400c60045040032650990040d601e550b03140700c8200c0040400400c034031318056081c00101003c1d1240c82e0807403100d40c40c50801646504030000d41180201080306400109800d14a5040220342c83d5407501c03203042d0600041c403040b511160541910344840e0340c5034602220491507a40107004024a1101c03c5a000b41c2c011411030310750018514590300112045904103180d80d0703000840620a80c03200c9075104007460100d6141c5c4d50b6984651440e48a50215400203c00100340c12190901f80700310780d045030740c1d808100145490815543d8036046c8074480c0c003406c0d03400350005500b8003100a03191a48509007030151313180c01c140c945110900d03959544441d000928901001c1c1025400760803007076440c08009103100d061002ca407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 351563848 1250 351562598 351562619
    0xf010e0c1e0d0f0618020702011b0b1b0c0d1b0212061602030c0705090c0d15140d020a2d03050304092d020a052b0c050c07 54
    0x280c480c4120400c01c2007007400850225508a15504454900541d01e07102648040203595002d01150700c2d952602404000c03150705685009010440c0301c40140c0c403904035000580e261950520000700e50350b41e03056a02d0410001d10b06451040703000320076200e4903a25203100e1100d103010700000313840030f80d0120558000d02405503590a20144c1400b4641c140e81c80c0b04d601007100c01c416040360410b941d204500b486020310300807600444209003440114100002901704564518680c49058000c80c0f0304d4000c00e00c4040c48404135012030340812401d22000c07000f4180d02445020b14030031400e0f042c005c0c0b030740342800d803034008034040c8500d8000f08404a11403c00c4d0001c1d58000c8010009001052104040c80387c05c0368104907000110300032400b0390348803031600030540c081c1c9241c0c80e2031008500c90781340c0000c0b1a60b210102c42d00e1004122030010303240c02d00b203101030f13039031340700d05500c0c1c03201c0d45440300540455001c6a49000c4070107c01c4403084c00484210b60050703801d4060401801c00541082c0c0084c042203100303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 351565098 1250 351563848 351563851
    0x903020f040e0304090615081012023f0f070e0709050a0303020d0801090c05030f06040b0d030806120d1d2209020307300501021603021b01050403030e1c021906030b090f010e 76
    0x204003036440500c450b039069109403e00c009060710024080d03100138a0103331903440841c000345407000c1c0100140025070281c54080c5070007640c4004100c1c0c00450016031107103517007001600c030161615211945a0601941d02e01568602c8800246c400002080210243c00f40707c10200071b130b49034581140c950007025007c81340c00800070350308281e840440d040c4546e40d4400e00c21005000e901d641c0e403241041014400c0411510030f00900c0e6a00105c1e40a0210703512040c01c7e0303500801c1e04109510213030740750005007603c038502d81900a443c0a030542081c404981d613100307000b0103108904503070303455941303415209026019206a02004207010000441c80c44100c122081080c46203000510b00200c010500d40e0300c213811501540103a02000510745c15811100060201c40002d080c03007402c1074911340e00100071109440c6118019601c241186034001200001a900a070f4020f2201d010001e412860502d075070a24070600c4c00080c104103464405080082429015a0640354103034801d17802d024280d44000b00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 351566348 1250 351565098 351565103
    0x60f080103121e200118020907020f1002191110230c07030917030301060311121503070b0c0a081c140402120606010903020f040e0304090615081012 65
    0x1001480303070300c0d0040c014150b00805043c940ba00103200c49401c040701049180314a00d01c02d10b81c903091900c9400c100d0101c01001059049030841d1039603940312000c070b007050500e14400c42d245c894180403910422664000c2c00700c80c00709034000000519541011680c50072050a003500382d03081501008652480c80d00f0075454a05035090414851407000442d540d803040c01c07140b02c04032400c045180742c2015031280c1808000c10340c0748945022581d048441644900c410300c83d000516540ea102061404402d000399203400100c16818403261a255190403140070038070203800e00ca4001e4040200d55445068281c40d5541e41081c000c000700500c81d52884001d41c400d200c07035481c035100c03808001c268180500034031803008941022107081c0e05040c814040d5101140205078441c4c2c000404002d15139030b0291920003201e030116035500303000c1112004240280016284204e05010015012620180b19003181c0c04503240720b200e1045d0080a034004440b08482070ba1184018004148204415081e9218401c46c150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 351567598 1250 351566348 351566357
    0x90f02091023030a0b0d050f06010e1b03040c032a0614040e0619060f02010c050903031c0b041d0606030d0207140301020d0c0e0f040510032004050c0d06060f08010312 73
    0x4405c0d4001603c184c64104116400d50000009040130034051040a0041c200c10054080c0e9050551000c0e000d04025034240801e042d02000290602210f00443c80080d030f0003440110b83c1c4c401d00707045006e14403400480400c2100c0c83c010002500ca1107880e010b8901d100a0352802d041a080402482c1209006403265500c6a4030010510350016582546401010281c441d00001180660043d080d52000240310040c84030900048001d40c402204942c00c82d524409505d1442882c00201402400103650300c50300103203042e0202d81e62441c8100a2141c0a07200001c452071591107400700740d82e9000c1140502c0c0160085130082000d020201c5150003150b0004002501300070011101404542410314400001140000c401c2d0240c1030140c42400d181030151030610041c5070035004a0394018192000034011188a50340f014860f2459006045d1050014000c2c06541890803000c45503402401414040d0f034a41840000d507a030040000c62141641030301e950703099038030f9901c0300190b03550386040040070300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 351568848 1250 351567598 351567611
    0x109020306130b0601091404092307030203190203150903040b0703090510140412170309070e070e01210e0625020118060b0307090f02091023030a 64
    0x6035018020a8030450349250219102c26641c1407145000c200500300d0390510040711410300400e6544108907030749403025680403074015540d140081c440d0810212600e0b00c2501a10035520400d0081101c3c800c8034000c400b03c444031895961900f5250f00c10729402076140d806510305500c26032000443d96232105d032400030740b07003829603da5081c461f40e8841241240002c82100c42445680390001003501c030145203140c2030106413840000d01400d0310450052001c040307400d139013480800062109488240e00c004010b25100c0c18180b00060f50359a190245c0c00500080c8000500c406124100070465560143d440900d988007030b1f0f480305400240c041100c203001c1e40701e001005001d07104002c10350280e070300001000c0403030150b034924024920b102100c1e9030031a41801d40d0300705044013402240da8466003080f0001103440004000910b0202d2075408859954100002c80c100c1c248668083c001344c14069030020b907401c014000898003207a058203403480c2e1121160103264060120000385511203518100029007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 351570098 1250 351568848 351568853
    0x102060f01151b08090a1205121804020403060234030e1c0506070813050c060a0e0306010e040606090b061603050d090f0c06020c0d06020c010609140a06080c0f010e030109 75
    0x5000f4070900680d24640000345038842410101095002000303c42040d104014407075907000d4484150f000c81d801c05034030116880806000140415104280007071085558982c0d03413410f80d000e500260080c2d1002c0c002c2d040c03d2401a144445011a0150b07040e8810141c2a900d41c0c060340c2c500b1600349916000580b0a10400c0415081c008101190340150020b104900c0e01349002080c0d000c008060305124004082c80304000765000440b607404003000c9601c69210003403054107c442a03260340105030306219800000400d00f80140751640241d00540d401c0c0019602d607190103007510343c1200440d800041c00c000c0f403044040030a0400c811b8501c42c0c50140c0c0b6102a801c420004c0d00e4a01c0c00c10786074041074800c018200304001140030010512030015221055141000450360101c40d540540f855130001190160302000390f1104001e0200d0001c03c102c0c800b001000d809a00c07004850f0064210314020002ca0b070100005105072036000b00910801001c40b4a01c01181c1c608000c00080b9019901c40c13510800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 351571348 1250 351570098 351570137
    0x30904020408160b09010e040518060403090e090304050603060603101e0e0f0f042a0e010512060f0601030f06030f05010c0f0c050606040c11010e07050f0102060f0115 73
    0xb4164400200300320807480d031042141140503030065500010400012189981080303d4000200044a00003015540c002c2141c43c0d251084009114071302454041008150300700d00b140d010303500184025842039840c0309400b60303a40700f58040c0380ea100d401800022030070314040780295480b4112031000b802c00d568440401c41d8005150101c03001030072007551700f804a90032212900b070b40000c01040840f124106654000c503441400340018060383e82052000a1440d0054800b001040442500ca19000e96640046c2d0403520203003e042c0c4034180044860881141c0000c0c014010080401d40b0340031520f403080150002d1900e040034085194640c480000410340601c0f9018010b0b01540000c9581c540204004100c0355800703840170140842416a840850710004040c0e40c040b50550300000c080e4045407054641a040940d404015070818803c51840380c4041420700895000380e4180c0c0e82c0007584001a80c5803402201c2d01255000040c004001c080b0000d15a00300303010b4681420b14030b07040134583c15132 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 351572598 1250 351571348 351571357
    0x1012080c100f0c12020310091d2e05100e0933010e01080606010f092103080108030405030325050601060306030c05040504051f1506030510050d051e03090402 69
    0xc400301da99102c1c468000703411070704945201004d41c0007149149086940d902c415010344c0548082242d5410701c1001c40050300b00381c100b00344000811144012132450f114007600d0745440d001d140d41c0002d540384170f008000601a19001b0101640c00d070785060306244218051102c001c001111030b20400414600a4500c0c40528203215512001c0100b00d20b40c400c0038100c03000040e030090a0b1941c07c10010080c0780004684660020003d1a081c181032011420840b40010141c2100765450240300b13591000344507a080c06c0b000ba038800e4481000301eaa0301e401c0551240160302c505a09608108541d41043c1d0301041101c50001c81c0c4d00c4d804003002980d8481c0d03032501009810100102e55500c0052042c4040740d45000c000b85401c850500007490244d40c0e00e92121590708600c1d2001c182080c00603074400c0280c100f01d101c00c0e1607500f8040c00b5a40d40500030080e0006581100c100f40841c5001300326802c02c4038803490b0158010740100407040b0600044a41d0005036800c2290a0000740825201595240004c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 351573848 1250 351572598 351572621
    0xd11010e0613031407060e0a1202010e09090f1606020a080d02040b0f03011d04020d0813090c0f030615080f100f0b040303020c0f210118030c03081012080c10 69
    0x80001d408a909131482c00b0015040002440300c562410071203969011103d0040d5488040c035035a140c0040e100503190a052010034070392201c010750070042201c4001a54074518500741040b01c0d241d0340c3d10350744110020b0302c0c2c0c000d400060304444003000214501c40014414030b00710742070042c40c041d0b0301c1c4940001030f0002d035002075a0b240c000004205a0a02002d2501550b0a030b901800060130306a002030800003203080003e101c65404125403110b403840c2070b0440000d2242801c00d0101d9511144d004000840d060116400720f460648003240d601d42c0f04540d45d42c1250079440310011510740302d1818000100050a01101482080c0013164150031000e89000904000419540b104e040d454040c0c01c007641c0c074490900544c011108411640c0c2c80003500c40001c5c40c8044040c03044112542c0c1e590162003002c07c074154010505404500301503102403226003c0e8000d656404158540e103082030301d80316581c41030034400c5000810f06d002140c980d00041c02d00084a004640c002c0d00c015058030150f4180766a00e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 351575098 1250 351573848 351573863
    0x10050f031008060702011b0309150606081f0f030f1415250804060e010608120915040e062b14060c0406020712060209061206030c0d11010e061303 64
    0x411003030300b04110440e040500382c0002d0203590036607200540c03140070000c1c04a04140e181c10f4404144201e551100c1c8d01a00701d98028046c031500d81c80042d05011003034605070760403010b022402c80c102c214480c0c0c10080e5042051080401303461034a80b01341310020004180c0d00d280300c0000d100d4114108101e104101400c0d0084944c00e4600b000a00018a54041d0481d00e2061190024001d042c0d20550312680164460000103150011440d218014070075600403080340d10518000c0311031a40300d20081c0456030f90440d51203c03800703907540e10254103006620480d5507618040000c80c80d986800d1106001d11942d10b040440030704201c2c4420184130012840507195051001016141403009100c4207500c0254802c51624241c5001c2c0e0080d83c81020f481000c0c0d4400c081ca03c40c0040181a030101c8082401c000e10740e41c3c9845082c4d0390a000d01e142a91614802c3c401c0c0c001c00700c170b40c4c00c042052000998002004190220300800155082c0308501540765002100b04036500e003e0025440080c00340d07005544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 351576348 1250 351575098 351575131
    0xd06060b0c0d0e010f0219080f04090203270304170a02150d05180a1b0806071106010503070e0610090504051504051b04061103070804120510150510050f03 68
    0x83c120680d25182d40d4100640d00105040090f00003032a01c001c45002e2080c01030030b00e018200082e481c09003e038100100940000c0020b101d501940145001b002540c9150040040000c150705007008440e8034200036420600c01081844079014241340c11801d40f038183c81c7d50908d41d500046145010403401d004668010a55119150103031203801d5001903807412001c0c110414030b16103641e0341c1d4411401084000084814581400d20021400c02003442c581150442e003020807025107a1071a01481c4051071048000000b00c80c980003684404484c060300861001d03444500600c007840b0455441030090210030100000e040c0c07128032030144607802c2070790b1803041903265004010075201c014100e16248282d007110141c450341e14000b10707000c4404600f0302d4001d000c84035580a085008454010b03040d030784d01080004d120b80b6004843c1072110b01c0341d4151840c401210a403101120065003a44c964030320980c03014000350602d4820300d080700c161800d1141c10111480c20424140e0b1088a4208401c00e0740503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 351577598 1250 351576348 351576373
    0xf0f040e04060b0d0302030d021c09050a02010225140d0c060801090c050903060c0a0903080c060a0f0e151005270c251118011401030603020f0d06060b0c 67
    0x4211441c3d482d0445000358203c0e96620000e40c1c90281c0c212001005900103024070107050380c44000da4012008080070f01610071181807441d143c1001c2c2c1016030150040000c1072200071001c48900c407280c0325082020550f1424003642c40205000d1410300d5412000000e00c001c041510380030540020b00280c0d0b40c892072076050035682ea00f541c0d46d280c0c9403814400c05000e030003462f640105041c0e40c0400a6052a0303203c11050b00300304c2e01091143d00241055000081c039417625a00811305a11a03110848107001001c0c2c000c80000496107020b00e8107441d5000304440000c401000c848454106060844022809031038100203000d080c801800e01e2000181246d0543e01d004031765440c0743e48204c0ea00902030500030300600300021480c051000c0c0750141c24100201042000759612056012009031420850803800c00d81981542028061070707403505200b82e4010a10b40c428090780d01525406414000640080800d0080c200f40a4200b1108070780c0f035190200b0b03200d8070301001d012085d00c2c503001040d8111210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 351578848 1250 351577598 351577601
    0xc0607091e0504020904060e0415060f050d0f060f020c030403050606012a0819120b1009090b03010b04020a080a11070b0403081320150c120f0f040e0406 67
    0x154441c1c00508410315240c06074504401d041001c81e04140c5001daa00c0c00c600000500401d00d9400202c5841d44060a101c144400201d150401800c0c0341400c02c9020340300c0380880c0710f644080c42070507030180180304007400046115138001c0340c0700c2c03044d034001c02c059903402d00000903038110389181046940042410000c1c800300300038440d0000428282000701d40201030003903040f5510803d00800200060158104100380b280c1210314400015002624800494038010b040000150000c4d02d0030741482c045c1c2015240c04004400b04808a07240c1c0e051081c40c1c07403070980161907104c4080d13605541e60050500c041d15a03000504030b04404c1d9980d0348541c64071607401c608031540d1f00840003c2c030710248407510004a000c034846400c0303909410700d901c3c955203c0c100c0d00d944484040000f001401641c280080d218036608005050040888803403000d86075841c076030b100390f0199551414044d48070007045044821000010030440c1040101c0c14940b8011904842456100798070804554190000b00030901071207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 351580098 1250 351578848 351578867
    0xf0d02040e0c150c07060f0c05160503240a090c0e0108030301030c0f12060e1e01060812070f020f010c050303041b06052115042316021f020f0c0607 65
    0xd40990300e041181c444c80040d60307200030b401035600f401460201c0302001801a2000142c0950102c1141d1140021042800b4007103694443c103806031186120701508820038050710500d91020300201112651003810784405484c0620068402008604010400e00310100486020b400d03444000c0d50749500d980303040c01c2407070150380c000481d00391f005c0000e010b90380309440e0362159907801030070110300c1d180105281e81c1481643d050700c22850a401e40c90660058040d0440412551010140c2c4ea4551152803a0039291180b480000e21000399044c0700001881c0032241820811010300d00307080030a20513a14507196030b0050700c00390340026500301c00300706000020010001800407171810320b0410523081d06c3d4980c45420310401d0510984c814000403840c10500500c2c0c045850300801c01c0c01840c807034114035a0842555a2000b0100382e4000c0000d80e58004405100c0d204551a03004110b140141c980d000c0150088083c200302040e002c011412200440e0300241111244130b001801743c0e41414140503122610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 351581348 1250 351580098 351580129
    0x22209091208070801270e0f070f0b04051201060305030313050d0e01020d030506030c040606050c0c04060b07030509041104030b1f14190509090a0b060402030f01050f0d02040e0c 78
    0x40108004401d0380c06480d69045401e0000c0001030501e034a028509000a000b03c1b100c0518540303e0400801c6c000024482e1004140106660481e9100d00c145906003045000c0c2c50b080c004100010400d9080c0149210380c00008a0000242d103a103e540e01e03411503000b9680110b41d000c02081c0300090006c00d1100c42001501d07420542e1403420304d480040d440360031100440c01410790f07407400a00561030500090692800041040003040e40f0780801401a80140c88408a5440350240413800c0e418035115034401e451400c91081d003440c3c21568101e4081e071200c076000d07412944031402d0185a00380b540140025505c03c0c0110308a80c90013442c0f208009003d5512240c6145281c40204010790220459210030442071301d80c981205016401200e003003646600131074110b034800c001c01c00100c2003c504101d41034031401034105103440740001c01042c0d001c1584c610302e4820394240104032502c0c001581c20820300d4040c00c241e225494a4000600302e884101c241c0d40640c1061680c80c180d4941130818103c043c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 351582598 1250 351581348 351581357
    0x10080706020d1b02030111131d060315040318030b07031404020a050d140a030f08070e0a0902090d020901090b0f04090c03120903080a0201020d1107030c03030222090912 74
    0x111456004225101d00280f40c0025910740b0302c840299202034101400d400f11040350760b6a285102c041041441030360b40f007142040c0c10502e9241c8030300c0b6500c442d6603000c0c0384010000c00404990000e45881110081c108406008000c03c2544200c04603240d4000110f0244144020501d4000b401405807000c6009140c80c0f04c0c0b881003000016a04c0400c000160384081d110002d40d1011440d000048240003295803d05104a2001d201015400307443d22140b0710243d51035203c0e0b0b45812000395144000d46ca41607600c01c02109092043d00c80035030140c451010018000318401100d078021442d0001c0a8105415182d143d245256503410300080b2207280034420380702000301c000141c03241c00b48041c250000a014501040c801005144204c0c0305ea40a9904541c90b542c1e103c8030014064001d41c4030709281c20040f403d00304980c0744502c40000340d504058240e10b80081c90b2155a07822402944103449549030320075032528021280444a24043c0500130a600000d802491801c0c41d8080782d0682d0003040410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 351583848 1250 351582598 351582613
    0x607200a11210a0f060f050f0f0705040314010507030b01020d0206070807031b0207080717150403111603110d11130e07121109060a06030504060f05070f090807050a0303050702030309091008070602 86
    0x150f161507010048149c11402d68480c0c400450383d505c00c65101500c042d850280c07032581e00206500c8680101c407161801c0010318005001a0b0b12810f4249015003d41c101c0c400007100107004075240c0790700803014900000e505011035241c0c1ca0b100424004e83c00180d006c4203062090000c204100c801520b0003041408103165480c6130f41d542d640780c0c61030031240c01c85000045020980101d2400c0a0000c0401c103447c207a8164201d4500794604a01c0290362810300d840031403001c1d04011040210903500401c01c00502010710742403048084600c14140b04660b52032038083c0d54035009101c2c24010303200788041070341c6150950a1204035041e031801103078451752003001400020342c1d500320b8190440d001400c002c80c0590300c50803c10001c010060802120a040c0f20410032855440070040c0030079807581d2503842d602d039203400e8942d42d540e0403070281980050760703400d040c40828001d070041c1c11035a2000302120f10702903124010402903a0103950300c10208920000511904ea8180524400f0740110300c002c0010703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 351585098 1250 351583848 351583861
    0x100501080304031113050108151303050d05091006090b04050108030f09012007030f120305010305070b0f0f0c031c0207020306040204050402030f0607200a11210a0f060f05 75
    0x1c0784074070321000f40742c42640040180d081e00d804501c00403044140004000a607035034800310791a000282c12460060f000e01002035854084401c048104641541c2e40500701840420352500174807010f441c182041c840c0004800e08001c550003071002a00b9199800700700c0381a45802e02058410603040200c99030070138001c1264a80720001900c1740d01d107091030403086501c000710011540c64a11b03884558103005034840030007403000903c00c1d001a6486845000d1880000a00403421108207000060850704981010452800c00602802c8071106218607285080710030790000c2c0c910790107010312229075000821124081007640e64840303c0702d010000d0039480c0080301c1d400242c41e000010402845281c0c0e403404502075407000c0007658000e40a4204485103418910000742001240000c4090101803444510911000101d9422803550348020403645181c3c14408021440a00b090102045551070008001c20041005440b0f0b5050041d407520043e0740980c00c200050b644090b40c0d003850307a401c11003030040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 351586348 1250 351585098 351585103
    0x60c0f0816030b0a0b07050313270218030f06010627150903050321100f0e040206120c040e010b0307020a1103010219030501051305060d0b04021507050a0510050108 72
    0xc1c80014900001c083c0c1031000020620f46994010316049400456001c0801c0b0000008050b84c03000705950302c510554903c0801501c0703610240041003459954941d20140d5004e4000c2c000400201e05034904040329040424684410009100001c3d4807000040101c40d403c140804105600003078241038003150300c181010318030014441c0c40303004c0c201c0e80d5080d0102c40c800c0610303402855000e02500d94030203280743e0041e6101000070722041c0e07100c80d010100b82010468000e1400701c1e9140c01c0881081d0b40b41c401120b004140c0204140e810000c00c00007580301001c07001b40c0d544a02c40685010743c4071410611050242001604600e0034110100288440a6000104204051783c001d240051191003000402d0190082c1511160524120160001910f40503001181a150240c0d165102078007a6001c010603070310141c0703140d40c21a020361411000304084ac1c41c810751083c00a4401051019400b941c130140c0d501c840340c103031841d03000080c14034108401442070070400d0f0402c9100b449507504010b180380c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 351587598 1250 351586348 351586381
    0x2010203070b1302130c0207090e0c06090406090203090303090f072607090e07060e100c200d0602030403080603060714070c08030a050703141804090203010b0d060c0f08 74
    0x802611042c800200701007828400314040580c0a0f02d41c50f1014070a140d64400340c04a0013403980540603003c0302080c81c0c040c0b0700c64001d030300c041c420080000c200d445090050030351000d0360309a0019241c2401003800c04282c0021401104900e0055a80340303001c40c9114282281c14000301000e40201c401045455070f4200031070780514664140c030b400d8203110079901c1e03e40f0107207030f10074442507003401031009c3c4004012402c2011181c10303498500440b815a07041000c1c00b4500d40540f40070071082000a00441c00401c820740008805c20f590100c402c0030000001c1c07501650800c11140342c1e80010400c010103901104d080e0300100107900500f100c2c01c000a018013550301d01c80440700002c01c086041d40a2110f81c242203001015208107817a95070320f10081c004e2071075101003025400f2512403488003461b0134040013100c940340d41090381d05034508071800070003001d0807035400143d9140d0340b03459085505a9600c0d801e41105840b800c2e000883c98411030014001041c3c400e04281131040d0301d001c00030b41124014074030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 351588848 1250 351587598 351587603
    0xc0f04050f12011406010905011707030b01021905241519091b0305070216030326100f060309030819090b1906210b061311250201020307 60
    0x10515501c10000c18a40e40c0085060b010560a10042059040010300740e01e000b04400c1e81c9101040351900c0041d41c00080003400341086106802c00103007111320940c4900d000e4070701407040e110308613400014903108451050083e10150428201c5442407503d030f50201c0c01403032003601d198020340340026002080b4409125070a0086003190305803100140d12401081c05042c03214010403445000021700e003641c0d2541108500480c6c078210101d201203000044102c00c5c4081099999031940c19564201c0d01c0c00d150034221035150b940c0c3c01c0b121040340000a0007602c2008090908038907285400c4004803d030b0783c154000404d051401c090720010951081c2d9503175128810090b04404400b043d03041c00001c0c5a5510054055000c21040c013101940007107011044200c200414007400d904e40c8070142c0c218501841c034080d08140d05041d80000703010441d6980e44900010082e51a0310100c085440070303034180c941601e4040c900041c1c105060048107030750113003140071006078400125281d03002030364074480c25401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 351590098 1250 351588848 351588859
    0xb0a0e0a0f061d0105040507080f01060f051c020d110408030703030e0f03040303170604050708041416060e030709020f04030209100504150602010e0a02090c0901030b06040e09060c0f0405 82
    0x10040c0800e058000800501440100f84404101661454203c0c2821301a440c801c0d8142000f0500491103402c201c0e00480d0110814107203179181c40c1d808d13115940400c00d44410b0100500c40b181c0381c403c6040d140104900c2649003d683e88880c9143c05c03040b15075405c4103118401c414401400b40281c0001528007031681810000744e00c00030940a01c1c9003e8500d081c040350b41c44005000b10800d07501c8980d202e91010200564410351b2240c0040005807501158000e0016581000081c0410f80c1002020807146204054480d00d000100f19503050b0070b003581050001c140840c040303681c1030604100210050559250850500903440c1078100316104920001c0d01c078a100001240943d002c901d9506e004007002482040308200010950341e008071548030700e0016510340500400501c8003c0b81890100b07900420705840e581e1116581e024a400103050380b81003541d515901100c6458140040c0042c01c1040c041014500d0320072466407905400500521603035000f40320403030f03e5100300801d40e801d60b441100c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 351591348 1250 351590098 351590111
    0x40501032a080105150a0807060e010e011101090b070f0e0609040209130915060e04020315090c03070807240c060504111e01080c16020d02010c120f030b0a0e0a 70
    0x6010706005915009142d1552030030060014403590b4120400110805481d010729680d0f5032820162100910311486001c505007044000c880d6202e60303100e1080ca80141020070303c0c000d6406004d0308441c2114003c503010040001440fa00303a40110060384060010f1604410300420200464014014000010b00558000c41c0c20b0750155035000f038004100450100c02c0080308660f08001841080399241d08a0301c41c6401004aa400c45020207540300e290003400501c041c81400c030300d0b6030041c00000c15498250095200010540c0d800340040001044490b004091040c24050100c10b02c1c0000c440711107111002c0c040d401c00caa0b4010100408568010800050513030f503038201201c1e180c0c01400030980c407448441d41302154403910200d401d06008282c1e03510016507664000001d007841600301c680f0300c1201149080c00145404500e135691144107140102d8511503d581e499000140a41c0000200b60300308900100c0d01d6040c030807010100380484002000a141c52000d43c545c0e217000e410059035036220b89 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 351592598 1250 351591348 351591413
    0xc0b040f080d0504020f04111605070503030c0a0b0a15030f0305090a03150b03010b130e07031b06030b0d020a1e08030a03020c070f050f100e10080402090604050103 72
    0x10441445140c2101c46140d848001d41c44150051008440407403007010170a420420fa810144160112807061a04640c40d284005864840f08500c0c0c020840303842c4552007012405403410b001904456040748014106001146407880c03624000520000400d40750229100d9001c0c2da58000c401200d4101c1c080b4024032001d030034215241d01c60a41c9503504a01101400001c100744240d41182c1c052940c5000c000e800320400400d401d84001e000e10541c0507601c0c0e0a01070b0540d01585c0000001d812841c02c54040984e281d466030511800c04079110000a0520000c010503a0075002c0d115200350201c4105600040e164001185a00c46000c0c912004416618070403442001c04400400b5061520849884e00d200050007006540854181d01c6640280710380090100900015641610360082c118485640040c06000c00c060065400700d042101c0119003c000d41c9520f58100090035260366410010316090050080003440900700034051458000100b020401101c00c9110b0a80000940752a407035212 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 351593848 1250 351592598 351592613
    0xa15081603060816080f010608100b0310050a05090609030f070f0501140a020406021209030a0308071b210507050d030b0604031703060406080703080901030b1206041a0c07030c0b04 79
    0xb900203a601c0c0c421404c0022034080d240c2000401c407403501003107500026555075044d00f03807002d0b8410f900d01d69121240072000800182c01020082c6c0000c3d0403202503014960450096541c16145001d41d560f40700d090004d580d5044c40001d6120210600941c940f240580c0b42010034491190050720501f0104503c00400000790041c1d14840c120421010083c248941c5200080d0300c0352003580054410392400c000503050400c01c0e255100002405440c561030107032000d855803000203106408012000c43d072001e606580d01c100c03c0f1a138ac0525070180c6203d800c032940112401c0a071b2000313018070205010820001d10700040c039030704a02c418580401c1c07500e00640414070a000c3c80e000103010044940507000c02c001d28a01941c85400d00b110140b10741d03030351002000d071500070502024201040401407400380394003e410030443c201005d07006043e081c0041900d682001000d840454440b03010514400300a8190f00700c03960004a801c0300e040c40c1c2980790b5406010311038000d02c010400c131010700002e01400000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 351595098 1250 351593848 351593861
    0x402031603080a12020702090403120506040c02070504200a03020c010606080f04110a05031509070b03060a031e170702010f0509061b0f0f0609060906151e03011a0a15081603 76
    0x140003002c8c00d0510b4a400303403410500d4100000c60926202c0000d00c5803030107010b084030a00840d001b414000341000c0610020301102c010b5280085118485000407402003002417001c00900e90340141ca031040c072462039095074456403010741003050003000d101d40c00d52000d41c0150019840403140340c2010800c00820039241540d40619418010034010344481c0d03440d500704070b1090b1070420548180d10b40303c05603038519000c141e4038590801140c1d5018070014800c2c1800350303981054149002c0076002c25550701e9031003c0c0c000c0c81c0300001002c013051180031941c102c05c0c0032895881c01c0c10254188071401021980398010000c208260344c1c903010200344600703801c1c0070f02c081c1820b03504191003501d00403042a5588100598144403948195800502c400c0400704442c0d0182d500c00c181501c1d2444210100004441309404040601250110302d852503a000d00c01c0c8502a8400f51030191f0b8400c2620811454842652258014580c0030f0784281d0f09550012030141e002503e82c00100c43d000080f0000c4000300724 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 351596348 1250 351595098 351595103
    0x519091104020d021e040305190f08040b041d070e04090602040f08060603071d0a0c0e030106060905040b01030905061b120405060a0b04020c0a1502120109050402031603080a120207 79
    0x40024000c12243d2140c00030304074001e01500080d880c0c29403501000140c4194880a4081d030060721a0244001c00110603a8025015550a89440c0e01030340300c1001c0d950155100c4002500b00190812030020400c086202400070380200116515140901030002520709420703520440d075030801c0c00c0801c400c0d07506131009002d00700701625000d41c4851108c0c0d078403070f010780b0002d00c20b2141c9140080c1102c28060710340780303101a0050901c2551141d036810006000802c0c00c403c2070180c48110040c1d280c40c24410100104001c0d80d51500d035519041c2400100c8096400b240c2c101810030f10854046180043d4994001c483c4000401d94010801c01e402414042c5c01c040c5c2008080a83c00e11092107030014107a80030b2250f41c0f20400609080b541008101e1040018244c0b45810075407841303001c1036101007140c10341407501e440503241c244180d0528a03861000d8001c00c50080c1c0d11002e10056080810042c0100400c1080c0c1540c070a0850b142c1401c01c0c0561b07101c04d42004191100c58000c140c40e03805851141d503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 351597598 1250 351596348 351596351
    0x516030225080918070e0f041103090610080d05120709031205070c0905220203011d010e10060608010e0402031e100e06060f040207020409050d0f120519091104 70
    0x5001d481c155045034484404184a000e900940711080761007400c040d4014105512200300c0c1c240301400340000c8940001c82c2d01d5115a40c0c000d04200250110700952188040c013010f84400e00d810103142d002444181c00c00c2d4515800900c0d03494455803c241101c0e50203a100d0541c0f0700a90340d007071040b2140100c2da04014041d8042c0d8105e00c402ca500b00000c0c002251181082020103504c0300c9030281122000c446c491280d02c3c2c0c011456441410b090304821495001a00108030034a03110100407681c4519001c2e440c0c0c5039034ad10100d072400c00050040c040c0c2421000d4042c49040d10f4020010852001030050b00c2d00c0c5413243d808281155020001600305070b48610304001200c0000021544414001d80c02c0b850890401d00c4090303607900701141c1d051150900501d0031019104100501c40290031249080341c01540d1005480701040c001c000040c1c41d80e8507580c851082d80b00d00c40000b00b140300c1c00780641c4080d82c00d00c024030001e0703a4034048003848100d06007400194281a070030070305c810046046a607034009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 351598848 1250 351597598 351597667
    0x90910030c0f0e060306150f0409020a0807030c0e0903040e1306090606090f0c1d0a0306050f040203100504050705090a2301080d080f010e09030c01020f03070e010305160302 76
    0x101c2c0c00c0318580212100d101e00d20500307580705000d043d211142100e8010083c007142d8020303c518038040c543c0341041103019000007241a440ea0100b4070001c02c80c1c004034529801104104100300180c1d000601400351403003400c1085c102001410f0340c0f03026501485450f00704400c0040c030001001c03050380110f50b422030300602405d01c00e420158020601c6000f1403100c4c505205c04206501014011101c42e5151581c038a00f0004000b00c13032030b100304925200a60b100d461960000b01080032402618060101c21820103400d0400344101890aa000c25804600714140010003000c228080390200444400303a40100c0d40ea41d4101648006100e00b079594415146403403c4032242d034119200590582d80d542e01144e0f60140c2d045000d4407640002c5401ca0030840024005002c00304080c5211a0081075600440b42001400b04a15003681c1010740d01006500d008010441c2c03e80c0c1c400602c0603010b0080c00d0401481c10710401d841c00000c1c0500d148000d0540000c0d5505592010009440000c161144000d400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 351600098 1250 351598848 351598859
    0x1806171602101b110c01020703060e1204082d0a020f01210b01111f0216150906060b04080a0b15030d0c0203101509180b190f11090910030c 61
    0x220f2200c1101e880003a802c4640300c031094034000b0307400c8540d100c1600180f040c50302d50341d901005003088014096030380c024100c03403075010b0a24501410103400345001a214841d8514020200c1030300403011004010b841010002483d00040740d0b5441c11a010f49000726113000e42c0006850307045c4908103200c10100c00002c182c2e04680142c1c000302c4400c4007640c40205a00340342e040740daa20a91200011030342c0100c6500b6442c3d1590990080040070350844510070448801d8458440e51041c504d03112000648032000340c0c0c00c00c0002d109540203842034044550919003000340f0f0907510004003074000e14480c0c684c8e0202e004d007817014184240300c00000701100c801408008004113242e44004040f8041c0c8200c1002120314007040c018103695290030b103006080a440c000413803016064000005e00c101240c0c45000011030b4610303074514400d941c554045442405940300c204100d4089203900c42190741b48c221070303040401d82c0004881c00024111041070140c0c58959502440180aa000800c0d0385083c800010f031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 351601348 1250 351600098 351600131
    0x901030809040b0f1305041115250807081c0f0e10060501080601181d0603100501050f060c010b090132060f030411030d180617160210 59
    0x1c640c40a48007403120006150501c000710741e003481c1403540700582c074441107948000c591003668800d00443c554a042284000811145100104221a84100051148000701e1b038080520042c900084000901003200e4032060f2003030207000701c001e0104e0400107081c40c03000050080103985c0099124200074080c01108004010000d407181e01e0703081d001300115826064028402c140c01c0740d5040e15030490940d180001141c0222481a40c403141c1202000b01042070320080c05030400d98030010510301090300785202017502e0840904047e043c840d0414005004079181e0f50b10b6080005015559952034801e404007031809840d43c2d0f040290070002070000021020942e03106181400d2100120343d11201b010b203403140c0603100c03607202c2d80d405c850100305c0702c01006100002154400e0141c50281c08482c201320010307003000b4100d1000000a504c8100d00c1ca45160300007640e200800c028244044020b140441c60703843d80034010056510a601c406401d08654024440d074500848240d50410114502a00740c03007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 351602598 1250 351601348 351601357
    0x6020105011503060e01050103051e04050a031e02070b090102030f0f030609060607030212030601200f06010906050d020f030a23071202010203070605041407060306090e0c010504061d09010308 84
    0x1507004680b502c000e8086400b92040006035400c07581e481100e82c0c2008019805081b000d07104880ea4a800070700080200681302c00e1900461040019003144a91030600401000e0101c0740190202c00420390001c04580008046044032400128240c80f1101c501c010307800c6000b000f210200d034500000310b0f03500405204e0f00861081e20308a6600d46d05444401c01d1203070b14052000d0003405648545100e00100c902c4501a5078449014541200503400460584e01c807440b40e0706c0026079544c00708800c480070000a001070360141100810400c48140b07400c001030b40d00c030500c80000c0c0c00b40b030228030107800e40d46080c801006403a401108208081400f0721030703000500440300200f00680a040300100301442c46054200e80d281d01640114104079950700c0d11002041c0203001158004440c0c01900b21040d0240107482c010a9580c0f40092a146401c08000c180c402841c0c4c203c0c01c90b0040e50401300704d681c009007030306d040d9079640c500198055081d481109006160050312030380804020300001c1080f100030002e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 351603848 1250 351602598 351602609
    0x17030a11030c0706082d0f0a0f0c031d010c020d0e0604090203101a07030914030a050f0a0b0f04080403170405030a060605040e121608090d06020403050f07030503030a0e0102090a0602010501 83
    0x100800000e072210030310410b150600c100606d010190224a1b070040608003a0b401c0405018005020150740000310202c5003c1d0f040c100100f5120318504142c04000004607a040342035200911080303401081c029250b942041c0510300340608203035600c0c11500c502081d01c002d0000d0200840d42c0f4200401c0010700c1e02454850304a440062100440b5800584070648408980c5a2680b02c5140e09203041c0201040030f140c80517406206201880c004104100f11250491a140011b0040f00c0c446040106540368014407a214840005050000168600040302c0840740c0000100000414100341c8503040c1c840c03680f207241d2600c0380350044000d0000e01d43c02501151022141008240401c0701191340700c95090700cac01c0007410003c0c8082e00038260005103000c20b651007a40241d1412501c1c20000316040d0740000b082e500c01e0fa0200c1c3c02c1c01000b008000740b43d9a12003c01c014a40c081c6580d85081d80c0744401041070b4545901e80c1d01b41c16040e9404d4050351407900700101400110794031032100174000e2409101c3c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 351605098 1250 351603848 351603871
    0x9080d0216060c09240e06250c05011209111c050703150c0216180603081303110607080904090204110a120515030a060507051209070f17030a11030c070608 68
    0x41170070b481c80882400f0420a640b0b65818601d1804200451904030446029004000c2c80c0c503840c203048480d45008100c0d00c10040d0301c45440c184400100340e01c00b44c050f0506564508507003a0041000c41142d021003035001c41d011030001d0030303030b4040d07901d02e454400300200b2600c0f0b8074401000300119800760410b02c0050a41c02c00800d04400d0b0b04a940c2e5212006071005600d454200b4401031b2401f840c116078042c0b001b1004a83c00c0d0792507a136103401d548100301c01204a03400c0e4000344104000030703614203804a4111200d608088054460f40d400384030310110f0074411950303048100b04645031a0004c900c94440c040300300351103844180014040060303034000741426030300e800700060840614201c00342c041d80014005240120840d50740c4001004c2c094070030300502c14180079203c3c801140301c540b5441000c8440140840c18078000d00c410f000381198201286040c1c80418080c3c40f1580003060b900c10b21a18504607483c00c40340300b00306040d84a2001c46010078050f0680108085400c003c06e5030003540000c06 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 351606348 1250 351605098 351605129
    0x16020d03050411010c06060b040e1801020708031f33020619110d0c05070c0609061b140f03041d0c03010b0d0b030a111309080d0216060c09 61
    0x40850403501e00b01c50052032040c6951a5284551040c42c00d200702034170500b8006000c0b902c841c10020290015400a10002c90034010044404945801000303440b03083c030029410714507156104081c60100901d00509041d0022600c0d03034039128814184010003600301508110b2420710b03481041c20035000c00c4e00c085441c5030340f240c0c05020b10025511340b00b81c0103d43e400c2c1c0c2440140c5c800c0d4015101c03000803018030b0001844000b40001c0d45200303425000c030003600c5095888d82e841c074200d20390f048194080002c2c4018075400704101d82d0008100c1c626140c1816201c2c01600041c5021001241018803081c01c6120720035108140c001700100810640e80d807655082c7c0a02c0c0103000858443c1002c48450780300343c1e414801040546003200160000b80380c2c5601c00308200b148140440e140ca80c90301c1082e66000911101180e5509107805401c1c845800000305000350422615108824800c02d5510b52400b42d0000e05c0b480040300d80001c0c054010b5100e001844045007a940050901c40d01d406002c502c10361101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 351607598 1250 351606348 351606373
    0xc050a0f0323030d0f060e011511010507080c07050a0501090b0108010f050103050a02010e03070b03072c010c0305090d08070c0306052d04020a03021906090f0b07020603070c0b1602 79
    0x300c00c10080b40c4034500451522460954020142c8119807102c0c5045468400104801c401e15007094043c0c01c451040485050140707100611388840c101d601c8065924050034000c0482d80700286a03441040c20f0328a81c0e1700c07000d070b00e8081d140603d080343c040c2c11946000090410000034450050496403401e0080c82500e0124203290b04a400030722004005910502120300154090204100356410080503995aa40c4d1000c0b016180c3e4401c0790840009810414401c10202e9548407560701840e2540020040140e6080040c010380715146010741840b002090070512035482401d500c070243c0d0311108154030b0391510f00d020800b078611400100c948505003000202145101e80014408a03091448080f6141e01d00c0c0d41000e4a41000e08140d030014044100800540c80381c1c0c94445808811060148070725103080c03001401880c10f50043c26030403000850421100f0808400e81344c4243c1c0480780155207894040c01501c40004004004000c2d91410381000b9400c1080400c01c43c5070003598003034464644440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 351608848 1250 351607598 351607643
    0x141204020f04021819050a0308070201021908092215170c0d11060405041e0e030f180d061503060b2209050a21090504020304050d05070c050a0f03 64
    0x407000c0040b02084c240307030070117182840982c11260401c504000c9803540350004205409096081074075880343c000760820031568104401400009244410561543c245d52444920710500015510a0b102c80c0c940a02003284002c0454400900f003c0820401002251001092400340f0441120746440c0112070120300c00403540c1c0385912401007900d00102016a124020303022a200800d400032018400030909403168490140b1041443c50164040303482c0000b907405650b0342001c8020950011700011a800c0c80c0311043d82c0260419200d00c00100d401100415691003518001529507814801001c60ac3c4111904082c180c03400b802050080007034113820300405442030326007400414441e80460040d40143d50081c122103201c1d0f01175444990094a4544134180d0100100e04804148418005001c4e04070001c00000c01007035500b03505614050700c609032181a90741115003403142c006039140c200000e10000300090040100342c429459250b40e42c420544110f400304881184001001c5020070042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351610098 1250 351608848 351608857
    0x6110309070317070c180506030d020d050c21030f0709060f0509180c1305030c03030405041d07031a0604020702100509041508030a080705120402010807141204020f0402 74
    0x9240c01400d440346595100400005240c508120402c014440c480c00038250a00384001800144040007441803180050300c1124006401c080c402d5100320340e043d10b00b60300860008040d1140342043c54884401c00196030800c001300021441275100358042d12041c10023031000d14040c440b8041d0300d24499a03007940a5070641080d004000100304110070201245120380f0041803292000344c0b103101c4072201f41c004101c0010040d00c1c40c9110070340100746c142e05c48103000c4980004050807030080000c0d081c04004291a44100d001702c6009640340c6900b62980780350f24440510b01410303802203501d165078070b003081d420b400404130100f018043e07090085280d03450140282c43c03516800a048100d00b40c5003040c25034203a804854420f07001a2201881440701310101096402800301d40302a50f5100000349000f00a980002c00c00c4084c8078090105e65a46140030002aa010b603080c204404282c584601c240d81041905822070101080025800c160021242815024902c2924041c1c0d68440795410841030780034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 351611348 1250 351610098 351610111
    0x1d030405060a0306090203091506032407030605091003120e01050a08060307050a0306060f050d0c0611010212070f110d0e0f04090503030903071509020108150a090612061103 76
    0x42400188114038000c4000c00e84000c480c1800a0f010b030362410320005036001290320381500d4100045c0650b0390003580c0088c560002d01140944981c0b0b200d9800680074042c4040d8070000540300d100000c0e10b00c1e00a512070405007500804404080c0f416500555101c550360108035003e01d200c110160107640615900e102e034080c1619443c4c14150300e0441214607004c01404181d02d1311500c0e07000031341911503210120155000368404a90740d42070001288065000d940114083d0910a503802e02044001c20040c0a81d00680380c13140c0e034180000d00c0c0c14013a00850751200c0b2000c0440e01441035030341d0020200d0103203000359142c62800e242c4421706651944c0341702e1042c0c408241c40504100803450401540684054020310004d5400d0b00341d1106072543c6c00468500650b68400100c420a00c50f100b00f1038070424206150a015010540d80000d110440151040391a00303502c801d02c075096651618141c01a000b804c00801413a555100d041e81031030f00104040d10a50b00e0100c0c207410120041046038450fa1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 351612598 1250 351611348 351611353
    0x70b0304121209020907030c021c0203070b0a020f19030c0c0302070501200304030309050922030c030509221104080a020f031005070f0f0e09060906040b041d011d 71
    0x41401816103440c10300096900c0500e50f00c449000042e503403041c2041c0500c1695800003801c07491250301174505610960b16602c10700000c10b00180b565800001c45001a900120704c81c22911408039040283c020080b582a01070390204002d910000c1e0046000300e50b284954050002004460090f1a003648151002d00182c1080c0000d100c954000d0210404084400b0101e041100804003540d056800c1500100c1c00149005c00801151070160102d58000000f40e880f020f521200c02c0e012446030044a02c001d040c8005281001d052500a1040d507405a00181071401128001c0400010110200308102c030710500d40311850250720100c03002d5400307440c00e110041c48403154640030030400c00c0440308840d90510a5071407408a03406913000c0d01c0d000e1540f9485890010340c0002c00074000d00c0c58a01d2000c1002907120344544913075070f42146241c10140540d01c89401d500c0e8080490081c00007c02e00f03d8109080400e0360700000381c04050a2000e0030410020042c421611052200107680101d446411341e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 351613848 1250 351612598 351612623
    0xa090b0408030c040305010f0203041a130b060d02040f0609180b040f1106040608010626070e1201090305210405031b0709050129041a07021903080309070b0304 70
    0x14110381c000b143c1040519000c241402d55a5484500351654030003204035181d0040103200030010a070701e014400e031100c142e01059901c0d00251400000556401c0035104c100d965001ca003150b1581000c4045207a0050030503c522100e00b5171030009800103214000355542b0700100b2170318162105a003c00110740c0b129280c1c02603110b40c0c498031a101030305201a24096126a50701140d643d820b402071005064a0712580460342c9090000340c014049840c00c01c01c03480c112242d861081c0078a840c1a584541e640c107004202640890104425080c41541c1044561800881505243d00030000d007140741c0b041481c1c030b0031300c1030141c0e451a880c01041d10002c0c5164400d102081814182c0c1154840b2440b8090480310003640d1819030f003094600a900202c0305245200240101c2c400c1c8034012289030000e0780c1c4d41071905150010005200000002c200c010381070110b00c0000315500c2c01c01d009440d4054420410707207140c8a00f40305000f42c0c41520310030014803c0d88000a6140d580b502036a100342c0e0018011b0100c1e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 351615098 1250 351613848 351613853
    0x6030916060f0905040f02090918060901110a110a020310062402070303050a030b0a0906150e030606060a020f030a111c0504030221010606020f07060c170f1c020a080a090b04 76
    0x19201c0b480786d54505603028020310095445038900c0701d2184400640b4021031410003e1120305000014159807404c1c0d04103407010f10710190034011a00348194030300e0301141c0400000c2c00340d4109440050700039814003036903549001e14120b54100ca000c1d9041102c05030140c05e00300c290351003012807050141d8090f0f0032005042020074000c00250801c0d5a0906001c00c6048494000480c010318503005610700c00c2c1c0d10350b41031020750038428a045111181d030400800000d48030001994400300286100c4c895500025a01030b840c2c0f0074803018011248110440f9111500e10390080e0518084034025000392142c000d01ea1036050b08041211036240c8a83c4502d4a4141540c007441010214a0000045801040b8428140810074130905000740780703540c003510030034030103040181c18085650720040821000c10104000b00c2c410322180c810358911001c00540d41c0c185100d030034115000f00c5408203441051003242d14000310302a0002c0400324810f5461070b03415034401034003104840115101810700c2c03032140b000800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 351616348 1250 351615098 351615101
    0x40623010323030706020a121802090411040905010501090c0f05030c120c04030209040b01090e01060503030909092107020a15020604030c051f1a04020a0f0c06060506030916060f090504 81
    0xb602c042c22030a4034540f03041511208247d9205520100000b0303210310000010030001d00c201210060941c450b607004020a8002440400001d0005001c0801c00001007140d0390321903202241c500d6001c0001e03c0305603502d13003d03080201103114040d00840d101c5905030b8040c512401c1140c0c071a220700070074903040c690885034040300798070005c0c6420100f000030030020015070b503803164031071182e417042c40345160b65810f213101101a41d8001411555603030500b4002d00041c0d03408400e45150090544071206c159840415007881c1c5050209002c800101d40680d03000742d02210030003008a203009540c0c645099a60341d032102d0341d80b04e6105040c030050b000480410300082c0310b01d0620b06654015000c658041c50285001c5104000c80d81c07491542e00e581e20040322101c41440d004a401c14822181182807406004025101001400d610700402a00340d40345810000c00340e01c0380000c0c2602910658036031500e2081c2590390764001d80c401c40c040440f42030008001d44200400481c010566a804050520b00000d100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 351617598 1250 351616348 351616403
    0xc17060406051306020f09120d0509040b0a120f060506031605010503250c02130c02120c2a0111010b060f0a030204080111070317060a05060c03120406230103 69
    0x211543e0364440300d008600b550018200c0c11050600c1240d545a00744c0800c030301040d020528540c290400309150a280d038000040d0381c00740000f5100031035441c0d101c500050710006c1503004004500c8001d00200140b004500b070700b1a42900c1072000b044a03458040406586d8040000c0e4040852203803c4103101d1540720744042d542000c580f0400d6203030170040c004008003d070004035175040041c8000720154254504030841c000710b2440418100220403400d10300075110400790542e400044000521010b446004012121450001e801c07104004041021000202d03541072004a0001e4041d8216401e28401803185520381e040040c03102e450b002440d90700700083e410207841c003024180c4c00c1c0000a2100400e006100d00c50401c5400140c1c1e412644c07038060001e514012000079508035400c1002021b03150303082c070141074940499400380c4a2105980c0603144d44201031015030300c10084000c2c0300404c0380a400180c003002402d055001c418075010840c2070108403d21000e00340b40e1880450320500d01e18940b548 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 351618705 1107 351617598 351617611
    0x50a15050d0b01052b0303020a030605061206010833032e1104210b06040e100207052e0b06030106120c03180b040c1706040605 56
    0x18100d82c414060350b400f070000c220489090007001d104a1401c0544a4800c0703008007580c1c0382c002c02a400c0194140b0103c4d040c41070108045c038051003514090340400d0180e80300c1d40d454400440d415100903000c2c0d44031040d4a00800d0480c2e00c1a071440c060302e007080a082d400750342c098003454541782d4416241581c894154110720300402d000790140b2750040c49c90b4030106540c45d05002c4210244500d6010310141ca00c1d4920b942503400100b142000018003a48401c030095030745200b0720090b40c07030040100104e600300c0540b0300d42c440b1407a8040c02005c0d0145c01280d003200c0c1c0c1c0f900c22420f8140030714071440300c1e429511402c1d91030040a0088010b03004013510814115458540302400e0a400f030344070f4000035515641a010001d02c26405046120844204000340208900f004800c1c99070039181503540f131010320304c08100c040449907442e03943c000003c020642c940c1c076611030800a0002800c3c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 351438848 351618705 := by
  have h0 := BRFrame.cov_init 351438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 351438848 ≤ n) (h2 : n < 351618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
