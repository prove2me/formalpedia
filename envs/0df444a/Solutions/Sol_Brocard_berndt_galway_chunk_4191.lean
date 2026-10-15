-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4191
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:50:23.840263+00:00
-- url     : https://prove2.me/submissions/7a056f17-b0b6-4719-b7d3-c821ac5f3668

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 753597122 ≤ n < 753776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 753598372 1250 753597122 753597127
    0x7120512161e091806180504030921020d081e0304023102040308030a060e040b06060d0b0a030c06110604080307050d2d0b040209010e0d020a1d04050120 67
    0x30800a000540b0100c0310369418810700099480380080c080c581c0c04c1c982c0340c54181d6600400e1003110b5403140041c51032071865900f0001458140d5000d041f9900900031034020b248007400c0c1d60034030714614019452095002d031011800c01c00070300d041c401d5900007042000f501d4860811900700240044190303031150744c008140107494074002c0b0301c903203070380c49220021042c0f11050380080904d030700240018001103114420303165403850702400394401c40e491600700607182c048240034040860344141583d600300c00110740840c0e039114282082c0c0010310b9201145500a0303200b590000512004c2c2e0300c01da04456907070300c035113810241c244042601c641040701e005018034024000f0803203540c072401c040c240048800710300180f44104907100007103c4044507002c9002120160000c0c20581c15401217940c490010b41c0c040d401d111001c80082c1600d1507020f17201e13010f40c5280c0c1c00401559038080c4500014007405410740010700c0340860043c1c00d51000ca40c1603515600340a0120790b040d980c08040303100307040e82040d45030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 753599622 1250 753598372 753598397
    0x110d030306090606231b0a0b09010b0d030509011d040e010e15090714010909050c0307110706090e04021f020714060a0c0213061a0a0e030703050717030712051216 71
    0x404c54000304840d84516214a1b810090400d0801000000900842d82c805942c0b034280151801c2d2000c85412034002c800c10021030300025041030941e801c218007403c1200b5050702c0344040000c840316441d52030b640a03042c0345001c3c1601d0410341c040304c0041003140549008011501c3c0324032411100307488003a07146c1e004000c1040004000d840d60481d16605150000501d81d4071a020703c2622010341d510300480300d0010a000c05150048204488440c810014080301d51030000050310101451250098000d01c50b00010210b540f0107243c0c00101c041c01d64000c06081c25201c000b1760f24801d5001e50405003800d0400350245140dc0c2055400000d019561a0b150740c20740ea090200c600f031040e010790070407030726550045003403614400c40800614080e00b60315211403891900070503100d000322006010390400c92050002c1100842d4a100360740c101c1e5a00d4107000c00d50440e0350300e0351040c5d0710060300300d103160301c404010755900000505400a0240c1c2c60106900c0380030700c072184101141d86000c081500e1000720b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 753600872 1250 753599622 753599687
    0x90c1115011205010e03031006030b030606030304061d040f150b0412080c2d151b0901020f0303162d030c050409050f040521040b07110d030306090606 66
    0x40c103882c42803001103002ca1001505ca03103103810a07140e0301c03d0001002014800c660341407290064050084000300350074101407010a40320f2003240901410008848000c00368500140030290203407070050400c000d082d069100542c0244126100c120500c01104000a0420007040c04d8905650200102c03032041c07280c0790f0300d5841d10390000340002030501031511603c402000d031641e800d955580000710301c803503901c0c02440c0c45c0c144809414151810a0704805111883c9000d80c04190345050740e415441d41e074040500141d14012900c000c02050340300c00010000c2c04941110300f240c00ca034017a180d00c40321900280b440e0034100070300080131117402d00d80551110004c1c0700b6040002030100906125150603101d024200031703500100c03000e03c098445001404200314003009144060440040107400b1200340500541452290f0301c1012510a40400d50380280308c800070081038000c40007000130085a1541c900903024051910401301d140e07181c80300000350b0034011030846950f40d86403061250319290b006c0c280b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 753602122 1250 753600872 753600899
    0x30a050702150c070e011505030a09080913150914040b060a051e030d0206070207030807021302180f0a0f06050f0d0e0616020a02090c0d0f0501090c111501 68
    0x160ba01035030705000103010451000092a80058030006800c6640c00d28011210051040c0e011019080158280306011540075040e40d8200301c034100301043c1d405150900d0350080c060711084d103030301446103103000c440030ad203591218582e18040750440c030502c0d42d10750001d0300f150300a04002130b20303d42074130010b80010f503044003981d030104004140703070300654036030000c01c0301c0601c5000003040e42d007101c00c080107c40c9030030030032214800650310042c620341c03504803402912401103201c024107601002c508001103658030039126011100e900d10454441c8550f0000061a07410308003d103004001c40d00000c001407c0001c840c1c0b007524019501c00d440c881c60150216007580c4803105510f20a2800c4c0300340510442d0034010344441c00d00c0782c1d00074030060030b014100400d420101c807607000a5620101c01900141c4604589035807000100120a4a40c0c00c42c26062000d40f910755801c00d6441d141c800040784816582d800070710000784543c0c8296010080e50540c5640d911095406003901001c20010420005034001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 753603372 1250 753602122 753602137
    0x3011e051f0e072a030305060d0215070f0b0a1d12180409120305010302010909020c07050607020612010602030a110106080307061503060603240c17062b1a0108030a05 73
    0x7002008480c03500c44d04034449071032000318851550100d854000f45903042c010307a41c1102c0100e804058202e83e5a000070001e10302d070441004d500b41c01003468000c4c13020f116101242960800309507602490280c0407078000348200983d03c0395400f044242201c4114000442000c180d0b0810149072600c922071a4008120b18000c1000b84d20a13184c8903900c00045001072140300d00d4040d900e0214555056100150102d0141d4000344210381c810b0210407901c007400a42d901c1103030801e865841da10480c134004a007542c45080e510400b2060f90070000290305034000020008040113035225000040d40d55517403400c0c4d464a101e5841e1a51050080b4004500e00b80d101e020840d001c000500c28059690350390206072181903006440c1a010508131000141034140305540710041c6100411910030f51000140c0306020410f614200e02030040d000840d1610b8034101c102d8000c0c0c451010605e0061050032194000203000000c8640e0241c006800c0d1600e01407a0480e81a168208007450802c10420000c0310a90860740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 753604622 1250 753603372 753603377
    0x304050a0b090f030c06060a0501110613110603130302061005030a11040e1911150304060e0111040b07050d0315030b0a021213060c180b0d0b03011e051f0e07 69
    0x6000c81d43c900300000c01320b85060320050075051a1a4082003035070212035009906119111214090b05000031131040d07485009040e003041c1d01416400c103204c018624560340c1d500098000140000b00b2901080d42414612a03802c82d40300b9990250607026000141c890503070580d004075011000640c6d8000326200649028000180f0f05083c40400c03071910f002c0518800c0c5160074248440b0a100c45141c00801146041e40c00c2c00041218100c142c1c0c0520000344050031544c3d0382c1605500c082400e401070300d820030502c0c2c103042c1c0b240d449a0400380c0030b0b4003400c801c0340c01c0e108041003620784600900644100e5050a143c180302d4620319112030101e52402050125800d60800104050122440f0030501038403943c22180302040c0d00340b811000f00c41c400000c2e0002c1c000c0c3d044169210503550010802920131196440d40c6419000c8400b0b0080c211107180c403503165084c500c4810168809000c403d44115a0306424845078640ea107070021749501c1ca800d00300c0703d10b141e5807003841b00500c1811802d07002251403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 753605872 1250 753604622 753604633
    0xf0b06092106250314070309140708010605040617070b03040602090a032f03061602151320011b1110050301140603100611070e0903130b0304050a0b09 66
    0x1030071420050226182e0507080402c4180740310202840c0c6106400a04a080c10031602c030550005c1a2600e100400880425403280c606500700700100f4403108900002c441222084c9840f40d08050107401c1030b00409010718030709200003559410300781c045005e070000c400181806604040020700c03280e00081060f03480d142c08002c1111643c8800308500010340c061540e181c40501c040492a421140241a01c01c642c010303514500c00ca03581c0400c0807a0080d9003441d0310b580c0d010003294240d052081580f019840350071020100200d8011892581542512035001c07030700c403403a196012000411455407058001018400c0003141078080e85412003015002e02c4000041c0751000000030303004940c0b469990300195011004100c2c0c101c103890786821402d800c0750b03518110314041c81907083c0100644113001c1001010041c01c52107007020f021460191070751a1407900c00d0302d0310000e110307039036400280a04030310303c50f1040c0040c81d100648180c0340944c0d4044003a01c0c00c6115510380c8551444080d213003c0701400341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 753607122 1250 753605872 753605929
    0xd0209040807050a06050403030c1d12150a0b03070b0307020c01050f0c19021c08030c0310080d02460309120303060806090706020307170d021c0f0b0609 67
    0x400503480a00c5c49480041468502858010207403041e0700a05000d11036604101c00300c8128085500303143d00015510664044904910640303811588650540504501400c0c0080100682c010310641030003541103c090300d50b00c5044101c64481124000c00603000840c076151150322802c02031503001d6103843c603036080540c0c50407158240404801102c000240080341a01141000c001021351400c035000404010315568580780f02d503110040920050740342c000001048014030100346c0c80a41012000c56041c8100948040d42c2d884040030942c45c0c0020440c01242821481e440040d0280320701c0b0441342d514000c3c101400e0210b510218201c00307001c000240031178403541d101c0d1281201c0b4040d96001c1116490002d4103403c090300503095a8080e0008081403020b2a0000101d5102c13691203c012030303000b06040d000c801180208041000388500000740340c0f0045642c480681403010107808200802040c2e0b118210840700c3d542d5120b50004410f02101c001c0f460041c0c410750301d007079503a011180e18250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 753608372 1250 753607122 753607133
    0xc03050d0c0e1c03120209060a0302090301021308032206120c03060b030c13080102040b03070f021227010804050706050a09030f0f050d030e030403120c020307170c030c0d0209040807 80
    0x70140120403100d8030003c90024594411720f10b00c11002c003e6000c510b00308200000c03400d24810040d51505041d0009800c4415440960445d80181d00380158443d0700b54681c8802c07a01c035407142c1c0000014025080c00c0da080001c0312111101200c45940761740c5203c100381c0382503e000d0014071b000c0b201410781e14540054001a0b00e00254804d61112180a0fa602400c182816102150b03130042c051a0b80305101c1402091011021250895101d09210044c0e0401c104100e182c150f101e85c01c54010b07040890700a0080d56140700746804542d00b410548034404c810001141c0c2ca4a00302c80292007540231080c00c1003000d000701d00a01c0940f40744c0c6408000e0316120385428551082d0000100c520408900c400c00a012003400220301000f014a01401340240260b001c55030b0303000e907010181180b0780450740b000d51607000720000041694050300340c0c0c90303041e500e51a941a941200b0f210403000d020b8281400414038001c02c42c2d0f00e0130704008002c050350a5098007440699040200111900c0d00b0400915001c200d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 753609622 1250 753608372 753608389
    0x313050d060f0e0c10020109080a1809090605040c06020c03120a02013e0a0c0b060d20090c0702210a0507150e060c03072409030e100c03050d0c0e 64
    0x692000200038065070781c0e00f07010651041178207420442e4504421200000c29400403100014100e00c1c06240150041900706100d84540c3e105c040824a0403040e2400c028003034200d107200314010200f01d550036036140c4082e41c407860200f892a0385034003c50301111007500514050b0a29034424400014200380741d0968081501c00220f8040c6000b03203441c2114004600412204c004201001c14641807859802d4040d20b400048240146440e85500c00241191200d03c1583d61554020502c0140c20b0019000074500804406220b80109a180300090311000700741c00b16a017043d070240c01320061552018085400140030615501079001e10b405840100e5402c2013820003a003000ba14405514403070b0940030b89600c00e4070b41038074005c3c0350030310000744d03c01c10100989506541004520910150403d14041010a0700b144084400d01d002200c07010b040d07001d0040e1440700c005541032050f0030205001a05e071022001c00c014006201040400100e61a81e004019100b040d810704498208044000900b0032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 753610872 1250 753609622 753609641
    0x30702060735040c06050a0815130204170706020c060d0e0106050307080607020d020a030f03051e1f1a03160c0c181d0327030712050f0313050d060f 65
    0x354a40d80902082c0000214210001c0c45d2034140f070781c500a40c2d0341020b0900e8800504500c2107004224a140e1a5103801010307200412004008640d11503e951000e400072800c845e01520610551202044050001404010004001b46024207000c0c9019540c0007400d840c249114503952280f8001410362020013a40002c0d01c0908041d12107460682002881c1242500381a0115400303c040d980210303401c50400c0050120300d140c003040c9940c44a000c0420501e98049443e1402510401c0001c0b10421541940f00303c1034860907044410340d2000c5000b080e1560f40414107050800708041100c0d0030030360103100c82c9030070181808184515241c80f01c0440d161680c2c05050f07203024492440780d0300c100c82d00c90610207178005103014022100c200042c658a0180d01004002c3d05e80c06841c040c2c1d000c55005556588100080858200a458080403150080e030500102c92a10580c080b000e261940030043c3c0d0520360010b4030240005261400b00005420700100c01e6501c180c3d9481140d04101c0b142c00760b101070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 753612122 1250 753610872 753610967
    0x1306031502030712060b090402070525050a0f0311060319150906080604051c03020c100e12190e060d02030f01030b070207031a0c190207090f020307020607 68
    0xe0740f50002d400b81c02484280c0700025040d1401001707004c1c040d2031406441400d20b040e100140c44550394605103180c011108502900c8000342d00d1160089441c01620b00244c0300243e541c3d42035560758a1120640115078040100403d004c4030082100742030001c0070f0b65100c0500a08402c40d16805889502210440d1b40352120f0044044c5051151000ca030040c1c4005000903c000c0c1310901e01500c03a00d86801d0741413030220300004075080e1a45158420b07010356603903c400100b51206400084030302c130004d2504102c003e0b84c070f02070750303603e0104000182d043d980c50101d48606901c0307030484002c003100c080d9001d00105500120900c404081a1a02d1007e5485400800c00341901035065052400000c0c03001002d0008561140c1000d20001e80415103142520180700c0c122603c80c0c403000030a180c02e008205460105030f503440c004e540d040380d001070203808a401c01c1c00d040000c8015440305d10103078402164180c02603809031010500300f0384601c00785905a60035640b47c3c481115440440d00c07100301b5200c0e0b22a603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 753613372 1250 753612122 753612127
    0x103060e06060a0e06041a120a110604060c060b0d08070807020306090c0d030c08160305040e01050a0e2a04080c120106050108040f21030911031b1306031502 69
    0x2500d000c015290b007008040303500740701252510905608100d0010951070142c0e072500c0c120048130305051666a507840000b8244541c440c280426107a440d08104c1081d15010704da085900010f041020803242a01c605603100740156065403200c0c000b6241f041501500500f0305204d90700881c1b03500c0044d0a1085c07260704903503a103031000e0042601c3c0c4080545410800d802011002801c1d03501e12040c81806545030610f2180200765041c208502d000c1c210543c0d030b402d4901c096001c00c05600c81c0080c0180c0700000b4818496980302c00912600b01c0f01409040c48400c0103401140a00a0400524420a2110b0320369440b00c000d4048903002030b04560300218055201c0c18414280c0d02d03040b4108121002c02e00000c110301441e00c8002401c40c2400303800600300f40c0d8200c21300300034000e820007900801c0b060070400456202a8075001401820000019a05030b4070401c2c02c214a443c1c04100d0802e031a401150b51241007080908200d2184028903d10a006603202c9002000460321560211181e404141c0182c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 753614622 1250 753613372 753613391
    0x30702030c2a2b170703020f06090c01080106030b0f0a06080109060603020c0709020913090b011403031201050f040e060f0406050903031608040c0302120d0f1706040221010306 77
    0x81502000307002c2c03031085a14030008116030245954860078100c001c241c0d04030070035903400c004d212a00d8142d220b11002400003010b109254000500780c00c2e0070a100211602991802c103030030784034003040711001c1c0010041001008458400c1c0c000d04050500140103041000e942c41c001180d401b45e5502c03500114100c0300040204c103d0a1203024000d24403170a040d840c040031071003166140d40203400381084541d80454440d5030b40e118541028003802031090308009102c03180c1481909146c09215000c80c0030702600030500c1905020041e01c042d1005000002266400c120070040e040ba03c0900e5990055075071903403284c980c0c00070840140101ca0100c84049603007801d06026060b1500102a80c07000e500400512501c0000002c0b8514048054541641c090f19640b0f05a42e509142c0c0d0320203540403d0450301c650568902149608070348840e0749550a00149000041d41d144982c800743c3d10174613503d04005000e034202500100010b041600c0d28100184c2a882030038410382c001c0c0c10665866640700843c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 753615872 1250 753614622 753614683
    0xf0e131515020a0b04030302090616020f0105070809040507020c0a060e041a0916051e030a0c08150607060207050601060207060201110f04090906090212030d051b0f030702030c 77
    0x420261160302804001501c10503406580c48065110007000d11125000150501d4406d41c1a40d034a548000c01d03d0341c0d502c0c02010040303d803450994060f807141c0d00c0da00f032111181d03001d00102d40180ea07102d07090a0801141c913003000b0007406c00400110a5001d00c214500c0b240c2d44010605001e0199031b142d12400201c41d1062008440302d10015910001c000b20701e0205035995590080ea00c10b19100414080600c88101210603000b403c00030990109030759202c02846503140d001d54030507075501504024200350b0301022144600300b550b41c0103d42e03031426000c84203410400d00070721040d030107254090729084040d5203c43c0b81030801d9008200507000b00308240002175083c05219100c2c001c0b04007a90814111100c664140e00c10380c402c0d2440703599600e80398400c028068110400c140e400500040e40d55035681c40d20760b100d41c06681140401440c1000149103020012001c8040d05000400307a800c1a165a182d5101c2e0343c030140006081d80f02c03d10006403482800c104402d0b198080201c0311001e0210344505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 753617122 1250 753615872 753615911
    0x9050d020328050301030b180703060606080a09080d02160b10030506010605040803120612060103080912150403030e0703050604030e100302031b0d090206040f08150411010f0e13 78
    0x2c0c070a00440d40d4000c14081c5602c02c003500d06403a00103085038160b40701c800035580d849a01e08203031440390154040c0002031141d40d41c0140d00702c48142d1a514010395441c0603517802c580050340c00810540b800c0c010568075600c50341c040d09001840107203400511038580c075140106241240d151001a030001f2081c001c2000a20000b8010301481c01e0407810300c1d041c000c1043d22800b868004440008000d80081c2c1a50364075010f004000c0300c3c000558485503107074101001d2680c03100c840760b40a1b051100c140c1c01e103060001102409a82200340d0107a5545450f03a088000c0d00e03c45241c1c1c0e01310701ca002c030301001050080c801c07140140e10075180d4007849507580c0144101203200042350010302d071051081102e20161180403000b98505181410341c0c401302500c10320020001c1520182d08160081000700d00315030541220015644154110390384141d071000403100a40b01120018001c901c040031052507540140703002003641e0b007c0c0c00c10704100070300c090100d191080742d6042036480c6621524142d56550744420f2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 753618372 1250 753617122 753617167
    0x1c062c010209210723040207060c02011505030a08130308030f0615030f0613020c01060f03050c1512040206040e040803060a060e030a171201151215140409050d0203 72
    0x90034040d46810003d46495810b207108241000d801000c1864126460481030212107500400454a501503410002d00030030000b81d50300055840c01c00c001048814501da00000c45100270300505c40d440345543c0340011504030004001a0016060000c00000d0044016510600704264002d200d441c00c0400c100e41104900e080302c4116008009112945199010b1650711074003c1e15010f03412100d0601090081c4906030885800e5440d200c3c000c108051036a8113101143d02071405c458440050b0707000c2244c13000110f2007900ca000b00170404000d004240559007036000380000c10490605a98000c0711aa40204490072250300d8000801c0180600e00303985020080c03c51031a02441300704070750300841e1b5a40c0981b4000f030403480300c2c1103030042070031218001c98080314542c100c600305e5941c2d5024444036022080a0000c0407030304112250b065085c580c420440790030380c15404055904c2c81c003e442c0101c141175600300d5402ca43c443c081100859002c02458100010f02c0d8010f5076143c11160100910701da4901 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 753619622 1250 753618372 753618409
    0xf14122a030409020f130f151d0303191101060e240301112808190204050406060503060109080c030604030509030a0516050f090c1801020708060916051c062c010209 72
    0x80c0402420f021074520008c505040c00300301c120416444049440060740c0081d8540b00004114544841d084100d014000c0140c88200700301c589481514241d43c0c260068664020209001031210052441c54540110007600701064128040c00800d09413924040c80c0b825400000541400384009c1d10011402000082d0351610b500340c4010000348404070240000c10701c0c0c24000703d0380d00c00300602c1c0d049a009000c01070081184030799031030000e0540e810850701d150104043ca81c001648800100700e01d480e802008028040c103695664040c1e03125002407a2682c3c0500c04c02507007000003202008003d1500b0b02e6500841c8030f09140a0030061543d4014084a0240314a0001d010b401c0241c8003c0c0d52044250f41d45041d20040c0c1100100c3c078000031030f84420302610170780040c451404000b042d0b0212508160340210551500c52003031104200900c0366581c00c1404041d01d103004222140d0100191007020a207181c03100c10060014603241c0d81c090f101602503540080c06000030700d003400c510171803440b008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 753620872 1250 753619622 753619649
    0xe011e0f0e1009140a12050106060315030506070c03051c0501090e0a08030a0f110d0b0306180a060f020c100e0c09070c06090303090f14122a030409020f13 68
    0x100d000074081c00a51140000445a00b000f04c1c010341c1d030340c1c00320802400269038941e8058019084c0385003c0c000380c0c450030001c20710f402c5c910b03500000300c0c42010065a4011b001000c3e6915400000c0303555107000c2e0780503020000b007440422840e030300c903688040203460091008101941442c500c0401c54042182d075518a902c01e4a10070000303102201620340c0002503000c00184005050703035540c06440d440c140403004040004034848040c80c9a800401e101d002503040702e00c255188048981120080c4000700c6042e031010707500030001100c9800c112403c0c080384201506155078444100c0c60300300140054400152100c00244100c0000c003d020360030142200e074040d03030b81460341c8046d06040b285480a00055150922181854040d0b042202815032000348016001800d00b08000c41c02100400325803113015460509980e0348120b4295401d164034010303100108000400110180d100c02903070030383e042c0010f02001969054030702c00380820b140011085507842110522049611205070030000c00000031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 753622122 1250 753620872 753620899
    0xf12041a0907090905121606060509060604050d03121a0102063d0b07060e011b081819060e0706050c03040e060f0901150f17070e011e0f0e 61
    0xb66403001c0b1008100002921407aa00742a8180304d1502000c8104090026511000c2103444241500142c0150402c03c82c00d41c0703031b10400013110303070507200e85a000b50280402c1c800e51400c2e82000c103140b4824103203e003102c03542014000688400105d800410503584090b1041c0b945c050129952000030502c2040000b29410030490501d00c2c625005120409900340154012162402d010040c00c0300d2940e0319202c1da02482c024010341821110705080307508110324000c1c00c05082c0380f941054900754491800650305c00c1034810340000e40c1c40380d11589100310210342000016900c0b8080310305005000c0401c032407912506191070440d01c0e90000040060801510f505084007000361002e40c2c41d02072141e0f20700d8079030760002040c095425400d50750161443e800026200f044a04403403408955840d10803103124801000d44507941c50412060560310781c0000124042d05c143c0300701220000504050032071461140b204040d00d640c400104000c5200d010300740c034a2175000301031a183c1d03200854024000101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 753623372 1250 753622122 753622141
    0xe031002031605130902032d0601091e03020a0305060403030c1704060515060c010903030605040b150d0917040e06060403030c0b0603030c1005011a03060a03170f12041a 74
    0x54100c5070b100b000400f060440b4222030203c1c02030014401d070b030002e540f64240100c00d14400c810b00021561115429415800400b610005017403081f9030507100e2507441c5203006031b080000206ca102c032013640f007014100800145d60380d9803042c0107036005800522040c58140750217021624100c520b20f0620004641010300340300181d01e102e901940c0f080d008030700c0d9242c030110f98020000304101c0d00d80c8100c0108200391118415801181d809000765000d202080e50380302440201c9070040c1865070880050240c3d88210290b0f200286a80b0801d0100080e15140320f0303c603c441003e068140d030300684800902046509a108000c541150013268024079061030344d500a800c540079668000c003071900c40000240300c0d650a005035110317200c02009540340740d40403001d07400c020002401540e4600013030040304c114032002d80c2c0681380b2800028201414982c112f0700e503801c10ba9000d490b8207290700745c1080064038030740200380075140d10130740081020b406080500e040002038084100280010703000c801001070034007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 753624622 1250 753623372 753623401
    0xb091003030311091f03150b0403060207050c0a0e040501050702120307080921070b0f070e01110709020708040501031812180e0103081c110711040e07060e03100203 72
    0x241d050400044282c0528609652401428001a03100340198100c200c400d45221010800012507901080741c0207005960b101c0300c103003900510348010801d120510004000e5401030413214001c008481d05000310303500290f654440782d0000d8048041e940207200821209025440d0001007a0019103940e50200d801da140c240401800c902c1041202c0c804190380f00c0d814000020f05001102940300c80c40c0f611f003c2160309a020107800c441203d41c120004030b034a58800000342c01105503a40e69225825080300440301410440340e100e00c1c074043c08a001074188039510080000601c28400c0544a07031820001600702e40e980740b03100405401c581c0b6248005481c08040c2c800350622410802c100c1c80010302075814012403a000803807400e44040000c801d0100050140465a4003d828480003c100c0c9413090240c07401106c6421414109000d544002039040c2540c4c05000c1002d400091907440c07400d000340c03600c00d080c1e0214000c200310740030b00003140c282804804084500c2074025450360500c45070138440740 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 753625872 1250 753624622 753624629
    0x12904063005010608101706060907091701090c080102280507020d0f060e0313060f0509030d0c02090109140402090c190e090a090503090f03121c0b0910 67
    0x2007071214680841403401c075440380300040d5110420010b544c0c50f031001610381801611000d51144240000091703071003440b005240800d214001800342c0c4d844810500210800280271702044c005101c1b0017103490400c103295820007451020000c50074084a0034204424180da400c070803600e900420031440da1255560600140300091003544e90100280803007111540134181c8005c2d842550007019100b400301d02105800f00d240103000400038528410005940c2c4e1240098130a03450340e2a00007045510702070414540440858100140b0b0310360200b00090a0294106840c000b003101e0710b0214081d410050401c5001d071615000c2000012480950f01c03502c158002c200070b108a070040001458801681e0030350700000b84142d1001c0002070800d40251021101a416900034400c000001d001c0f03001500800300400d0b00180698a00007660301800b0503e0080041c407900340c450781004074441d01000c4000c0c440a104102c0c44548201e01c56000820744141003c0c2500c208000e1003400040c8504000c0035045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 753627122 1250 753625872 753625907
    0x20c0d05071a09061b0d11040320090f07021504030807090609080a0b0a0f0501030b040308060f06160212030408100f0b1008040f170301090e01050103053301290406 72
    0x40ca540441400179100d2486003601446c2051180c02c42c0018a6000d030041c0d03403107080b00e01381d4008000d90680c0b80b072032414442c82d486910072022880c5009686442138002d00d03a8816a25511f40400c4401c0e0342d28030a0f40e00318005100142013207115540b00310060050320940c80d044107c2d520342166550b9403801c50380d01400c640a004081101ca0b001540301421b119003028007440340e50381da81000700703440b20b0484064000c501d020002481c0d5141c925000942080011b000d1414550030092141e0080c0003c04100c0c0c102112a000c024140002c101801c0284030340c9000703005105141003048107680501089c40d10660800c2101000c3e030346d9099032000742c0ca0151509440554036428402e04804c0f88035005019080100f011701c910611020003035040e40e0f41d02c0014804182e2600d000b41c00c0311400d10010340150400100340080700c0650300703030700c1c908154801c0c05080704125460003080c191003a804100f102041040e155401900c0740e140800392441c02c0c4856050518200c0c000d46062058080c140e503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 753628372 1250 753627122 753627151
    0x1303080702010605010e011404080f1e070509010b0306030f060c04090605090c030f070c1b1d09060403052b0501030b130c06030f020d0e01050f0a06180f020c0d05071a0906 75
    0x1d600004d803055400900c10301085a0001d00706021542d102c2241d51840403030046033541c125000040003075540203c0300c000e8081102d9a1912042e01c00c2a00003421031039060140d48d6400b64041820401e5034040c0000001445d81c542c50001c1e5401152840d034880e0f40111f40c01810003c0600c2e24105070b03039004420303450301d4046503205041100c04103039856000702403080300070380c050003488040c084605403803102030f11001c01500104c05500064080b00d000c0070903441180014002071180c8054131030300b4012010002880c01d11000d02c0205000300403070941c107654440c01081030002081a66411540d24128840d0442c210740b5004a03803c044c1c003070305081c1501d40c5941271680c1c895a04603062132403c04c3d81006000c1000712a50b01030281038a0101c080d14103280070504a00b407a118030b0040329190941c04c5070070300c10b01c03480070081c00c4041903d4016070350900442c10161010700c210078405001c3d94130f15a031a13901c2d1900401383d02d21070300300e40c0c643c011102c2005862600000d034641c014810a40004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 753629622 1250 753628372 753628397
    0x130e0a0206090a0302060310031502031303120204050a08060a24170a1a070f03061d06150a020d11010c170604110a0f0e040e0304030308041a1303080702010605010e01 73
    0xe00710f440c01d1344001e420050002c20402c50003400d031030141c1501d1080e01254000e83c010341210b0164001a02c06400d094501070711140000c0c050359000300c910900010150034555903a0010305040d20315404001160010010890114181e00c60100406101c2c0c03002e0040b800c0b039884400d01005540034071500c00c03031210161402180204691030106900a0805071008607842910b001078800740c070300300b000c607004200b241c00b064041d00840007511080030a90f10dc0464a0440d0031141f0f0002e400302da0009410b04001155140c80c200030b00b003420568000306001c0903400d2000b007003503400300755440c416498040c026055590007680b00740d101d800384401e200c4c41c2e184c0c070002400404100840100c00c84000801c441c0542c1c00c903000d042140a951581d500742032443c03041c8400c0e50f070500c4010303130a5001084144002401070b121540c019000c0c50a0182c40090803141a075541c50503a207009407a18403034a5103003010752180310154420103a20007881a00c0c42e24001a0513100c900c100f460500c8080d85045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753630872 1250 753629622 753629629
    0x1507270b070210090b0706060e07090b030c09131d1b031207150c021e2107050a05070603150b1c0b0f0a0e04020a0f080d0f052106130e0a020609 63
    0xc03020b031004805c242d6071015540340c004010b1686114012054040100080519000348088400c40b6603d1984614598580b81c403042030354064580708d0782c8034404040d03900d40b0110b5445080d2105120700c00054214103010301041c40c11000310480b8806d6141e41420701641e480c00b096407280b072981c03045c5043d2100c10724a40760036182e015001d604820303840c00c0044040c480d03000130406400301048180901260f10411b08949400207a82d03020344d480c079018001041105a00d0081000318000c00958117000c82a5480508260103a4800c00000391036541e0507007010a03403450312004052407559103103400303c3d890f0605910740c21050310301450380da1000b58580c2c0d902c0b05892002d10f403200810303240e14103840b145050f52400040d58240d020303418005012845211400c0743d2400d031000000108400d03450901c3c03c40b42000141200400c011042c41508901400035911250388108100201254601402401a65400500f20031070142c100181800d0f20940465401041d503015940c0f69517507076030310011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 753632122 1250 753630872 753630887
    0x90e090a02040b0a030b1302041a030a020f0303040509040c060305012420030703090e060603130b060d0c151202040b09010309020a0e01031401180c171507270b070210 73
    0x103070802c1586c1d070400c08459441500032000c036101700c0e403c02904140400c0c2520551074603480035059813280c03c404000d850242540265218000c0480e45880c0c6c0301d001107504114107560480d039050401c03805200d01c90301401141d024124040003d0141c005000c00d540e98005100c1208050050801809960103c00304d10b051029134030100302c03540e42c612031500401d0b142092240c000383e1407040c004204c59103098005c49010b07400445010b15540e00540780c80742001c401401440d480810290098006000350356400000c04c4034041d1089544014031021f0000203152a103045120701c100428022840580182c458482c028a00024007299034808101d8105668001d0101e540340b8000000401a40d0400b0280b01c007450802404641001d6441c43d402c00100c44004058030104170040c040c48900200800920020008680c1860807455945442c40c0082d18207200292270f43e000c0f0658411460030f1850103802d42e460780e1803400d2801d03a0700f00c414021044020311a407201114061118803401d803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 753633372 1250 753632122 753632129
    0x91d2503060302041b230a0f020a06051612141f080f0d110610052205090c04060e0603100902060d020d02040f0803090918072103090e090a02040b0a 65
    0x20444504d21761881c07041c075503101d6080000100980804444208208840380402c00001c00c0503007442c070060801d940354022140b00b001140309807083c001c007181c01e42c014035018160204543c03170842c90762200180314055203580048207508100c02031141c0b10b00601c0c081c6c1d10000c01500110200001c001c0d02c000c03840d099211405604c03400240304000325020901d40c40344201904c802ca00803a0785510a5201e107001c84500c140044c0c4400100281d0400c140c949012100351a080e148030610195094101d410a075035480e126800042502b910f410076100b104040d14a000c0350540e03c0c502900000e03516002c42000c085019100c10080c000c540341d01090300c0d40c0c0c0e021644103640350340c00d03228000c0003034106110702c01d2200e1140700d00161055011040301d0481c50045d000d9001580c1f0f010604000c020450407808051003a0480060040008910654030341c0d03c040c0e4100d8501650304000301210600e80081400802840502c1090040040d9441669605580100301c00c0300c1c440004803003a24551 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 753634622 1250 753633372 753633379
    0x50703170708040e06030c1008010306050711100507110f0a122109050106090c0f080c0c07091d0706020319090902070f0b0106020303190203180d091d2503060302 71
    0x14000c2034000110280313901c00c0400741d044845100440341000841040c0f070701540040b5011400520100f507458000315800382041c1040404412420552450011020360b0966402d55607410300c103c0980c401e04140024604500401054141c1403000351218032001008103c804c0320314602c134100303000b004401c0304554403080c09402000c0b0856040081c01e000d00741243d281d442c251001c600309046100c3d00039400020b5031100c1b40d03000310400680300c1d0000504a0030107024140942840680200074a0f40070300b140f24030100d841c0098070354000840307a4014003140950440f140a22401703a0000c2519640d03140400c0f102103840c0d0702d08058865441c2038106845250000900c942888645655010b00f2807184455180c1030307a85000c201e03241c0c002a20682c810b405980c0005002c1c2000782c018580003040c4965020003201e00014080c03510701c8058400e004904d00d024200200700c950052106401e140044941c0c1503c1c16402050402c40b02c0c40481051210301003140700440e10070391000e40510b6014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 753635872 1250 753634622 753634627
    0x5011503180b09070e07230a0e040606030b0a090e0a0803070933080f0114030f030d050f01080303010302010e01081512010e07170a080c102a030504050703170708 71
    0x4443c5603180c000358091280e0034440da0700800c03d8a4401d0310580e260b0581c480741d01d1118000c0c01182260340d4414070b40369080003890f9103020320940da544039880052540d6100000da4820742720a00417400495801038010b980341101e6445003d8000c1040480c29500078006680e99071605026901c13007200c0c1d08400315884881c1c2074610420441101c00310300e602548842c6580f40302c0c4110485260f007048816000d4441c0000040000220030f880c1c1155031072004060368024900d042c2d48500e15040189120708031034079034081c043c5060400904501600040001c4c5207150b0442c1c002801e0601843d141904022001000411454081d80240e07640c49000b44807441c040900c00c0d0b56400707445c040d80c003481c0c280a51381c4002004040c08195103418030410700917003d6034666840d03020040e0461010030246000720310810101c55007a00c191f8449402e40040004003c20840c01c15412820703071420203092510f020103003c0850300000781402102e6110014000c5c081041030345000e2070041c40e40003808907602 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 753637122 1250 753635872 753635881
    0xd0c03080d0f0b18070c0b0c030103031e080402010c020a0e04060b1c031b06020c060a0c090e0402011b0302030f0a1205070e09010b0f0712021b0405011503180b 70
    0x2190001d08030101c0300242440081103288401080300d401d4098160b004c1501200e072078800c032101c8100c0f9804019030030150004060790311111000f09045807060700c103c40010060040542140151800310314858094642c031000200c0078215100250005c1e051240e003015001c11035a8118034880903152800042859052a14005007e02241c400841c03264100e081c00314103041b01c88919040b51a095a03460385005403070401034000c502d41d2881034580c0f6400304600400b03400200101e60040001c6880021410500c6400a0032410744e6041640c2c0c5070300000601025070391011500b1000109418422001000c62400340d15601c980e1400300d003045004245440507030340203283d040e05070f9003a80303060140d41d07600c40c000c4411f0754045030300b542d002e02e0f031400502c0000c032400c0c0038100c00301032030f080685000110307192908540015000e800c010b9025007c0d0780304081028050200d0100d05803414004c65040489404004030302a40800c1019902d1b840d102c02c0e075002c10f030044da625800912080c4103040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 753638372 1250 753637122 753637133
    0x10060305031e1603050a121a09060409020901030c0911131e090609241212030e0a0605090d030b01090902090a0509090f0712020303090f131a030c0a030503090409020d0c03 75
    0x82003242c600892000d2440860000480c003480c03040c02c010310701900322405200c0402c805030270003074100f60b08580e03204580130043e00c0d5201618040d50052101414003481c0041d0270302519141d1841103a0765400307015283c900920303514410250303401c0e00103801c1005c0300c4202d491404286680918400742c1000c40015444110307900942e90020206402c50442690418200104440b44505940e440a00100c2070104040440300ca04001f524a40071548591044d4610b2401e4041ca4064950030355407818082e0f4440104803007107070702085041c2400003042e1440068541c0c60b4600c50746828a030005180407a6544031408a0082c19000f003841106040c8031000070355460a16030174140038440d0240100c0c055140c10043c12541cad50090003980340042e52410300c03200713004130600c484d000301010040818000c034138025210984a41c1100c0642c490340c00341007500e021280118a4082e0070441030902c003041c80441240d800c01810785010440401a10120b41d5440030a4005040001c01420101c00c020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 753639622 1250 753638372 753638377
    0x20d05010c0e03070504050c0d0b03070f182f0d0f050a0c020706081902070c08010f05040201021b01141b030a02030c060f060d230a0b0910060305031e160305 69
    0x74140e01300c91200d6128001d02c81100c50076075080c02c0380d410500440005080070380107280354400140a07910001d07600c42e414401000c460b00315503030b24080113902e030088244e94400c800b94900380c2d42c0510304070b50f41c1c0304030340c0501109059125150b850000742c2e441e82c2c41d22508450701a001e20a003c21451604442c000e00800d07803141e020005010b08080050340d140305404060240c04030114003008244d6043c0088000d501c03902003220a404032080c0000c82050a07c05d4945a202034000840c56142c6803000a04045440862514407100701c40003103050f03640024040f601c00b52051020341c1d81d454580401a16142d50158606144000500c041d181c544c0071020b00018003804045800c5505d0304041c4182c241012100c039900550f0a90305a8082041d0703910421280b28012050070072014810002c40c20505030745016690406900184080300d5010001e15155080722001003000780d081d50b68060316031040704101d481da000c038016030744c4118844104951480b894601841c101415902e40a48240c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 753640872 1250 753639622 753639647
    0x90a050105010c02191a0c07060302090a090b0411071b080d0e010804060905030304080d150b0f0717030c041403010506100c03020708010c09090b01090e060d0606031e02030f0304080712020d05010c 86
    0x340a0680c001402720f0081c02550619080200000152400c200c0d4100041c00c855aa02c0e500030307100c061840c0a0300781c0d0750040806501454807101140140251550302c0c445039809554158003156042c03480030341c860442071b04038200f40307450002a00c03213080c54409006082005031003800004103010402c41544010b201c1c01d401c01a0500c02c003a03c07011002c0c8410b801d40310382d102040b81080000e440c00d80000c0100740750f61144010001c603c90410f03c0c440290000c031600092598002424096094403050522501800701e0080c4000c0c40c11001081c0f001172440c0036001070050034002030040500074003080000e052640000c10644d041381c00010825074140c82410030182c03810403101c40b40e500c0342550301c0580d00321000320044d50305c0710b5003448038040040d03000741c80250751258084001981c0c0c614000d108920460001c3c0a6070542c01050f00707109903040395180d1580304010400c51041d005c40d191085551003145081c824600e030002c24207018003843c0003445540f9100000380760941001e44031540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 753642122 1250 753640872 753640897
    0xa03090c06081e180f21030408041202130f06030308060303090a0b0d0e07080a02010f08091c0e04090506010305120403030504090e010615020606090a050105010c02191a 74
    0x910703541c500a03101d1441c20f9071500510080c100c01000d042e6080180c0c190412007810660301c84654050030b80d0f00300340401c2042850b582010507110100c0008400042501c401c0031412071450926503101c00d001e109502c24409110301c0c3c5071062081d035a0b114003208092000c540e040c04a5030401c50700c00003e00107800704402140a100101d0401d08002080c0c44242c5809072080300e005091075480c50031380d0410400402c445850325140e18194805000da28010002c000007014110302c07a100140c280960400003504200c203406c200103420b68001181c80088003000781510f1024000e140840d09001282403450708242015401020404000ba14504890082c0c0030307240c541c0180c0744070890354031842c84082c00140c024842408004040d0380f00c6081d15032010b00024540b60740d8035201c1c040180381682c45000d41c000b403003084190704203109159804a0261001c00040d8104030010b400e18140f198061300a000e440d002c041050520500c802c094000004041d010303654501c0500c2a0760700000c40f4495 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 753643372 1250 753642122 753642143
    0x8160e15031005041113020c070b090307030b22150605030d0512060a0909030503011503090f0809010306080105270a0b01051c120509011e0e0609150a0309 68
    0x30051980881220020040140c00204445800300300603160240064800c603921038404181995000d40412031510140c034090303111300118140f582465010352095082c0b010030451300c00756039008140102501d034480142081e948a0394401c403a01d2074180c10481034988042601020300a01d840c28040002c1c4400050100c107403034909140d11908003044030008204280700d094030310031080001e86e07405813001d000001c400c1d03620b05640c0143c82528a056000c80c00020060101c01410309004050300f0310341c02d0034020020281d0f910790520140b0355022f0000700f00030818224582c4280c00420052100000078015070030070005140c100880b16607040d030400d10428100514200120300078215907041006901c1c00e03846d10090182c82a041e070380c0c000c85844280448070005004015001309550f80d9a643c0342c44142c0c3d50009801410504201c0c005403111031540c0c0c0c1e48542c070251402410030f003518807586402034080403a03140200c03070400d1040c0f0580850000b000c150f142c0d012480c11805841a1003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 753644622 1250 753643372 753643381
    0x40f08010f09200d080a1e080903042102180114120303071b0b090d080a090b0c0c100906050f010f030b010b0913050906101e0512030408160e 62
    0x404540700307800020034035264902c48403441c0e43e150714000080c50300900303080c07105080c642d2068115807003003026001003013615691141074455200c52008a2990342042c0e081d074148611195aa801903108031010b698550480c0c4000003092842180c4c41c0758040c02c6c50004000c48440361001240074040c1414841d05860201881e06c1c0103822000c0381182c0d00d020f14555228548222641c440e006810b07032455200303099580c00035942c40e003600c0c4512070308000351100c2c00c5551402804004050006001030341402000004500c140038101c0d0008195800d096950320f02c1c0701c1e05030500310700e07460003129140740280c90b0701444400e0f0007a501c40c5a010803072002e2684c8030344024a035001e490101038010178502c40140400c62020000f0510304000401203581003024002c84030641d003040300d840750300f50080b40a01100c2400307032110700b0262517485031414900201901401101149108245c40340b044c0c0c2800c0d680061041c404c54018000c40c20603a01d0060418049241195991045031540120000000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 753645872 1250 753644622 753644651
    0xc0607020f07060509060703210902090627060111011508010f15061d06030420030708150c1b1f1e0b0a180905060105270c09030102040f0801 62
    0x7602940c485860711428489004140151b680003d4003c80038040c40036441c2d08014003005098440c04103008012030022268818082ca050010309194020071150003000c550318180a07000808806007001002255649401210300700042000f04125520f88015804402d02e80c2e1045010b0310701220080c0f1400041c01017010071120304040b01d02001441800c144180c0740b103060f207401e000404460701400c103030048002840b030f984140d40c111017121160402000c2280000d040c07141c2090110090300f0031b5440c01122a413179002d2940b049485080802c000380e4000034000540d80121a6904004001e68642510503510501000780c04004c8000c00042e03181d0080038050840a2070803440507a0b103200e03280d03524201a0451600340c40d84141c040340003041e141c54000600804003850b840120340003600d030030507034184541030b00000e0040d4400c0054100c0d4150040d0700185c4200304050401a41c1d9030710720400b1940c002d60400301d6265000241c00200c042000307026030190380c01c09000700f2881d01c43c400758 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 753647122 1250 753645872 753645883
    0x11e1107050604120b0c040305030a0801090c031a010f030e01050a0606182303030c1501090609020c1921050904060e1005012001090c08011d151b0c0607020f 69
    0x20296540d944ca1004000185812500b54020482c441d056007007a44907034400e42143c100350220400505054010041054180115408141c2d6410104100603030700301031104803206120b5030350621088081150314688240c1c08482c2600b2000000c2180b0300707010100b04083c08040c402c0d040043c0d0401060203010565100e0b1204a400b207074082c43e440301c0c1c1e034245c03500c02c008400003955042c0014489200d040000f031000140340b00c068080004290b040c20307040b00488403030b074000b101c01500c14821111692000500c5503040420b0b15210b5880b10410b01d0702d018821000304034100800c1008900d0300c94103070400003030b0a072210304803010701c84680c40f02940f13008800704603280c5103903070364116080000e54002e407102280111281108003101300000812801d42d094010102c4001c0506c2a04003c5508288141040c22209072110f4009041804d001b81c0e844a50b04080462078542e00c0208802c203201d040c0d40450716041805494446800d20710907915080100d64800c00b5000c0e071140501030b0030021a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 753648372 1250 753647122 753647129
    0x2030a1d1026010905060a0b031e10050904060f150b030619150f031d0c0d0c17030702040c050304230109200a05011e1409030105010f090b010305190b011e1107050604 73
    0x74a410760140c60f5070031904ad80000c0d22038204200502000710703960722140c00ca14072480c007400d40424480c0440005070211400c0711039581c0b01c4640182c050202c60b0080c070450b50000000c85000450880c0140380c5400e01c0078170350101410080c0d6a00e855400c0d13803c041e899800240c1ca480070041c01140410720165850401945107040c2c0208890744e50500d00300c03c144c0020b80c050b041d20351032251a000788520084603001c8600403a440425a0000c620342030080c4880342240e45050307401c41c2003079518070801303000a0800386820185104150001a400d500a03940750fa040507182a90301508800e40b103a1f40750024890f8014003004801103403d50040d08103500040082921403c0e001c101102114002031200074828560b13000c101c01840742e90309004903406032031210701b034000003807400301c01c1c20458500c9103d141c141400c1c801017005000c84400441701c821003281d40446d0703010f070800c0122010360105101c2e0141c91041e038845440c0300e0b4405000c402a807c20003c03151907580351000c200950150b0312 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 753649622 1250 753648372 753648391
    0x6031a0a1e05180a1806020309010e070b040f0b07140a0803010306150b03011a040306230f0c03041403130e010512010605100e031501030302030a1d1026010905060a0b03 74
    0x102081300b1120320b90103000030303410244240254010b0b40d0b8507001647d00075640018681e448130003107011034a00340548001845107580f640c0c1b50034036080100c80b05600a11034004680004a003800500c101141e0703845144070700d001a04c05007031161900e001e642e00b0030300080c7c0d03174586840704180d51038012811303000907140d40c11000f50451303181c141c10284c00106800c0c000c840d0074080c000000054582d0007031070688d00200301035180b003c03000a16010306240c0100104041d80070207003480501b040000481c1c5c0c1040e01311010b52203042c80e00b80a90f2652140c003501517001114400c00054491606a40754142e0705c0446800c61030b001c2180c10b2034241da040b401503036800707904200d030b001d4180c3c001c0e286d0b5103c068025080d980323080302d6000c1da201c42520990094000d0b80000403038500d565803200d15604040c014401c2a503c0d4801540421101811200b01030280035a26400064001c00640c00c0c0300e40c594103906140242d80c4940c0c072017001d0101525420700500c81540007251b600d1054041d28811901303503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 753650872 1250 753649622 753649669
    0x3051b0f1302090a1d07030c1d1009150c02040b04020c060c0304051204030302011b11250f1d0703141f030602030a0203040b060a050102030406031a0a1e05 68
    0x300740c008000d60000b02e02d81da00180041000614682c034903031182500c051001410000d2800901c090151042d06d1094010030007180f07102003801284080340861031500740c0d5890001c00c4010300540784580070307800c03040110041c5942d1405140e0701181040065100f0744080c030242824400b07101c00da000e58a1000c09541100b40041d100205903406194443c0c00392040350142c001c1a503044050350300c290030541c0141d45500c10349444152034480224501c4551802c41c0d9040d0900c10b4041d218000c3d00036100d620760410305919081500007407114042c040c4841c0003012650b0b12101c1036001d140400701950302c8c02954000500d29030191003141c1400b040c00c06944800d58880202c030342040020350020025000450740400440c10030710240d0300c00c082d03095006980381458103003000c1d50070004202c1d51142d8900ca01c01d20450341c0c04829902191443d00700419440301c4d041c48030042002c0c80c2441d0303400c10380e04200041d00d41030148000b20581c04903654401010f40311424001c2da9003e90010071229000b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 753652122 1250 753650872 753650899
    0x1011040b0c10060b12010e0105060a050304051606050c0f01150303110f1b12060c0f2104050a12080105010203091507020405040b2d040201030b1903051b0f 68
    0x30400400310201c0040a0741c540c00c00c0c209000c0111452500400038122004c5025807194410300b14071400f4000f84c0d0462107240d03141100040203403041e0b4420300c0401c10702001107001c06c841041140802945400040c01c0c15866800080036034020500d00c19051107442c1000044803010303c20b03588040e1045011280850035030f2020b8440031000340c2504214810020301c04e159541c24040300303000c940050b4043e41e003a00c4207410407156110320300d080038594104205000c0c036041c60038206c03007040751206801529082c49a01d10103401400c051045924a0504100000c001004c240d1804051095401c403070344103410a011a02e8a40074007409000d03900800c004c40b000d152601c01d03050001c0c0001d031168541141503010078140c1d203041e01d044030074002007802e0010a80400c000d8070560b007808080000004034600c80c00d20246005040641410f50745c194220b4591204600c40d540805528003000302c181da20301c0c01c1076075034075014903008103a82c910a003007111740784c1000840c019500003468552510796 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 753653372 1250 753652122 753652139
    0x110d0c0c170307050f0309010911030d23070203060a0e07080a2a08100c0e01020a0f0206070519260a020604061113060e0918060c03091609050702101104 67
    0x40c1040f01404400d0102c2040c0420782e4005621510150b000800d0000c5c4070701d800c102c140003030003025100360040700105012a5211412004105040110140c0b201050210060b640701e1864080d4050003004104002441c541e0001101c45082500325007800380c1c0d03000a03507202e40c05404d00808660b09403c0b4502c00315501150944040102103035404101e540e24a11850503461140601d0405d488860159050342c05c1904082c1c1c503013003800986061840e80d910b455415130300a0000b807081201040081c2481400c1101c4888140401500090001b80f07003040c0b04c0c407840c070a401c0d40403440f0349060142612140030944030f8000c00385d00103020715100c1c0c0c0e4030080507100358021582c0990091000520a28044511030b008001030344422a04086250500c03524030401081c10803e0541c15406e200c00100009034980e01c1611114015240d46443d0034050a0081034031051070f42603e0440041504040f81e03210a00542c503d4003101d03000340a461040f020f8503403440e0b0703800b50f15038203003c10011480c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 753654622 1250 753653372 753653377
    0x1201050d1703041a01080a03030e0606031002160203010c0519020123060d150c030501050f2d06041706160f030b0f100809060a090c0504090f0204110d0c0c17 69
    0xd100c2d20400d0f110a201e0860034213800000d034090844e80c0d0118404105142e010301c02c100054200502500c41ca1070a040460740e240e200c0403c01440300c4e40061210000c0b85409184844207900178028000c075588044020000e403c1080032030440740070b00100d501c40500500c103c8d1400000c541441052414003101421814002401d00f9085001420350000141c0310240c1c407101c640d44481c00041c1306503942c00040c100c51058008a010f001d45a000200382c0c1c0e6175010500803030030186440c0c1c040854001e81109240401204140c01c840081404214860382c40304c14005c452130031040300c03610350301c508030704001806000c0c400c0c01141c01c3e8807030101058403c0e000314540c41d80c0648024010440b0300301040e04041c0c5040d54400040c50007040c860700c945d051090310703009100d108042c0201e400945400703030804043d210b554410380d40d400c00841040307680080182d115030024010411038021034050081c50380412418030300c40745060304a215aa00036600e800300745820450560600c018802500e4495 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 753655872 1250 753654622 753654631
    0xd02010c0c03030f140a331a0c060114090703050709030215070b0a0522172503080a05061203070818060c010b13060b1204030909090302031201050d1703 67
    0x1589445d00000009041381306107004407004100083c0354101c20000790389082d41e8107a001d406552030700900201d484007691030010784803004801c8280621256941000d48240140300040703000d41700002807556840450382d80200c0d0251283d140556404030b04401321507048540e140441c41c00c42090025040801e0100e0301c50001402c0301d803914209458025a88400301c0e41c40c1e4000e5200d80030400001130300751160210310506c8240d0400d1809642c1c84010a040d240d00c070f1100071002160030340d44140785000068160194091805a50004c5e04004044140403141d81540714101340c0465040e060a0700c0e0501a007004501440c280011559128003961007040300703a00c84d2030354900c01400c65031103400030300e00b40384400d00000304621050280b003000d40d0f001c107014804d03518010301040200d011100311004142d40d942c2000d519511442e0982c4c0c81101170b00700302c5505150214810030150004024105030030305054100070342e0b9070780c1c040103071011541000901240106180420403c5144041d5822 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 753657122 1250 753655872 753655901
    0xd03090602090d140705060a0c060b1809030a0f110a0605040812090d031a010f0e0d05030a091a0a050403020d030923040524190f08010207050d02010c0c0303 69
    0x1c002c1d907540064502036400c40c042c2c0701c11a1444020f20f9038441004100020082920b00c1410b105207001c0141c10728904103409800c40351220300301038944d42c070002030b00c10504848251000340d09101c2d01003079803500000020800302d104081d2800f0914040c2041503086e40550000b071040c100c2c290344540107030801074401c4898400a000c9a0340700d2a4040c803061142100780000d000420a91400505860382e2032441a1f1a0448405c1d501030391743e21124481d120742a43c1040c0307079000c081c600410030241d2414805000c5000100786c0c0080070b0b60215400b02110a00c91303010161704a81c500282140c82030410950103c0d104200803c0103003450048214154003d003030201c1d2180c1e583c824001100803032485060416030030f4451020514051280d15004007510f075000c2d0042014841102100c0e07180800c442c031881d50301011030080c0307200c405204046c000c103160588085d980d4207102c601035000300e50102e405000c0c4140b20f44105105205404d6081c0d001c3d1340f01d8011100c603407003d600400761030038005032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 753658372 1250 753657122 753657127
    0x170a0c0311120d2a0e0a140d06050415150614040b0d0b010c0c090f061e140303090414040b010e0f01050603070c02090405151501080a0e011401030f0b15030d03090602 73
    0x748002d013800541c41c08a103603d40d10b407011108800c0101144060f0403183c1226800304100b540364895000d2200c405502000000d426203841c20040300c00440080703031012090520030326000d091140d1501400f100c00c1c0d0307201c2c0310034081c0140c0b800f5070600903801198409002072240880c07608180d005484ca490060400f54010b42d0161a005203000c500d400201ea16074841c2054901e404c52846080000c0c100c001c031041880c1e4494075400f542d02e02c2441210124180c1040540040c0e600744115040d800e401041041410070f00c400040c03183c0c40480f000e03100106801c00010350107081d1800244034080b88504d204046c0e08140401c081c6800181128041000002820005031200401140298001e40040c00030204950840c4a0400028025123410307824012044c42c50b40c01c03031021504442001c1c1e000c940c500c08200d071140145070a8245000a0445c0e0000000340300460804107460307406003240f2901c50356585080116020070304c80c0e803034140e031241c20001c1d04030344030394804039601d0300c502e20162 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 753659622 1250 753658372 753658421
    0x40b09280b04080d031a040e1207140618030a030e1c0513170c09060d1208090d0806010f0e010c140c01020717070b0304170a0c0311120d 60
    0x6404a036003107030341038490000e000d2240e49420819203030550034501d41841205e80c506003d120040540900f0381c0140d85582821002c1903041c88406611075454516903156541d80c24101000d00e0b044260041501135000403c1e1405044003107915040085002185018074401d002c400a192820015415005e845c4070104290009880d43c60184a16501c3c203407a030001c40460310b502034850740700010090340b2607440c000080703001c14280c28049003103070140070603501c43d4081245070400080041624904000c004d48054000f030701c4901590111048441805080400380c50800080d602103011841e408141c1c0459407060046180340401803610860070b00050b528609049010080c8829541110020011950741000081c00070401d016642844200490900d40c440049000301d68101400000140500c501c01c1c0070181c080c240011074550350301c0b0f9a40020300c040042038046000500b44050b00c4c1c00d50a00141469440b122601158a42041d0b070403101c009201e1502d80c1c1044002410380755 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 753660872 1250 753659622 753659689
    0x2707030c320d11072d051b061e0a0f0306140d1e060b0f1f0c140304030506061804210905030f0303010603150e0c0702131d12040b09 58
    0x203041c140d02c03030b001c0008013150101d21020b0340c0b64840c45490320170100c078040001140d40000d010101030400010452982c0d40071700400e000d03204000079440565400403241d440d11000c00c0c000c2c40c035042183d03075402020485c507070100e0588007180f03c2e404030056540c801001516152000c18540c0703215100304450010400d40441d4500450001030303c10310f80c1c40c402003180b414041c010000c0c0200440d440080341c40300050210b0244285825038040141c16003100e810490500b0b900492004102c0485e40c80329a240b500544c0c40d01d04035000f601420340d00e42c1e880d00d002103140030f1074022548880ca0710500b88005143c1c4050580f40005a000c04c840030707400084680f01031002c0426004048080c682d00e41c1001c0004e815500404a03100b0b42c8411900c0c208000452940c01e00d400c4051400420780c0c5203418000140d0488e180a5180005071602003031903181c3d1207000d040d024000c44c041c15100031003d010203240300d50189101d00c900c00d00c07042140c01c040c3d2524030ba600e00010b111960307441c00312020f080c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 753662122 1250 753660872 753660877
    0x20f0705090a0624030b030f060f090708070b031b07020f010c0204020906070605010e070c03020a031809020a0c0c08070623041703030708010915052707030c320d11 72
    0x50001212500824084c543d42c5030150564101040c1c0041026490440d0410f030344400061055600604407008240703500c03024480c4000a0009104a409407921602100b08641c81030b12902021140c03049049150300020b0282d41134039800504815104044000540340a0010310040382c6c440d0f030030416030401d41c1c4c3e108054500c1c140504400070b401c2d81031003084020114058185010b2003007140d02900001e50005060411541c50b24094403038500c070240803003040303500e50460300c8158008169103036003c1e40003040c120003501401e80100c83e07969072240180c03a401a40601e2001600c4656500c000c4900100311200042c1b094290314509642c4001000110074401e440000380e410000c00d105000398000030841c0034240c400d000b0000d100e889003032041e84500d00e103e00ca00a0040300c40403080c0703d610300a0342c10b4032440c1d0f000c420754a16000c50014001c00440d00030b02c0201c0d080e0040803a1486950344010240b01c2a52078910031540c8002c0e200550760002c030000c01318607032101d03059030107100448007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 753663372 1250 753662122 753662159
    0xa021006170c04050411060d020d06090e160608070e060d0204030c1d0906041211010510080d1407020103151d0a06060309051e161d07020f0705090a06 66
    0x514624078408500c2050400800100e000d110724100418400492002c00c10320f980c600341240c40c140e81c0c10310b10714203170041d000307a20840490b28548580002d1020644e000542c0741c1000105980c140d12071500c00d220f4506080c0242000114244002596180148071040040c1001060141000d00e05c4511034281d911030307002103c1c1600c40600400400d01c40e003078401c696040da2641e4002516041c1402d943d030b810001c01c040c10611446c54610001801170000710184000b41c8001e00642c540325403d1041141c892082c00c8a0303100c0c40d00000c802600c94800784404c202e412030464038089041e0011000740c4000307250a00d410907040c000140508034a4688a034503044182c40c49140d00d0718014007011104180d005109050804140780700040c1c02082000850400b140b000d40a954580c0301c07603280c0f0f0410002d45594981c5140c011441201c0400c0700c080b070b0f0707090401902d83c5a6800c0ca049032241c180da840100c55130b006140c1881280b1704a204540e2010798010006041c55a07800f424130324040340c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 753664622 1250 753663372 753663389
    0x15270a0c0e15131d0d020a062a090e0705090d020907111b04060e040521040f06030e0f0706021f1e140901060b0405060c010f0c1709210a021006 63
    0x4010001d09078104d168940b011140c500070700341c1d4071108513000c0d40b00c4444040c010413007607803a40d02d034142100d80200c0011a15180c000d10280b600006009001c03c001c6020360100400c0820024000b203205004446641101411003604050b5030750074446801d90140c581c0b1f00b0311000d66400c165100342000604403464482e8204402c0c90101014441190800e0b00281d5002034140c0c10030001c80d1000032103070440c00d0b11013008c403d00760140f101c04629000325004801000080c40000545640c5034000300c440320480405e40d000601d0741c030381706540d4250300d200740070258100110400c502c90761130035403894070751801c81d000c42c03a4101039002c0003100413007103050702c1440d0751f07100d80700d03120256802c8140d404440704008210217401c100c180121405240b045c03a21400000803450700c110001c2d081b201c49031402d00e03000c0c07041c0203031104050030400f040a14025060340c400300003208100001038440069107021180760b40c480c1680050402035200710413030400d510825220442400b0984a44402000400b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 753665872 1250 753664622 753664631
    0x405031e0a060507080403180e270f011a030a020102060606031e13140106061416060204120b070c02010516022e0210020304022115270a0c0e1513 64
    0x1f81b4000e40740c105d03681407040c02e08204d071906005a4030440c0315a5044891440c204290284c0100c004171940030504410013140100310500064030015001020750090f0040d80b0303072490b1019428588c0e00d030643d0201074016440300011905505101c8001d5400c8800841b03030460b0b07a4001105001401400c1c0d0f1f2032180050380c21b5000061068500340003c100340c2d840000c0c803050740f1300b40005112208440085006820018032480801400d00205200c2e035484001551919a6040c800300c40e100d80b54016075860200030005800307244030311001d040c0194161200c9081c110036141107543c108160f44203d0304103141c8024001640d0b0352041c41850703000c80349140b5008420041000341000b80c10071020708101c1c010300501006a90340210703c41a10008401c2d0078903510030f24002890558002c1403042d00e5500300040c42110380ba0181007030300d10444071b51b40e080c01c00880e41195986400014001c0c1030741d103400b84203010107054030812640021091b003441680c156004005017461080e40081c1c080b43d50344 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 753667122 1250 753665872 753665881
    0x4090917040b0a0e09040317070c0606090209030c090f0f04020a0509091c170c030901150f0e2d04020a09021201090c050702090a0f2307140405031e0a06050708 70
    0xd00701213006407040d2248100340c10320342d0700070703240503003180328000458641000160194861040c41701000d07002401480016034400c604d100075032104540c0390090250140001c52810524203050280396030600c21003082ea601156403410380b60140007264081c141d00400542a52016116802605100d028041e28a800540030b041e415068918109102035000b21105128108030306d00d6100801d0f4155035900e03035132264014010169219000341c200f99030340000c1149145d02e099603065850650a103012904c0b50503003200e0407000012907214100b140200c08441101c18020705802500c098004c1494540303450619041e41c1201840002480c14500100200c00d00d0380074100c03005c1c3c040d0404c1c600e00001754022900020005100c141099211002c00400c1540d03980b01030106240f5030b91410f181e0022020000040718151023540008540500c50045243d401d000c5074103c3c0e000900400340d00018842c01c00c0c0403423501032001c07a03c0c000e040b111030120300a8000d0f24803c13090b035900c0c100b50f0b261 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 753668372 1250 753667122 753667127
    0x9040516180f0501031a0d05030c1b1318080d0b0a140319030212031e0619050d03021212091c0c0212100e07080c03011104090917040b0a 60
    0xc065011815011441004110b00546425a1010b4a40a207004603481c814281c00b0700c0b4002e60a03001c9a005103002042e00140b00002c0b014000040780c800648142410b040b84038100d86d00300100b2503900943c1c54003800403401c082c0d444199560f211040741d641008c8561100e1442d50031015950400700c0d29401c10f0045403404a1081002d0100c1d203584400a002c800f0120740d4030301c4051140214010306c00d80781070a041c000c0043d914840540065035649107003a409072131740f03030300c6c0501c040d00106803041c04560140340076211458020154107000c0d12103070bd090100042e07100510f005074154056805c418407600500d600800121002d0042c00300c813418000c0b555860189946103400c004070310301c140c80740c88a61255143e84405c0c2c0403280e0035880e9a0b45111107042203070143d40c900401b85000c0c4a070070504004034402d02150400c0b01510003c03c11072040c9400d84401400b8481080740802041c4510380d15a4007800e6158000c2d44200014402c200340c1300da007640690006140c207070000c503441c410a507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 753669622 1250 753668372 753668387
    0x10e060a0b0a090212040b060a0f08100c0e010c06021804050a060303090803070b13030504080114090d0e091602120d15120203103b0d2a03020309040516 67
    0xca482c3c0114904203a60451804100021b480100340e4800c0314040750090351a90744500c00381c00900c4110740f000f40d464480035683c008500030104824203000200c40a54001c100340c43c68000103850f10814500107035078200c02544181888541c2203080302244105481d24816284102000f2b4400540a420b6040241448801d0f13400300070a80c1c001c00100c00040d501402d40380d0030600030b09145034400024541518a4007454008c40600d42c40d01c030300e1895442c81c0c10f1075280141e41c0c0030150340510040c10012540b0704125101ea1780c000c03080c0404207074080c4440082400202552040c0c51501c900c04503600c58a40c132400d0079800217a04d0306052440d1095682c0d5000003040b2400c100c41c64120ba560201c0e40b80e04120b01c007143c500d40e0741d103070501000013040302401c02c0b038100e01b0702c07140c141c0c0350001400c1c0d900410f180210380e6403140e01844100107006200701a0b8030796128045040740c004103812813200c0c1c21a44000c8045000130300c0b0701922034845010f660301038103500c0150040364000000091549 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 753670872 1250 753669622 753669629
    0x15030c0e0c04091518020306041d151012050f0f0304050a0504020d09150608010b19151e0302041e0f0603020901091508010819050618010e060a0b0a 65
    0x920482807004505110046404861429502003107201402e000c2a064030b070940d000e0240150341103030b10003141c901c80d80103503c14141203808100d01040d0851034400007424030b8610034294082c6038501c0c0b4506500c4441940021203148807013200361160440d0380200500b15040303446601504a0410302801070084401d60204000114105440c18002900c050014400d1501403030340000c281c01c260466411a80410703820602c41d40014581303040400003440c041c41100895460444108502d1400d902032804c03081c0300c0f5124041950a210100d0004524a40c1240601840c00d40c49408080100c92200005509850050311030386004010b1409100100c480004650038850900580f50b010210005450851a006882d040c4070b50042c0d80038003060304005484020f034516a581b01d9400401c540c1078401d400b0039110700d8050001007841908500c40000c001da000403002071140062062001c2c0c91801400020444c02903002c00c041c207122040e07440c2220f10307445148100c268104009044000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 753672122 1250 753670872 753670889
    0x50601080c090103171207050a020712020f06090d170d050f1303050906040b04081c1e0503060112021206010206241302040f0e04110901030f060504050f0115030c 71
    0x2900c0501e00181ea06a01400014106001c1c2e0400394481d004000a9078046101448512a0743c10801000313041d5410510486005110740400411100c108080c0c1c120910360103020001180044001c001080e04440a0240c1107810907814902061910300c2082041c024013410650b07621624a040301600c500410403904904148248014010740700b912210a03a0507180290311740c440303500020184c0c80341358011000303958041008a03101001144010100c40744031806640e010708481d082e1100d04800c0b06403c58035244130444035805007e0001543c0c88181450000800340745034491400320f810015140c01d9000c500c500300101542c04000c1d03581c000c052091a4001d030a03075520341083c004c90040c0d100b409800641c10f018980c0c02e403601074602601803600d900b282180c4400f40f22024100407141564901c640d1800c03001c880c00c0494140b4180c07500114149520100c54a07004050303c8090821a0750b80314001040214070401c1c842e0352901c2e50101d221890031851400c01c000d0124503034001c00031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 753673372 1250 753672122 753672133
    0x80c0105071b02041a0307090501080d1e0c02310606020115031e05060718120809010518040e0d17010e070f0512010b0421022b1502030405060108 64
    0x19408540301004103401c3d81101c0c003141040780a01c801e071441201940054141c070412a000c204d55000750400d40c1610f20480868a05000059040f1240042400c410351800c48081c60403032218816004022001c0c0068445c804c50314054502502c00d884040d0410100426000c9001003481317103018036401480548020b00000d904074034600e280e41031a11000b80b0310a58079007034907031107100e41c40110b4100f5041001c1c0e074290300d4004006440c50600002803000000214004a81d981c1d9034601c46149a810410060500d4000c00066400c1d501106110100303410070000101326603a81c1c020030303101a40ca400030380400014440c025003841001c40112041c0c2d8404e200501c031203a8014103c9502080510300410103104040c0f041c0d0342c42c0b08100300114000b2040b0000300d40600c10b80c00170802c40c3c16031501c004c3d1000c000003a413a40f8a01000b402540302c0d140d000400c09220b1307011441c0c0b00520100b40a8803441c28a50340e680e00c0b01804080c00c3c01c465401004000901600340409801812543c01820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 753674622 1250 753673372 753673397
    0xc020618031c0206161d01030906090c030209101214011811010917120a17011212020f100e030904020c0106141002101e090b2a030a020a0516080c010507 67
    0x1003001c80400600040b0f06d42403404001540e20940010600581007a03040003030301d040341070841070441302d800282c0c0910241c0021a151210416190040710410003291600b00c1007652142200c444107900c001d070a41d2210507940b42c4e4035094050041041c03080d1980e01a0460600c00500501c1984d4045202803c0011b0540504500491444c1141e4a08800303a5a40e04180506585d841540412000740803045030000c103c61911256648044d0701800c2c040d180411600000ca17540d481840ca441050742105080b4101c4070a00d0b0843c10400403103505580c10400031001007003c07a001040305000982d1100d8003004800341c1b03801382ca6681c40f020303a001d290420881e070000c0e40d0303084130340c05e204201c07580d5881404142c2c1a184c00c01c8211130103588184421400350411a0a082c000d5401001d024414801036282c04101d02070300f001c0d0401c803500182107988480c8030000940003a410801405400c200c10900d910911501e5a81d081c0f09000894035018100860307800c4910003405002440340654011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 753675872 1250 753674622 753674627
    0x1f05030a150f090b010b070507090903052205040f060915031a0a020409230f01061d0a0b0406020f010e0309012109060f0b130b010c020618031c020616 66
    0xd507080400351001160900d1442210001003041441c0076290103c075000100310b50741500000c6c92001e00502c03c40318086d4441d20900d0860305d5440004020540421400c2c0760b82855501011704a8075400318994080d55982c00308081e01e01c1040518070715035845206004da00080c6c0705206241a81e01d480f80d03511070940d502c0c89414441504c14481c139014550020300c0001c0c168040794040c00f4252010f1040c41c400c1080b81d02a00c20a400014880e512640014041080115a141242c445079070b13844689919803c295600440f110302d90350030408e0304a01003448100c0c24014002082507600030305c26030002140d0300b802c460036401c01d050313660420494030700e00e40c0c0c1c04808440c400e09004030001d8000301c402110300040012400041481d0b040141c2e4042d400215031010608007019109004040c0d0716807150011950141c0460303000c144404029000b41c1441c401a1603036500032403644004e504000c0c0000d00d403141500c29031101101da107400c5074020750305202040c1c00041c0705280402a44200502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 753677122 1250 753675872 753675893
    0x1505011d2101060918050607080408030105040c02010f1505030f010c020d050c0f1c090e010503191b08060103121d06130e040b01050301050f040b131106031f05030a 72
    0x51410141d07018040300c400035402c2d0b0100c00140080441000380f42030f001404000350082034400e40310b03409180001000e0500440750280300740e40c050300c890324607824032040000034002c11480b40215940d0b500e01140c110150320a031462100040d41103c02030f8508010145007040105e0394042c1641040400080a038001452010002c0ca9040c000d4075040165001e40c40d20f035803078407102c1907403152608031142d250b03a05c030030003c0c90300044e69005c02094450406001d10300c001e2090310340588c04101c003001488100d18005504a11039500c0403085480305c3d1182240a080e038020480e01d0700580c0040080010b0007006400c500c03845c1c1000d500219003050914900918004564050240005e141d0180385c14190310300043c191181010b070307490419003041001403200f401400e0003507280c040880c40c06841d014100d071103580c1c001d85002c01c90366000441c10661020010441d254800303001140900e903100c0b8040c502c102c1207409103502c09074040008059561381580118040c0c0c0110030101d001c614007802 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 753678372 1250 753677122 753677149
    0x403080315060c1c0509030d030c03150302031906020c0a200414070e030f19060e0f0637020a121b080c040509070c030212040605091c061505011d 64
    0x4400f4090b5280f803401e485c14819010600e80c94029100e0b000b20b020340551040c0c40c200940d5408011143d2140800e40184c0147d0201075403560000010590810760342100c294500c2c4035800c003500700280c1c51552464480c030308200f112141d0419808620b900c400303a02c445400034046038180b24a1950007a03442c02c05101608260400000201240d500d071000c004240b030020500045521001c08501d00c10041e41800d8400c40d103c0d400c0a60348827900000141f01c40110200002402040c7c944800081507008000500c00740c2984106411aa542c075800d5149155414008003503551400504000e000240842c4145a42803138041c8070304020031054003581c0e40307104604111000303403560a0250280d010ba50b010035481003444041000c1c056000100e207851902c2a002c603140c0500900820180b07000720f0060b100068002c0c490b13640c0389e00c0d2051180040b81030365a82c00e03820305060b44800301664080c40c216180d440c02c405041000d0350b800420104443d82c55442c0c00b0840d10a000040d007490810304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 753679622 1250 753678372 753678403
    0x2061b0c062b330803040812130e010f031e150903110607051209210702010c020d2306010815040c08060406060303031103060f04050c0706020403080315060c 69
    0x540300b0030070001d42d84101020b00c500c05114810b107001c2403100100c4088445040850b20381d0000015a04c4030000c00da8080d144180041d0819030788108041d40940c000c2540201c41040701c100000c2c880d409000c85501038a000c1f88100b00765810343c18a00300d014003085200081342903581c82480072600d510201d4641b100c1c00c403404200b40c0c10038103040340c0501000d00505200d004d00c8061088550300603004002d1290203e09122055580340f91150300ca56000e2203600390079480303840d144a8440b40100810050788141005108400d140c0c02040d1800c008a0b4200c41454080f0181240100400e000c030a0f81710780c410080205604100180d510350aa502441c4040440540402e0421096400201c02b8003822700841e0354500d001e00f001009041107203c15000b080c030b802c0b481800303603091508880c40f42501a0504801204070003e100081000420314140c0450a000c5000015580d000402c0151300820240e6120b0504803d182c01202e1003e54143c4102420859620260004100c85c4080800d16 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 753680872 1250 753679622 753679687
    0x70b15060418050402090906070813081b1f0209031906091403090922030f031b1707051c05040305280e150d150302061b0c06 55
    0x84010984070301442c2c0001c00c9104800e82c08011910702079101c03a01c507500032610300c081c0751600944035448140991b150400a41260f00141d8085501c54002110520902c1c07032030b107406450300002c030550100900e40c00190300f050010010540c28001038030404d04040001310725164880d00042e50313906c0400c20728103480303007800c203000180b05980d4410507002d5045180f807048060b808004c19140e510640d009881074086001051214807103c02881075510001001011120941c40070364a54080c56542d904154a80310200200b03901590921035040342a1124030b07207842c9000c40741307861240c010648410050306100c018454104401324a074001e00c00d4500141d140c5650408959501c2600402482420341c0ca1400310501021000c40c1c0c0160f62581d90009141140c0c0100704d071080742103220035000301040c0844140d0221650100058006070160012440d039654041481c0e5005103858045809a80b51605901003040c48880b00075481182c0b81442c0c2240e00312908540450001c030000c00e580702 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 753682122 1250 753680872 753680911
    0x5040503070501060b071a04170306032a090c0a020c130b0d0c090f11091c0c0602030307021005090a080702010221030106120e0d08061f02160605070b 66
    0x5008440302103030000002c4c030003075440d5201405668040002111004d158910107a01c182c41d00409a020f19400b110816580710000d0001410350000342c0324641c9405290100d4002401e02e100030040b00b10032204800c0000d0007201081035000c4018800c10307500d8070030469901ca9039408158200020740459149080722401c07904900104041c00e0300c3c54200c4101c192110a02c2406000e070000c540c0c607800d090003441d940d42e00b100240c80c005e00c40320341140810700801c203142c90246458000040e541c124038030b62490540394140070721419481070780960000024020010383c180007100959071032800a0086042130703074101d41c0c0d424100700702402450000c00e10504680c820300880c03080100100c1c0c81c6c4003030081042b240000d58020300c5100c000c00d40440a070300c6403400c00d019482144024002420903588112810b03116008001c20b1903510010452802c8d5005010080660458a05d640200b10342100d141a80314040840d802c1030b410b1001c103004003000038060781d00182d4460381056104540301071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 753683372 1250 753682122 753682133
    0x90702070305032a01022d070b040605070f0f050a030c030b0918010c140d050a0b03030711011404030b04260705030c070f08030d0b03120a020c0a06210504 68
    0x1203600024090f0100182d42c00000c410001c10642d100a80c030008201c01a0924581d0300700d1089495604490a00a540d034500a00c10500a4411080812114680301d0b80360f45205960300e040b181241d0301541c41c400c2c020001d0780038000492000c02804d184090f51521000584180a04458481056104c0040704c2d0024401e410049088402501c1c0c00c5075170600d01c20745d0a900d000c80060001541c81c04010ba00c005114403891000900000c584e14a040302101d404c0015010041c401c003070030b0380c8510104110380c07802c20060000324007401c0c0400d40101030b08001065800c000003c0c200340101407005002051405240507007290f031020891100075944c03481c00201e440c24103628881071a01144101c28000701100410402842c902034850442d100e191107140010240600459075206001803500c141540d4001d030350b0f00c6001400c56086000c0c2100c00c02e0b141d401407520200681001142c464103081c205c80d0980038008600340020030081151591071003041c00f10b0700104080c1c65001140c00d100c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 753684622 1250 753683372 753683383
    0x41403010b0907021038120303010b04140f010e040c0905060f0715181401141006020f010507020606010e0a171501080307030507150f0c02060610031505090702 70
    0x25000d02401c40303a14060f00080e440700d40349105400c8883c141100029220890342885010403088038000721400003030362a408405c0880c2c0b2506030499001005564503910820141d40280a00d89100b80da9038108014002140c1c0c444028a014a02c25000103499a80081d64981e21140a03100056017404002c0201c41c4c0ca11643e0010750452000103100c0c000704d20308001030940c94041d01003042c01000055a28003107a00d20f20a4a215402440740680003601043c411800c0365903440c0080b840408461400c50304101c2600d949a081d110b103c030402046070180032402c610700c903e0b0000c002c0340c075180e000603485600040200d41042881079400700f5903500c81510300050a07440450241a800f0b80354038030341e01c941e6116485865100d02c00001805100041220b2066038941d442900340340d0f030f5540d40920521418651508a0f0301d6448192001d15144240900e030545d550080000d41001e0007400780e05065101c04000705070901c400c25924070030300c4142030101c03013042d5181d420a41d5141030890510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 753685872 1250 753684622 753684641
    0x4050303070f30020c2407051f06060905010e180c0c100606033903180f020423060907020c030a0b040308071d040e030c0d031a0301050c04140301 64
    0x4203080d101601c54501d41d82c1d400c403803202882c4c08980c50003449000700070444140e5445002c0d107000504008002c0203041c0040d01040344128102e0307100030b4101d128007030b40300202c0000508440d81c2c2c08003003180642c00655500240000e08022615a10407804540341800c02000c04400d150703003c02103003c0306004821900201001410345840f0707541ea081500141185100d8080000e0400000d0007a0740703c06940341108120381ca5812140348460b008010040c1000e20500082c07680d5a02010b01a603d049409400f10f8030516200303c060640f48100400c03240c5489070184c05601034007811018104210b4415040309003280c442026565441c0200e00d051400100b03540c00d40121400c850400018038511805517109454200c1c0c940e0355a14211540b046024184440c1d0030444c450302e40c141000c2e403101404801c1d40068a1821007503400c4680f510110b21150710000e540ea1170550f1000319040c041e00441c410450080c461070802d8000c200f0f1034000c600400c1000b000908150078190380035886280c11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 753687122 1250 753685872 753685913
    0xe0a1a060a110705010905011b0303110408060403111c08061c1506050d08041707080303010b0d1503020105041806050d030e030d111216080f04150504050303070f 71
    0x71007503401c0e0001e01031a405190640144500800856258000d2041000f50f0310180d454500e100724948828510004050f01601810386c2c440520340000b81d001d008001500322540140036900302032030000c0c408540b08901c0c41054021900d6070011041c8107515851800d89440c01c1d0740301d611150006103105084213148506003418281d07000400c034500b060034514102c030030000c001075a03642e4248440302440190090600c00d08000c140043d041d02400d510420601c2401c8588107a100c407481e0345194020381241e01c02c1400411070031251003041c0a40e800d0f100200102d8580c1d10718503400a4814012401030500043c6202241029402c89510400c01800e0042c00c070202d102c1c6506028000d9038400154078001d01a80c107000f007400f40074400b218040d002c0c2c00c00822110300c540082c1c1c222604075101451501c4110300781b03480890300120151003008480c840c9103503940c0c035141c1c81c90741008151945100f44a42031000700416030300401900c554903048080407182d10207510300400450040194240c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 753688372 1250 753687122 753687127
    0x1d0d050f07030c031401050705040306020f09090907090c09030209041103161203080114030a0b19050901050f07110606090c12070e040617030f0d09050d02060a150e0a1a06 75
    0xd1140c11841c43c2c0c00c4034000c02400740c0d030020b0145160700b80c0310300b02d07901c0c00811002c110400000780300d0743c004e0400d80001002d43c4d0030320290f100010400c2c00c0c16100042036620848051004041c24482e440c284902414a1000d0501e19400302d03040c000000c0c00074210505000c988050758506114040c109901d0b5501c50740a940c50f50503401c80d058000034150002001d01c40086100d1004040c428950b00c801401400100c02c103a844040307940c0b00820301281620340b8003080014403003d010b82402002c1e4140082521318141c445051401c5000303001200b00481c040da81c00c2c0c40c0c8404180301d500200240c91004040d03403485414100b070321426880c0d0984004400c1040f40740356101001ca214031104031401d1010656032032103500300c80d04001c50f01000b904100402d031403400f0040010b15406216040100d0a40000d1710703402e040409075641103015070003080c100a0340c0d280d540706410030701d5000120840381500f014061200c40c44014205403013150b9950400710100c030308040ca024004070041203d503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 753689622 1250 753688372 753688379
    0x180b0306060d0221010c030b271b0c01050405100c1b29060405070e0105271c061401030b0601080604090c06030605030c060a05032e03060c020d1d0d050f07 68
    0x5000346802d21b407000c0002d103400184002440c01c00350505228000303100c07580304107501c09894581101c0281a041906070040c284070b050080d03c0c000750407040e0b0020b000254618203800e20604003040c0c103900a00c113900c0c1c0079118400300d4110403a030801007284080d1803880080f520b40741d0200c49044540c1001d4001d08056400248140d0741c12034400c6d4802e80b014031258403068000d0b502c01c072054103480d010803170074080198840b90040d5803181106400b5103000301c64041b080850050400549440c4151406650400c107100c03550250050301d4801240340702c199851902c43c0e480c0584007610040c100000d80b008106141d4480d0840e05925410041c001c01f01030703942501800401d07403072007141d000f4003580441ea0110f14001007510204100c0d61629480c60741c0e01c00170125034640070004101c40403509080f0201c40c07a01c2070030210103544070390700000b491401880040e00d0880252041400c00104580a907440310035410322040e103c4096070740e00b0440e0074600d8514105030200400014134440c003407000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 753690872 1250 753689622 753689689
    0x1020d050403020d080f0a0b0109050432191e061403160e0610090902040803040608010504021305010f121404031701060c0318050301020310180b0306060d02 69
    0x3580607920a4080701c1c80d6030481a416982d10b1011181819500c906100003441d40c00715030049070144105160206441c0d0301da0300050215006049003810782e1039030300c8148100714105040d0030300342d9007901010602454243c60040740880800c9000c04040d071540ea0290304a61480c540012001d120001803000c1074440b502140c100c85950180d511038403c903600444000352148000e4180c40000c1d08003011a035501c410311100a41c540650420080c0c2500006410000f9101074005800d444019560700e61410700010300032441a00000c2c0719520400035215040c05801091080f1a02070030300007456282d40300155100c141e1828140c1c003113402e100c0305011030a0203440701340c0714502c2502c1d10100c080301c1e4081501c02c8682402000d010481c421041d0380031034040c0750400d054007802c034054003049032900c0c042820b981050b522001206080c10003801404161030000d00c102c41800e00030800c4280c9440003a5a50340d001d0320450080444040e41819500c0d2000c00842038038050000d420150b40440d0031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 753692122 1250 753690872 753690881
    0x1b0c1a1b0f010c03090c140f0a0b0c33270303090d05120403120603140102031512070308030a0f051918021005131701060f0807060503131401020d 64
    0xc1074002e510b040d00d010700361802071180324402030b00006038030100b81c1000d03c0c000409002840c001d500102c140302640c102da442c02c1000d0090154000b1980d11744480002041c03030882d034540c072440030160b40d0f40d4012003080d03040c4103801107900c4a003411040e42c032419510060548248201d13043c400c00c8800c0c09280d402c00000441c068141030040710300004107032000f1140c078095400d809003040034280220340882d21925500450707120306e1200040300707582d81d07032512031914401010030400d94010040000c0036241c501303813502000d0b090b01c0440504804c0040552a0a414040142841004004545500f01c250700850301d01c3d6217001d08000900b8203031031340704440c1d1000c10546001070401c00280300e51088410035500469003d803c05500b10300100c4140c0e401d811109442121080f6207000090400c051101c0104842d401c00000601900b00102491803018036003084005038000d80003003080b80e50050440350b11003030413a1001c81a9109150800a40ca0ba201805241d907001003460070406209901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 753693372 1250 753692122 753692143
    0x30e0d020d080f06090106050304150f1b0314011203020a050601140901140a12030516080c1b0d060e1603061d190209090118050105071b0c1a1b 63
    0x220005641d8440c078600c542c043c0d00b10380702ca403ca0010001000840e0044001d590054454035400c8840d0402524040440360410701c240030094496604290140c81c05200300e01c82d0181e880c050210850740c0d0880a0581d0f81071183e895000302c10307080070003407502c240000d00030164840159184c0f540d45d29224500c0c0a42d000c445482400003c000280b4800b02122900c041403026081585540c50b115144184c0588481c06505210080211140f400c2d40400e00710240c610904c07107180c0b92145a03500501e8085c50641c1450341d460303809950302a90341c13090061880c1383c0e800a004152541900c05c0b5508003000d014404000380195031000c410041140c0040480b416071002800310308a400319620303900c101c90542c0340010b04080f5034420160400c020081c0c1c0c003102103c00890315845505036005203c04c62202607805035969018050041d81c0f01e40c2d13410741025440c0c1d18442600c81030329805481a000d11980103882c0800880707180701c0341c1284c280c4081e058070031503408141d0803010342e01e61100c00400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 753694622 1250 753693372 753693377
    0x70207140d05030c0c1f0c1509060504140c032b030e07090c140909070815060f0c06010e0f16091802070303060f290408240f0f0f07030e0d020d 63
    0x280d01411001c50080010115200350340e034440304004984600040138074001100b80030310f444035108802b00b849401041d019a200b0342d0744502c9690004912410643c0b6a40480d120ba0080c2d0010311071002c140500005100005081da084100581c4081d03004000012001c5110700940000240c00c5269a00c030040c802c205d6120500c8c03040c4c42001e4400da0703108001d6003a03402505040407441b0144100103103a440100703d075600c40d0b80003442d00040c001e50000700600200b010000b40103251104244600ea0040543d40c1280d40c150a00c2d801d01c1d164a440101009410b059070012a90030920860184005021003030010440c030000a030303814041e5200440c04e8020900b8840d002980c0380d00d220715502268005041d2180341007003c65540104000f402150365100401d01000c916154140710001e0450420102440189032030302c0c480034547c0c0024804200b04460104010140d00800091b1703900018003620b40786107940c0c4180550041c072681d03212280340e20070351521689544d000284107900300d2694 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 753695872 1250 753694622 753694639
    0xc0c0f16121e0c0b0d02090f06030c030103120c02100e0306100605040501110c0a0f080f01020703020a022b050610140a060f090909050a1703070207140d05030c0c 71
    0x1050036090400380705100030300030103001c03800701d0b00c4030100d1600301c1c07480344140500c0c25a550354004d031054075000807480c02807242e80056000b010345040000c8080501d0300f55121030035480c0c1003d445409020520000e01310017803281c3c100340f68900c030b14414400745900907c2d005080d016900004d24a1a0400d101c1c0c0c040c1c8200c0000c9604014205608001c075400f40c0d0b01d40345800c0c1084c1c01150040300e00440c006e0148100b001c090304030340d140d81c00b0700c01030504004030710740452401c07005a1070b21501c1c0d1040f4519900c1000385030007007a408076114a1554065803047d61151062140b07000c00038484280148540c07072004203004100c400700c0ea480c0502d09004003440c85948411010100b1000c1010300c0d0380c0180d050300d02f08806801500c0c02008620f01c3d0406442d02c55445007020180ca12402c01141d0f41e4100d982410100020031589030f03003200c1c0440205081d0b2500302e1000c1d540301190f0041014101040f50560605d680d2003002c1042140d00805981d01e0384071040f082942e41400e060400d109440c2c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 753697122 1250 753695872 753695879
    0x308042301050921010609180203070f210f06020c1e0c010203030a1113060903020108070302090f0d021513051c080d0c050f0a0c0b070503010f0605030c0c0f16 70
    0x16416200b0310034000b4000e6540d106102100749101000e010300c11304a540700d040008043d041c41c416150b054201881041c0044104c6c4109820b02e02c680e00040c1890003505c40c00c0c0204015501c11040c0c3e121400c1802600c1202c03800c281c2010004030f600180f110340000f5400e41480404100a24040321110f02010b540d6031342404d40d51200d070301c3c0030450300507401400011031040e0140c1080032245072048000d491b2600411452540b1140380d000440840e0143d40108110351303002001c164008150700d004c5041000c01e4002612442d80c51100d144168481c940c01025943c4040d600c1c41007402c0c4401c0c45589001c4c02200606000142c0706907845100c004060814251a10815101c42940803241d0352131b104888080900810f13900c02402e0400c10309004000700c81c03099400818814200d900c0c0c0c641c0c200401e00c0c06501c2e043d4010607a508004061004200100102c6100020349405080446d26652048206646030180302da4107102c511880b920349070303001404500e103000020b04000c11100e041c2c6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 753698372 1250 753697122 753697127
    0x40f0605120c0c0a020409060b040e0d090f0e0103030e01090506030711060a09050a08031803040609080c0a060519030f110c120711040b0d0507030503040504060909050d180308042301 80
    0xb00d2000410729041381440794014545940301045040c41440002029810400842c0842c2d211490b03000c2154042600e210b505e40c0c000240000070029058112540c07410b000c20804440c10601c03001702444418054200d8680c080c20891000e408003600d030580320b140400307000303000c5018480b90070158001c81002c2551078941d4010900000c1d040300003400c044a0719a1200c40503403004000c1180c0106110418041890038001440201442c3e42c13180f0110313080c00c00c134500f428041d4510b148144004a801c100e5650490182d0700b8040340d040300641614280c420a0300900a031040701d4102e00d1600c038421406403a800d01902d2100402011a480f044d00480811410703c01c4680140c0124141590003180e4074040c0c005075640807000d01103201e000c50310b5071061b10385036841d0022540c5070000310381070017681800e115070802480041400c1c00380d030506071510f9466901c510f00000822920801c0c6502401e010340c203030002194000c034096a100d58910304c00c01002503201d503200c0f003002c08803a0301c0660f61 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 753699622 1250 753698372 753698377
    0x60a14010e04030c150e150604150306020d2a02011401030308061509120706080c04030201051803120d0507090501030e060a0e2d0705040905070605030705040f0605120c 74
    0x2090084581410b484544003030310042c00408044070640590034180c00c1c0c201c154081c041d43c0e103007600000d001c2101151903a00107d14001d080350300603403805891520b046000348040f81225048800103030303540b201c4045c00c405030000494410a440d11b0404038142c55409c101e483c18880034079802000480300d01c081010050701c0c01c2c0b001500040688021400b98900340c899000d50100442801307103810005d0f070200d0511044003401801c5500700803410484150409001a4013450349003840d49024110382c0080c1950054001c00e0104254900544849460821502e13403079290300307c407840c0c07a0040c00d6602c001903c011200e4000207041c01d0f50028555000e07000c0c8403401036419001c0d04165070703400403600080c00d885644086070721800040000038600e082d56400380480380411a03041101e2509024074001c10781d80100d0040745050752000c04a507000c1541020f80f00e03503190042d9251030700c090486140c00b950700031103000d0311070384d1002801c1c0f504200101040c8020802c42c0f441e03903561030391000403030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 753700872 1250 753699622 753699629
    0xa0803090105190c0c0b0315010503131b0509040f062d050a090b011805181e030f0301060e04050a150b0703050409060605030601110105070e09040206120702060a1401 73
    0x4a0920010400214401e07446150a00f14682010181c40c581c403603041011a40e80f040070008000028820120030310701105020181c03e003400c3c1e2650400084081d0110283c00000d003482d110364a464407204114012100103041c02805003905042c90704016030b2460800b00c00301d51540ca4135600450710a12455941000d100c4070396031074280e4214200d404003810005100070001d40d03898130a0000074055518a1303000e02694a100f0701c00c50400c01c060401c035040603140c450b0020790010076004c0725000040034110760b150741c0e1011500f0124441c444d451402000e81004c541c6d00084000704000d07521041e1507118103422230307041c00f040d10b40d80202401c484461120070000f5840c0c14060040021070802040d040348a45440c0e443c240d0b8030b15210040314140d0708074000103000003052084942c0d000c0d1035014984441d500801043c1803e240c0a4010004005010300401c4003500140940d038411044c0c0340700e18001d01890881e0300e40500700079104c0d041200c090b999640340040e6140803044090007a4180c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 753702122 1250 753700872 753700877
    0x6061509090903080f0901020c0a0309050f01080118090213051603061202010801140a090207050c0321040e04060e01021218010905250b0c0c0405280506040612110a08030901 76
    0x307905ea190070015048002400c08407559002c010500005001b04841200c09009907507800c6a5810001004034a400341c400813810031042c1401172003400c446c042c0d950312041440b907000420104034800b0625416581c0642200149000d0400c601e030020044440c90003001960b042100e0303511801d10f4000715403149000390009110030010302c0183e40b00b00502d901407100400d400d01640c0d54068203400c0c0d90180c44110b0b041d0b00907a6a42c2c255050400520649540910760a034403446807160101150080340725945140310140c1c0864148448ad50200001d549410000e40d035544038103548058510043c2c504021072649502030300c0034401e041c850b142c41e8039440340140036445d5a0300b00304941160101103c00c000241900002500d60152004110030740020000d4059294000304100403203400603c5040b030080070901a00c00e0301509074940e880104049400141a102e03200843d00038021a0420010503518985010034850142244942200100c550031902c0e81c8425181d41c40e80601d540c035501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 753703372 1250 753702122 753702137
    0x1021f2c031804111303170301180504060207170711030c060a08180f0607030c0f0c03031802090c0c01150f05060309030d06060507060b041e0b060706061509090903 72
    0x5a00d48550514482c8020060012a010000300c010311085ea03c08200240c4c2160411810000c109800e805910f0003584140000c0c01c0d98034245089425840b805003100c00c581e5a200003c082000766410b540c4016001000ca400495280020414540c0449401e4400b80d41c8a000d0290900e00050b02803010b90000c0c00881c2400581d18003a99030400150040300e4540c42d05458040141041181280702c0b001c0c1401071619042809002d0101c805500c2518104103032810401e01950708045058003036585850700040d68095201c44c02511412100000e500512410030f101c2d882c6150380103460302c40c0c6d0120007044400d43d10319420704441418070800f00ca0300124442001940b4000e005503501c410070100baa403402c28a10540350444295400c248046000800e41c5414801030b40f18000c0c1c51603041e03808008000d45403002039107001e20b1003e41560a91980c000b041961501e405031804290f1040090006079242e0058804d800041d500000019050791400201460f450084540580d0152107030310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 753704622 1250 753703372 753703387
    0x5071116050f0d0602040819020a0f230303190305100b040f03170c0303100f080307150b030f0102040b0405121f0b06070b0f040320030f0901021f2c03 66
    0x4010f240c40b100580d1070b1075082c0030000d8429800c0c441c0c000240c55411000591004600c1002100d06072030700001d0760b10130b00b41001c1c0803615088840484000101185072404414500068a180300c0c3d02c045800c0c03002c40000210101c5d400d500301500400701c0403520307240a0740751524070000d4041da2003084e904040c210002c101003501100101303022030713007005410b181403800d01110b861548103540c00465699055810082c030114003108201a00e0028041c5150150541300c1d4844c0c05e0010512040551342c4041084044d5010024075510311422002036440c0c1c0d0f80d8414101043d00548211030044807481e0741e4542e0b00302e000c01c0010300711112041c140e126038211000c10008003114002e59401c4002000f82c800803400c464082d80c801c51200150040f02e02e41454024540000c2211102d035010b0041900780c41144040152014244d64140280c0c848100c400101e04d48491003551400307800b408030840883c1c12180e0880c503400b00c8801e94000d41c589942001e032640c4400a900400103030428007504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 753705872 1250 753704622 753704629
    0xa0902062203080c0c01080a050603250503070608060f040b010206040f020d02061c1104060e090a11121012170d09060507120e12040b070501060905071116050f 70
    0xa04040c03000c26031103680c5036200d54a0220f19805103180e94415404104d0141056034050340503176100c2d60801c2c0070301040c00d040012039600c100700e40e4140f0001290300056503403110100c940000401d8010115280242c2c2d074940905100b01c2510324a0069681d980c002034282441c0c0290001c0c00c606038010310079555241c84031000707a040f9400c02ca9004249840034405651a0313805419000100b84103c840165401d900300c1c101c0f106020400c031102000c0c003003040303a1500028220000141138850b004140c0c1e86400c01401411150304841e40503101007441c2400c2c00e400c040c0180700e80c41c01c0728000002d90b00c07800c0c480d0070011060401801040f000040314040c4030f109011341002461028040f418132000d031782e00c9042c0e403811249603001070010b1803640d1041105004200c800c80307402e40079009000a86002107480d21490082c0d115000d00081c48408000c002d6005400400d104a010030481c01c04060007080d00e011045240d00c10b204071281c103683c5005408109003150002040e0310311003508401070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 753707122 1250 753705872 753705907
    0xb0106140d20160b060d0201090317070501020403151d100c110709321302130c02010f32040212070b03010518250c172101060c0f1113050403080a090206 67
    0x11502f900d0b020b0082c000010024001745c805144540000e0010303029498050003101d0080f20048602c160308010700300c00e840c020400180d010080000441c100d0018070083d502108c0c0c20880f080a0300c225840000d0b045035507404807041d50810103043c0b080c81c022603941c404403651b00d40708000c0b01c001c44000c246036100703036503c1451680c07016042603500d444070100e820458840381c6400015035110310f1110340200c018400da150f405200206000c0092040d0a80c8500180d18000d2100701250b0401040c10755450b1100c490240c96030340308441081d9220801c101d81a082071186602800c2a160380040007207580c0d0b907991144d191040401d1400e000d1000c2c044151003803e62100500018034440b001140d40340b04001c40040800e80b642c1c1da03e00800102c139110407000c54040f084444a20014040303150f02038002c00c682e0b600050105244407d9080081c0c0d549000010168441c8403900100010141d5412143c415030080d120b03011203685120009040c1c914601c0c000394406c5041000441d00840b0041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 753708372 1250 753707122 753707153
    0x302070504090f02040509070e1602030f22030c030b0703050f04030c0c0b040905090d02060105091b1b0a020f042f040503060c070b0106140d20160b060d02010903 71
    0xf200c03c0a010140c01250455100b80d81014041c1c0101c00180002d8420400300782c1c1190140025440407003d05070000d48902480c130001c1c6041400003400d5800030752050800300c55000c101c0e0986c402c1d42d41c0e46402c001d0980c0c0c03440b00300e9002c2e8140000070b485600034403490b40f00e14480d054450f1141d81e941e5040b01e440e000396004442c016040a0003148500120000d44080c18916400040034205131030483e01d8040b00c1140f031421075200d90010300c29034540f00381403a0800c51803440c0300c0424010465840c2c15000b1401c0703501303802c001400b501801403800101d9940c26030090300c0401d02c080100c414403041d2140c001c2c080c004211001800f10301c0b4542c189211100c41c1002c007540b03042c1520780d000242015429141104480001b18001d0140000900703120300610721400c2c0405c491101000017051400b410350302d070131015683c0541445046685820704110640400c2456403004500380d411031459006d4416180100b4901c005076550510700d5000d00200c2d0140c5658405500d15030342c40b00785052016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 753709622 1250 753708372 753708383
    0xc0a030809010507021810050a090c0e27040303021c110412080706050f04050d05040608070f0e04110c0f030f03360a15020a14130302060f0903070e04030207050409 72
    0x20786c40b189903031004005000f100340034041c481d4a8544400c02c035040b24141c0109803200d20340401400f0b01508100f612900a038261030041c103012a038180400854120500440603a120000b007204059241e4004c02003120304540c1c45150305500c01c103440c00c070798075600c55030040d980400c03040c000c580040c00410080c80c0324166039440c114442d51028140e6009a80000449200a007448204502803208941d80b28441c40c0190078113140c60b000512411000e010302086c0280400941d00152207141c100c20883c1002d80144824110421011a20b50002080400b039000c0c0c0ba094802900c40441202c00640b40c030604c3d14290f49994240c0305150404c44a62000c1041c1c85000d22b40c4a511090b5100038000f400d009840d01b101e0300d0601e0300c04030842d03003c0d44880c04d2040002111094103c2c0030b004060008000c5980c550300d080c0b4511a80c211580c002952141c0c2c045204040602400028110688183d00b81c81509540f08640e0700d005105660060258101c3c1009200c1810f259010500303880c05031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 753710872 1250 753709622 753709639
    0xd050f13080c03010c0203030906010303230a0c020321041412070602060405190f060c021f15090203040b0f0a021608030702070e013c080607020c0a03080901050702 72
    0x19880310450821a4801c0c521500030389001030301c030700c0c00703100340840000140040d5156161980c00a5110034050000030706024108000351080c5542c8200c000940c6016500c8607941c1c03900c16400ba080300c1a28100301d1082c41981c212520010208215404011089100070301781820502035000e15004c000e207450700000356800a10f0b1107042004280020802a00507107624142810014201441c031640050812901180d907800901806242d51b9607507041440010013520381c1c0b00032410000007140117400a801c0c8200c4809114050340512106407030520031036159940c50f03c5281c01d1303000846000c0c02d400c0d0384c2070004049030554000e0320745c4a030701000c00502e0180c41c2c0e01034070401780c08164191160b010200401c00c005404000200291411440e40781e00b41d0701d40a000041401d01003035542040380c001c51140f40c4460701c640480112616107900200707189d00c5600d0039aa504c421a1824014804c46d1030007615070508000781c4046d281c10042d107615004508005407225400101c0807a00007859 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 753712122 1250 753710872 753710887
    0x203180607081005040908030109020a0903060e0c090a06060f140706050103061a031218040603050607050322020102031806162102010b0607020f0a090c03020d0509030c0d050f 77
    0x14400603100d120251030748041c03030070600080b18500703c140d00b05074081c0749040c1c1c040021030b11030001d13a0304607101c40d2000b40ea01c1000a0045035491825800200b140d401c00c84500074440c4003144811403240152441d030f21981d030b40182c25050302e900380700e40b03004181006034800c100b80c45000d2170040740580c914071514120465030303004103c071030982c030a41c0d9245e5901808654000c905500b00e52a40045008183d00300c1c0702c011800045c441c801115400300c066050030b00b12500d07550051001180c00006030344040c41c01540107000c0390b0048490212600190700418001c2016014524000d90182d0085007003800450b00c42c0d074490b9140c82c820703502100c01d200c41144c041c036103028002014844c5036034034661490103030201d5481181854040035a4108a04251191034240981e181c89404070b5800c14118500008146c14242039000740820908140f03441807881d806070000d04400140c120304005941d1a510403644030b0191703010311011034200c46842824030b4401c0d03002d000200c0305070007803c1c5803408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 753713372 1250 753712122 753712171
    0x3020d080c070609060f110c040e010b0d1119030b1918050c0f0a05010e04020702040e030d150b0307080f19020417011116030f020c0604080a1b180203 66
    0x12168030910004000c021300f4071440794030080c1601d0b0401c20307081616410300908072060710f80c0305070401940a02d513142c41c0c07500030307070f109411800d01148090100304c00d0706040d040c401c0c42c544001203450700461400008141c0720104146181c1140d8010b2154101f07900c40011812202c40d01d4219084c540d501c400150310102000101142407601c20320041807218039542c180240c0100c0c2c451a20f200d018600130411040e40c001000346040202180c1c0141da03056a0b1000174010b080945010881b07110104a0204041c0a98803034002100e0198210914642d204510300143c0b0007125901d00003258003001c07464110302100c0c4203401c1040240b0600041e480e210614040b60410780c00445510038020301e8122190003841589e01040c4d02d101c5d070b185400000f46900ba000390241038002d0801035850702070381c541c9100740b06080071a54000c007429500c40d602d45003982c1d1000c1c10f40040d0303900041040305070000c540310588542120b103512409002480244001e200940008004585003c01c0c02c03a44a030458 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 753714622 1250 753713372 753713383
    0x60f141b0a120509100617100f14040b090106050913150917210919081303061a010e01090603110904020c030a18030f0204020a120609020d111303020d080c 68
    0x1042c18001d20740492005c16034410f0300d800754008091140c113400c4040b072504022400000c5051040d001062a0a0307240b0303c0c8000b840408015400500207038240b0040100b400c00c881d000e940c8140003409026114010403421001c01d035685801d00261040442c00982c4d90f83c80d440102e580188000740042040e180c413124241c03280003418240340b0026410342c280403040d00080c64250354000c0c180c21413406c641580d0703070f41510803201040042c0e41030602040060000803506040503982074049256035914081e0050007400d0340c4850740713400070390f0302e01c40030752042541d40c40b103500507900e1044c04d910f889020b500070b140703900080c80d24076810480210300352590700051002601c8400110f5954990010050001d034904001d200d007910100004c0001c1200d070102240603079011140140d4403035418605032043c01c1c0042c0040103071742c00c2c0000000c1d01d0207203074041c0c0344880045600b030111754902100a4118401c2090502c511103150301d00344003608042c940580360601c50340304d4a1501e500d80f282186403c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 753715872 1250 753714622 753714631
    0x609140102031e0405190819030605121b0907020f0a0c03121b031206080a05010f05070c050721080c0d090501110d0f05040b07060f141b0a1205 63
    0x80e9000400d108803140d51000066000789200c4108445081c9940d51075100c440e01441160450724022801082c004080d0403200d0550b580039000300c030030442440180242003244215441400110380c5048405000314454006820b5070710401c495800480c10031098071800780600d811481244008540c101341080540c3c40c1d5402510641150f91071032801810383c01e24250218104600c00344884202c04803c1005010180c3c9400d0030094440c0f8a056503000344900e91001e056842180f0482c0144003041d408072007090701917002400240c0e03400c4020307103c0c110702030710090403a07110f00e00c2044040e0058141015031100c0205024091400707031200c006035085591492056085941c1214101d0b4120012078004c103800c0c02d140d0301d2601c4c0c0c112070315150b1382408441e01c240702840e61800a0300344101e08a40141c11a544040e80320001e07410142e005008103da003070541881e11068949030070b401002203220300c1140b0702d940c00110000c2021500360304509000c0040c80040340b0100840e004d039004081c401d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 753717122 1250 753715872 753715913
    0x10b060403060f050603011e05071e1e03050106090e040510050c0c0c101d120303150108060a080c010f12090f02210c0d0305040e0f0718051c0609 64
    0x6103ea0703074540404507440a441c1d40e01c6a03240003140a642d07a100d83c8112138050114000050554902d003042e901445841491807005480c51080c0c603450b41c1240180c11041c11030210322124004103902a0203c078000c0c040d94000c5083c0610801ca07401d110203060b03038814840c500b511083c084048000c0c090316020f85083c1300b282c101059103501250304000350040c0c4641190420170240740028003414069a464548050542d695907207085030321b86034040844244a441265543d03d41650412001302003461520b00083d011000b060551500200f644140c507000405003514445410055407006c0d1100c4a04091103512072081c44d0002607489103d0070140602e9600b40041070303c2c0704020010112412f504503500740003c200f031600100260707600d076075001030304c000c0d6980c10642003d07201809a40e1000310720007001010850308548031910315000d03034102d4031400c0e00c40d2101c13503403c000e5020358011190080074445aa0521000320100192228010240001c03011200d0700c0e81030103c010a49080503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 753718372 1250 753717122 753717131
    0x1a0c03070503071509080f07080c0f030c0f03042d0b041d0f040b07030b011205150306090604080910050d0f1a030f1005060424030204061d130302010b06040306 70
    0x38003841c0c0b080940b444e00924000c0100c9040c0760356415040c0079280d20601c801d000407803100708200c0e0380021a880d40040c00120b0741001811313400141d5a0b40119004600c501500c090594104000400c0c3c0d026106201140d09001d01400300f0700b508a1144000007202010340c641c0051280104401040500016000d0f08020081c030b6045030500000139242010b8446402c04000106405032a6141c10079000d01c3c0c04203c0d501c85000407203c07182c2503c0c0319041646443d00340701080000070070050582b001601580c80c0c0b655000307840c6e502c0388022a4058400030080003400013070700d400d801c0010803001d28104241001003100e111710071540e8210810023860342e641c40324002145003841421204100718000c18a09032841d11241e11340d201010846031154070f42011440950b1660400c5001c80318a21f80000d407100f5511501841c58850320081c0d003da0f250000c041043d19142803020000c1c0c1d03a03202101078a45031845101084142c0c3c017010350440d5070740c0740507004560f11940100300070b41c00cc910206 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 753719622 1250 753718372 753718387
    0x13020109030c151b03210b0618040b03030708070b10030c06081b09010203040618080f1c020d0e01080907080709060314010c0207120f020402310803041a0c03070503 72
    0xd11603828082040c4c441011040701900003640130241989a85010003425040d40d08100010041c048001459601c40000708000b150686000b64117421508110790500a8071104000d00d44c5920500c5405020501c040189002096203002144e422072182e9100300c0b100c566a4070741c550702c0c3d03600b03410440002da220b60030f204c1702c1c14407244c1c41030160f01103958907442c200603440040c5d9288100d10a40c000d000303400600255010b40c0741d4000c07004145030b00a4a1f81a08662406911180282800e18801c00b4100d106030b01144005a10500c2c405941c82d055485483c0c803005543d50300b17009000d04114400c1d5200415413180511041c4000c00c1d0f40e09012a0032801d5107402c28801030003051440480c0c1c5840c4403003185076030001e80302040301c0790214540d038440000c0c01c040101c003040700c801030741060001800140300c04101c02079a500c24030385107a0741d000500e0104222628030b02c5109010b4198000c1c001844240744e014a040601c4640c01141440c02600060140c01e41c4c001a4099441d1f800108089 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 753720872 1250 753719622 753719627
    0x31b060b0916091802134e020d140d020d11030d0b06070c0e060a080a050c063405060702150a0f06050303180a091413020109030c15 58
    0x140e4010407403850390425107090b00700091181010344120380340d80503095030440c9440380950450322070071007401c90001c10035102ca00c4141302d07581048003c042003081400c5403400002400800d840d840690029007c510509012405002d03070001082c0d07405241041d00354000f940380e4038244054807540c00904009551003030040c0c1808103074050300c0140844684051802c24010040741c48401c20f480700001c41c0704842000c90704500818030002c101c0c40b1821b86c00300d0400d00c06480d1a105640488541070110744070507441da180c98849800a159501c60000300140340f0381a0040c05206071a28035a501340f03e03080661404800102045100b0035000341c9c0c1100034490144005940041507000400090700680440d080d840402002d040503544d4910540e9040c0c5955007003100141802002c40e9103841c840720204100b955010400b510440c02c803040002c42036200c0c051106130103202040c0c001e4640e10166424007000f1881412030421403020008000541c0803406a8003030034072000728034800070018102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 753722122 1250 753720872 753720889
    0x9130f0608010e0c030c1905090a0501080c0d26090604060504030524040807030203190206070306090506130513020603070c06140402100c05070b030a090201091d13031b060b 76
    0x1680e4580e0808603540205840006d03103015154029105d805103035007840c2005c0786800243e0130240d40301c0c00742c0060007281c1c449a04111305a58490059520400442e82000029010b21000401020480c1c4480441000f11100034141c5000741c0301075841c0c030450318005507aa6000f600b001e00441d0011400b48240030782000303070101c0074a164500380031840700a40341c4005500010002000e6240000303000b03040600c00d00c199510707100c50804040410182e40f201940320801110344c480000c0c503046000500f9822030254600a071405458441030610090300040540b00041140284031007544c0c1100051f1518402140308900f569103a02401c2450700e0100c0039130f0034040b80609044200070511025a81e5031072090310500050070b112a810b170051a0031420b05219901034000e80c03201100f040322100c260b030012070a043c401d80c0c40d603142a85816018500400303003c4d0501c0038400c241c0c001061800e103240c0c4c0071156030282c18052090303424111942c1d10040ca4600482c0d10548441c43c1c10f1290601000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 753723372 1250 753722122 753722141
    0x9060e010f080a0210030f0504120f020604110112060e0f0708090c0102071809020301050c0a110f0d050c0a1704030c06030902010e0103051008150103140f03040b09130f060801 77
    0x4140300d28a15080e000c0d40c2e80d83c40070380040d00c1996800e200d440c00c18040d60100c20040c0226206110600d003030f040010b0711640700c0364904040f9001d483d001954600c080381d80c9106503400800c40001d910070364011140c203000840e100940d90b6aa280100313501840000c07842c400d00c0a13204031542c44c903008400502203007000d401c44031590f12032163b19029a802144003420740c2c5400396442e010840c064140e03409021400b1000c0d426519060500000452281c01001001a0703070725081502100e94605581d100046601d000607600302224544070244914001c00c045203080b401c550914400fa220400f100001495000720441c00080c10010080020f0790310004201a0030708000100240e00080c01c0301c40c21030030050405940c2c10005000b00480c1c40341001500c00c1100b101c1000c1040600b10038284001c0c00180c0d00b0a02e42072198821000004d9040a18200d0402640c18140f401807154803e030001030325154442d40802c0c1720040c000c1c0c03a11402c0e41d1212083e502141091800c0300c0d240c2121406003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 753724622 1250 753723372 753723389
    0x20a020708070f0302060906160f02281a1e03060a121a0c0c0d03090b1312030908091003020909070905060f0913020310060e0108100608060d060609060e01 68
    0x30300c02c003d10404551200101da80554100781c1c0c54030b128001414902c00d001c440403030180980700c00b1003849141d5200c00382c40c510a8a511104074043e91100360302c0d0300c01c83c10444041c000100c09000c00c4240a0804000c8400008400c4c20f03c1c07900e46400d1101107990500e942d59110102c00c2148525001e45400010300d01c848059202554640384c003640760340b0303642400b510314029001150711b510312542118a01c00c0c4070300a40d0420601080018040e10041d501900d04100c08004185580c034003400c00e80e01550700021003511004140c00c1640544428181526102802e1044810f55100c20386c0441c0290395550340165905542020840c1000025140004001241c0e07401d2126071154811a5611891070a0b071648441c0d1042c00a00d2103c3c1105422509500110034002504100000101580c04645070410450144401110384240480f0f04a2041501e02820496070303000300111600988041c0000c100150030f600c80c1e000790b844651000403d03d5071004108400c90143d02064050b20442 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 753725872 1250 753724622 753724633
    0x4053312161701211722050d0311210703230301050f040207080429030708070302070501090b46050903120a0917033d0801020a020708 59
    0x402c0741d41a03182050040f055615000b07050249280c0c4100c40d8120207507031010b9580c0c040c0c105180a90503a4111490003880c41500400d10308002c44401c80c0320781595800b070590f4510540c1510100d0b0503a0800075114030300c1c01407811480784801c81003d0244002d502950169403412140b50007000280d180021400b040711419400510b04104811241150021603a00f201c2013107410001d4024440c005004044020000b0002003121401d40311500d0309080451240d505d0408480003010b600c02203c858000502c80b10024410724026030140000f1030040f400050070881e40d650351550301500f45e402c0c80011410640003040c103031701400c41c40404001c014410782000c01c0d03a521441003d006804214103e030312400000e03601c0350100166500780d540d120f03124007a400c140200c0002052604000d958085585288076007402d106c4044030700441d580c15400304202c24134204aa0000000541159424500020b5044180391441404094420b2800050b0740380c8c001e010103880d0407207543c000761858100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 753727122 1250 753725872 753725897
    0x20703030f0c030c021302040e090105100b030103030912060e0307050c04061a1b0f0d120f0204030b0402220e071410081f030c0611070504020405331216 67
    0x1c108134010550545940090b110480c42c0c0d1800303800f03650040580c0352002010800503060541060740140780144038006869214402200c2c41d200900002d00891541c003410010801012000740d81903000b1030b0300140032805000c10030f082d980122025071b15a400401550381626041c0315010042602959803129400030303000140d11801200303003150a80384003d0300d864500314140030070500031001c4820b440003c4494032000c0d18941843d1070807030443c2d1414002010a81c038510880e41520b4100a6903841c590b02c2d0f03800c004c083d00000b81c00c030700444084a403211610581d80180000260110050280d0134242a800002618580d4269102d01c40c0c0409034104550400440d90b00903002003503405203242d0081c4010140e180030b0380700404062006000145a0398811070351007140c60b114017500c400c19900c40811080c0c6c0142d016490f44022100c071308440446041c50f0035510048100101e51840309800709140780c640001000505080144d010060442080501f4030110000f42c03c00c0c0b95001c65 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 753728372 1250 753727122 753727127
    0x16060c0201030f061d06040e0708060a1103010e180f030a170f130201080405010e032b050405030d0b0a1205030910030903020c01110a23070b180108070c05010903020703030f0c03 78
    0x200111041709012807102040d080e40b1560000c43e1142c418000f15145151f580c00801d540301e40458081c0d072080e1400c40600a44004101168100d518202d40040303961074030b4446046031540940c00205601c2101c50b54660715000380042c010984054075901507900381444041c6058030010041070b0f18141400400c88142030b441d0030b103107800f6028a82a0081c0c5e480386440c6004205182a0f07100511011668118404004604030843e42107440702244000008030b80b0f40c180e402c1542d0080c40ca803c00d00642d154460183e10412020000901d8031040540c1e5074541110038441306002e07901c64000140340615410a982d000c80010068901000b11032003e40f030081d10350304100499410404000c584040503102000389910b01a0400d43c3d000c0c00006188002100119040b0071070310b40e009103140007030144040c00560380028160a60320050681f0500116840d4000400c0003090201e034004280124400f4480c4c181315611940003052082e09505020313085101c158000c500b04850001010000395 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 753729622 1250 753728372 753728399
    0x12020904080f0f0c100b0f030c130b12011d03040b0403060504030e1207060f0e090109020d06080703140c04020f0d0c020c0d0f0b09010504081b16060c0201030f06 71
    0x940000740396445003504007504189102e04078400d040d0b110041040e0340d0143d400708a11034004000c02c001c01c80a400d01052004032044111800c0e8560001c846204250419904411000011000000e090190300b0009048081c0c514900905a95900c1541512a080c9041c8400c130200001c000d60406107425441ea04a102e14000141031390345400204007014083c0000b4456984020a144007103585240c41d00e680303525520501c03001654a0000090441c01401d5201e500f01010300318020985c2005403250182d40004150780042e560350307030002100c000603c18080558441c4002c075030045021501c943c41d100b00102e071036109602c100200702c10046120211001c0c4000820003140400700618181d00303000f11260b2480c0c001d106010403404000151070500e0409120380d456403526240c03482c81134201c990480b4001c008850820000022a4401e15401e443d2410401203034504421480c40c40104045581700102041e0a050100110368140c01442500015943c0400c0020f00c0e0071017484000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 753730872 1250 753729622 753729631
    0x40f06050c150114030709060b09010837060506040f050409050114100e010e06060301030f150603080c0c10090b0a17072105010e0705030c0c060903090307120209 71
    0x800d00090078050190180916050780414a0070b12030b1560b9546028240d2049a6014501c24002da480200301d490031449144c094a08010481d03060002110044d82c01c554040c050300382900406800380b82c4030807100c41480700c988840346c0400d01040390718015070546296422503803045030180310074008160041c08100440380101da001c941683d65040481c0102305405c0f403030b80703265000c1040202d152003208043d42200d1240c104170b40c2c0340ea0717518201f1000503030544440c0d50040d8100010070101d480300401600440c080e20b0900c3c842c4800180240403946103a108803034000d004035404006407000c1c04400e41c1c00c42d00b83c4690141400024005001c00c0803801741201e203642c082480301707006203c1c80d40307400b925840f010806407505040f00058103901c45500035036000d079103105590414815a001d402d04035805403000380c40c10f071102003041e100b60308000c021240d110810300941c62030b0f41e02040424000d81403000607564403101c203c2818140102c41d0000741d550040310300c950300140c49000f0001d506c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 753732122 1250 753730872 753730877
    0x30b060a08040813171b18061216091404030807031e0905030301050901050d0b04020d0f0f0b0609010b0708040905150d06050f220303240605030f01060203040f06 71
    0xd650b18589910580104210b810103030365201d80108920f00c000141d22000c00d10102141d201e46054041d440c0c40100098490350002100080292030407501c00e001c603007240c0020070060b1000a0008031070b2400c5104c26103c0300001c504031007040326600a01c5420800e03801044500e41c586010380340681101b00240c462410140d032103102000301e280c0c6520301c0c2100040c0080c148514051350800131703602d4100380120303489883c0d4200005074529103050040001ca81c03000d640a441d9036075400308480710010f02c10684060004403a01c3d80050078038400800c020344a030b00710568a0404000340501558142c1200203680804c120b9400840ea200e015030301291210300b0003150325510942c0c50306082a1038100780343c01c2151502c01004000940d0411846429007006412550340d862800c0c01d801c003802003640540107202824640030902c03d801141280c5590440c004481e5400c481c176021203d01a8801000540040709100304130308102c418038014149440203500f81810201040e00c0380c1e480c2d1041105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 753733372 1250 753732122 753732137
    0xc050a0501050c1c030e0d1101110c0d031521060e161202030a0203010618050a1104030605060114030702070e0c07020f06032a0406030e010507080a090203010905061f06030b060a 78
    0x1300184607130003a414982a440c00e40328070340b000902c0034050210701d40d0f600d03005500b40b0850000250501042e02c01d000c85403801024011142d4200340d00914001148800746400f5140104901c604c410442c1d50040741d4802950428446050030000c80700c1a00072160140c0240418001d00208a2412400c1c0c0d60b03c0c00318588001e0b03451001030f19180b15560002d40550a0200c002001012165030041c00349194170240490b541c0e560b80601225030000d01c202032400144403c0c0702050395648215400318060421000400c2c1402840000d41c2080342c468006074030625080c441a4840d403050398000c0c0400010f1410085142e00080044c002d142000d0302500c00400012190382c1504160444500c01c6100c1b044a03038880505070f5465401405500003180c00d02c001d12000c18014030503a4424032403030f07861691a8848000d600040c0900d240305a03415920b41e101100410414082103000715034400750b05800d000504040c00e804a07250744400181441c103080c3c4005503e404040347c0342d440c8685410007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 753734622 1250 753733372 753733423
    0xb04061a0c0a021008040c060f02060f180f1605040b090103080a0c0f0b0f06010c11040b01030f061d010e07050708250b0f09010c02102003040c050a0501050c 69
    0x10b2601c40382603400307036001c003840030714142d081c0d00040030360b0156003e010300e400203e40300d9105030307188256140300f403006038041000a20b14282c2c0d0012950040e92211707040024011442c2020300d01803800071140c00c141c00446260700142402c030000401044141c4060110320900c80000e980a50f051201601e500c40c006138040301c00e80303e800800d040301d500c601d480e40b6150807410f00342e10031031003251074000d01011203000c1001c0b903000301c0485140c1980001e51103450803c80c0c05100c041c0081100c501e05258980002d401e0b01c05207030080c0c0c00502010b030040900e81058000403c20850181c3c40a90a51441e1040c09500713a0700108950545da00030071042d98500764614440340014000300c0001110f00304880702020011070320091402450b5080c3c00100302d0311950280c5c0e003264906200980541e01010172400d503500c4030341002c00c5c40d00c9098141601c0104032401844540d10843d4100c5500341424030a03c4240b0346040403038040c01081c41c200381014096500c880da20284c0701313442c0c81c2c0144c002d29000f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 753735872 1250 753734622 753734647
    0x6180209010e060d050105041823070902070b19153302010207020315062103070816030201140705030408070212030f0703080610020304030b04150606090305010b04061a 74
    0x282c8124001803e01503440ca203407842e05004040a000d070030711480c1000e001d00380c850101000c144500f5000007030a200215040710302002c040caa0214000540220403000850444038805084e00340d0103088100306901e08102c040030380c1c6003541d0031840c03d00d02e400307500207030050412104420b80340c521040c45900400406100b44401c41607058009100c04c0010803625140d041d0040c0034213074420340454007295006410741c19001e00848800d90030400b00d102c540ba0303008000c00038490284804082c1ca180030f00c15124241554480c07842e80c1d1059140344c000d103080541c24800c2c1e44801c0340642101e41c0908000d0002403003444090b001815030b00c8049295000d55465140804a050341001140d41d5440c2400c2078000a0300000c44c16004a41d000d000102182456080d528641c500d0b0b5028520f0a0304554810159a0f4080e1050740c420142c1000e80807443ca45128030300252132580c81e2441400c0c03840c5403c5003500e01d400c410301c3c015800c04401304102d41c0e070074140d420604510320f065512040d541008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 753737122 1250 753735872 753735887
    0x6100b1e040305120d0b040905030a03021c052a071e02040222140a12060e030705010509070905150a05040f0b04090606030215070812070309080a110106090618020901 73
    0xf401c2c07405103261030400d4960070b000400140c5141842800140642401c000840701c44103006451600304000f070b04481d51007170b4010700a0811041c504e9003411481c01c03054049404c11075542c5980811122260040074003036000c0d2001c92800700d011032800350143d84051180710103060350041b08807140102c00c2159525010740300900840700c0c0300141c6011a18000000a51501c903008400a0920381000c060078000020020382c0d011503027144440410f540c54000410b140e46e01702d119030005010f02c0340056801e0090070b01070030760355000b003145504080e02d0004640c1c024040912070300701941d8480300f03500c566069408541c0304070f400080d0503642c001c10b40041c01c04480c003103500c14504820310003040020b0b03000c0742c1668003c4c0c5880c0084080d0b040d00900794440d1804c0a03142c401d081c000310b00007040c03c0752507951081070b40c0f03004194011551f0304d201203034000c000382034041960142c1c0da4032001c5091103803a00070000c0d46824040e882c80c110112007540071036240030120f01d400184003d000d9000300803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 753738372 1250 753737122 753737129
    0x120804080c0a030818030702010c110d020a082a010818010e0106120c0f050307090207150606030e060f130201050717071a0c03062803060c03020a0206100b1e04 70
    0x42d64110955890010300c1c02c10200c895061708040740c01d281e10100d00020683d420564180c40310b41008105403990a82c1c98420300d4556400840e0050240043c2c80e075640030720040507901e0040415002c1c40d28070b941c17454071041d011000400c9140c807001460780c1c0b101c0c030603400c4031030700c40c4040d04080310507c1107001d000b43d16103006c25582007920004e1568201c0082e518060301801c50000d01d151202d01034104e41110340314040d0f01d40d2085030705120812041d40200141032040c40380c071142c0c11000d000c4c0700946101d6804500880c4d610b244102d051a8140400e942c084264954102c1074070704800c0f0604d07207442c0b40d60081d04104000c903080040213100100204a14228003029854044500e40f201c0301901c040705441224446001043c10070b10614207803801004001c00151340e01035070000321810922040d2015084422120001011903a41e100d480020350280d0740151340d86000c00d0019251600c00f48c5038086406a0390800c11034180d0700019188001e0004e821151100005e04910300103008680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 753739622 1250 753738372 753738397
    0x130602040f05010909020408070e0702010615123b07031a01060f020319050f19121404150e1c0f110c10052a071a0712080408 55
    0x5001c15111046800803088500990319004010345414881d02130b40105d11440a80b94080c1809003c107403540400d80794130407213a00c00090955550082e105081c459115800c000c80e100b6081103215614034010301000b028403040c081c1d2800e03000521400102c1400007589880c040c0238064030400d11062010300000c0d50000c460710803646031a0450483e40d4002c0c400c0b00c001c01c02081024880700c1c00401640c140f45000c0078080c1c2140381481c03060300e6a62000b2a61035100c20100002c1010710b641c9031002400e16010f5a511030483c440c00c0c065412210741c141d007100795214660404c0005000700c00717001014035040d0008100d02c07032005001854003064041920440200e05400f9a0301a4014000da044481c581e48010140e641039000b103446040c40b409140d04184815421259580a90005d04802e40701d1365011072810714183e407999010841a0080815070804d182c03c000050302044448a145400401c591600d411076070340320380089a029484023885001c1c80000d0070b10079510180c030040559230 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 753740872 1250 753739622 753739627
    0x60906080c0111061506070f05010c08040c09020702060d020c030f0c1f06080c01140c1911030d09152d09140a06030506241201061b0209130602 63
    0x3440003944594114030350500048268442c2c05410f032000409a00811007580d90700d2004020300d0511043c2d81c409102503590b030208100e28000510244a65961100c00d035445911900f042d150030a038080e1103501c200d41547c014400c0501503991441120801181110011707682e080c411740c061309501900c805100100d1010526041140000c80e03080985005001840004410b002c000011220a030042135415803006600d044107500610038588141c082a0340f02e428403010300041e0385013195111001c1d0100d126214042c08000c00004044c001c034a0480103040d8144100c100140f482180d0311460b00c1e110880f104003207055000b0342004062014500070702801d41192107000d00c802e40b010900f4400201c0744080020a048505d030845442c1c2c000400d21403006281c50421005440040c2c03203980d000e000342003e034203c055144000b061909684098544520080e8500c0780c808405034403050600c43c40c0ca00700c0410158100c032150006134110340001c0703c0e48408418042d203540d14400100620b100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 753742122 1250 753740872 753740879
    0x20a0605031902040303080a090f05160501110708061b040902030403080f10050f01050a02120c06010314160909060207060e10270b1e0f06090702150c0904060906 71
    0x3800452040d00d05a4085a00e0310824031810300f01c0c81a072001800080460b00815001c42160308a050300305d01904481082c0c5025445450402807004c00580130b00c4400c00c000c103e03650b0030160b4030001145030f02c00340c09550304e4841d0701521079000420440b0840c00300b0070801390302c82040042e03501424565804546902e440d1901400721202640e1100422182c0e00000c0c0c5140301c40c13600b2070152100035044000c0e8150050056a0307607005241c101e0301707500039018601499000030014010100405009100c42d501d14200800d508052440002d40c64018004540882022808410458004104c00190300c0c06500740308000340650700300140424146038102084080008000881d1082a04100500310b2000324084602c8824000710b00e81c4e6481c03411420104a0744425241e10200086004061180c0700d00d4030040c400085400700007040e0316505014040c04c020120307c1d8041070330300090103040080d01180a2483c402850300e05400c80020300116030751183d8101c43c2c02003078a42d50500410b80c0b03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 753743372 1250 753742122 753742127
    0x140d14060c0702040617070b0310050418020906150301030b0c1210030302010b0315060f01020c10050c011b1205070e10050d150e04030302030406111909080303190b0409020a06 77
    0x42d50083e4400c81c03d0080106034040c500310f196001c4540c80006046042c6041c2040110313410042400c0e814030340244000816885500484213411b08000301c41c5550300311342c4100300b85c0c100b01408050060185000380188407044c4800c43c2d040d030740c00404052040d541c502c500d00661140c0704200e007042614000703114241100300800c0003a42d120780c0081c84191080d80606a6910280540c000d14041060103d5450700303010314815020001841500e181748508004100156880c0ca1944000fa01c00201c0300030740c21080c0f05640c1469088100600700c02c030b10b200c000b840d880c1e40c01b02e01c4c1100c580e56008a0348041c010b000b0b0300d1207228003400003104044591000340060300806654140242402480c09500c140164000700b46c0e101c10880c2c05598039181c60480094200030401c80d4029510107690140d02d600001400e005004944d841e40b80689a00009000311a0380d13108138140d900c1841803000491002c65a000038400921002904200210005000c1c00d500e00010f90455080b28000c100a82d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 753744622 1250 753743372 753743377
    0x80c1009050d02101b0c05070302220e0105010501171503062701110a32070201030c0e280537050607060b2101021902010501140d14060c 60
    0x2d0320740a84c2c1d00c000c001c00ca1042500c0100e0303160752a00102900101400e40902c90140240f80200d00303c41500b5100da01160340050720085070a840c486d036180112840c0c680380118050000e50f00b00a100a52411002804a0b030722001c4410508401c000007450501c3e5281a80252480090884040b814180408880c0940004442220100b130340f40b00c100000701400358882090104400d903261401144084031000c8003100002e0690b81051004030542001d0185140b00703010550308150b03580541d100140445400880c250144840d0b02c102556030b665101d0103c0150b10007003000081450900078a510317154858100544c08100d011600c0001c030710b0310082c16106605501540664940000d1050001e0300922500340e2043d404c10440d000190b480c1c100c034082000c00703418082704520303010555100242c0c118040300140e502007000038070440012851182c08035503000802240d4100706503070b00034444104210740509201a080700420004048000b081c0c07050300f0a176003203030030501c0e00b8410b50b0303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 753745872 1250 753744622 753744643
    0x20c06011e0503010513061104120c090509010903090b090f12030306010206060603040c0b1305060c060609070504122603040b0f0601110d0c0507050a09021321080c100905 75
    0x2041d840030100e05400d05201e0390703004081c00c211030300d0101c0b41d1355110405024a000c2c0030542000501c40000c16040160b040303a40d0600c61480417010500300007042040301d80c000d00c1c0d80f060b41e0402ca040d1000c03a400c6504242503900a0804075501c444001c041040000c1060302c0b641c200341f0039200600304040c080040c40c01428240e017554202d88a1500300f2a00b030005840160040d500000e0804c4800904001010f4020010080c4440d440e902e034001031180d0031280030030086402640c204586454080380d1181e200105041442c00c050818224608003010034100400702e104008080400b0081251800300b0800c2c0c4401d4150303240740c0f81ca0a5110404255407040240780b560340442d41540c02000101e00607141540240b9861301d02c0c0314221030740080c0340010340c2c040c000c41c040030510361904e0384080c01800c01c4060160f5030b2103180030720b841c05c3c44980e4003c06540702d60b41c06207010660100203100445400c88209620341030043c1e003032030410104034403456600d847c04001c8010041c004c580d14654 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 753747122 1250 753745872 753745919
    0x40b040b06040905180102071211070e091b060f07020411090a0f030611031312110f0106240c170c06040b040302010f0e0705060a030609020a0302031807080c1201020c0601 75
    0x24504001780e90309034080c021004000440c2501e0b041c4042d0b100d81715424021101713004030345e400c0b961844242d403030441c10f40701c680454104080f034070b4091588541c0580425400d942c050328000c08240404118080e0100091107140c0300ca4285a40460303010a480090100614103c24290380c0c0d5159000d041c1d151008840300b6080001d05074101d11514141c91082c000e104803035507580e4656550030b010b01a00c0201c00180030020450a4451000308540403001d050341c800024030b6420044c07090b002c1c00140054091600001c02c0900350300f5400001c040b952a80f201000c0d568810800c142c50351401140030340744482c810207042105100010b409035001e07500980003048122501620001581e0000d56000142d074001c480400c66810940c00803c0f5150503450300080440d00c480e2000180d03482400d0580002e0380120034060340c09500160201010500c0004103034681c5000c49460f16a0103a8590070b00c220109085000803a20a40441d000048450143d5506684442174603051104940f0360101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 753748372 1250 753747122 753747151
    0x6060302070507120c180f0c0909061a1b1f051006110606060306040b090a0c1806080708070c020d0c030605010503240705090904050307210c02040b040b06040905 71
    0x11a40e81c01e0940c168103e40041010300c105e41800c08100036a22550080401150358410103010444d891083c04a603016644d50803c10a2422070120180c40c01500a400c2c141d00e011011402e02e0f40310310881d0310145c0c0307544e00001b41600402441d0300b007000b003d24640c44800481002c40003c200da6101c03911a00c500e0348040701454a511307048400c00d10041c01e803480c550169000c01d00d1071400d54089c545c003040041003c40c400072041b001c15903e4038140c2c2e60b105416100c29004e80201e4000c1c4a0200c42264541504091803505074000c05551018004100f441480740110b01070768420416035101c0c640107080306420004a24209a100e1258030090340c40d00e140c82d0002c600303131501007441c400168a40420700b034400e003810700c038182144000d041c600901808025035210fa440c0c89080307a1245001d40c018584540c054204080680c1c50040021010050140d021411a41022404015a070195800a0310301902004a00244089905250b00c1b407030101d40098451440c0c0c1006211f026500c00101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 753749622 1250 753748372 753748379
    0xa02060a1a010c111309060b0315040c030f020d020d080d060b0c0a060b12060c030114010f1b0609150b0f0301060f0e0c1309050601020d0f050f07140106060302070507 73
    0x1c1001420715a150b00240704204450045285a030801c181e8140c011301812000414440501c1100c07105442100c8103500d40b0a84a0705140900040c0b100d81c1e030f4107840074141e280555889000c0318490000501c5141c40c030340850155181c40030345d48001070780905156403200041c1000c00094220000c91903e070780c146000130420200341c4041d1856610fa200c010080c901d00c941c3e808000e42400c00d2403e4101c54428814540743c034080044500420300d020707510b1350780d504100c1c00c102c0da111a00c0d00f00d414403081d0700e00d1003410390340700c0441c522242d01001c250854180500d0504090b149228002d484540241c290201e503c02c150711160a02c001141d12200300d40c1c14405060a880084c41224001c2e00b58040c20414202c00e90740d1503038040c88007400c4a00c0c08900018014070381c152034214580007952041080810350301041480004902410807080380f40c65050020100d02ca0000310920040340803840004208281064544035590b20000703121007902c0d404020001d4001100907290f41c400c4c0d60000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 753750872 1250 753749622 753749651
    0x302060f0711010c051216051002030106090605030610110f0a060e16080c0d0309030c152703140708070e06030715091406040503240a020a020a06090203120a02060a 72
    0xc0c4e4035921001400ca5506005540c6404e03400c80081d5440c512419044c2e54002901409180c40c0c520543d0001a00c950601c04010a041601d0300311806100c41042840300658940c5110713441142103107800c0e1040001190b0381340c10041842c1e018040c505c5400c59501c10800c4c030784c0080c81c2d641c0b0700d002205d02d251880c06c3c00f5000840c05204211254000c07010100c0503040c54691482810f0003070501403040d641e25600c2c01e91411907940940b44080059102643c1c007030744200703c880c1d0103480800e0310508140c02c1c20000740e2200c4a20005121400082919003241ca09201a90040c51484240c800c995070324541e20380d031700c5421500640709004202010400800b11a4001e680c0c0c8855502c2d511500c0c2042c40d81c0310ba0041b60a079031a4818010f00002900b0b90b010800301c031025414109404410500c3c0801d00365080e0f01404506000340180501420305600040d00a1070503004070010407500191b001080c10311350f0030031141c050158000748803002c050700080d8460040350310040410815840c125074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 753752122 1250 753750872 753750887
    0x5190906090b070212070b04050307020604060207090f0605091f090c0302030f0a050108060f0916090213050103020a020a080721021c03061401180b041202010e1c080307090302060f071101 82
    0x185600da040c02140d010900b42c02c47d507a481842101180e290410780e0f00005c6082c0c01a80c010001a8000c21003844482c8441c010911030940d400b90030f0141605120018070b20050080141c44046446009114400c00540c51030000b0128800300300010014104028003a5008503090b410780c81068000c12010421440703841e048a82480c043d04290b210307686042043d010141100031144140c20020300038401010390080140000140166a44103003031401c8442c0c82682d00080c103061040c071080c1842a00071424240a517480540b03e0343da608686040010740e0a0301d80000200c261021600c0200c54000038248049007101070b0309a90b101905100300c0685800780500b007181c8140c185001c11395401056402500445100d10724400d984035894030540e908964800c01e855408020b805081d17580003400d030039841c0c80540706030298400405842070044060607004003880b600000046280380b003084403401640c0d0091840c2e40d5090729018661a9400c1070409840f8030121307410f03d5441398001e401e07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 753753372 1250 753752122 753752143
    0xc280c1a090304050628170709080607030c03020706020c06010623040e0c0d1407030c1803120207150305011805090a061503020909010603170a090905190906090b0702 73
    0x5510f0141400d0610619801880364500001d00b1805102d00c80540d8050142075201139a0300c01c0d8001c1900d108400e803026000d840c03401401480503041c41141e0011414a5101c10107090214900e40b021600b14000c0c81290809040240301007580c5080303e00c0412541e0407102d856580c96007280d41c45100081e001b1810f400c08418000401080001e000d02000c45607102642c90081410001036200c00c100b525400403894800c900d142c0700300700c201c0d601441200c5000d1b402d4901010016504001c03041980010301025040245000b40c0c1120280b003009040090030710300f03440c60f44000700e02d0005409000c0a005102d4854a4240030740b00140440c444c5d98812404000284494000383c1c480030002c14800c03902c01c407908100c1a000c405030b1112120fa81c05000795000019500d03146041c52815480e0780701e900409007400b0008284090303440240c07401980c58a0f200018161640c4c064045081881411201010305203007140e000c0c444503602840c0000e010340365010f02580e80c1031040f078413030900c0303203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 753754622 1250 753753372 753753391
    0x608030a0806100e1c0b0a0905060414031909140402180d0203010b120c0f03060f0106081009091b061404120c030f05060709050d02090c280c1a 63
    0x1000404914103d07a000c0c0d60020340d810201320103111500402c03400320100400d6441003044400550410990f806a16804404d5a004000b1038a86071348564a039400070300302a0013846410881094210144102c800506848007003a10218819034098041c0f0348610828440341e0080401000351f040a0088038480040b80030900000c080700000c00c2545a155501641c15640e2101440210b0321031a02405200b200f10009000d005005810041908a6444814020f4210409221f442840c907103030755040d9199401d00344d03d00e90b90030541488451a80c1d00501000b41410310b82401d00804680b00750b5540300c40440d00c003940713440c1d81069415081c480e04402d0021010030080010b03a100c0d41c0c0c0c661916104507042a0301d19a01d8603240e1200c8207429090f100380c0c228009010343c103608aa03840005200941320810f1064254001030711810b0000d041000c541400208031103020760316010424117001a50f0308021020301e000c401069600031300c002325100715981007021810701e501c0d131409100714031f80d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 753755872 1250 753754622 753754637
    0x30c0f06031103070819020c07140d02060a1d0d03091d010602070b07050a060906050f330409021002010c0210050c041413091209060507020102071a07051e010608030a 73
    0x640d085410010003846120f81c200914590302c1c611b00c1c0e900080402645000041070903c0c10420060b82d0b800302c814800c2c0c408c101c108100401a214103041d600040f0395400d090345112101c0c0c00c4058820201c01c105036005003046d82020404d6009203510060b240d034005155003440181e250b08801d800c080c0281d00259001c524100078919040004080c4907120f43c050320450045a42d50701c054400310311080304c065458038200480181801e20695004040c070944144040c2055030000c202d801d90284881d00003140c5044980c1e40d01d642e000100c01d0396010b4905601445501002030082468044940041c001c03011424000e2240e4040c7c0c41c01200b01c032003110300d854039088000780700c0002280d5154002c00451400c4006c1c04142c414900c5072400f41010108521580300002d20300300f0150410010b200060280a0143c1d03070000c1c40d40f0580d80340720f030b90b261854622940100e150141c400010024400c0c0c007825480266910707001010422950000d200060b00d0300d0300c184e2a03000b940c01da0340005200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 753757122 1250 753755872 753755881
    0x902030604141204121101090312031d0f010b01030b0f010e060a1803080c06010b0301030b0f0c0c10060305190f03270e07080703053d030c0f06031103 66
    0x8190a0445150b41c8004840744456400c080c5416500b142d03004010b8001e41d090707888144042d208410346010700034a080c4401e80d00b1560342112405000d0411020107685540701404081404013295000d003103001140c0c1240f0070b44989a020348118004240081d00300700084c0c600f030500c144506a903420507125500ca03680c0c031005101a58216080c03850400291041c3c49020900007070b42c0310b0280d030181040d107580c0d4500c503115500c0c02406900680f20b01c5810801080442d2032000400d4101034901700700c128a4907203401c845100c1c09441c031080c0d03042c0a02e9a1046d10b00d5015808001268498030a80d1086810031000e403841d503041c010050010351302c810400001070f1189030323059400100c00045445100c2010440d19481034250070001c0028002d000340082981c000008680c82020351900380480d01c3c10704103030884c03500e0040740303000c08550b8034001916101c1402550301c600c40c0f031614402c10165990400d401c1c140e03142c2c400e042d071440070820040f48451190150341044c0c1c0a4031066841c60301c0c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 753758372 1250 753757122 753757133
    0x60913020309010f0507020601170d1b050a02151b060103050d11010e0709050109050f06010f030902010c0219051302090603040210270609060e0907030b19120b0a0902030604 76
    0x20080900820f5541c030400600c0701105481481d00030002a80141b035070390306002c2003c01039002d40180680540c403c07078040d02c1181c0d2008001035551541c100600541c6600d107030081c03611565030700080d80324148407010030400b00c0c81806404840c800743c01c000a08200413045c95181d180c203003c00703804c0d6040a0f002d080b0311070040d00100e03c1369074140000652031908060b902d040c86055000150245d0329071004110122031405003d030087e56401840c1c1560a1010020b00b00b00c0c821481042030540b83c02a45007560702400e9800c00080d005040391a1401d14000785480c40c01c803d0040e00e2143c881003000f02e080d44220310a0310401400905900d14545440c1c08224684042c3c180c0308003001101510442d11858246c6000741400303444022888607420a04090f10801c280e80000041000710451040d40355140b154564110f02541070002d2006280d50218a10071002c048e068502503442c0c0b8002441c04954604035007031801400510590380320750703415000382e07000c512029625510000100c0c010a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 753759622 1250 753758372 753758377
    0x10801050f0d050a0b0103060c030501051e2403040f021018051302070f03020601050301200301030602090d0210091e0834061815020721021804060b06091302 69
    0x14000c030100c0303a400189644805c81240243c0080b6042501d4010104a00c0c1c1c00d406050301410044480e0450030089040e10750003007959185040c814041f805a001c404448000d84507182c1403003038221036581c0b0b480c0c24000c8070740c0444c440890040040803e0341845500c190510900740d4000011030b0102840c03c000c012410288145d411184d5a080103402e00140d0001c0300c0040b514032a80145c03907103625100c201402c55005001c1b003864a5480301d03444200d810f0040480313041d80d61084006071642101400314a0001c083d0170025040a0310011451845412a5640c1d00321030400b0b0041b60001d442195003a4030f000f0511440202c0e80c0400640c40b101e0031080140c0a150001e24140032444222402039107500c046030703101102040c0040200c070040300010003038a000d0b040b9405a2203910245a070002e5a902e0f0340d00c1401d120b0f2410380701a014134401709550000f803507001841114010b24440303610400c0d41003075900b141e0b06407030080c50380c0e4681050010750349101c2c802000081c1a91b0b061070b40c200030b503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 753760872 1250 753759622 753759649
    0x1501061404170312130515060d02130603022706030712030809010b04020d020405030c090601090e0408090607060204180b1f09030503040603142211010507060c0518010801050f 77
    0x140400e20130091800c040c4800148592040134010980c180306060890074080d0440c82c0c1c0780f01200c6001040516201e02507a0038149a040c1d500c10b0440c1024000f900c002c1003281c00003948000110100e915102d04040c0f0a10490114203c0c0c2074940c5503001016550b010600c00d440b2250080c015071000710b4061440a07038003107011000860800240e10000e022a4001d10b0328103010ba07130228041c00b00c0d003000c00600038524800d94004482e4109000040e0104030305215602e50f088904001904209000003501d500900143c019911801c061510b00007a401600030a02100000031030f041000700640220545080080d110f10340b01c0320310700f08250b0480c5030f1000c0c00b411b01c03107050000400501c04000500c000e0886a03800905003d4a960300c41c1584809401c1c501c3c0b074002c0c00301004c0080d50014403113400c550302400b60030307002c00c03008016038441c001c0020103010b241c40c004c941c600080e009401410b906c0c60b080b00340101030319040010340b441c180038010103400481f2240020100e04141000702001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 753762122 1250 753760872 753760919
    0x20c0d1401060f0f08340b070807031103031905070207180b01080c0c0304090b0f09130512070b01290f09010813050606010e120703051501061404 64
    0x58181444590a4071125032203d010000c3d01001009194800c0c1d0180024003490303406005282c24841400980050300510946040000c81101d00b5400c0c0081e410001444003000e03460b2260140e00f07105189030002041903012800c103c1c10907184060101c102d91049031151410714404610743c05410007418000d00c01d40c00e51155140c081000305900c80d03056203a02c05808003141c00311070300c40010004800601040ca60107002d0020020402011007074034103986098400113910781054002480c8814001d107032507003152103001401210b105c3c0300d00302100640100d04680a00e6420b800141c01445144005041d0400850042c044c10b0f900c507401e1220401101e480c94591380c103456034174000307500c2548200003210340040e20140c15604082443e510545c9845070b0310000d8141d8458540b01c002c006e16842c100240031081000540d82d0020f282001d80d91a402c071500907481e481c001d035030340842e0700c2c501040240034000080c66074403d0b000e071034601002c8c8210904082c41c2071503203405a2103038031080b00c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 753763372 1250 753762122 753762143
    0x9010b1002062712031501110d0509030106030f0f0b0702030a0509090c0d0e0f210319060305060106020c030c060a0903020111100c0525030e2403161e020c0d 69
    0x100f588041018220040010301601c0e520305102c482c460390340422110383d60500c90f1401c1c22203014200481e4011034100181400c0d03540f00c03050b0000a00505c802d400050009443c1c1d20034000344161100004030b590704c240e03404c0c42240c562100c02d981e24010940c08400203241040b42c0c81c110f082c03501c4000c0c0c0200c2c14054043c00e01040d10090401c1d5000030703001d0307540d5038814840812424000c00407069040c01c80034100f0318042c1988820b00140c400181405040741c81102040030000321644104000c58111702a10b0907561120700003501d401d111542180703e44102c61401540c0d1500004035848039610707445892880e840c0d40d00642c1d0708100146c200215018440c3c1c200e521015601031a00c00101a590740d558909a150000c054800171070950016403071640188070001e038208500c20301004013101c5412848480c481420b015141203900d01004580c04014065544542c40d140710382d0038210f803100407241b03401040e120b001228080c45403006034003154220030107061103502d03090075034080c00d081c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 753764622 1250 753763372 753763441
    0x2060f0c0d1e09051b0109030803090a050d02100606080f0610170f0711030c0c060c01020f13210c0506030c120709080601081f15030c030b09010b100206 67
    0x50307040c10400c160042e000c0d1204240410820300303000141082511262200c1c0c6030f4007000c0000c00e189154007000f010901c0010100705081010070001940b103038800100c2d41c0260508030001e484e00002c020001c0110b0034860041303403050040c181306200c0c0070349070500c12080d41d6203810052400e04124402003070000d4171100e8900b021100e64241c2c8120784400801e2894200b02c00c000300504400910001c55410520030301d048000c01159070701c105030040352116240d81c54840c11314024070400c400c0c030300c2e00900016070710f02403842c3c8400041105d001600e20440740c1c05100b80300300070881940c8007c094101c4542c1c01c1c0440c0c0b170008017458001c03252008450400440320180c2040304802e0b00c5180c00309100c603000f00319445040060350b0141c8400005400c40c000c2e4030040e405a450301c841c8254000e900c901d0800183c00c0310322404c100454101e9000d050403543c1c2e007000107202c9015102d40a0b1542000b04d1400f190500c074900d100210110fa000b0001591511282080d82d9075126001c2101610280b194 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 753765872 1250 753764622 753764651
    0x2120918011203020c061c110f0d0e0f010b0622150e0907032d0f1e0f0b010c08090a0302030327030a0305090d050327030d02060f0c0d 59
    0x2030192142d600100314495403410007a10780072028a89a1281c0000c020a24200326401206007405600220100b03520400c0440255a4000c402001d4510100803c9400044050f9002220341020a07070070746811401d05a81e890984035012041c039080101005000380e0400c80044664009420510716041191103000c2071360581d0002d040e00c0009106002d2141c1649800228150446002d08003000f140c00c419141d0b00b0310204d104461080b080713100541c404175440b40e0300034280110507111f0400840903150180010340f040302c04444840c620304200030034490300d00e108501d8a204140c452550b403c0c120f60b107d000a50085600b02e400c030707500300e00010040c1c4040010b081c40d032440711000e0101240703c50101401c0c80e030009100e80b00358440544140460307081412200321000664030525120300e642021451803050029803610729011503c1c1e50f1841c0c0f548000d04628030b10460554070039072440c441c100c1c0c1e9104261086c0c50351020315000708d50700c035808400500d041310146034003107141c40c0c1d0103914 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 753767122 1250 753765872 753765919
    0x70b070e0d0f0213090507050409030c21020d021203010909021c0503030712060515031815010e0a0c08010510090b0f030114060301030f0609032d0f0302040303021209 73
    0x4480b15502d000e8004114901409808010700c40c9038030070000da201a0322220b648440700d2040500580d5100280c00c18140f1501c000c0d408150019511401d1001d100c80601101c81e6030107420005002e003008114400b031006c603100900c1403041040074196400c1181e0840100420300080f43c1c400c8042501100212a8600f01d034883c034007a5000e142c0701d140c504009000c500308065540036a918280041c099690b948000d5403011141d100c03040c0e01c030313550103842034681400320b6410100e521400e50307000b0754881200f001c00c2c140d5171500c01242245d15150303103d400752101c030040364000c00d070b00c5401407105003421540e080b410764092034001149aa128580c40c0940d0055024030841031300000180800c0346079403900b660070542918001e15540c51070719222001c1700c1c1e942c40101000d85614610041c1031244810741c0710a0108403042070519000c40d00c0c413907102c16602022002c5110140070440481c042d1080e582182d070150090580312140c050a4a00e603400303200056030144016501040c0c9210a808 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 753768372 1250 753767122 753767149
    0x307081b0702190603110c10092f01140306010c032316050d0507050706051809150306070905060702060c03040f0b07140303070e060c01290f09010308070b070e 70
    0x544110160034008005c0030b9840f19003880c500c2d02e400b0814100d04000004440980001c0f06900140136074003403038104091440c50a42103801310410510340c8880b181c9640913000c0b150240c070b81e4075000320909400359a44c0800c03a0554003007900c40042c5008071f0302030540f100c5465029041110030818880482c10180c008512540000c00003031440740c10800108683d98000600381086030504141daa541540e9505034041da00030060041541540700070010712410344a40e005008018601c1c015420003c1c1140141c106031180c800c8a0100704400c0c01568080b0503103001600907441c119094082c800c490780440541c02c800c2c8020000001e5840641000002829a100e000b99455049080c9034040c00d55221030340859401c1041071282080d00200a1445400c050701d02c03030780340e9a0032941c042c010414040c0c50059002600d482d0844442a0061019000e41c102c6a54000100740010300c0074802d42404000c200320000c00100c0049081d80c0e17011503205201d4074107075101960510204445588407075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 753769622 1250 753768372 753768409
    0x60418031e21090f140d12021201060507060609140f0a090b1501121409070b04180e0c040908030105190803030a05040c1a031e190b0f041506020c060307081b0702 71
    0x4020400c40365000306c00c21181c40c07031f000055041001070603401c0b0480e0300c107200b00000e02c0340000d10703507040001503000080100314048d020041801250070f078142903003048540711389654040c0002030400b0340030300c94040f8980e00202c1d009581c1d43c0704c107000400c00c0c6002590a052040d4403054440c0812240a0314071003100f0040100036030b0600224603440e1801c01d4100c51007260342440b040c4a025a1044104a10710342504046040b4078000c4901d07040141341340500b03810604000c948024440140000e6040301d000380c500c1003035a130380281e9803241d2245030300a000c11508208003040601c50b85400203a007181c05003166400349680c8010350302c5120111180b40d001002d0200c10440202c00e1010741d0700e00480c01405d548500d180001d8501d030702441441102110540c2d40a00f032440c1c0d241c54104200034400580b0410580c09103090620080c0039921407100103110703000d05e14074141030003810f5038001c0046403540101c40d250820243c0400ea070402e03c1600154082c045180580d882c001111494181c29 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 753770872 1250 753769622 753769633
    0x10305070812120f04031101020c06160302160f0507050904030e041d1e1c05120c130902090d121d0109061205060418031e21090f14 58
    0x4080702c1c2016a40144005824003e0000752041e8040c2205907600c1940c40450301096070343d5140c06d44103100034240c03214540d8404a848812441700252150245010000d094213840700d0300c100300d0580c400d4030090420708040788900c9000921354408031400030b1294054414003a1901f010031000700c0121002d80c009014200c204055040a00c80d010940a0700e00c030400104403804184c0755289500d040450540c00040281c0c0d0f1490014016820158408085482841100a401042ea4100c00c1d1203e4014200d140031400070309082c4125108242800e800b01411031510b42580001e40000072102d03007003810030b41c00a0002d11151140f56412070b66450f04407203514050300c0d1844642000503a075040c801c4000050000b0381e0424103801ca038400022000c11503546500125015150303400e102d4003e203c1c80350100e030405800405502080c02c1c019102d07000014031800031111606841e440205404002096031132004407600210840ca00440321915070011035940c10075501100205402d541d00b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 753772122 1250 753770872 753770879
    0x50a140702030619110f090d1119032d080711040501090e0606030606130b041d01091401022704140c03010807050102010b060d150b07150c020d02060105042301030507 73
    0x1140300c0d070001702a4440e48603042115540704001d40e4415060306d1031045075420010b50400450803240059410041c03c00e850402c2121011000306106010840c0e106d4803c010318080306402d004280d2006144806118a4810680302c00300c0c154404001550500003081c11550300d9140d40c000c0c98003c02c5404800a200030508550909080020b8a020320075040301082c00b2060740d800c03038810074202c662100000c100250030009002010b00c1c214440c02845106900c11a04406510000500d802800303010103140410810608034400c0ca550f40f003020505550501d00c81c0004030a110400a000d400012194038030007000059207400c0300c6407c2074000000040c0721508051082170000c100c280024054001f8142c0050080e00616809070368040e0744040701c1a0810417842e070306000380940c007695940c076026410082a040c8452510b0782280c0d00780052881d44a01c00610403101385c005601900c000c2e4240710406c400341110100c100500d45000c455601800c02490300c031070085101c0c00091100301d14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 753773372 1250 753772122 753772171
    0x5070c09020c1f020909010504052a0a08010608040c0303081905090f0c040c050906030406140f0405070e16110102040f0e0f071b03030207020418050a03090e07050a1407020306 77
    0x154140c0c0f81c03951500611803161292904a21a419500700301c03008102951121071103c1c80f05a0310a80ba000e00121491100b04400948000c01c0c49295a03610f001c0240e8803039000740d4402c2c070705680080c80000549404c10100344035210594005503043c00e594008068807c902065810a80724119113410542c00244020000c02c04510650710a40d01400500c88503607002d04203029105901c0d02407000000060b0421065500698000c41c010300c43c22920304010541e103e00744011030741100d19120310000401c0b41085414103501c1540c07a08111003112030070030340881c1d25211100350382c0c20b07641d000d00000c903050403441c00d0400a42120014403e592034022149110100c01800d20b030f061201000030612903c20340b62503a10400d8150501607035a020300d00c046401000e02500c100f9141d00c440000d4400c00c8030101311000240e0181d51540380141d01d45c8040558001e06072180760110b00c0030440360203401c0c024070900c8044410b10b03100c00d0030b20800c2c1d00031074240302040380d04503442c400c0c0900200c003005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 753774622 1250 753773372 753773413
    0x60a091d0f0607120f23010f091107060c11030c0d09050904030c1205042c0a151202031015051c02060a05091c03021e0a05060705070c09020c 62
    0x681c5100140300600f070021010b006a245050000425a201c0421190044003900061a02c0c02d8544004a60070b0102c108161200360a010b00c10341c40c01510000518207400b80a04c5001c02043c1c031140303251034241d40c1c80100030700e07185074a801884003484802840401c00e10140401d0111000030f0b140c0c101d0260002082d01d5001e4000d00d114108200174440400d83c840035000c0001da220005410759400041c05130340c01d015661041d0240c541c4410641c0c1405025001d040d0f421401444910140d2150b0781220251003c012160700952920842044060754161130282c0030381c000b4081d2065007140c2000b0609a030701440810300c400c8958a010061400e0040d4981020000c000043c80c006419600041d683c0c420340078480c04020010030301d0a02d42da10001c1525004035030285001c3c2a82c0f09240c06902c50038401c84901000822419958800340045541c0d030f600c9a11038068240742c0e4400400351881c2d004694140e5900b000c040300490398030400e01c004c0c05d11700d440304000c0803101f01c19116062043c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 753775872 1250 753774622 753774643
    0x1d0c04061e0b0703020304080607020d0906020a1a0c0906070530190912140c041814030910020a1104021c050402010e040c0302040f0807080a0605060a091d 68
    0x328025040100a400d008002002d82c1c42c1804002d0782d8030000c0c02d04a02d10301850300644100d0290704140703c1d00c150001004d98a141240d2200101a80d0324a8182d8480081410280c4003086180764011101101d040f140d80c056003c000301e6092003240400300310182c00c518011245c0c0c0d8404003c0e0003449410070612040d0409040007490b079403000040401903802000868141010514445190300c2d0068600502a1a1040c10b40481c0d144c0740c2444072510100340085000b40c040d00300304098070f0800e0b01800c01e24400c21282600900c00f00d03520000c40c44440c21040c030150205004850450703480554480b40300740c0d5580240030141040c1810906500d015108030f104600c100320283c2008810907101e104011020300000c0c9650340d03800182c0d103405814659650241c03620749021007071a051750190040d81c5009500242240d264000c0642e1055203010302e0741079038480032183e40002d8140c0c218640c40302020b8000003609581d1020342e420344541140030f07415841e202c040132421000410074500d40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 753776978 1106 753775872 753775889
    0x207030201060b07060219051305060708070b010b120705070f0f1b090c0207051c15020c3403020906131d0c100f051b011d0c0406 57
    0xa500c10021887d48403d09031104910390310178400d8400c0700000b1601440074034188400c12846421a25044812100c100091800078002d8803209000708104024503896008022041c01ca24000500075010040180017800c00714130004a950007080d00000c0050403010181070078000d94a0044400301d0300800d103940041d21780900d41c062080340343d5039800d6600c010303225000c008614001001e5509401513140a03400400c08001c61450548080c800041c82c2840e20b23000e0310f00f0030f9000350984c900ea6032038980400d112150580505040c0310003420070440d0a0845d800141c0403800900700170300891185900d9900700034541c1c08883c1442c10340e041c500c1d1a0401424813a50b90645405441c05200c03102840d046481c0035420310a4801c00720b0316513a050441c1441c50121000d400302c54404250f40b1906c0f000400c14840e0503d09506151501801d80380542d082480709940040c1c2c45050b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 753597122 753776978 := by
  have h0 := BRFrame.cov_init 753597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 753597122 ≤ n) (h2 : n < 753776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
