-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1229
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:52:37.328217+00:00
-- url     : https://prove2.me/submissions/a3a374b5-5669-42fb-9359-557bbda43fd7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 220863309 ≤ n < 221043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 220864559 1250 220863309 220863329
    0x30804080a1226040501061703070b0f040201080403030b0a0302030f0304140307060e150408030a2601030c120501020f13150c05060103020105030a0207050601080c01030c090e0f1b0c07 81
    0x24800705030540b006200409842100481034540c151a81c440d4610709500a2140e000087c16544401008202c4a1750552950b001d078004611401009401d11102d5044006811910141e140603030008041c1c680040008041507100c42504185850308101c001c0615401001d0303800701c003001002141e60703400c02d100d01c44181c5441003600c0380504002c1106010f4900c4ca40ea0031030340400c02c0041c44060b510003400318003e08001c200026814100303102500c0d000346c0c140d6030800203082c00c050581014000d004980c1540c8000c0c0d004100081c0000340440c103c075984001c140ca030301e40707509200f80240101040da0070004d00001d02e543c1d0381c1421480c0c1a040d940c1c0c111b0790307030144003038904d00300c582d007444400c010110341c40500180003560040c0040c4bc0c5c4891034410251a00c161603072030f10f0a107042a4001e6685503c00903a00e0304075a014003444003400107600d404940949491000e5110507c090081c202e442c103080041400524220340d50804502d1000d5030b0303640ca0014940c1244d4481c602e01c00c5000b80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 220865809 1250 220864559 220864583
    0x11707020f0c060f03181903080703050a2307020f06040c03030207080d050406080c04031b03201c060b030601060503010609060f0507201005070c060c050322030804080a 74
    0x43c034110707040d14030100003004824215603078a00300010700160740440c01241d12500d8203010402620400b490f0140d40700c0e07911802181044d03500031b400d5440c050141c41c220340c1004120410340000341c4c040d0404150f24401e002242c1c0b5803070b9060303041943c0d8440f240c40c60b0041808000901c00b2008107102100c0c800e508841c05c041e500c130748254940c0300f080722801c0010010002044858032410010740c0048084003c01c1c501a0340381d440080200588001c105c0180c04000100148005010484035101103000e40d00300b81c0541c1030000707050008051030844250407039203400c01440f00b5170f845807400c0700700a002c0391010350315020041c1ca00e4109120790000103440d0180440c659124554100c0641c038191280c0342401d072165202d00d000b8841c81c500540c0700d0514014440c456444036103080f180801511615074441550070811900002904074100780441c0c00d20070800203100004807400003225103185e01c1c015082800d56849104294405048503038003140106003041d000c0b8030044418032a01c090000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 220867059 1250 220865809 220865833
    0xc050a050303190e010203120411030c030f03070215070507230103020412080c010f060b0705010b03031801050c030c03070308070e100806010c050c10020a0302070b0f07060b011707020f 81
    0x20302e2007a0350b80c3c035000c4496069a41000c6002e00011110510140103903420030004140c08444503000320703030990342c0c1c10311150f410781c280c141403181e01c9160070142c02a05c00a00d406191594070320070780800900400c9034a2005800c0e030710f03440959a0241d4804256042680c1ea0601003103c120000b441c10000215415594104c0d030003442114101c40c220361900040810a40703e4421540104100c400203540340c100f02c02090f64244601000307088041180da80340c04007810b2040c211840196940d002e54010490b582240000354001e4110b01800d1030070640e10507901c0440350440c0a0242c402200748001f04411042540003070304544245903d603112941c0c1c0d1095030420182c5020f80100314081031201d0080b071165441030007a600308a000d0700071200c580d00d0610104540807011b80c00c941c0142c006000722410550305208010060000d41c40f62810540f0450780205603204024008054950b50043d000469010301c0a8080d0b0805038407503800d00e07282c0000080d46803c14401003202c0e5010350040f03284c0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 220868309 1250 220867059 220867063
    0x5030a080c030411040b01030b0d030207180e150405030f0f0406030e0613060507020313080d031506050d020711270106051606050a09080a050d06050901150c0201030f06030c050a0503 80
    0x3c4556001940102600403000600004003140314680b41015128007554a0a8a8100c402c0c1901c910950040940f00e1a20402d1002e1121044030b42d15030074181506034180380c00c0096030144c0785d40803920241aa4075286090b5186114103000c910090748041803901c0c2000c09900500115a0784c0d8805100c020002580103417a148200c2e12030001c81d052011030b5000c00c2c0e0b298080d55004026004481c40d0080c194402d80100d0419400044a079018002c43e920720307589801039811545c1410800d036685410101e01500038060320100768001c03075000c070f440010300405541c20b07a0102c802800009031041d0000918405948400c0743c5600301c1100c000001d0110300c1042210304024081b0f4556041481036039419020b040064949400961902d42c08008600040000d000880f6039858065880350b4881c030704016554a40e2266101e03407102d40c01001194600103c0e0201c2c2d1407140303030003002c45c4824070040c2e005041c00b055071600d0341d19100000c0100716a412101c1c0a50300101e401d100410303035903003c040e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 220869559 1250 220868309 220868311
    0x2101107150801120f110a120b060f01050406090311030a0602191d01090504110c0613030801140a05061308031b0709020304170711130606110d05032701060305030a080c03 75
    0x910107004a00a0030204400e01501105907200038200c1080d01d0748c5110300100051240415100ca40c1c0d00814040203150840c01214214001e0809038102881c00c8005040b942c501d2001506540d81700f0b080c010982c2d000d01c844400543d1258045403241d901481c240b06c400100c4400354040784105036030032a1031014410301d9070300d03000507542c610a0030300f441c0601015041142c501c840d94003060002d20034440d0280070b5184220110320302a004800300c0e042c014000801a480071108940c0c19440d482907172200802603040d9801901d640c2c1d43c89003e41014810390240781d01034521804003003041c10b14481d843d00c01086c0e454042080b551241d03202d12a0340124402941c4c001c248180201d003030104540c1e20000392842c01d0264943d0b0344c0c100c1a05001c94a40c1c0c105c64494442281e40c0e83c2d041c8100ba03000030400c8814505130b401020558801540a001403001a043c03203841c0d01c03003208821086612403d0394241d140050000d20400340e0328076040e55139410400001c0042200440040c14000c4008241c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 220870809 1250 220869559 220869563
    0x50a050a201906120f0203010311011202030105010215070c02030d0206100b0c0a030e010c050706091a03060d020f040608150406110313170d022b090b040210110715080112 75
    0x4514030324030340f03e025101403400e1010100c0741c680300d184101207501ca03031000e58000c6010383e05a201c8048064001885038904001c1ca01c1c0f02c030301c10710050003a81d03030016803a4880e5040c4090030400e5281e00c00140c81d01d001c00000250b01d8865141c0361a000390340803d0b1640581102c00109910350303250a00580f039806511450346a90b80190b420402182c4102000201e03c1c00c181000c41c00300341e00d03483d440c3c01c05d09070343c0100e004541c262804216050380901c01c000c241c0109105c81e81141007080001f0072a98420501910a11483d40d100075180d4640d40807800500d4070074215130428603581d6004010120407182030f070703a05180c0402c1c01440f103030a1086a2140c0044034200481c0e61290392008111543c1c65000c1482000034014003042811b50320083c40c014184010b00384030061500c01c00c080d20303040d4813900400740b4200001c1c01c000401140a0070703046981107407050060b11490100700c504050410312122a442031035400105080380c020001c00c908595900c110148ea211500c0314a021404640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 220872059 1250 220870809 220870849
    0x50703020a020d0218090a1e05030304060518100b18070801170304170a1106040b0f030a090b0c04031a161209020604080f06011a03060d050a050a20 65
    0x315070018601500e40710000380c070040240c000d2241c0c4107118801341e407003244d24442ca640505e8007441409070a03442041d030310003041d84d8181c0c2d04441e40d40d16901c1e800050402000306840b0b0012510f0120120b81f180690f81180040712003804c2c600001c00301400703800595501812030035817440301c50141911290703c41d502a03111002d0b1646400f0010002d002450100c003000d000c01e0201048141000d9445207002c001180140200001c4d42003415601303003401c1d00c0c1e500c9040d040100b000070f03540001c282c4000404c0b04100703e40301d649080010b0007a001b040d8005044410031000c10a20680d03910262095074000c1028103100d07007160001900b00c100a8515a6440d03010300c0355800d01c9842070746000018501c01c000465802d0301d550200b030f46500701c0e0f04012103a030000030703828001d401d00300311440c018050101540601000c171566039000d80300c00303400540980c105c080c81500b441001c1040c035100711750120481f0388010b09428004011003903050784201e4101002d55190007071522080b00d0780f403c0c031040c0f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 220873309 1250 220872059 220872073
    0x305060d0c060c080c070f05011205010806060607051c2c18151002071806050a0b0906160c05090123100c0b0408030f01120308130312020307020d0f05070302 69
    0x8415115105415001c5502e501c0170841352174001c0050000708014021407110784505420b00001400c0801003c0ea42c055081c0380c80010003000c000064096001036044c2c441540d1261241022414211007800d40d248100b05081840c0d803241e4460f4108a9003e00c200300f00540c0c55102500e00c1e064403900d040c3c80d50020042c4c034481340d16202c101c812600309030030603d40d0740c07402949000719444c800d40c0c10810780540c00c000d00c200903605107851500034090950300c003000054280f20008600030380f039014403880c40c00045031020041e10b5481c200c5180c0002c02c403a400008000b840c00f5403101c0114051940030740e585800000e160306881140e61410300c0c400684050955984052010441c0384c0c1003038a0030824182507407004212420765090085004940d0701c0d07aa40b03055480100401c0c01a0311811b42030040d000184082a1b02c40e1031a500554804e0340c0e1461440641070440311100100309154000d4800414000e03580e400050618411800da100c00400700d1500206071903070b000e2501c000d005604210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 220874559 1250 220873309 220873319
    0x10225050f0a0b01210b04031e0207050a031205041701090204060f120b0411060d0b030d0c0210050f270102060105040b06040e090f01090317060d1203050601110105160305060d0c 78
    0x41c02e0700d440062100100381c031703018181c2c41c3d0031000d6001361001d80114001c440d80a01c41203d5010110180b415800104026894034001c0341d9138038424400038118031440d4031400c28840c49102140e0080000b10b800691480100203d54003c202c42a0100d2003646846800110302c1080c500e40802c4400c001400368111a05440d00403207040014011103490010f1a1401c20355074484010384540040c128002404071000ca061503e001e000004c18402e10160004140c0140d0ba014904010140140341050b1900c0030840150100d000d00d4800105502814008980445804d2032541901e0301c00d80c216415a6a0703901404208e50500c000e0a0300900100000c1c400c01243c0000c5580003031740398003121300200c0480000303800c403136005600302c0000300b50200c0d515003040d500b510301d40c02c000100c48400c019050391303843c0700b1200c4030031a1840c00e054940780050310aa00403015071458040f1a4003d1210f0300e86002a815920500c1ea00400801d1410010410741e04000308044841036001152455280c03c0c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 220875809 1250 220874559 220874579
    0x51e1503100c030213080304030816060b1c0501050a11221e082a01081306050103110a09060819150609020417060702120a02010225050f0a0b01 63
    0x4191280e40621402010766500c8005108007480c0c66226900185c0b00c0c100000740c1c40704028642d0041040c2e074000d2000707202246083c41140e00c60380d0707084842c5d41c444000e403601c800500160748410354811100c140421141c1d0020350140340782132080703000304051b64803070302400221140d10201811451042c804d0f007030104040c0d001000d9803540c0d502c0c205581541c1d05c05820225414071220540c02010030f1082051501c208801c030149502040c0304650501e0306003082004948a09545040200303042c041090403207512480240c1d103070400014056507859062070b2088201c2248028003601f044100000c0031030803403043c1010785480300c024006d221886602000c1c0440d02c903805583c20350a00746101045070a0b8829140100710849001d41c94600d002040c00f4003846241003454160400010040c040e0742c085000c804203d40a6081c45c0c5504181701c0403070080c0620400d02e05032909000c51038003e081c02d80c0340c044000b8441c2d01210040036000c3d092a44410f26003200070659447d54005215010308 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 220877059 1250 220875809 220875841
    0x8040c1203081b090a080703140316020f12030a0c020a1a12090f100608010507031109040908091305040b0a02040e0f0603010216030c020f10020a020f120d12051e 71
    0x5142c841e01c0c00c00381c2c4000000c0e4000d651b548101101d0b803052030104100300141c2c11145081c520b0702c01039030418101c0241c0103a511401500288a40400c9502d40380c0d55a0381d0150410290911007203c1d00d40d440038501400c186880481644208c140d110005180d001590040030341d010b802c0c1e0300d03504291600c42c03004036070b80000d84981502d000d04146924a020b0421011024201a034804241a803501c00440d08461000d080d483c00c160178803039061700396034003102107480e1094152000112100c950a140c0c49034025448841d911035081c1445e06000d2015802c03d1b4003c500071001c00c071103515038010040c03c9200358031616509084010020388074203502c403481940404c0203070000d4a40080f1890a03d101d461094041700450b0481c0c901e070080d410f00b80400c8003c4030040c0c90b45403032502500c00c081d40e14880c14400038803940644050701d0964896040080900d06000119181c5211644010f80001c05007c02c0b144620318100c00208100d0b503110310220020610030308888a621071900980400b05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 220878309 1250 220877059 220877101
    0x402070204060302062205040c09050126160206060d02030606100c0f1a090d020601090f020408030c010501080d0e0f0105090102010207150204090c02210306190608040c120308 77
    0x1e507400e80000580c485000070482400303001c1c28154442403100108040e4a081e40099019a140038810f09d0a0f6420281c1d0100741d407800d003001042c14111600b40020240183c04206407007240d041800090984030040b0044020340f5000e42e04603541d44000d000707031001d140e030004c1c1d07141e80207802180b03403800c10741400301103c3c00c14504030a00e441140c480b01e59044003440c08139410300508179441070310040c61424981050f6110064400210080002555014103010f2650301994541851314036410580c11500140f114505a0740c580003090b1066008103004d01c41d41c0d105006a014031071105202d00c100700020310004021a10310901940111095000303842041e0640d9403c01011020036001d61000d033041d00010700140c0d441d8288034040007030350300e80340a03502507600c2807c040700c480686c96000200c07850b100c0030183c0c881d0b40c0e1000095019200b00c108010141040320085034856010000a2041e40180b8881250701c2d03543e5410590b02c800c949010740011010300104181c2d028030044614480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 220879559 1250 220878309 220878311
    0xf020405101e09050f0f04080d090501060902030a15120f030c02091503070504020f391006050628120c020a02090c040b0a0c05190f17180402070204 65
    0xc1c1ca907442920344006821908290340744200d410800030f4000c0c0180c40c1c1c040300e0300c12003402c1424101c00342e0001c50f001402c001c01400020449030902107541c1d02020500340c00078004e004541d0b403130090100941c802d0b1405407600d410b00243c080e10040407107400080312842c3c10620003081c00c03901c03a40f00c0010314420403810003e4002d501c2e0003698401c0e1080b40039a0032040561181502d040c1090302c1c180c074640c090741c01340380184a4901d040c100d80c0d050311400c03800618141c01940d00c0700207402c01c0a000d2000054004d6039224282d00402c0001140c3d50000400c4c1d2040102d07a490f03c00300040d17809171000c681ca815500084260200200842ea10745541c45410417480101c100784100341a16641041000180d011324190000d500e41700507015003041d02491024a09401c02c0904003452041c200d468062248960614003004800c004c40e900e80c180c124003990742561640343c1400e07103031012801600d041c3e120100018803007502d9801c603800807550300c3d00300fa21400742100340301c040c0d00b0002d020303603000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 220880809 1250 220879559 220879591
    0x50310090609020903010c0e0a050d020f09090313050f1e04090203010c030905010b042013090c050703020c01080105010e012604030507030809010606020606011215080304050a06020a0f020405 84
    0x318029001c0c800203041015409078907500d40109150031100d82860b94804c110710039400c030205490303544498007a03510966000c50000014000310341828445205590820140303c01c200107550b000c40038242000032440d030704280f030f41d441007000070300c2c104a54640e0f8040c800190120b031300304000c48a100c01040c0500042101841d9800090844111600c400e000c00e0b00c4210601c100302d0284201160400b040f581041407034000d04050f0008a1841c1070a00c401c80001150300321501d20120890040208240c1440007082c10100200160003101c41280944201c0e148880039602511140d07040c1c5806039a0040800000c200454400a5400d0500590801c54102014082546c50b00b94452070082e200c00c1d03501c55a80c98002c0000c8c01c02480403482e07900d059400d0001070750110340203401800c2480e15100c440d500e0a440002803922804030050078a002c2e20000303080b407010016004851045590305192540c8120990b2200c0c04040024001510550410010703d410303404a500200110749604c05c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 220882059 1250 220880809 220880819
    0x100e09100f0e010e0102040f05060c030307050f0c030412030e040c02100b0604090e03040626040209060103020c06101509060503011511060f09071421120714010c02030708040303050310 81
    0x8444d4001800111a500000c0600841e144007407004024101980d200f45007004036400a034807400041c1a40080010010703188200c2884a001c0d9004000000c007a255640d44c0c8009840008005200480103d0f40a44007022903181034801d0000051280c0c01a140600351400410018220100305590104040c007006c41d603200c141c4180f4200d0b0b00203138021a512414028064000d011034680007e00044018134002100c010003840c80c0c000d9030580d65143c0586400d40141c02900070030385000c2c2c1c18441d8000300003071602c4008030f41080720115800020145c0031480c00f1202c0c070b00c081c01000042641000100110b4042ca44800c03071450943c41d00e10003620188080303504291040ea0071414000c2100d0a001c0426000d10002006254000700344207800e0302c04020404000160503500180040b4031022141110240300c0108000071100225a07203c042e407501c558492078546a00b0020341c680600040d00c2400002101c0c0d03015000800581060328580e07040740ca0740c0c8000d048409120100c040059 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 220883309 1250 220882059 220882061
    0x7030f110304080610050d020d030518100c1a0907051302071a0a0f0501030218100506030108100b04090c05130f11040303020c09040b160201020918100e09100f0e01 72
    0x5041440c010341201d040c417000012003096203411041c0b20798100c40f500e034010b0741c0707040c820342c50070b645401c0668484034501000400b51640401c45500000000c01940000c0d40c132a0002a4103407098414854064044610411840d001c5400d16010740c05101c00380014030301780303042d1003a00c3c03d4038801503d45400c0c0e50b04c5101d41007180c81d80c40440b8503140e00780300b03402e1a81d01030307100805d150540800441d032650700028900d500e1a00e40d903400c41d21200200d40301ca5502c00c04a40a04009080c0d95640e507592024203582d10340ca01502d6003d24588400c0010614180c0a0000c0090f0441c22064600d820141000855402c000e1008000b507514100071301c203494503002c3c4500d4582224400346c1c880340781d800c0103400e041c50710150720303c20003054041100040d8190316403074002c52120100d07042e1400c2c0400c00d90080c81419042588049005007403e91250360001080c851180c5181c04110b207580c49008600507241a05c2000d00c54000c1c0b1201c12502520f41d1003c040000c0012011545d1065081d04d54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 220884559 1250 220883309 220883317
    0x60f0804260c01060f0501020f011109010e030f0601140a050627010507140c0108090c0a170a1704170a031209020117070c110f0a091104030206040e070e120307030f1103 74
    0x2c0d00075017800360400140d0f8040c002e104419448000a025040f40310322110020700c940011181030003911903090f000f60310204071041d0f105403040c0443d101d5507190400d59030035018010000d40300d440e1040c008241c17403c000341a40c5a580d400450322a90340210380c030316007450b40c0d4040041d0402c0024051800402c409000d03600c03900002c44003a14030600a10001407041d03100604c0d400b42039000e40b2000030036841d02400e81c021541801035100c03040750081d00550825030106000317002a061440200c05c0d1480c008001c00484034000c03d00071025844400d10740c0c03a265004006004109840c015108140031a00800105c510524210030078480e0340051040e41841507034184009180700401c1c4040014006040000c0c00045034141e03c482c00080004000341094040c40741030390348030408040301c080c01c101a03a001d1540103007040c2e151922007070580e0700b1807005c03580e10000a04842c020885410115180005426110050761800400e0748095528480c800244020416099414411f07280d040c8098 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 220885809 1250 220884559 220884569
    0x705060a1701030c0812090f090406110c1b0405010f210b0a050a05010602070503030a1808010e030a0314040f080a0207090f0603030e0621130f030801060f0804260c0106 74
    0x7400300c1d01e05281d845c038601300a059a41d40e483c0400c01202d629075886e81c1c5c4804131800204d402c02429039491810700060080c4408032608400041031030305220b080803910350030100e042e40c001c8062021b07a000308802e9410a104611660503c05018801d00201e03a02e01c0340c00b4100100d40c1c0b0000c2c002543c03600d800d06021101e4180da103135500f0910901c00a213020b024018800c0303200801c0190704010019480344100d1390500244011607031508000082e1856040050010200811010320b14850064880d1b01000000300024035142c0c28001c0c1d4203e100140d4050340c0c010464201114140e0344019407039012030b540c4c1083d0302c00c40200042d08042401a11000c0c4210107000c6562480c524001d01800d006d401d07940d02c240414082c01c3e45910302c00d0640c8502c1c010f0490746821644441c441c65100070b9204502070149681010351005040c0c1081c034150484c1c0540e601c21aa0380a082d1301120300c800240d400030000b03419000c0c0c444045503d81801425400f003072403124a416405401a0b0845038141d000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 220887059 1250 220885809 220885823
    0x5061207030b0301090c051c0c0f050307170a0303231801110412060b01110703051c08070f0f090902030108010906140c0702042c01200406020705060a170103 69
    0x20408001d515014a03040854103074000d001195455a40354031650107405543d00460381140302401d00b00032800345095942e0414507450303041d901c8001e03413604080c032400b800340644244d803000201a0000700400010b0f10000f0054085d114060b80c0c224003414405652240b4102503440c4c1d1b04420341c94a0b219800350880c4184140002d90610701c2c01c3c251008508528a800d401b1300040044902d0541c1a140d003940c06040001d41e00c03154130060b5020404160300c01031714400c0c280040204440081c1d921400d400c1c000b40140e4811203054120b42e1000b0031101c000006900a001c0f403803440c042c243c01900030b03507182042d03500151600e00039030498200740d00401131030791240d14681c01d205142c440c10b8440c400c28031010245203440004c00365544515040240940e6a50b084943c19003403100d105000781c00403000201da0b4200c0074a5050180500556110307040403010905401050f5400c112003c03540190050b00d0264602820441a504030401d40340500c180425a00e09810944040a01035441100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 220888309 1250 220887059 220887061
    0x402120d0206100b090108010b070609080a17060a0b0703121d1b06091e03010209280e1003060e0102070f14071e0306020a0c151e0507050f0f04050612 66
    0x408461810000d40c01407030490b200300485d03510317a41e00c50304039415100f1110a141d80d40c400da103400c034024421150064070514000c03a1404401e5400380341d1401e03006050060b900252a508100304460079244a0001e0105007000400c0000340035090b92000344100c01740025010250001c105441510034405000c0c0d03400c081800c0b039010040348034032402480142c6280d803c044c110800710700ca841c0c00ad0301001501043d504007060a41e0250125540708201510300b00300481c84284000c0864280344109100001d55003000c00d0250070002c0312480b83d95081c54101c1c1d00c45c40c41c4c0b100c00c000c04581703803544102d540822402c0e021451090584200c9841350000f0b80b040c00003000c0301d5041a00607007006005030540110300324000300700c803c05002d07280c01ca400184d649000407801e0f5107144102c040241541d035140312140c00040280d1000090304820b1201c4901c00c0e81d10260710342101d80494080300402c03002d00c404100f802600c1e019000302080d08100d68641512440040d102d508603c3c4403c10b4210494 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 220889559 1250 220888309 220888321
    0x10030210050a140322060f090f060c0e090a02091c0506040c0e04020307092c030316030e030a08180102070b0709140906060d060902040b07030305070f080f0402120d0206 74
    0x1000e41c828802010f10282581400d84905c510ba4007003005030300d4810200e14000e0240b0140d60310050000d6228401044054881d00d080d82803640703045800c6e1005441d04107100c41c43c50003074291800c080360081c000300b01c5540700da60b0070000350041ca081c0e1f5000f10b03c480700b03404c0006454495080c5207014200070484e51800b4504200d0065258010383c01c002c50000c01d100058030005078403c180c410301100401c0001c0460002040d4090b0074107414203161000c47c075429280d901000460146410a84071041903082213030a0f004c3e02e0f80f40740307400e0255204025040c0c0c0c00780702d00d11058228014214000325088048101c5003640c0100100b40c401078880b4003440711942c0c01080c00f00060a00c6940f00a460b5007183c0020b40c0803c00a110134083e26001a003207540083d03070390219010305481c00c0210b442d50740751813a090740d0b9007103880c080f0046494500800c0c1004d001d034400da04a10a41d554210700c0d03954545106480b0540508100d030880500a9010706502c011700c40d48000070320560007003416142030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 220890809 1250 220889559 220889567
    0x120c090601110a2402030a0f05090106050f090615030a0203160905010f030b1903080c01060e0603070303110a0b0424020315060306030a050102040303080f060a050d060510030210050a 80
    0x5000a4140064000b42403000d120100e0840b124680040815404030640b20f84202040800840b040c0454400810851480b50981c80341300640c0d00a00c040041d56600c0e10030714202c2d0702ca4090342d41e01160030100281540381040350682c1c001f8000d4a42010300c040d89105000a41080d546040541e8000c410080f101696848000c1d00c0c0f45a894490b211500e0040042d04040124a06908161b20b940710b0b0101901d80408040a0500c4000d910282c030b036503810004900c1c2c119840c061070550a08100042c0c1c00c106448171070244a00801800c0c400349159416280f203c06521300b2012401081e031041e001c219030481c3c940c030a034003a4029004121264540300410220a5400404988103009002c40c030095840a10980305080d81d81e0f599940300c11000a10b440c044440042242d03000040120400d1382c030200d11070040b4840c200f21020b6440342810480040a0381c011650040c96407100100440c141c0d800458009222440390191141c607078000c240350740c03650000f030f40100d50b0005520702031643c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 220892059 1250 220890809 220890811
    0x110d0f08070516051005070f0516030302101505130908070c03020f030a0302030a1404080303090c0306071b151409030306010e0d0f12120e070512010903080105011d120c09 75
    0x143c01042100340d400c00001504000f0210038140800102058200800001400f10050300e500502160000d520611042c510b14219000403001409480e1800c4440c0b216401a2107034008030303c50501c4040d0030b103414031026451003080f800215841d0101c1c0404a0317501d2000380036160007002c0384101c0600718010712281030343c030f021402c2c040c0c0e02511114003c2507001c025078040c1c502c18504100f402008032210040ca01454025040300d000000503c030b83c80d0340009504a2032003054082c0c4825a075a4501a00d010100d038041445206c8181b04070b00010303a000140030b0060040c0f000009104034120300e081c0456204880182e80f44e4000400e00c46150f8010440c80146d840031101070904944c65520843c84c4200504000d020031500c8240d4825076010b14200f10324084548402c00800d4800310140e5034803052031103030724002c0c42e400381b46460400b0f060144040141d05600e841c505a4a090b00468010303074032480d1540800c104a01c1c3d548070fa40d91008928034441030030000c0034032901c000100045900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 220893309 1250 220892059 220892083
    0x120d0f06060807080c0f0438040303080a110c0d120b0f031009030c0f050105010501090609030302061303090b120f01090606020706030b010207170a0507080c0607110d0f080705 77
    0x6004030070014001d40c06034803950300036220300c15203840b048080c0c250360050241b500141d00c0040c030f008072040e2023142c1e0480a801d640a003030200c1100c1c11807092011300761246000207070002d213804002485145a5402501c032515000000c3c03440d00c44070042e1682041d1000100c0c00000f000e030030040c801811903005000c2080b0007215520320404000300004e903504014100c0100301900e0303904000a05014451b1101001d4001200d9418629103141850080000740610307408543c1081d40030500d28801c1601c14183c03580354004040544443c40d43c80301050000d43c0480410500032000b00d807284140000d071156a900e882c0380300d4a0700b4203c0420300f850340b0513040020071901e070041c00c0005690000710501200c519080005004142d031700102e0901000e074000a8190007402d03811191100c00050810302c0c103000382e05580f01640c641d404103841c0c0c20751007081a80b03d0405d0090300301240c1041052656000000c00b00c5e8182401640c0e644140c4070b044030b00f954541c10100e203420501c2000d00408954903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 220894559 1250 220893309 220893317
    0xc0a0c080618011a2701030b011518050d0c030c06090f08150402190b070b060f09061e01020307060c2601080a0b040206090d050303180a020901050d05120d0f0606 71
    0x71300003940c29582c0412203420b80300d42c0c0f000d1600038070103100d222560421507101401c4a41d035a140c3c02c00b80b0009030203200384c42221a480c0d0701154021700c944007107420f6540d940d501107105490441081080c07982c1e100140c5c0c4500348001c0c0000040c584091160042041c0d45403030101c00e1134141c2c0540203401030b52203041c3e160451402904508034480d20264400e504541e120600301021054086905d803940041c0b03128400000c50005000b00308168a00c501400c8030710242d1400d4540c2800700003041540d030160408480b400f00350300014101d00a001e41d0780c0610441c0d00b01400e9840302e00a60302103032844408603800b460b9100301514a000d042c603048604119001d2107502d005a456660714001300c0140001d210240440d04643d943d1003210041c0d0340040c40354402c0c00031390814a4072540142c4210b4844424440c0e075903900d40011074007100540e00209008407980c0b034103050112000000f00112602d00594901c542c00030944009045101d03a005000540c615661071050100e0b40142c001c8420300c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 220895809 1250 220894559 220894571
    0xf181f0f110303130308180304030f12031b030f020c0a0c2903060108060d05061501090f030218040501060509090601050934110a081c200c0a0c08061801 67
    0x1503408690703c0e8002c0b50b458134001e46c0e00e0f0b407044500303101000315001002c4103001c00100041031010341c2c0800480c00703005e443c014000c1c5481e07100c10f40485900000c5881000c2c1d0000c00c1d442b05c20b0003a40100740c00300402c2009481c280f001c0307441600741444160b080341c580e40001000c0c07003100c0d1640c15034071180801c1269074010b12191007c9235154040100690304100880c80041c1d22915858440c40c0b0b2958003404803038540c02d02d141414a4402c1c803500050010300b03130703d500050390f009092000d000c0301d40103410000c1080e80c4840303200d06050001d209540300d40d22518001229200c81004900c114148005822994146010029004005040041c41c645681e0012071f035801e0720100031032600303100844c01c15505610903054502089454100c015401168a98400d00015500405002410b00480f00034221200030f04002c5405a1841818480286061820f4030000c3c000071300360b5091030001c4030341b50b2940c2e84e140e0410751050780000d6510f80200043c42540c0d0304c050911008501110001d001c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 220897059 1250 220895809 220895821
    0x417070b131401090e0f0a05090c060913060e04050307051002040311010f02160b0a020c030a1a0a090f1505061503160509060a030207050d03020f181f0f110303 70
    0x40c00081c05045401000b2103540042030380991100f100404468201034141c0c5400132171341401c0340d03086031b006000030705000000b240e0420104070140c01c0b101c0200040c0c103010091040c0849072101d80d6200011a0f030b01e01c03010031402640d10010f4480e61007140210f5650b40d25140060a160441c000c62a07240d0041c4021b100203a00d44030b0411181c0801c1c64040e01d040f9008400b01c0c5030240703d590300c41d444001103001040b41fa0b5144001e00a41c1e43c56000c8400341e408100601da07541d0310002000d01071000c64100650022900b240840d0403030100704003c41e80786143d880786030a01d800d500048601c0c107160003504001c030600e4020642d0040040340e0140c524100d506510800d0310009211605a01c52094051402c074080d10070307030750035220142c210360b15416441d401900035071207510180c585114111540c0811803081c021112f4514038080383c24202401198100028180d884840b0b5000500c004007182e0b040001c060b04c0b90a40541c0c1d20b02c41000310307a00c2c015200469103170584032039400420030014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 220898309 1250 220897059 220897087
    0x170c0403060207211e02060903040b03060a0911070605060d031202310501090b1e090112240501020d02061302010e03030d06180203130303050405030904020417070b 72
    0x1080300c0e0400d5000d6500d021070302d0118105140240d40c007618440408003d40c0312903001d80e11583c000c0341080034501c6101c1c000e6060313039121811142c80d200d0b40d10800080c00655034010181d81c000c60f015003422205a1548000015a2000b500020340f0390808034841d03052140a020301c540298040d00c14401d030010700d4a00500200f00c51365100c80042d0005840c04e10304580c158103840e00316401595028845219400c40b1b0403000d18803401e80003810825021502c4079054080390454050300300782e502da0a51490f43e000031071700074585440c18402c54a000746200340d814016509a004180d04030411000c2007100304510031000e400040c1150700135007081c0559a00010701541000148422a00c683c01e0340c40100c803c081440202038250001181c0c2810b500129004a0b054840d4201c48124607002d964074041240401c590320601050381d6898040820702961002da0803600038030640f840c15006101150070f85c7d0083d4003452400420503a1a41c650009200100182c8003202e1414039180310300107015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 220899559 1250 220898309 220898317
    0x7090b091305070e0d08070b07020c03190201020313090912030b1c021906080708010801050c0a0c0311010c0504031a011d0a02090409030c0b0603060f0109020912030409020a170c 78
    0x4044556800201d010b4500030035420108080003415400f002403e8502001b4941040e4411a582c0340c90102190405e0f0001c01e90070b1900b640a001420aa0b6002e4441100d4a040b240268190300040244000a41c0c0695013000680044c90780400c2c810000d14040143d00e0601c1c503a84101441d0860300d9545983e0090500e0a985d45005251400045800061084412120514095000920300145c642d8011080d5413150420382c030390429036070ba920001801c0e00d404039800c16a03808204480d000300c2e4011043d0407c446d00038a0300070b40403003480c54628210703000c02e0b42202c04910302180401c200980380c005a0700f14440d0304221500765240180c0701c1029810113407040301503441c0c900013070000c0710036905651b41d20304002c1090094003c24100503100c2e400d4800300ba1004113404c4005915400c000800a0040c0e08401009116030320302540c500007504070509417640328039000010b1031085e008001500252451031030040e5075041480c0003030900990180c00111542c084401c003d05102210300b03407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 220900809 1250 220899559 220899589
    0x50601050d0305130e010f080303060d0f050a020d080d0c09050f060f120406020d0606020c01081602010b0306040b10050a030503070201080a020d0e210702060d09020f0303040e07090b09 81
    0x507800c81c104500d030035903030750080555048043c588480e002410704044003129040341c0174041e00c01007068982d2406038032440100c4100d50019901c40d41030b8000707030045c0c400142480c05101507138040801c6030b00054411442480036102c1100204142071042e007284507230b401050300d41c14009911442c100104001618074886584905800706103648110351001c101c462150310324004241a142920f070000094015251802e002840d007807010844c00e000251164003440142c42d290b00340c2c0d8030380800410904030820790f0400c6540721030850a0355181045843e01844c440c00d07422106151080c0103d9919100783e101e588942c40d03800040000c0f560101c01c1300c03c002d4082c82c00002a03910000824040d2282c415418420361408030f0703444024801154030320100390144907030402c800122071039000c0b6004000303019500c024100a1303e1324174074051b44961503ca201804226032540107000280c00c40c3c02c90b62183e000c10320784404018519511420900140c1000b034210781c280700c0040702181c080039840d569 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 220902059 1250 220900809 220900819
    0x501020a08070303091a0108100b1305061f0224041509110a1401020105090607140711090709030b13030c03030b03101b090512031911011409060a0905060105 69
    0x800014035109170061880a90032440c41b00414a070031303210700720b010320911806806016186d154030010501e4007407400b4841004040d1074500441c541400003c20b0081c007480e40c40928400400007481d01043d80e08090300c01c0f03401a0402c0d80c548403a01d000c0341c28040b2860300c50b42e865030400c80000c56541d900003604004000000f04070140e17180c070842c0080b1420606500c00c0a6002c002203d00d250306144008003030070390007840302d43c4132041c42e284c0d65a01528548045410001401c0344010180040c041280c05026001c210a441d200401c4c2280820f450000c0014140d000600a0144000c031080e00141c00501c0200300c0c40d40d42d10028951100d2030307401002c26859000c100c1c0b20b65010448512103412002c001c00c4001226000c1c1689403000c54810800304400483c00900d43c54003046096003085080051440d09480c006d102c00c0c4100600c016500f44007010701030324840d100911507410a01428400e805040c00c15462503860a4030080200b0b400720306140100000500208a560468006540d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 220903309 1250 220902059 220902067
    0xb070303020c01060f06021c020303070c0314030408040503060711030a050711120319080108030a03021e070f03200703120c08070b011505070f121202030703060512070501020a08 78
    0x25084010784140c0c2610718041d800c14001184c65108200c44200300c4056808840309000b203000448014541c1d801ca8001581090002800e00350141480d211707110310a10700b20700c41e0411903010740e4094000303490a84a0b2140460148214203080091613080361b09400c20410b07401001140595920079101c96108124000c2685010003500c2c2c10410394080c0c0040480240545036101030f581c0f074201e00300105404021501c10320656000c0c007409810ba1703400c00c000e145084000e01d010b4029600184140300c166200481c80d0314aa050980a058283e205105503000288039043c0280580130304280a0115a000100050300707080029400701220b50184c50b0043c0b894440c13005468240c031601010b0040e003000140e04040154848009060321003100c4228101640e4410440e00f0380107428000300b201000182c4d09012803480135502503140c45501e819244605400386d800f00382e80090f41c0c0400425118035042c01146000503180d0340f040f0b10314004080c01e51034080000d5840040c024080d0003a10001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 220904559 1250 220903309 220903313
    0x5030d09080408010e100b04110f0c0c030616090605090603060f12010f091a0103050601140f0a03030309051015090513062c0109080901050d1d01150504050609010b07 73
    0x2000d4070001e00c00748001704201105910345a07105c201c0d0300d050346070991a0161650061402d40b040401209440f84003e0410440c3c0e9442126548104c1c50400c4511511803002c0740b070b54040107118400c4071102040d04c0d0043c04010068401400e0790040380a21006220121003a180e18007601c0d442001103501d48144c00245000c6a40c20701d021004401a5003014848441c00c0c0c0d80d41c20000016105000c602c0031120035503100c0e40c09400a000081c0706400480c010009181061080c111a1000514a4204419078400a00c03c6640303503104a0119403108500d001380003041c000c001550240300c1007032040c00e00c1040d005c6040d59880c00b4070354078981c0d24404640c64158a12014400e20361260307080028415021100302c0b00300364450400781140c0e8511710b82c40c1007201030003008a0349a11205603403c002d8580015956900300300051704810360303150502e41c2c20540d0004e480d2020064207000080980c070b0807040b01901041604000e000d2170a086c00e01c0000d4a40b08055030441300c400381c0c00c58650a0328 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 220905809 1250 220904559 220904573
    0x71b150e011d07081920130507031b140d0204180203090f2a130f0605010212090f04150902040305010f0e0f07140a03051203040c0e010305030d09 64
    0x140d8800c81a40c07900340c2a003000c06036002000902c1084204a81042e5550010540d48818070340200920304071801118000980100f030850071042400c200b102400c1009011501007203810300507850341b43e141c0c0c0034800d80a8152081d0005d98808000101090250403c00741082d04030180380c8000d160009060504404d0913410b41d4094109240124401c8445007031020281d0001c2d21079031000c0c001c3d091300340e10210340010040010008801c0c1d0300020941000c0014400d00c0360710380745421820b07034052501280701c14481c1c81d8080c803410030001005824030300024500b13100401c00d07900410382040206000d503502c2c0c0800100070000c64011594030000001c4e0703040c10140e0f41c030092a442c00800d01008106041d0841d8040c15100c100402044030380002c0d0544d01c442845050351290400c48040c0510013146000354000b074005844030b11815901c0d525945000304156084001722404400d010400c1a0a91890018106640044400d504546500e500d1380319059041c84a03986c3d80030840e080100c6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 220907059 1250 220905809 220905821
    0x30c090a0b091006030b01020d090312030b030d0216080313090c0915020a0201020d0e09190209030316050f030307090e0a090b07080414060c16020a030203120c0105071b15 75
    0x1c003030210700311420090200c03042c1101a0080c140440c1c18084110b18a510004482c64401d4a0303907503c000c01451600c032084518000d1202c4003c00d07444108400f140d407000c000c2058880d031030360700a000030200141c500c0d0340003901d6003240003190410448850b4410000707c0010507210014800120f84c45a0642602c00203815448000251000c4050784552a000318006250754000c3c0c0a0b103c0b0f907218003504488480c89400d407940c0c00842c03080031460268101100001c1315800c1100186800e4020001a195401c4804102c070000c00ca24000010450188070a86501c00a04002c500b9030511100c0680138510300d0203020f00000b41c2100048146446410107a0110340040d0860031508200c40f0050090804a9098a008032400b0f120840759400041d2184030360952000c4600704442210740054641003000c050b64803100c07030b42022015940a00c00d86e408210007441c40327036840122240060075100300620110034414419008000740b0f1001c1d200700c2903c0d82c0080407401c0398412410041c01454 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 220908309 1250 220907059 220907081
    0x30903030a052d0a0f030c12090c0b0c031314010206070c05120f0d0c0c0c061d06030109090209070207051c1b0602030d0605060f120c0c01020a051b0606030c090a 71
    0x80030070404450b900c80d00030100c04584d9900c0a034040c0e101d1900f90196142c1800c940b000a8146202840f000d403035610120f02c0c00e1003840b120404580c0d507001442a0381040410803000c3c1c100144844481c88181035003801410180441d89481c0b420000103912500700034590814001018064403c0000500c03190207110007c2441e0b0ba11284440400d000c5a000044040d4007035241c03411032038515001d107507504a6654000b02440c0c0ea02c4c10007904503024140e6500184600444401342c02c150b0b9118005580604000400000c40c2c9505004200349564042c000072b05642022400780921b88070169610550810318400c1c1400300072038900780d00c0c00f643c458440141c21525640105006a0200040c030304580080c106000090712481048000e2041c1c0e04203043d08401000700c803c0c80d200d1803017480d501c1a040c0720f4282c18000714403070185c26030b8004190500041d030b00007269040c000304043d0038050b00c20112f0080010b07203441030210f655a0458042c43d4030036003040c800943d5842694211a1080b6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 220909559 1250 220908309 220908367
    0x5040509030d02070323190e060906070615050d0f17090d0302070806010b0f0301090f021b0a020109091406090c040510021c0201020a021906180807060e030903030a05 73
    0x1c052030030300a0250060b0000c0214640c04c10200d482000070400c240d4401048400007403002e00d0300900151000031230524201d4008500b84188441d55a5250103881e1241c000c400100d1990405c0030103205000580d009944120018000080070803241c603404107655074003600a01c003035005d000c03400049000d5034062a40c04451503954804040e401700300382003107640303000403a144d690f00c840a03a0054055400480318940042c0010001070030683c100315061040f03e50014585910510003900c10404658403030800d51107a00b880d011541e01c486880c009244040080001d1070321807200100840c03000c0c001e90720468104010404250001c000c80b0004c04d00180140030800314904040d44999243c81c80c5540c0421301d2382c44c401d0007401802242c000440590182401b101940c0360f00402c04540202500c401d03030f03a011200010303c9011441207040e80181031854031116546000025954502e0200c1c1164200f4000c050503505c0010640e07000b6855828102d80340c80e03c0c840e180d030144074485060071041c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 220910809 1250 220909559 220909567
    0x10603020904110a150c170706051006080705070b2e120614060913030c1e050c0f100302070f0b07030b18060307090f0e0d0f09050411030105040509030d02 68
    0x80f800080a9580600a8421140c500d54500380698081403006050707020810000f16040003c100c80c1d070700d2142491002c0c2c00c2c0c2c00d01c541c0b503c8140440c0c00440345c000d561003800c003043c40602d4011003400c0d4401400d2520925204c000d9581e018065006041001801c0c1c00002c100c4220500030307000c0f0f20405625044800c0c0a5441130860ba00101c0d241c0195103051502100c22a50101105600d204040150500c1c000d62110541c00c00340300500a0141c0070040c070303200601c00080003148130800000210b500303030300c411415040250030800700c0704031584210703642001e000458840e0302400c80d510085080058440d549400d150b00e1004020a0003000c0041040030404a0758242c0d20031101d510317080d10051040c01401e0354507e0442c0c0c0640e07810798140e10101c0708204110498103e03e0b5038205281000c40d44d4181415040e00d00190740c10749a000c0791a0110902110754000d21483c02410119000c1c0700140b0b18007441d5917070344410b004480c021a190380c0001c1d200c00702041190b0125500700401c541e9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 220912059 1250 220910809 220910813
    0x1011010b040e0c100e0901031103100603060605012c010e01030b040204080a1e030219140a0c050103051f0302100c02060a030b04050a0507020615011e050c01060b0309030a050c010603020904 83
    0x641103110080b600c1000303041e19490b2014411070f13a1703420140c80075017180d0f000c0c0d095481e070b610801580049154507100c2e0010322102c141d0680100c000841c401c50700854482d090030009800784035809102140071903081c40b110380480700c4450b06540c201d03003824248055981040104c01034010b26400030380240c0001000501414000f403004180c03400780d42050321050703958407011400f554403007010300143d000180b6207035113600580072290a14869000c48601d00b02d41200c035828903080d05400d440c199250741e000c004650301030013a10b910860400f43c1c400036141c244c00d035021031f44c05070001034000c2c911100381da00d1040c0180a80f040150300100a1030300c450503c00000c1c0501030350500380e8040d50919004c610b100c2194010300303004041d260050003107a41c40941101071071313403102261810014690148181c00c81c25034403580b0b0310851a9039081e43c46100000f140e0a4524543c0400420305003041040355280006c002e480c0d054406290036643d400c0c003a20814003408481d04040e510500c09001d00003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 220913309 1250 220912059 220912063
    0x6040318120b09061806160513030b0402150a02070b1c05160906051603210e0c090f0105060307051b012c0a17090112050a050402120303061011010b040e 67
    0x310940c5000704466581d580c01c204c134903581441d14007205c001c0e4410008150b61095405088402028030718000d0f08019040600121104140d841a50103c0c050001e10040d4140304850404048580007007604d010f0f02c40707100a6582d00640b00d02001c2000c0400c030048100d0066544458140e1018000c0c003460030080f0894141302d80350203001740841c0304064006800d60007002a11540e070000ca041e0400008152415556589031012848000c504107100b0062507025100303480305004050010040c181810050103240320014005c00c14078a0840d00401803035a6490440354080f682e4608240c4522100d2540507488140c80003050095003062400e2005c01c0084254440195042c0c0c40500c0000d0310b01d0085454843c404ca010340540a9218951002c20519004040580062504a07611745000c0003110803a08180c4540d1071141d116801d000079441c100c0c01c072a440328921740c051803443c1003810000318165522401f01c814047da00c03d60b0310310560b0a520a512214001d031080c0107806400403056 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 220914559 1250 220913309 220913311
    0x90315020d09022e080705030609090a0218070e0d0213020a0c0506010e040201141207031505041805011b050d05060a0b03190c020a05070509130f0c062006040318120b 73
    0x805080c152104c2591a0b072140014900403000b98480901d145c54640038495440802061520f041c412101c08400580300c10346d02085400b400d03448501a420006c0004048070710a0b1040c0b40b2a0368002c00680250b52081b449054104201c400140e60b84940b400c103075080c0f1602c6801134464000c844c00040c540100c0100c1500c654400d80c0c44028201e04c84c0b0f50702d02c40d4003842c00c002088032030010014800c24040c1d03003c5550b42c801d07461882200c503590400601590b801c04114a41418607190007010040c0074051100e41c0e05c0c00c03919a0151149545008003540a0440181031568484001c212141c0b10f100c0200c01624090402c0c60380c0c0e24185d008480c0042803800c002d07601c14034020301988407502c00b2860b0240700e0350100103492118a4281007048003540903144074910740c03425440074001800f00c9800b406031445844055011072400501070040c106812800c3c00c0d004940200101050020541a500035454244140d145456401c010341c65441c5400500c0350240042c941e1040c048100c0e481 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 220915809 1250 220914559 220914619
    0x902180d1a070305090a02133c0c080a0f0216030c020a0905100501140d0501060c120c0206030a1e0f0e06090a03140313051e060601090315020d0902 65
    0x40e940760342c2011000c41c1c0c0304480602141c3c00c122454801481d210311003004075120b0183c042503401148401d5011075100c0421500c2c9801007455111243c0020b10f086403400f10032500c01c0090ba01c00380d001514521004001030201540c0b1218401c004c000b03a416541c03000902c1c1c540f403072941c000d4500585003640d0400103a00c540008540014051158013903a4400e000c03c1404c1859540341100541e000012401c4215560394240300300d8000e03103043c0c07281078000c00c01d035500c894400100741840c1a144081590110030041c0a5002c20096260b84080304d82051860500103800e60141c090b840845070074214419095081500e0b05030140c07404c1d001070554500c0d40c000c0c4e401130741780d14038529540ca45040b8020302081c7d900c100d1140016080c1c2c05564132150900c88020701c0b00c03070b50356400d041152149005400800964564280200800009610040a080004001e8110348a100d4030039071400d503211080790001922220045144c11040b021a4080d0040c0420706200c2203440035017001c4882 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 220917059 1250 220915809 220915853
    0x90c0304052d0313140a1a0705030c0639030714070606060306050a0803031b03060111160e060607020f1309060915051311040908070515060a0503010c02070902180d 72
    0x8042090f18046c00400100c80d0b480300c49402009a081210140c4e800c03940c1c05984a010500118490090078818244218400519400400003a00d80c81000300013506100ca40480170f0002d098a280d2010b040704e0704110075040450000802c6c031403000040c8148440203010034100480016020380682048056450454000d0303483c948440340c039980c0340800c030b80031498a0702c8070013600c081d00500c8000b0b44e004070043c034101e4440d5030640d00b5a450003001c02020301080c907610100b080f040c20b002d0500d41e0843c40c102c42c51031a18032a6000145a80601d800389441610b00a686500c00c030001d500500380380754080380520400307540e424800c0150b207500082d03620f0300c2d04240000b001c1c0503042042c3e403056075001e1000710b1000e00c1e010601009094070201202c00701010414240403a1003003010181c0e040500004001d685451002d102900b409a40500d000340c0c141042520116008143c0c0c0040d60203403240141c441c010300300c0350000e4110704201650003004185100b0140481440030f89000d40741418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 220918309 1250 220917059 220917089
    0x42c010b0f030309040917030f060a0501080603030d0e19030203071b0501081303020a0f110406080d0c06110f0a0807080105090f0103150f0f0902090c0304052d0313 72
    0x1007440361404010740381c02d9050300200700c4c400852400394000c568003402001c6c90303401007000b9008041654070071350356000c5290116040000920b084810000544428a0b090200e82820400b09650340184407110000719111040034220300401c02244902d0350900010900d030980c58140a5144c0e4402d842c150ba0070030b0340c41c5904c040801407001c81021240180e45845045e030b0369100485070424115012800c5000b492a0803001c40c15003105148014020440c041905825404000442d039003035111b005560040e0500b07081090708102410545c540107140410116540401c240c801c0c0300d00701c2007000d1110042000604540e000100301e204900035210350100e41d0721001084518001160f03401e0300c46100e10014070014034a4004140305080c0500085081064090b840042c2e5a419402c0348242c0d0f031781c1140700198a407840307610303030481840c1510700e00e5400d00d600c40740d40320304c05525aa25031014101d40c0390543c61072407091440c5d80d41300703009690719070a5150758440851140d11540d13428115103c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 220919559 1250 220918309 220918331
    0xa380d0f0516180e010e01080c220e01060510020102040602070603110a030c050d060e0601090608090604020d02060d141014010e01031d1509010c0914060306042c01 72
    0x110a06014960700520400303420100c0d8811110b0346440c0800108681d00c15200140c5044c2c907150460103441c0c0301001c1c011a605001c1507600e401284101d052280030303036803804051b042808401d5400d1003994080400c3d00c051601c103031809415a640310a8008165074180005d43d83c3c10750203402500e101d41d080e0b0320b1896682e8000c40030f4800c050481014400c04110070b91006020b607000b80c100c0380d458102982001030703201443e01200c0640d4860703030658120b14100150396901c003524a0252a69040041d402d04156442a50b5010010030090041c1020f259807400d5584250941ea40b00120782414010034800507020a01008260350809810306e80c56000300c3e408100b040203800409040e034603004080344c0400110041c1103550302000180b050302041c00c5440c00c0070b0160b500a402c11000e2240c90b41442000c0900b142c6140040e0380030018195418440c4c0707a00c04d01017040300300c000c4503030580b603484040020780200111a4812404404070107021920b10035500104400244000200600500302c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 220920809 1250 220919559 220919561
    0x12210c06060d120c211707020102120112020d0206070f050c0105072006040f09050f01050906060403030509011205040f020114041503050408070209040f060b0409020a380d0f 76
    0x1801c00a00251941550b0030b411840303980f5007248140500009111009400ba040d021404046407a00008100306c054000c0040004001904181036100840c81c00420510240c1d00701410b00454100e160070521810540d80c0384802c4d0707450320380c00520307aa503646181d103860112428525400c0300e01e40074180c1850784a6004000b51003210750800c0003007105926103a040804071205001c10396009809100118603500c5d400c405101404104030300040908290000c0e54080700140e0203144154079030800c02c03515032107002c191000c5980c5400d0441c0c03924001e00041e0350301440c0e4101c964845160008100c180500c1d900000720250003a01d4138001d609500c10600d5161080b400381d51070403190782c1c5008095078070980c4096446401214450b050034010760020b41040001d4905580300426841640203000c010321642440c600100c40400c0341b418680c3c04103820015038800d24204c0a20031000e84144004504e000f02c0c04c6010305440c440048115144140d2604250728180da0030385010030b000611081d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 220922059 1250 220920809 220920829
    0x611070914040b070201110f181203040302060706020d0203040b04020117070207050d1b030b011a04060f05070f0f150f02070b130807050609030a1115040212210c0606 73
    0x241e00c1c1442895516a2a0442d48600140500e070840d0340c0c944802c6003407441080036046204204c09800d81d03413403120032011070b030011050100d80304a01106042030f14003000421a01240c0c0d0548000351141c0180c02c003a00280500b00da10041c5034000010030041200319a074040c4114801d0300d03a450020690304145903060300489450b4007591000c01d060050b484c012444617105882030340b040541400c4e400c0301c003c01c54403691040b039042d104100140611071480e0300d180c400072a100d0b49142060724040009141d5800d403035200003840340c006914414410840c10080c4004e07000081034011100500d031030f003000021003403040480351a005101060041e28000c03108c1150700505003090039100d641a000b60700c40090f00c21640903104210000000d4020700c03c00f0302c241d2801000d1529454034150107040741d02c005c0013401654021080040c4030076540c44101d85c0103501510468014038a0402ca01c8c605540c840c80075007940c0003107500e600710000203c020f000d80d4905006030f55171510703201e060002100c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 220923309 1250 220922059 220922081
    0x1906060924180b12060a0605010f0c0602030c160311010b01050f09060f07021206010e1003051b12030d0603200604090c020309040c0c06050c0306011d0402040308030106110709 77
    0x1004200820403080c556112022a0070070082c002050405000042d01c00940912021072503000f01080046101c00c51003a80300920007800c0507168099401c0d802000c8821806000300500e602001152120303220f01c06503441800f001004611461450401070070a111582e0070031700c250700f04203052416500c507100f03680d100c08000041c5410814000100a6103400c00e90394401c00e00820300608001d80e4604845420804a6001800d200c1d4100b00700c905481e207008100e450314510007541003000a50010310308030102c000f500c143c1c3c11000c001d0300050b4100e03103928000030703544000301d80c400c4c5000c0c5551026007182d209051200001c05244134640c143c403241000705501410a100c20007030346515401000070b00d185407050f686404440c00008040b00c04002180380000c0702e04c00e0700d004000d41c0d0b115564000014017902421844c0940c0002c00403001c0301041691982c0e0210300c12620745458054401441d4000d8090f52a1368403a40b005100e00365007900740c02a481890400201041c00d8810012010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 220924559 1250 220923309 220923371
    0x1309110403020103050613090c08070515160302070305101d0c1c0c0503070e0601121406010c02040e03030c250804050d021207060f03290108040519060609 68
    0x785150010b500804008003015045107950000c0c4040782c0322480b410103041c0c07141c140c000b0304a040044032482d0a6040e04124020600b1640b04403003508490141c50020f400c1840c420b044d103106140490508030191320046c00751140c0715840c8040801d90700070b001c151088640c240c0758100c40220300c2c0c1e56401028000783c1c001c20b02d41500f511080c42518082445401174140180350b942c1d030000301f8609030041d807094510411000901c05150303440384110b00c24040d550b034140720945805450340a007901c05800300c3e0500400030b428074110346503600044802140c1500707681c2c603480c11445020555100f4640395034030051030000e00d004400076620f148161074100a920f81402d00384024480b29070040082603070b01040c41031020640c018104225005081c042e964102c10039490240541910002c0490380c920038040c0d1500c1100b09444920344111020901c0c141c299070321541400e500300114000c4158000715a001c84200380b00543c3c110b0002c80c2c102e0401000085440f6140b00e00d10603802c06024042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 220925809 1250 220924559 220924567
    0x3010b15190504082b05090915031204080c010801060f08241c0c14011b1109040c081005091902040b06070f021f080406020a0306050a0803130911 64
    0x1d000000e40010407a2090300b44140380c0b5031910009840c11401d00108100b04c00041080000303034903c648901620440c03418038904140c154000100982402419440d407011010561002545d00300709514004814a40c82030f0394239100c0030708580710240e86204a01041544000048051041c107801342d142000d6070b10385941d500d880302d03202da80380110a02020603854110000000c0da031078010300303131308410181c20008120007646044815220254040840240540e151001907604000310b1600d00409503021780c0d55031070754601500c054521043c80303a04061030008110070050a004180190b034250b86c1118650031308644c0560580c0c00840e105d071100e40200c051922074860050080104500c02000458064411070106100d41c0100400303485002004400da1700317604000180c5815803442004881d250a099400a025040c010308001c25036a030006012100740d00c03950026010b80001403291107080da0307826202c4c0d500e0b0018522128400d908081c009036221980c070582c004000410b0001e810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 220927059 1250 220925809 220925827
    0x80f0c090703051306060b0a090801060b0f0d020706090507090e01090c0b0901110615180403020307151401060807110f0705040f18211803060b030109050f0105010503010b15 76
    0xa40005040015071000000702e1344005402405940c02601036405000d484041030b180c000c1001d44668885042a490114140000f05030041140d50742c056103909281d85001c50a0940024070403520040d18039071920a0000402001003000c404681c011b00d4240407007040425440d00726007803044010404400c102040108280c002c01030008624141000d640d1403100c0da03962410a08100c51502c11690484900421403a00583c0b44502a100e00301c11100e0b4a89550041c5d580e125400740a40745100c040070048546070a50007414044600303011035103280d655480042c24884095a94502040302c9040c0c032660141d00081180c03210482c00d000b04038003490035044c040107055401c0039002c52511150f0700296031012500c0a01484d00c078601d07494607a0031070601c0030655443ea59012003003002e511862482120345459074030540790450030000d56500e080c400280140382104d4010050300075407120032025041940418102c2e6011b500a1040c2c640c69020801100ca440c2514406901d040c801010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 220928309 1250 220927059 220927061
    0xe030405100e041d0708030f180303040305030a03022104050a03030203090304091d0114010807060f0c05061e0a0c021906140a050109110702130905010209130501080f0c090703 77
    0x81014072034100b00340300105000125080c4e403c00e03c80c01114140d46030b11001030207001c104840c01000301c2c0018504007203070030040450748d20812669400d01c0703030240304070216940c0c02c0c41268011580300c412070755100c10446c0040c020750000c03843c0303800d10303015401e110244400643c4c00318441c5034000042c18201010b65010760082d00003801840c0144000c4c44013080101d9540300f1030244109856001e4040c01c0002c89031800e503001c02c031407290b2440a24004001d10600000e51310251100d90803d11203a506248048803001000790002c2c02911a5a0610003045c2210140184d000340c0040c800006a4901034080241e80b8282403080041c0d1180c0014000360081d101901e203494403804001c12100c600b042e000e5044241512041001750f5100010045040544100c03402e59000c0d0312507a04026540e00002c01149030101d803401a580c60b105080300b041402c7d81221400c4900900d022903a40750b506003840100b409000d1070a29110303c4491031a00d0307000003055440079000501c1e1011603074503900120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 220929559 1250 220928309 220928329
    0x50606101d190b070b0a05060a03020a060e040f060b03061806031e101e0513170a210b0414060a0b1605120904140106020303160c210807030e030405 65
    0x16a41581c1c140c008104480f5000082c0003050260101d10300c1c904143c17626074120b840140c101c1c0e21443c002c3c202040140c5503800c20b40304403125410807034007210320103000c5805030513025000701c88185050310104642140d0400340d0701503803081c0c0c2c5881c100c0c2000d4092000d009800d44000fa41680840c1c550b400301c4240d8034180803030250360403d8440b88914560707940d05403001055031800300309940014000f0559036218840d0710003400f03407082d40b04012640b07460341100f07012140024030701e41c0080c0303036860540251001c80d044100038144402610303251000340c1c018011414090300c902e04101e11070010001e460841c60145070010250700c2d14520300b8444980a50007000340c200c030a14110100c2d000b04800f400582c00840f141c000b21551804101c041004803505100e201960411140061118541c000252a0b00a1a281684010000d1f44000782c458514142c3c0041c203160302c40f2001100000c10640849080c001e40d180d1034819200c0361f0f000d0702902c00c5480101d400f40d0051004010504d48007481c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 220930809 1250 220929559 220929589
    0x809030412020a12081e03060d0201051b0601080c030f2d0709110409230411030a05060c04060215010b09090a06092a030908190908060103050606101d 66
    0x1280c0201d513141c0e00301c3d0010351040e50a032036294003c180b5650002406082d46015401c04112919529000e4001480b80c01140070280c1000004180f070f100455030318400c4040d03940010b044800301d60b950400c1d5030b600c207017a003065400380c0203407c0f8000d032603076000500040e042484402d000e80745038440c003401c1c016000000e10401c24461103d00040700005031040e05000c1e05842041543c2d681410600000e40d180441050701d40354442d0000700c4002d010b10340749600103074803500340403001030914001b0749828130401010705a0300504081c844000d9030032008000320b54154081d10181400801034008400c030910820f00b810750204004011031a180040703aa200d8081c060000d42651200f55080803120391004142d0810320b2200e841d1448000807102c02e20001c0c0c50316003407041403903a0762108247e0192540c0c48916441c15040c6450450203007061002420900302160b250b98de4a0500a0f603520040e59064000c2046003040f581441c072804440c09401c0307401360b00d5403010550f4014411090580410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 220932059 1250 220930809 220930819
    0xc080703021f06061805010219080f0c0a060c030c020604060f020f0a02030d0e010501050a0e0a020712200610031103011d010b0a09050f0403050d0f1812080903041202 73
    0x412034000d0007000c80c400b41501c80c100c00081060400700080d1000b800c8030792008013900f4540c0c0822281e80d00091407804220581d905000049903031902000c40d000f0000c0910381020042503000e00702d58001103010885000e00710a21000d541c2c06c5050301100d21858880005801c41d500103004241030790040c2ca00d80d20b200308018649461030048410b1030b040f5410401c010303000022124642c0005010302071807009100000c000325450240007a501401a211341c200b074082290000311081c00c554180d0325004d801035565944601000001440014400c00b601d20600ba00e030320101c909400000c5142c42609030b0740f42c3c601110b04544814081005010603c0d0b815034031418a0000300044802c000c1c05402504004a001e05d6560b080141481c07080c0c008600e414549020010803002130321400d82c1050705420110354480540004001502d0b40944401c40c1078107189120100c40c00d10900c1c030342c4590080c040780b4005800107c0880d01d00c1402e449845403540140802e1200b0951080c0e000c410341c1c80189 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 220933309 1250 220932059 220932073
    0x1050307110618160e150109050a06032009030a020f0f0a1514071707020a031e060e0d020601031101051201090c0906050406090b0a030905060f04050c100c08070302 72
    0x400390303140000c200e8603038900c10342c203900e80b060000c000c1080d0031905190700c003000552030410b50184441c00380106501b0482d0f070f81802c2c9018590280a034900130f03003000b030200403e81e40c07984409070103051400d880300300e0003842403001e8280942480c10303694030b420020f000e01002c130b000350200426400d44140c51903000c0a60400d4586603542e0898484c01007040492a00c40201d8510001e8010201407520309000541044044001030b040c0300e19140c007084540c4001d0700c41d4694004548940c000360801401c10480500314000d41c078581c0e118001e403903c00e1130f043c0401000f552030b80f074030384404103241400f60340100300600c0010001c124030841d003541850114207040394110150a140d03002e9004c8a1400e0787e81c0710107040709130f200900d1000b5002a040580c606071802800810140507031140c102e805d2004500b03207030301c01d129412103502e86400c041202e05d14146407001d040351902c20b4030115000d00c1070702464113941c14074003d071800102c0c1079264051301191585943c40a540103502c11001c502600c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 220934559 1250 220933309 220933337
    0xf0607021002030a02091f02010f090c23090106051806070201080a05071103071506050619030b041806050910050115030b19030b0103050d0314060607060902060c0318040e060601050307 81
    0x6d844601d01c0406111180047d4814060b0841d1080380c0d8034011907040a40ca0404a8882d54800d01100c035050982c0b1141602383d02d064660f02c403c180203a07030004501c00000b481591200151602ca4003035003070300c01d952045c0d01c10449144170352070b0020b0200d1011400681caa41c50799201c59401041800c04604801c030010250703003140c0c40044100e4600c1c000b81e207809441544c0f0300c681005858196a101d103058010100400c5070452820780c20109500c42174a2030094450340c22031504484150f85884c10385020b46044401b41c82c00711203c0c0d42174852445180c0504840780a1a8100c403807411086071f036a031140c0d0040340588140014550480a0310003a10300d0308000804820041d8020306a2100725411403401d036061900d4050f140c4c00301410a9604406806091011504490121600c41d6a00078610780400509580c2f000a54017403408a4600d500e504c0c0400103020480d8070481c181216010b01c410030080314002c10301020658894000a003030b550003000190b81281c010300b09096540012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 220935809 1250 220934559 220934569
    0xf02030c120c0403050604140f031306110106150f02010b1215010e0603030423040c0206090115030503090d03140d021b011404032613050f0607021002030a0209 70
    0x103581200100c000062524072004650301d0036a0030070021041549050b02d55166540e40c0c40024001401142d00800e190011803400c1040d00d070745100307660559403140d14880c40902850760610405d40410040c03003003041e0080046c8a11300c01d0300c2d40e04803c050350010100301260504d13000700c8884150341d1b80b407040907650307541c0545201d850010341e8020011041441400100c46206a01c92041c40044e80e00303008043d6400301c16a0262880002403502d12041d003205007500703019008449402902d440000d20285502203440751080c1100d900038404600c1070381e500700200c1e50901c400741a507003082c07010003624a0b043c000d11009500910b00000850001a1005030f60b92014100200d103942c0040d440814050701c40c0002d808000250081010040c01c0110b4008910b000300010200480c401c2c00c520344015071140c0900c11000e5080c409554540410440da004040200560b41440760780300c1508030f02c078006441ea2041d070003640501040d50a145134000079400c05802c02a000340c0070702605006840d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 220937059 1250 220935809 220935811
    0x30a080c0709020f041e1404020d060b03090610050f0114030c040512030d060e04051005040618050f060112030219060603060c05180301020a0504050607020613030804150e09010b07060f0203 83
    0xc000d454645d01c9280032408030007032104d20710024980c04a43c608201c00380d00c0c400720104030f000c241c0e80540e40c0c0f07402441034001013110340c2054052010110600c035641d000003400314400c10180c0c001c645900c0d161403c10020071070350114640010140040f408484d5000000303150003c510030105800c0c40cad2540009174180515000c204045d90001c0780c40c1d9050600c034081d08009040c82e01c40601907007401c0e2a45074480341c110300507140300c2e500d07079000c0b408005040c0d200203048119204441d5042c0c1c414a00301d611241591100c0c3c150348070f0303000045004c0401e4003075444015859002880c02010b441d107010b10140002600342c4e9480e5545e180000480c2183c014220400010356030300d6510010480c0100840601c099501d00a030303c180310044856070008102d40c00e980301180c0745905c800442c40080d0051242000f450701c1c0409203400002080071031030280c4152149002d414660101440c02103800100500d0403a511074a200010484036211400a04005015100100340310031386da61003c05a0380 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 220938309 1250 220937059 220937077
    0x9020d0b07020c090402010e0d0c03061e140c072303030a02040509100f0909020d060204060224061503040f1a070e03010509061f08010513020108090c030a080c070902 73
    0x1800410010229410f002a144a0b002140e118480782803503000203100c0c0803a601c685010360010141041840a06140c0d40000d641c004414001c081c00203502039100c1c040d00d000940484c1c1082802c0450381c0c3c81c098028411307410108485c1c1080c059444140030024190200f0a0b41d441600e039200f0058010b100840c8600e490a03005070303441e80347c0810321210b0701c0004d05110b180c02e0b55860500c20300041d1075031001100d00051012904081c04d00000300540303011403000304550700c00140060780301d40100319084010805404103001c0c1d031008107060620003048a4565003c0b00402544040c07040d4940a190402d00603401503640135226500d000309034100001c0c0c51907002c081020007a141c2d500880c2e5006100c4241d000f48160b00f000480c4c15551280034000c06070b0104220844851003180c0540f0b1002451558028480c604140a803040e004c264810180d0001d102c2200290300c0304000905408a40c2d4041c004012980b050344402d1410b800c0b180c02e124450160b40c50001301500c0500103082800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 220939559 1250 220938309 220938323
    0x3040803160203070b0a0c020f0a260c060406020d0b030102030f1f1a0c011506080406050a050403020604030f0203090312130f12081c0c0e040506040513110409020d 72
    0x420301c0d02401079500c03910100041194010002d00c40000ca0502140d070700014411004240c03c040500181c0c00d040d5540e0003000307a48142c018040901004500c40c0280d60104d8602c00c800101c0c2da0950a81446600030030f0341d041d0720690110340058410307401400c0c441ba0101000820080c00e50019082e0790060b41e00c2500700020710b0500c11030140600e04540404002e287d500301c901d16100700c44d44011150f02045020001c042200100f883c0290031140f200702c030b11108100d90684483d009008490296001d0f42d81e149080001820300c0344a00c196030242da010b40050000341e4659a003200c050720f202d41007078114042404010300c5624200074100e007951030140079a403929012490b144e50042950f0042c05643c400d070004029029480c11001881600b220943c0d41e11012840b44403c5400c0040030071040a2520f810200100e501514040c0303942402c560500142d00c0c1d410402c4155041640c1d49146402c448441400044175034405500c3c0a901810101d41c2c001030360009080c440701031506032209 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 220940809 1250 220939559 220939561
    0xf080d06091d06090a0308041a0c0c0607050f04090f11130e13120809010213090209040c0905010905060c010603080c010b030f120a05031801060810060f0e13021503040803 75
    0x2c11694401c01010503030000145410314105046994a003075801c0c000d81481260340c08101481000202031707001c41c9400d5011000b60812501c00d07205503202221844481c002c0e0004110282d10640807500c040d048603030420306103802c0112501c001c001044001c80410b90f5089449081c5070118043d06801e5940c569912229240c00314910072a00000d103406031001c03070b03c5035040004003c0010081c503071a252030081d0069581d80342c078a00a206501003454100003000d0300048086468004010203c030030788007440181071941007540d551780a401254007040e2074078402d01546c10101c028051010f070140012030b20315604c0d00c1e204003550200c450816540d4682300d14000d075040410070a03980c500310000030070400340108440c0d8075501500ea034040810070000b0108624074074940088400c110340390000c11015a076121115a105546210a440700342440c4001401340c004081542c1120886044040d2507500c41540625031082c2c47d100301e0344444410403404c03590714100d024501c55442411003a07a6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 220942059 1250 220940809 220940831
    0x711010f0b0a060e03191e0b0601120e0c100c171b07140d020f041b090f14151204031d061c0902010e060c070e0c030709030f080d0609 59
    0x4001070b140c02150a22403a80b00e18203044d2800101602801100e0142928052082c40c09055448602075036904000c0854a004148401d111146000704000d80b50000d40b1000d01c0d85010944d0540103010005800415608285080c5869040342d2041079140402c1d01c90981e0361a5250001d001031a121207910100300001c0703150720000c19844440032003004003211443d0400e07054280385000e0440380207900c0c3c020550219125200c4903038001c0e100030424003408600c41800c03154880038001040000b00c0c0044001b1f40a9120b0000d88241c503000328014020a5854052241080c8070340d807842d4039420200100300e440046990224001c91280e82e40445a604841c0d000c221403400742c615501c601010003000201c1d144641c503003403844c540340702e001c512603105000503103090424001d0b1540045000540000504000c03840301d040d1440d880300d000c40d6440d21043e1202d140012169100030508000c014008aa180307200711084621816002e40350480d0030005105555050f131118880f96202c40d65156 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 220943309 1250 220942059 220942069
    0x2d0809010b040e070b070204021207080a0c03051506070c0b0307020307030207060302181201060509011214070b07020112060906062012041404020903030310030308010806100306050711010f0b 84
    0x50036070021207090001c402440c100c44d4980140d8070510894280c0003038020219113458040c1c40801e00000801c9440c0c0c5001d210141004104840708910300d40b03048a030b403035154020b10605029824140114403880518418880b040d4403690081c0c41c512100080014130605490086206215680c05940c4540075440d01a01e00003403a000b003000d060050241468060f0015228080c10400301c407141580c10b84007140600401d101d41207035802c00c000c2c1c00003191081001ca403100d0414400c0100b1032002140d66805030b2a40218090310740c0c403030300402424000d507100d1a00c02e6011480d081d40043e0710390744e420441e02280c446c1d83c4448041940c1004811401419034200d1181c460070502400303015047c004901000e01c40c502401a000c2300807078805002da183c95054414540c00039084981e070381002d54080501001503c030450005180b400081901c89021414600a0260070400780b0002e041d540c0d07007005000024100810420f098901209911090090f2622110020340004034412080c003400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 220944559 1250 220943309 220943321
    0xb15150a0f020709050f0601031107050109060c1107050a0515210f01150906030c090f030c030b090f030f070f02090414160b0d050714030109020a08070305040b072d080901 75
    0xb22884c4e142c0f1082140c40400e2a03000c030303808042440c000804001f0307400c0c80007440c05410b2002c2c0a0358a0103040b202004a10f902c50954405640c682054014011511329595041c0d40070f0280c000410031f008101d10f007030401610b0004514403240b68280f0030142440d5400c084401003004c2100c0c1044244a140081c4201e000e01528400407102c41c04c0c0c3c40c4d80806005150a84681c0c0105540e4030200c0311801c0c8102c507403101503c01100c0010045540341003103462800320780030513030340c7e040d06801244513004006001d04504154001460400240d15000b130080d0300b203818241c0356401c3e218401001a40c8046140340300300d2140d09541c0c40201070111442ca0403040c1500208418210003045c08040511406c1d142c1f0000d45d103501162558a01c1c800b220b80803c0303524000402c000100000c254a1440c0d0017408102159603a12643c981c0c2d181e00440540f44281c4010b071480449001042c03c851140500000703a01395800400c80004104d4513401c0450f524142d06400600d01da01400346007442030183c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 220945809 1250 220944559 220944569
    0x906040b060406080604110a17100e01060503070e130210080f060405070207090504050f1c0305090706090b07020a0510030c021b0108011502100204060c1e0b15150a0f0207 75
    0x800c03c103810b240000313175900c001810141038500c407014298559994074496901500702600c4c0c010200c0d01442c807840da80c0300141d00040c1c106080420b85a010030741489410200e4034004e0003004c04518001c40b078641d900d80075222800741c0080c2d24008001d81c0303070141c0c1c421703a8410560f54500513160561f040d4010003805451644200d081c8402d00007010b0b80020800140e644000000801c0e40f80e5203000da00d002d1242081c0f00f01e41c02071000d10802c0d41d40052002e81c41c0e9045840520156640c0300c02c0a031500268056000401d1003900248401000d11014013005072019104103030694035040014500036802c0d040400003910703441e003c400d20341d061040041e680c500428a40550302d40e0000644103000501078001280c040d9004841018420040da5121400088045540da03484600051140740244c0c426101e02074521304002050041c9034688100540022180901d6211292880b1002040307403c460790200c5200300504800440b4001401d04143c55258a455200e280c032001e410aa42d5501c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 220947059 1250 220945809 220945811
    0x403030209191809020906060d15031209170a08071103010f02090a05040902030337080a050606091e01200105070305060312070f14100e01060b0c03040521060906040b0604 75
    0x55034011b131551058150001d108642076503d1705240c4816900411400301e500c903803150180c60020070f005000940e0f1101c0c8026985100401d034884451520303004030325403254403550105510f035010501403030160070301130b00c520a1150b0a200540019082d100035415000e4221303070008615800d45001e0000000038a01030310180100c41d00e41e00020346a00601010b4081c000c41d580d03003010180d203907108107002614a50219501e00340050f41c010520a41190130302103242c68134000c036920b454180107072170100600a101d00e00380b5a50181118403c0b08408441c0c1c1440a20a107020b0b408442140785a00801c1d09000060a0b20780303010b0050554101400c0e41e4029042110070300c11140102c021241c2e4a6001a400f00082401c0c0c90f01d450b21045242400b20a0300074a0101c03940069160841100c80340504002e0101d030b034646000000c1485240e441c42ca2981c01040b0400203400d1442103038001650500c02081c0c4091402c0009040100898005c901500008108010000300c0c191680d00983c080c1e030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 220948309 1250 220947059 220947071
    0x90606010e1801051c0c0e06010210111b1006090b15030106050313020307171c09122301060608041b0e010b07110604061809111204030302091918 64
    0x500b150524074107005650040c10750142104618440116448a8a610000241e0129640c03c1000c44000059130818010702840700601b08a40e402d01540801c940030715044c03460540f100c682d404a420a200710b11450303008900445d11220401d02c90b0600901d41044007281c0b0042d007104028030316003503c030304024a00d01800140034640e880b40c00d03a9030105526070420400600c500021b854508164070200b0f60586070200d41c02d41c400b001c40d40c0400f40751055030041220299803000d442e48000d90180c1500c0614003011100800c911088840d08820340d030100655005107840803900b0b4802c00e800180104030f10034244010404096501d4440c054203500b00c20086080120440500e01c06118103182d15202003070b103c0a00040f501808601c56004106541e0703030703a5409018201400300340d1b40c40d000300c0e07e4060006054000380107032a0490140041c0500d001418500c3d081d2066000e04203800709942170000d0200c2d5101c1035081c441031000000305203a6580380907002840c2d080310000011801d400e01c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 220949559 1250 220948309 220948339
    0x91f0509030415050706020d0609050601020606090a0b0103090b04080c0607050a0207060f05160506090c03010504020307062001020a0503160c02030a0308060609060f03040210050a0e0f0612090606010e 88
    0x301c103036000d542040d200c00d000c5a40b154804c48040c0226080503002c0d034030020306140301c2d0a860f40a0011511002400d22066481200590700c81004544064100200e44002402e40b01158014004110f05040c00035440516445514010780101d404640440e4001600c125014040082075030084161034071a18002c0e20b00c50003901d40013644141410300c048005c5886a041c025400d403840c4442d0541c1d81d08110505080440d40e40400340c42950083c01506414407150406001c1e01d8851a00940103000052900070100c4000c50700c602080401d82441c40c2e00101101c003800104402442641c446032a41004080443c1a01e80d043d40034081c40014030004006860100b401800305826080c144031a40d44d0002017511803007a82440d940c8500000303407402035440102d001d5401103000740d42140b20340369140740a0341c145c46040954800300e599a401403507035280824052800c003034080d01840c10202080c1031002c500c80f041e6520004c6802503c10441196400740440c260318404035860b89074803400d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 220950809 1250 220949559 220949563
    0x90f0606051207031203060e070201060e010b040605070209060d0b090a03020d05270f04020f0705070614030c03090c0a120314190507061d030706060e040b01121406091f0509 76
    0xd813000412a0201d01d500c0c0340103e00990000300200024102c10015181c0040001d000304001c4c001d401560460b0400405c240c402981924156881603d44510301441e81d02085085038000f0413480c0c3c800a5900703900000380b12003001c1401030055000504c80d5808600c1d020b4103000c00b0400310390800c041840750324050014101d0311045030428011b08240c8525030408501102200408540c008c1e000103a24030081d19100e0061a0140c00b031000e603240540c80e045c003116151004030807400c0c52041440401c160460b18030040d9000b001e410101c1d0504c0c1000004120303040803660101d1000380c7d800c5c401c07109054000d082c4091800e03005001034642450044800d5030301c558004100b0801ca03001c2a40e4040203c958046891b241e0b1030709460310350440c441070303c0c2d0356a8401c0b00102c07902400c0000c0020600016400d132402507074840b4014840341e0034a1110349400040b41001c0d1420303650a954458650340c1800141d00500c688405040c80c1d50718030103c1390365000c100600a195600d4201003124403a40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 220952059 1250 220950809 220950823
    0x5010c0503130308041703090d230f030a090c030c03050d1403010909030203090415061b0203030405010302180d0605090c0604030b150d05010501060903020a0603050f0a050613090f06060512 83
    0x41800c064090b9151703400c10300082c03a1320b1142c260b50388034000305110000800042001e00203070305a403404900d9141c41001081020504003041210409000341440006072002850f03202012180c0092120000e8488040d00c15840c0d00a0368034100e621414001d1100070710030103204403210b080280052186040e00506440144152106d041c1e548000c081018804e100b112003260004006200d8006040080b80d035014607403246e20301180680740c0c03103001043d1050381030243c0fa030014051400e0500c0d00303005401950040c11242403116900000d111035960b404a01c1e601036016a030005101e241c4802001d00e0aa100984540f0523a001e01003003001a180c41c0801d079002d1551440182c9215081d004074400f002607940007051035007080004903505510034580c030b045a00032100c004900d583c40341c06a007101e00540e83c1c01200503449000903411301c5c21303410054200f403002d0a103003406061501c4844c101d443c4002c00700c0303951110701c10310b00600440b80174410191800f21603038603000b450009001d594841d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 220953309 1250 220952059 220952063
    0x3080105040f020702150a230d0c140a020a020102011505060301050d03110607020f0709021c05040311030412020405150901090b0303070b150109060e03190507120f05010c050313 78
    0x24580301c031980b9107010743e0140ca00140d4042c04801d8180501c20013018242c020041a80000f070f0800302c000300008000307800b800701c130000c03940151a0060b104034200c040d001d4001c20ba0240000842e581e8008a081401890b510707180b5400f50032220700720b200090954540c0e00740340c801a0040c6c03005120b5641d40d20100ca0444804882403d080106490192074005421136142241e018180400c02d0650300402c200c0016520403041e07a5645844007159012400340028040344242480c03c03440b41c0c111141d000541241c024100a00d02c1c00d2500c00c0701d481c551282e00009580001030340c0030000c41c00c1c140200390300a0008060b0760301d40c016203000306c0c5a41a05100f26200d80f0b840d652860710301e031000c0c0f0450b0740307642d085000303000f00d443c00c0740d03c0244404841c0052070000320091000078400e44038000fa00d90404004000d803281101501c07101503802e04516040d2a00d010700360000500d2400c0754496100300e44240c015501c0c940850400c14215001103070307448107012041003040342c140300d402d034080342040d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 220954559 1250 220953309 220953311
    0x10f05090a060b0304210f08040221160906080c01020d050a0909020d020919060e130e01020a020c0a0b0408070902160501060e09010c02210c251703070308010504 71
    0x580c4a10262028001e50f50009084600000510062151400341851903d402c4a204800e1500c00398003125528004600312000072402d0000c600145007400c00c400545140c40310028903c540f080c0c1c450308100d0700c0805d042032200025410005a4050700980e4010300114011300310240d5020b001079251004000c4030405c110b07000940c08130150080003480046c0181b89021034035018003070700e040000d42c00301c089030f4498001909429914144880e84c070050f03a049644061344055900203201c810340f0400388110500b074560040c448800c1d42480034020840e0f903603004054406040d024800c25001c1c5400011000c80c00308024401d500740041e40c0411035002000041c0d48217034103168085242d1034908000c11a50900c000003840c1b070100c2d100345004a180b04001c11200801a806a036100c000d4104140002c01800c044040f910071000540f0705040004150351590340d108607140d044034520780c128200e0740c01c0c0c80030602003500c40541c070300b10040d4001c00a62402c07481c2e480240c100c202c14441c0a10039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 220955809 1250 220954559 220954561
    0x905100c0518031c0e130c0903020901050f0d030e04020706021206091f0506070c080d020604020a0b040e0112143f09040b030c0d0b090d02010212040809180a051905010f0509 76
    0x1d0384551902c103501c03400e0401b04002d026884000241070590a2200764410490400044bc003854283c0500382c64183c001c11017000101c550f135050700c5181c8405000e80c2e0181d030031b109000114280c1d00040c030703040e40c03030f49401069454507208102010704050401401304032200000940250a0044c200035118112200340d2950414a040c0b0503811154001c090540180c242207001143c0009200740281e10031115000d4040d04c0708403002150140e4854101c00032280c1004002d400c1000200c2010700780138001c2811071102103141300d4a007580c0f42c0f0a004141d0f9018000c3c03010b2408801140604404611119500d14002d150a51581c010044c02d01d00c20f5590740d10300961640d04000031507800c0b00141c46200030000c1402c007a0f0281c0340840e200003603405203d0684103c144188201e40210b0301001c070458140e11aa26111655000024001d42000703d4407000c1240c0c40400198074400d103900c003408503842c9004d06089075240160070006600c281400018024038441401030303c02ea50040d902c040d6a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 220957059 1250 220955809 220955837
    0x304030516021306090f0b03030f0f07061d030a0f050909010302130e010c020102040518010803120a020d060b09031b01050f0c0c0a060309140c010e040905100c0518031c 74
    0x140820340070090302032804500241e05c100715080504114203c81c010001390586100b81520307889080c51070a0942410400c1d1817844404101a025041c0104030000303c0c16100b088220390032540a442d041c080d440411003091703144d404144034421380315924040b42403280910215214400c10f010080c0304400e00580120310100551203100ea00c400280240085c0c00a100003038001d5100d4021507000d01d4441445002c901c000f00742c4981201c0c8808019880c259028024002081014103a003540035000c0111140c890468018040680031240d4500d98450745e031001c0500c4c0c205e21804c0c205d4114030562441d002d030381e00b100c199840c862290624598800220280906100500f0042c41d800191044081101613250340201230030341c450490341d02c03640c003007008069403880c00d20400c500080d0148030b80600c508107600709082d954401d50454000c00b00040e00c1405640e030f01c1c03030380300c0c0042d601046804500f45006103401085400360041c107004000100c1442c000020601d060041c0240740300c00c107134 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 220958309 1250 220957059 220957069
    0xe030a0806040905010903030606110a080d0b0a08010203190b120c1002190507080114011410120207140706030c080c28020f0c0f210106050612040b0903030403051602 73
    0x51180e104000f00146d0030940b40180061402d030040320005030080e41440000c040014004075640d8000340c00d281817486583d060000703000000a1a034000340845400211b110b42400030f1401004001d02256082d51000354a10841b0329541207223202d02102d82109611042c0401c003401c0d80d9405558401007401507850991404511040d262161100241100140038012039044103681d40f04e80203201025169000c81c020210a01803400741c8000400d001c07160b4170b4259510004a11641850081c050185080f10101c1c0c210720000d6494822250045102e08003d003c3d040117480d40d410100096004540e001b00a10b1000301002001403000416500e030b10404420b050707a0280c1c0489407030390500340c0d01e402511220640d81d04141c501c01c1010b018000c3c501452200c6210750064010108214a000c40e40c820601c40b0000885555807414082038549482005150081c031072240f00e003c505091505504c240310003003141200b500306000340000a544042192960360074002c030443ca19620340001a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 220959559 1250 220958309 220958321
    0xa0507060902150a0518030a03020706050d1e0e010606020714040b04020c0601060c050601150c06020d0605120a0b06030d1e090806040b0609090d022104090606021c030e030a080604 79
    0x32800083c040342804006610100406600c500c03008000000080001415503400d0007220007005a0070152040c0091481407000c1c200e854080140803c0045440b000841040d04803070f542c10320b076901d0355001160940d090141c84020210b501c02401351503c0c006d07038900d034070100c4d440b1184116180c0940ba01c85568980685000580e0001034815a50359480060048030800100f1071f214043c1c6000002e95174000c1ca4100c0b45a050b27a00c0c2c4500b2010706640303000003503000c0040c000080740c0e11030700498103032a0b102400401c581ea5100500300005a403c11030800d01c001404240301c0e61051060030b001c0ca60040015100c021203625003400504421401c0c0da8002c0d994000807841d206140800050003c4070b031f05c25000350001d9529148688803489600e403a018a180300034090390290500da5001080b904844024900a81c0180e0902d034445c80c10405940999002c00010781c443c410461540c1e8100020101e40a0389080400072029501c0c84280c07640a0501c6007000d00544000180716611150818 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 220960809 1250 220959559 220959589
    0x5090306070207050901090506060703030f15151205010b04050607050304031b0f12021f110a0503130806101202010306120501090c06020c0108011214071d06060a0507060902 76
    0x500d031a0300d050400299100d076a4441d071407051401c10b00004401c45144a40350088a003d82618600601d40e00e09030080d040203408290740603a124010b079008910240454040c01c0848005a00c0245e85800240080d03680050a52030900e88401008440b0200c01104c0c00c841050707401f5a10741066051a6085000c0c2e6030018080a0051a044003141c108804420560340300e0000c41d5078071074030b44214404540a41400075000300030200e070300c00007079011625460001110310b0444c0c460200c40c1e01e0141050803400b02180c4560002c9181c403202101c4200007005480c0400c003d10440c907042c04441441a0248124034207900201c08400669111381c00590142c240507464031525110f903e0420b0080001c0203080c1c4074800c03400b5001c1f5410f403010a035040c09100c141d4600c101e9900b000400c003502d040f1104100c41101844181c024a00c0090040c4002000d82c0d100c042540b00d440c07400248940c4004210703d1154400f00701c0005542c0d017004c1542c0182c3d40203540022403001e54030101e907c0410391515 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 220962059 1250 220960809 220960813
    0x14030f0318070f2d230915220f05090f01060501030b01090e061f0503070206010b040608040308070e032e020301080312070e090f0411120309010f050903 67
    0x3004550044822a5002244000200e9041d20707962420b02000d903180e8011482d00c001820407101c0c1c45a0101c4441807100d241052140c00b81e0382e81c0940d4201403541c2c2d14009a905c10f103002e09031040c07034002000c030350051029809228101780792002400303c0c2c1441c0344410000c42c103180c94141e030304a158842c6464030645c00d800c02440c106402015540d03150300240e80040e41c02c190001c0f90700d502c02c0c002c0c01700c0c00506071580d44041c0d01304014000000002801140c10490240d01007410500050518900c040e0304c5e29070741e030b9a003010744000b810804141c0203e074072044200000c002032a1301110441e440b94041c0b4080801d1740310244104c441041101c0f0450340361003001c07410901d0aa16103612011070a1000e000700c070741d070380c0d8402101c03d03400244a00c0c04550400d011030b00040361001c4003e64002c040385401c145117869000020041c001c250303040f0a40d810a20104801c01150354403455080408842c460302d00c820002c0700a42c0c0740700c1c23255010b0400005040100080d8081c4058070001c2d031006003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 220963309 1250 220962059 220962061
    0x150504051e03010509010b1e030f030a05070b070804050307060203040614040b070e011b02060a02120c0318031614011209060b091f0905180a0b04030807020708070314030f03 76
    0x80741c1c03081c1c850342540d4440d500e0600494040c00741482010329070070b00981020301900c0b105815010111120301c1c40f43e05400ba200c0c084086a505000400c0c0210103616600c1d25081d0505042d0000030006000e0410b010703a240900020600010681e5a0349500c20009603032541d80b4501180a80320703c4484255484421003440200301c0d00700c0c411880307020544e071003044d10808a801110306202c104c1d01080d04213003015281c0702504101000380201d880723a00440b036044014002000e21a802220b0f01c401030340020a40d80100040d00417481d9091034114020503203120301003610136250380075110b01002d042c0444c2a10205074040c2c0f10381c44840104003800c0083c030007581007000240c40c141c8032a43c8214020000a00841884615000a8040d45401940040c249070301c81d0000c02c805440000b0350f00c42e00340f14054860040107c203040300d1017100c0000d013504083c41c1c00b1307000d08000340c1404c007550455002880a1140041d1900481e50440101000740080c0da0394a41035205408030303d80c1451b4000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 220964559 1250 220963309 220963339
    0x8030a140313020447041d0a08040501030b0402040e0f06010e030a0f0b0603151f030213020703020610051c060902040207050d0e0603040b061e0604120201091e15050405 74
    0x5403207510004c0c0342c580c6440030004180081e0a204414158417440032031503042003945050907444901d03556410420300c00b0b504003061043d4038298030340908480c24a00054103000c10b590502900454030b00c2900d040d803e09041008a0442d844001c1540b00e100c90400000341036a0310a001c50200c00f10040c0c192000784000d82000000c08522070015138210781d440d000b1a0b202e0500084840341c4c0d411883c44e1800e03985407020300081600700c25548113140d04508001001503501d82d403003022046085080103036a80a189406828100300a040d2110190449801c0110b0b0726007002c000f0700342a1a0180a10b43d1030b0034941140200680300c0d029412a00c0401ca1200f00100054a92000d2209880340100355075480100907441c40116401000c0c01c01b408085207113814460f9401c404125603650012020540c00c4c0403d4a58009500422a00d60217500d00815560000340e20809840c82e07000c541c009003040881401940801d104010f00c400014004038011842103049d01c01030070000b040006a40d90b04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 220965809 1250 220964559 220964591
    0x1814011815090306110309060403111203010e1618090b01050d0f05011d040f0b0711060703023004080304030519022406300708010e0708030a1403130204 67
    0x5000441d140e602e001c24000303a140e080d5007601c7c400c5002d00001c20203950f5655044480d941159002c0c03a061240034400c181500030000510f02034202400344950390300d8241c0e81d082000d070f43d004040c010700a030a04a0081c1142448101c02520081400455450400c4004071054860380d00c40f44000707458003c849240c0101c50b0015412280500180e18400e48000803d403540041950020407410000c6034090000300d4003c801c561080c00c42c01c1480074461661051030800c101203502400207640024040e000120b04040850302484408100c40603030702c0c2c0c4071403509050000e00701901d2002c1c084005810144500101d0703401d0034504039038aa17450301d09040039640da03254440d00710407050245465280c1344095864644501c1b001890900700319010600c0b54940c5015914440c001035804007500786030801004410000c1001c003000013a104801d401303081c1070440c070781c12443d2240c008100d820b007220b51007004980c000706a51103003540ca0300c42e0352070307010300c6940e601c0025000750600811041c3c10281c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 220967059 1250 220965809 220965827
    0x7031505150904020414030d0212120402010302160b0703050c0c071806180203090c01030209130c021e07081e070605030a1506050d060b090a03030e0607020d0804061814011815 77
    0x105804440c170080c4184d070305985403041d800e500c0e817402c1d4ac144211400b000c0760700402504a070060600501d0f00b04102e0030034509030802402543c0c001002c1040c8401e40d541032240c1ca44c0280d03560702d4141022040c400c800d841d50318600c204806141030214801e500100e40d8004401040c0d4006180082030800840c0c0010750812070342640107001d10460002c1d00c1d4040d00850301c10440045c208201603d42c0f070712400090a145100e08114490720024035103030b4826221001618040b60700074583e1900d4404054500003902d040d174601c003007140122249800d0300081d0081526803a05181c0d8803640c9618a54008002e4450800d08000040c1c00003d4080e0300a0700800c00c400c04100c0620045444203805561480340b0280580c020203540c90400200348284102401c00764000d2075546000c0f415000070380242c0481d00282e0320014002000c001e0140c0040d101060b20300c1e4560205012803800051014000403003030b180707061050012591130020040e5421070050803010305c0fa1210301c1c0007104028041c1c59 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 220968309 1250 220967059 220967099
    0x3220b030f070f03092414270a111c05010603080405030f0d050a0e0f0a03050319080106021e010e060709091406090103030309050307080304030314070315051509040204 74
    0x4041c01c1c3c44548a102c0d01a140015422080d00401002030005e8625060070f00d100d200c0402da500c025441c404c1c00c0454285004d59862250719218400da4044001c00343d072a00c00c02c00e0541e04c11680003002440c4059a1010100c00311040c60901810b0b000980b14210b54030b4004103994030b40240441040302420150042d50b800780c1c122500c0700504082c0c1d50752104400c00c1400421802c0c4400c005407131151542c003002c28030141c40c41c007092061002058280403ea001220300340c1010411440c0301c101d0713842a00401c4c40c06d00e00500f165142003000b03512101180515150001005d60b00840a202500b2144641200108540091411020081c1040316900440300d01c5428984a0f802c4000d42d4420280120401000e003c4a40d203165803d400030041402d04403901c0c00148006004601d07640051880303540241c40118030b01c421405aa940381000030080014186460b191790000c01c0e04066400c00d070b801c181c40c0c85144407a0391042030594080c4c1c031074203507015000140200e40746610719642c419280d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 220969559 1250 220968309 220968317
    0x203072010210e0c1305221712040c06170a0e0a0212060105030c0d110108220b2a04090b010c1e0b01051e0f0a05150702100e031002130906032405070203220b030f07 72
    0xe84481040b141437650f1880c081410000c48003040c2120003903400000801024421501d03010280d901069078058070b140c3c51001c43d001100100028102840014023004d002c841c105160140c50b501d1b502c2d8a1440a00b041c108014080010031035805c017205d1503100600001d01070010070083c5000e078510642201c80e400c40c03001200c1c0001c1d0f086d401e03221a08814018604090030039040c0081c441c000c119510f03885041103154044400410301405406070380307103007070f01049881c0c51070f0b030414403e0700006a0000d0300854080003d0751072125510145e421b88501119401542c00450000032072001440d04820360010030324407044d030240c510000508102e0320070303030743c1011a20f00b042064407240582d4020b1a0150042c0b00c0c030008a15890707005190b024444441d0801090b00c031803903802140c45d0394004580c50148100c00e00c3e1909251314240d2406282c0d07407028019407030040002920303400f981c020f03410341d0345112844003c0000c080d0041c00203003200c10300b003540300d00c0e15003d6103000102c01c1d9142000301d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 220970809 1250 220969559 220969583
    0x90b09190b180901230c0a0c0c090203072712030e0f03030d0905100905061603091509050f06010501020c12070509070203072010210e0c130522171204 66
    0x2014001070407a10546e000001c042c10051b0441098640c40c41c1c00200310398a0700d52001c0890341030180e201950040340c0b00c1d43d5401c003840001840202001d8000301c0031044048010040060060007000e40c5101585494081c1000d11004003040e0300b0380040c0340e95a03040c000401d441040c41c00e254000901e61340101d007154601d1400340c5031041141e0b4400c01c080d010340c00900c0000c48801c103918181c10100020700e0002001c0d0156215150240124000788031650745900c4400107000c010031414013401c0040d4050401949881c001070369900100082d5406511136002c01a0048002d0203d24000c2c04040e115031114640101c0c000d46070752103248210360f8036860314400c280080110072880060030001e88000c48944011b0001e888080042c40e1010031740b400c026161a2140d85400346124a110080007885034410328020003415001700301032407061500e0002000341d10303220040359840244000d035015044d441c0c2da003011580c0001a0400c800c501e800000c0400303821040d091541d2040c1e000e91030300584 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 220972059 1250 220970809 220970861
    0x303150b040b0301060516050601030b06090108030a2307060905011d0303070503060d14010e07180c0519050903060c091302070f111f0306090b09190b180901 69
    0x220302030390081460b040700500050082d213004000418401d41040b08001035041c40d03070344003883c1113001d800880302d54050b03c003405441d040c00e0307180b80e0140640348003440c10111007417402091064131a20035403e41c442c101c1c800e01034440c464211003102e60811802d20041d003060030424060604030b60a56102081d420622050000100a8a0080c2c2803540d5075031658407000c082041584100205865417281c1c9800840d02d01000d10400384c0000d049409007c0c2c0510b040110012110503622209195041c40600b030301080d0310404684501016001003800f003074285808407000c0c01103100181d058420345007840a0240820060980380c00202c4045605104020407070003a03000d078001c01852003208544010010390400341103400d00030090450140407410b12030602410302d00403404004a81c6d940d805006090182c00b42c4002828191983c44035070500040c01c0007241009010351a485541710a510a1707961088010b110a05039011014440d0030100c0c0710fa07008004046181803400c1005465080c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 220973309 1250 220972059 220972079
    0xe01050a0510050a090b1b060604051e09030c060c0d24030f0512030a0b090604090b0106050a0302040810021213021c060e01020f190509060a1209020a03030315 70
    0x9a401c05030031011030b041600d100750b031075401013030a10303040c012021000710f90388160308054407412608881140c0b014800c16000d504041015100d28090380c28007003008510628004601451881005e14441da43d4400c05c00a065006a0201c4045801440d041c40000700c03e50b0b02034042010600010001d9000c0c030684c903912080c1042031500041c9694000300041741408806c1066240100117075000c08000d030110040e660b0089a015040d2a510021440c507030502100e820392100040d60704105c00c9003192030340100e0f10014440d02040040000d81d08405502ca501594000e000b030302c0895008952503120100650800c0c001341015030200000500724590304030b2100d02c2541c001d000040c201e0000604205c2082c40030b00306031401501d41c10141d420710024402411460800c072403203512801c06003003003500089040049410420709015410040c0d90344405c1b2064420142401c0c10b40341000302d0000040d00d40c2c1d210103940031049020000c18590140c00c04030200f8a40d2488214954644a00b40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 220974559 1250 220973309 220973329
    0xa05181f0b0102190506010612050402030c0418050706050406030c05030f0c0901020109150b0f01080f150a031208010312051c020d110f0a0e061206040903110a0c0e0105 74
    0x412426034800500d024428103602400c9104810b1042d41c616540200800e1001303288101c08940c3e5904c10b50040281c958006081c51a2a90345682030015062940000e60344881821219100716990151568110340d20b5030b0101c102c550003016569940e98920015040c1e800ca4412900800d080000d88800035101d00126803182255480000c12503d485c0102c88460300130100d024151f45d49c0700844070200d5481c03074000005030400c2c0c0d000f20f8100031003400c2c4052204030b02d40030790620000f0302c103021003410400401d0358424802d4088114580c801f07c00a2080b074110390000d40307241080080039804580c0001a24181c0c0c4c00f40d8440003803000b24090440740703889103503c4520200c581220000b4245800c0c0c00070800c5a104d440049a851b40e0005031b8610b80e032280003503490360000081c00c0c0f2070340ca4014074402c9100d070080354450b0806c4208660721a0001c00244218401d9641710391010815004000c00500c0414050842e602c1441516048070340300b2041c0104d180050514000140c2890302c0810b075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 220975809 1250 220974559 220974583
    0x6130201020604030e040f1109040c0c08070f0609060c0203070b150a0506070c0e070c050f0312010510031410030204062408070e0607080d0b090405071404020c060a0518 74
    0x18001c83e079441c1c4040380d5a4804600301c640c41a1281038200b800e5515001c0e000724112040b032003c0d40e4030a0002048211696030503c08240180c000840010843c001c064031038140e040308001508003460328011008041c0c40d00010501403401046002441c0d00202411400384902a410400d44400008007a41b6140c58403a96001c88421002e11040c108840905850380c4545007036088035441385440054480215074850019040c0d03c05a030901c1070401001d080070049201541c5040a64200f601d1903103014080c51340605202038111000c2440303540100344103104908800a035040401a400260a840c842070b441070b410003e01048102049001c00c038000f018008014044159103010364419100074840340500611820b0300c0c0c0b2545500d001021601d200e100f440d03070b90721020003e0001311041c9280c8240541d0680040100003540000c0c64000e840d80101d005904855501c00034001e8414608060804c0c0559428002d0005054000c0f50150012034a404600e43d401c042e200c0e030b28400a890303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 220977059 1250 220975809 220975813
    0x9090103060b121f1a090c070b011505030103030f0203130608060f0312070b041a070305160302070201120e03160b01150c05030a2618060601090f1a04080a060902030613020102 77
    0x13601343c00070381d1648200d04110340c401e45180300e42c4140f00060f03aa640110f900c000800310000c0d080c070801120b0341c0e190740940468207030300040e090901b80042c03c2d400140030003000c0c002e0749880c103803010b4020416100604503181180350440d84603a0001d101c07603c1952128000e0f42041a001250700c1c010510785204403005031038500f4a4401d45607802001b0703001e03105a40351f0500f448c41442c840c0d9120300c030501c26022603c0200d0381e414003803080c0c07108001c0e040b444400c0510501020300182e0b1b000c08060606d00349400041485003002c06030605501c960040c8234400c0410140c01c80802104103452412280c03020078100000389414004d640d2100d00c0d01000300340d90001c002c0c59040c907000d680409078000c0e48540c10b807210928200c0d091380090044c1c1d50103c4199450100102c2800b007085180d900603c01e180003c1c2076458804920301030002c03401850103000341a00d40c5071600021000765402400750001f200c0d4846200d08100c1d00410f02c045040e8000c0c003806001a030700419803051000740e194181c2c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 220978309 1250 220977059 220977103
    0xd020f04020904061502010e16030209060d06060506280e18040c0e0403050c0601050a060f030506190f180b0612180709060f090912050304050309090103060b12 70
    0x410400290300030341000383c1c0940c0c1d07290302092040040c40c02e0894100c40e9000010310980079242203203402e0007412a520048841d02c001d00c0140c40b0703552079030340105040c0d030ba9482480b2940f070440c0242156800441c0c100c040403440c1c0c208165885d001d100c01c640000c82c20f000c1042103107021244001440e80b025040243c0907641d40c000d07185c00c1c2c15141d015001d081ca951a00e0703121104080c2010041d03e0a40c00500003003900306500c0d4043c01101e0042c030b0304843d581030141c034002004d008400b21590b10b9050694400004200740c13071701d042c1a40c9403114004500344468a4000302e40c0030840c1030040c1d00d0002c440d20f41350103c04156100e1041c1c0207030010110307402d003d40d9012980903140003d10305090b084001304401020101040800c02038280c11101054070750070245050745440c02e41c0d100005050900381c02d580440d580540e07d6440d4040c5140c07156582e9500c0c280310380307075105c1d40c036849410040843c0000300b80070440d4070112010b5401c942020641e4000c04030341d40c0d07920b125942c2c01907042d1094 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 220979559 1250 220978309 220978339
    0x1b1e0203030103140102130f03060c08010e0601050a021207030f020f0a050a0f02030c041103090c010c1a0c0f071b05180601050310031a04060c0207030f03142205040b0d02 75
    0x10313000840b48100c800075107082e210040c112000f4900340e019045160410300107004021060107007002030a100d103840c0055614040c00865803441c003401c041d0500c9000150301018074400d000301d10ba11110512004e556022500d0020242869440e800005003c1c1205007161140e02190b203862407500500141051403a54944160010071104101c3e4503115000384841d8a442e107000c1c008203440d0303180c86075440e890007001c00c0c0d050000b1480c03a1810454840f0001000440410881c020300c1e1200311580440e507100007200890b40304e46484181140d2000c2803050412a582e00c0c2190b8885014000040080c0d49405200919072120b260002031691140081d89651207500035540c844040c414501340d4550300d440d40a041900203d00d50003000d030f800200000d000c2a40910800070f5060b10050040c14a0b540b04c414118003911001010020701c5403404640c10181019111004060000f92002401c04020a024881d40d881018041c3d814020240c5c0c181c609010103664894024154009a841d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 220980809 1250 220979559 220979573
    0x13060e060c04091d06040606060f1713140a05030405180402010f210e0a0c061812030203210402030c010f0e0402090a090204060906080a09020d021201060305011b1e0203030103 77
    0x3d201411380709610714104c038211200405c02c40b4020fa0003103400140103414100000c06000c2d141c3c00d1901032011000410301d08428809040703034044004c144021080000b80740100f400000050409228402c14052a081c8507012000f001118800c46100841d4003400a201000c5401254007070301107603410001c0c0301114018050716504c07841c146000b11020b5034038600d08007145c510054110150b070001c1c3c003031410080c54404102c090b182d181000215401504040c060240e0385010711101e461003940d59000f094020405d0b01d031a068115040d085c0c80d800e018020344240800c6130145d101e84903d01e600c5051f54000c008000610381e055440e07041c034814020910002e9400007401c960480000c107000664102d0303a04c00780002d020349a0300e0b0300b4480d2078500300510418024080c0340340c031803402c08401c0050b42d030102001880c6034140c440304071806107140d00b140188090751000d003c2c0c2d420f0101c1c41c2d182007600000c080300203141c0d4452131a00900840c0b103a025000c0d1014501c050303071007000140013003120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 220982059 1250 220980809 220980821
    0x3060d03140c010204030c090b150717120702100c0906031503080a08090706050903061b1314010f030e25080d0801030201030b01020d020a140f030313060e060c0409 72
    0x64102140c6641d2412803a0201d0b600505180030b19035030208081c07042050180305900240004c081c140321000030070b0000b0383c1860b020b149000c0d02107800505001081030b464610f44030014400641502c400802e135400111a1080750003200501a4030440c0d9902801c40c450420705041c81d03900c5c460054102001500104440700a410041c501d031640040010403060050040c2c600f65074442020341800702c8654036285407500010207200301880000300340c0c1c0f400900e166010040e0344000d06c1d082c4031000119414801c5200c1c640405440078400b0600d1302446540301c0038001c0c03e070b0341e030904080e42c0082107040b200c4604481032650070104603451001c1964503092058804000ca4074000b0f42d45210851500d80100d10315400b2030f03999401001950b07058400c52021400a002a00e24210b00aa00a4a035501020b00416001c40d01840140e1030008000070020315481004483d640d090106110311015060b140407039100782402100c030203113080840c034071b07000f0120001c01c10304181c24801800003801d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 220983309 1250 220982059 220982063
    0xf1401051c2306010503070b0a031505060a08010e15091803120a05010e070f0512180d2001090528020a0303210509120d020d02040314010b0a050603060d 67
    0x2107103541810106002c1c100b0344441201c42c1003821428111031415a04201e01680942c1c403036000000c00700494503007001210710380c2003280350000e0100600a4070159400141d08103c0e0010404180c04002c0780d003000360281030b180c103400799036030940d1400c400341d45600c200002181c2144084012900f0420040c40f026250080001624105001c0704107aa0517140200c0d107a0114540700d00040111840405a060f0044d640e86450307041c800072513801401d148140b0010003145e6030f18100181d0102000f15281ea032050700343d029200e41005074200204107090364521801e584407083d01d0100011414814242583c0d0300c44040c04030581c3c1c465400d10750303810500b50700f0420740181c618500180c3c1d80200603400f07140b080d12202c0f0303c00c021228104031040031418100d100c61400d401d109466000185103104031000100b003680e00c190b1880c200e0041d0251030100c8220341d0011401104120034414141e6a4114110080000180903030401c0700c034000b1441840d401c0102040812141c0c1404c003c0300070a24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 220984559 1250 220983309 220983349
    0x3050a0f05160306060f0512060a0504060b0414031623030624031513150617150c0703030218030607030f0c111e160312030f140105 58
    0x30003000c1001a03401c100c411800341405100030402c03840d01442400082c12052030003000716404c01c00d01078440e1080040a00b031083d60700b40082d0350b079902d8060f60000381c50040c0c03003030011950383c01c00b8009c0d58000d4000c6e07030044280c04e42d03144020700300003958030380c9280b004260000799840d140700c1e02c40702044041100183d150911046041d61020451103000741090700d40110f84094450710810039441c2d002c0c8440c403d0b0440701e2204140c10544000c82e8001d203114422200010042c6802c00490b09404000c0207550300741440050079103580d016106c19111303001b05944501d009403c0c14034500c6001c6907100d98142c418044e02d00800e110b0344c040c4c003020107068460160010034100091600004541030800261620020301406142d8020f294540a250412128021004443e640c498180c03080580c02c0584901e17180c0d00c8500e081107200b81310300c00105403854281d01c2e4108031002d4801c5030405404241800c0c11060f07c4070301031181d4a9052150401090107908200030443c440c0090a05602d1382 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 220985809 1250 220984559 220984571
    0x1090b03092d0f03040504290103020a020f1507090e040503040b09010309080c010617030405030a0204110405100908010501060e13090203160f23130b01090f03150608030c030a03050a 80
    0x31810802c038900c00707880302d10000c4d03480b10300d000e0801050347c00c05246015840000314204e107004160001540b2042070908000da100c109240b0304928164001100726007d10403000000d0004112064032401641c4654620b01d11341c0d226900c3c40d0b8555001d442c010403e5008110400517880c0007005440380c8001450007056100140d114035001d0b030019488d0300c4450359075000030401d0004200007a030024403c00003440c00d107850301700000e07107030410b00e9030190165444060b01c4c40c60b1605141200c014240c001c0005c3c0702d244017207500401e060038600070304d007041d0701c4c1070000f10380c00e80a4001007196440c02803018030080100003001d0050640ca0704101d070548100b682105114003400c00300c1014191281c2c000620502d40304401c0200c920390300341c00d0312843c07403000001d403240c45405400c0300188000380c0121b80d04600c84012928046150701a00580c1358030403000c810020080300c0140c00728916241440401c1d200d0f614240c60344103c003d20101540100706200440d400380e00015844007042c4c03400198 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 220987059 1250 220985809 220985893
    0x110d0e0c060c010203061e0d08030a06030f03020f060601090e0c0a031d0a17030c09060f07021003050603060a0b010504050d1b08160806040b36060601090b0309 70
    0x460b00080000c4031141d40100800c0b5250400c1c42500f101220342e04010744214100e00042007107418107202c044d00c010740020000b00c8201880c0c01c120006c0d54032040510078050303070b401c0082d160709484204c80010702444003c202e9541c814401c0d2403d45407800c40a10303803505e4043c0040724950000c5150010b1644030b0703d8103d07601c085000d00320340d1084110702400740e102851505102c0c164010290b284119001d000748a81c204a0707a007075541c41441521100e03a20013012102450502502c000250f00048201040340f070540d0613004203002c1d40e41541207502607258050b881040c1d0305185c06460003d03600340000c0000707281610b01444130382c0c00b4840400041340b00ea0940300b44e115042e0400b4215030b001403000c0c9480300c002c07031901c0000d090441c040c041c81e0425036200c0c280070f00050800e130585c0b1003000c0a0380030303040300c00300d10707000030f11000d14100c242400300b0034040c2c4450f000ca506e20b01003041c5402c009184402101100d00c5030168002078074207000354050400005080c4003100c10080c050441c0c03290 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 220988309 1250 220987059 220987069
    0x5070302012405010908031c0e0703050a1b0509060f060d060801050903030f090f1f0e0105070315050a051309110604060503100b21072a060c0201110d0e0c 68
    0x110400030000740080c201c0c01d000024243c81030652080000350f102300040e20304000c1c03c28050209442c015804a1040b010b820b00501c0d020903a0000341440c002d19400f00100101c586540e01c410086c50b0703004410665070347c100120032a00b20351031600511030031903505142c13600c00020701030280b03040c0c00015815203402d140b80c03c5400c00c07030740c108065100000b4001c0c0e42800e4004183d01002260007804001c02d001155510360342e00c126204207521402d411030a907a0200e420020940c41490300811a40c40d10078801000350203494140305d40c01022840c0400c080c180620a1025034502034035803000e003002c036140500180701070b80003603c0a07104490366a41d140e892100520040c084d030b544840e1030341440000c0341d02d0954a6401000c40301c804111009041c0c0e4040e4000e00d000213038034440e0596583d5003400741c0d05140404042110108034040800d55440624100b0b10305a001d04020800440300340000c3c0d00f03c0d10b20313890165000f44140a03450003054680c021b482916500b000f0340d1147c10131100810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 220989559 1250 220988309 220988351
    0x1030e03041814010305071203120e03090a061d01080a02040b0708070c0e390406030c030609020304020108011502010b0303070f030e0f1005090604051905090a0213060507030201 78
    0x3a02a00a0b0840000c0c4120240183c400007a80319034101c000c1d502d142e83c0c15558211030301c10f4216010f5240e0f248030a2601884224559100c02c84d001c0c4486010001c1c010381b40d034049486103101d50a030030f030003266051241c60b4901d8120500380d9054000c0e11104015a042c2070014207013030354160200000315100c1034500184c0001391090000d2074940031646004042c9220b40d0304496038800d0440b080090040a104104181075200c1c2110100f2110b200b0000741c001c540264800c206030800600007500381d0341584040100404c6540400084d0340301d100c054264442030350080d000600190041c03101e688407080c0900240c00c64000010412404030220f81560880d4405841c00d80c103110140050540040640041000454001c103200154800142c1d100101035403400801c403000c151540c0c02d45800c421140900070080032055500c01d15411000071065502905008502c4400440d910b9105802070301d0460800780c100402c01401d0403006c46040c0c104650a508564035042c03082c1007038200340050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 220990809 1250 220989559 220989569
    0xe0307090f0204050108130b04080306061303031808160519030c23030c030604060506030106080f0a1719030902010e0402070b101d15030c060f09010e060408061501030e0304 76
    0x343e00e4914020014010420007400f140c01135100c440304100003842c0081c01036016501142880d22525030101040c0e15014400d6500802704030481c010080c142c00603811f5464182a0711860780c4140c035a14080d0300c800d5401b010105d0701c0d00040d02488180340c03d0840300199155414984202a0f890700c07180324031620b50744a8082d180042414040307401c5d4803a280b82038010300707500130a800140c05000c02d40e54900140081c2c110f60f510000303d28559400c1d0806002403991404aa0307080200102603a00ea824060341150582d0743c802c042c0c05505002425107455052034445030031a02c080b82c200b9404ad08002c4403c80c100040c0c4c518001e05980c0d074dc40582040780c0508800005803070504201480310b00c0f1074000d0303024240c107c0782c1c4034201a0f030700c1e5071298480100820046007800301d40100780f604d64644c00040c0e0051000c6500400f0350582d90181040b00001d985885e1000000030520110f44118040e8101c01e412920000d6096206c8040700d505460040c9000030f5401c01c0003a69904640080d081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 220992059 1250 220990809 220990811
    0x7120c051014070c0503040b0703020f0c0d050718060f0b070302010507091217090d03020a0c05010f170702120a03090209150f01080c0d1506080702120a0e0307090f 72
    0x14080c44010401e01ea600490507204202d00c905030860804140401803400040060b04200881002414810f64000302414020923440f84018540a034407440740c88004001846040c42c40c00051030002400005146c118000d040e0360b500382104680440120546907143e01e840b80302c00100c0c550b28200c1c02c001131100c64000c64680c082450000c0c00d540303000e0095400c1007500001440040b1a008d03d03886019844001c1900820101810204602942c8001c95100300018004014103402051005101717125511425501d0713151801511040c1c000003240000984030101c3c40110700e40c1010258100100740120b915100f03079801e085200d42e1100d040361000903140d450500441c05c04030021a000f0111500d0550b43c1d1101401103840700c00003540340c904100c0040c020134085501700e02110502500c2202c01d00c145100d82c200c508040348079100f8100090600030000344014404600082d2294420304a02e1605603c8030080304c40300705110020b585405880c01c001541145031055000c51010307084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 220993309 1250 220992059 220992077
    0x11030c0306062529010614090109030203030403060203041209060f0503041406070f1b080f07080f0304050304050a05030d121a061b060c0c061909050604060b031b031c02030712 77
    0x100c1c12588083c201c0c040340d070141404d80113008250300a0240504101000c0c0c0442c0c80d0f014041c0100c604018a0b440a901400300240c08010311055400852240340206c081c01c080301d8900c8002c4400800d08d2207840006444c0d8244400d10700c6c46240103540190044690402d007520301841e09040c03d0054843c0e0011464820301040f1064000803940b01c504c40b0302032400300301c10840e00c40b03416500c0303a0035252490400004000e070030090040296010100c000c44656164541b926159550382d100740078252041c0800040002e039440d00184828a100480c3e452019148800b800c00018280451401c88900c82a0304088031907203c07007000c1d106161a03540c429041c002d101480d60b04040c00540406182d50042290640340400010416045122010345100d03803094951008020f02844200030041d00902d82440b050107001d400c50404508100c3c02c0e1040d01d107941c20b07000d042030b070340224072901340d007001c400344013030700aa001c0400d040c2d9038500581f0300d01b884a589103116400704110360700214503450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 220994559 1250 220993309 220993343
    0x30a02061005040c023705252601060b070305040e1003020307030b0a090f0308040c05040e121c150807090227030a061a0411030c03060625 61
    0x8894074000b002c05a400308a440c00da070400945444070a00889451005020020081005402d0036a036070240540365a0500300245031140d101c850004030f42240c250054002c0d001c070148803429100b1a1660080700b00b152402c02d8802d5030412400440c201c55550310400000d40022003002040014485c0e0b072450360300c50428404105205000c1e080c2c0e420303050110410f1005171000180038080d41c0c2c00005030403036546c030005600e0261481c3c3d4001401c0d2501d40b0050010540c00034003281c000c0f442088150038164507881071004403124103801c03c125511000214150009c8440203055111020581da000c0b42080425001500c030001c0c001081b2588440342004201002d02090000e081c17008019481c122884c58140b101c4040d01e10810b401003410700301c0c554a9981080b003881c2c4c00c1d038402d0301405080340c141e0240440511081002e4019800e2000e070b00c0c00d000340f2508030ba101c1c0d45a002e01c00e096440d19400c0c441960401944052080800c6010382007105d10b0403941256a846248410303403541e800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 220995809 1250 220994559 220994581
    0xa0c1a0c0903070b071a1519080f010507090611010914060105010f0e010504030b130210030b031605130506010909020c0705040b0d0f03080601210b041104061b02060c030a0206 77
    0x80d03440b09204e0790302400030500007541e01c0150b816004070000e0059142c0c40340500108545540d2900302e6000c0c485901284828042c1c405120032100e40740e055940400c03c11002c4c07420703100110b8203500026061403085c00114002c100100f07040030000c0000981d03040a40e80c102815141624842065204400412080d80d0000e00440003a507a0310307021404c1d44441c000a07245000d140401041c41802c500041c8440c86d00c441c1000c02c09030000c003801d542c02080b20014000301900380c2c0241c083d01074400c0c2c61010000c40245a012505e0260058849807400c0c3d42d0880100300240000381002410b44000816160b070340060582014a48058241c0900d05070070401211041c003241402605400c258a010441203980300c8421070305800c041c8516a00c010040390640c52001d09018001800340c608506d4002c10313800007800e100103450410500903000c40300d80050003a44a06da000840c1500c41c031003d41100044045440d201818603070504c0c940490f51411a001100f0350801640800d0400030350400d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 220997059 1250 220995809 220995823
    0x241d01080a031b11030307060f060f0810022a010f1a030c01140c010204030302070e01090516230708070209060a060f030221090303040512030c0a0c1a0c0903 69
    0x503500080111011039074014248129000c150a81c249019007140d0034001075020401401c01c1c003d06899070340440c2d103010001401c4105801da0941d03e803030004542040035116001c241d0394200c2c000d0101d0440aa0f5020203036226119161127040b504608541043c1d0144644a4900350303600080f9011880315048800c039003084010f0a860404080035010f10346004c01c5190400200b880d20809020326919035095921030107480c4425580700007400414150301058200c180e5285d5600c03460310ba40d03900d00c2c84050700c5003502e20014007100d00096149890080c0c1d07107407140140070741c2c91140070700b031484525250b0341200c1c1e0180c03110341c1c00140c9281107103040304000e0740c80700f4212031590290342080002000d40d03881c0c0c00f0a1042c16400144004810045840f0b55a084903c0c944001c6c50300d40460903580700c0d0010340d0200c0703051181001d442e40440480003500e100c0c0d01542d10380d90410750040340899018410003000e541844070250040e00491001e40d10700e120b1421001000c3c0e940a04070305040c13400788 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 220998309 1250 220997059 220997069
    0xe010902090112061a0f040e0703080f040602070503030c0d0804030c020405040c060e01030606050a1b080a030c0f091d1807060e1002070b1206032e0b09060f04241d01 73
    0x1001040d900160b981091114041b4070550380043d026000c045068070b03024980e0070141144201041954420041000420a48032180c0c2924403599640061513034038040c90180c40d4541d000080c000c64014480c03000d41d03500c1380c000d281c005440301041d0040750403517106403015200c01c540d544042c0303c0d00381c004281c00b40c440c00c2032804100301c6103030140040840c040c0307140400400130401c03030b01e03032500e124801c0700804141c11000c02a83d8503a00d42010b130050210305400b40208294622680d5034a008214038402c454108005103100d48403517180481c41500140310100f1072160341c10442e14403004000403005440242c4170000c0d081d00010800041100344041c141c1154090081400300601c2c50003561910980b007800c001032078860000007402c040d441513108241545501c0c541410402c03090728202911030001d0100410110721017401205441102d6498000f40207801d10b020905056010a45408410911410188000e0707034001d050b0005511004800711007a413001d00046000000600620b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 220999559 1250 220998309 220998341
    0x3080f0a030b090f0118020d020c010212010e0f0412051b0c0906030111040e101707032904020f010504050a030b0109050c1614010f0606030203040b0601020708100e01090209011206 79
    0x115245261201d02d0070140906c2140d0400c0c08900010080780d40c041c1c82c1003410b10502591100f000051040c000c1d049208505c128103855400080c049280500079402107841301c0c0407403882e6440e504c07007030507401c210441d041c1080f50030000d2101c41c10181d55010004002e450280020304014803c0140f0440040d200b24442d924103445142c0d0844400212800c4a45010b00c146696880b06500c4241c1e00f400c1d801003c6881d0400b0464107a0342d00030915009992140b805402440000d904494520940e4065403003011000008a005031900104440c0200304c1450860314050b10b0781c0c00300c1e0400c401c561048500c210244014040c01c2e080b400f9990340701c05d10002071814016843c00b4600040c00c04070020b8088420b4081c603544190080d005003003200d010700ca040c004195103680080080d4070445003982c00385651030100b2419071001c1003150840b00b0000042254038040d01401d8014800885100150b65840500da4010f8945610080c028001400e040c088400541065829a03010b000c0000601d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 221000809 1250 220999559 220999561
    0xb0907020304140f0a1502061b09090402130e010f0513050703080a17010b040333020f1201080c010f0903080d05090102090301060807051e0a120c03080f0a030b09 71
    0x980d9000095600310340a022080881076000c801240301e03180c8003a00190414034024022a00c81900b0001220101c8960b0844903165102c402489840000c02d84855200c1c00400a1004d6460104070fa190018001800865059076079408034044615145801c1626511000c1c2880d10540134400d165100f1913146c16040004420703030741c0f45c0d2507001c1c502000301000c4002c1100925a4480c85000c0d1f0b1079000b011807242e81e56141c00042a29402c103100c11100300d22141e0300c0310751542141070286514003500d40460b1010704506d98840182d0403040f411407140c0410b00002c84070481140342e290007031180d0300140c040003000c100010021a11290440d0502405801c1003000840e0b0303404481c80c6090300c0000084640314185070a01910885540c240d0641c00c1080110380b904004c1140d00441d48111400c0c103c154075016486030601819014503805404501c042040140d80d804401403648035540842061343c0340d580b11051070700224040d03103c4420100701040007a0b0035100304003c0e01d004131201405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 221002059 1250 221000809 221000821
    0x3010806010306050912040906181b050a0c0204090602070c0b0a0c02010507021810090f0c0806060f09060d060806010b0c1c020f07030b15091905060112050c030402040b09 75
    0x18888040c40010f1a0a680b84002030b150710080c00b0304c100150458901d5a030360340d039132000034001c0d02d41c0d4000c00c4aa01c00300c45442045c05024420317540b02c1a100c0d114070803041b44003941560781e900551078190900a40000c1c0c1ca005a0b210710514000c14820040181c0703072161800c00c20350214440d00481f00a0a00308001d0740e44c01e8000c00001d032040d909107841a0380d00703900e10104800c3d1307502c1500480480644804d202400b00c6040c11141512080d01081146007984c200b50700030707681240c64050208140308089015801c1c04802001603045064023986480600e030f0200d402580080c1008015585d14881805141000d1104e68010004060080d00340040104029240d10a02060390a684100780d48422550700134005100040d84240c00c1e98055031b92400d0424418600316248410324a005600c50b10504d84001c01038040d80c03909180409641d24840241300821001e40700505000081203012601001409854829500032602035101d05162051000380c42c40003807007134494207084c020025 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 221003309 1250 221002059 221002063
    0x209030307120e060f0c0f0106120224030906041406010b0d051f1412010608060103030503070306180b090f0408180d02030a03031b0809150a0e070305010f0c05030108 73
    0x241c1d0781c1100c0d0601c00105981d01c15a1048441e542c1d2039080308010400d5984807010b000644440070500050710152140c200306282211514051880342c0e0780003203d12005410f0051001d00d040c0c1d01070b00c4850710f1071400400315440e90011a07210074a0b6100c00100400c015002c0121601a51b122000307000c59410812914440d01400c000054519a035070000703000d404091011507915414070445110058880d940c000c0040320a424070b030b01030030516403100541d000522981c41181d00c2d09015001c580d0840d50201c1c0c0690001d00b1a404058440d000850140500c0305a055401c1100200107242c120f4482880f000120080420190111201c1000f01003400841140c1c9000c5082707984c000b4055a00700000c94240c1c40c60360294251243c80580c204164242d880301c1001e0103882030145440000c02ca04a680340c0c000c94a1071a140c00100040380220a00d40305c07580c0080400d580421201411394a19281c514154419030341a074440e2009121541c50388125403140d2040c2c50601d1540d814581150b03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 221004559 1250 221003309 221003317
    0x60c0302060c09040906060f09061e0306020f130b03060901060201020c06060609030a0b0f06031207030c06090609021306031103031e0f0702060c0705030106090504050a02041e020705010501150302090303 89
    0x303118100002e2204155600c903800105c40341da0112040200980300c0e59806503031000e6004000d8843c0c07601101144101d00e80c0ca07030107006030b07494800007100c41c116502ca2029402490289003100c0043c4070030130903001c02e20300d054003920300c800fa5039440340740038410802e48140c180d002205691041018180511012455076849501503034115940e00360a4003080c40d0520041001c2d02c541080414000306540d2921001e001da4001c40491342e1240569801c004148144000100400c4001a020001440b00d07080041d021b40203403000182142c0784e401180a100300104400d41c1c6a540e88002d00c108000442d400b0441036003500150304210740780d480040410640d03a25081180008603490050703010300800c440326164041c00c0c042d200c00840c41c95665074442401494844d500b441d1001c514580c0c907103e003070f200d1a001001010199043e4090100404861002058030300f20040080f0108807a4001050740d94802c40002540358544000102d03090402081e103020140104841d110070394000040da = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 221005809 1250 221004559 221004571
    0x40506100c0c082b0e030a0f06091205070303050906010501120207050102090d051c03090c0314100c0c0b160225120b0103060b180109020c1f0e07060c030206 69
    0x785003801e8181420345024030640d0103080d50303206921400c1c0c107140050441c00c80d14020b00324000c090029043d0180d42a040d0302c41810b4140d8480c20b201404140110064901ea0b4010030000461041984452001c0116410303c407010501c005020300070585d042c422030307070300c841080040d16280d411305000800030001000340c50032540c0c0100c0d001040c85400e60454400700001416032880c11050710305261906580b1006005035903140842c180300354040d00500c1c8032580c1c400d0701135440d0b5041d071303441c440100c1e1803118981c1280300d03041c400c18110b00305100e140c0044401e41c4606400084520703041301041d0005010050490800c1020b550003600029044190045800c11a4004403802d0311a2a1404598441512404400c903003405002008501606a9000c1c41003032040c103d650f001d003c00051450030440009402000412a00c00d5540c0541100d001361000d036400060060507401041580080c11000c05550b0801614441010031145009004a0030007900001c00c0781c0303010f516100002c0c90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 221007059 1250 221005809 221005817
    0x18010e0d050c030c06101806051011032116050c0a0209041a04080d0b04021603110a06090501060806090f03030412090312030c0e0609090402040c0918020d0b04050610 73
    0x10b40410b50b0040c070a8440030300b04081201c01511b072503104049040e059100e4415005804007907150411054020001501c2d000b5245800c0002c0d100c90840755012070340040c8011b4001800001010303110b0f48000760f0000c4510200102d6418504880000d20480d10b1006c1c080c0314003000403940f4a1004180003016540442d41c2102c95502c82c1010f18001ca008010080c019046204210411600b240a070040081a1030100021140c0c80e091200302c4c42406a200c1c88c01c4242c0b150200060b00c59900c1604191040b815920032107440c2d580c140c20788150303000403151039440c2c84041c8051070b800c1154136804564240180340c0d00381801c8585840384005003014000d20701c0000200c1e050390060050200440d400510191103d0341d0003402401451160b40500010b02445180021440c2c898243c551070342c4001c01c0340e103164a40380c1c20000240340c00c4203481c0c2802003580340080e0766072001202d003070f4490140d000980c0c2c555045a58a0890740307221006031081d8030700000d2004503207030715131441013840781818 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 221008309 1250 221007059 221007067
    0x190c0807021c0836030304050d0306081005070e040c0201090b070305070503010902030601021207050d081b250c0617100b0306040507030902040510180e030a081b1218010e0d05 77
    0x3036009401809050b007404c83c5402480342145500c0000f00552042d400303902510720301ca91303540c000ca090722806d200f1512142c0c802050314161041942c000d03a000700460134454990311441c404078042e0743c092840d180151755103181e40811700c01c8021050b0f50020152a04200e180f8085001030f00700d000600445000325804800500c0303e074000c1050b080c9880e080c1004a0301e805491408903510081c41c0e0f1030000160304000400c110752084040a201c09007100301c428109030749020400851451011038505d481c8d00c071052880441e40324080d8501405485d6101c008811800d0f46100702048094107811640b60104401c001c03442070881900d42014088402144030348541e4400c4000d4848440c02030344c014a880184100f0040308040c440458180c03c440701c0e4500041340030305044804c841c0384812244c000b00030403291248070701e120303d9005c5181325103918208045101c03018a40c01c10076002c102000103030248000403c01002c509090000d130002030110340894466240c803044030028500922002103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 221009559 1250 221008309 221008351
    0xc12020106030b0c031504050105031905160e160504051309050a0b0f0105030114060a0603090804150806011b0c0501030218030f0105060f1903020108190c0807021c08 73
    0x2421a0000b9a04880c4031003030307820028803ca00983c0245d0b010300100c960301e0303ca0809410140259170490320000c0142449003911a110000e00c103407010111600d0086080c81e800c60500308198034050807a07460300700494036203c1c2118a07210704000e659814400d040c00100f01c1990340040311095400c50380804180302044d8a0310724509800080000d205003500f0042100415107960700c113040700c07000c5000b4412046295045141100243c0310035401180250f002e03c6018040e4000703050843c4074130b12091801c0d03a40c07030850039100300305900400000e240c1d07001e22855680c040e000b441081c130703e06036481c2c000105603103a84504505129050500d81c003c500c612594401c80032804400101900303a4640c10382c4103040500812040725254444c143e4801d000455003030070700c80da5040d100304640c50800320b811500152800c00340248025a01501040101c400c1c4100c1d024803002c0c605075848002580c28484006800c1403002d5140145000c03400741032400660303001042c280c22103c10740207201c41c60904 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 221010809 1250 221009559 221009561
    0x8060c070c090903170106031415030c060f0405090c0306010210110405060c0604061103040b1b090409050a0308010501140d05090a021c0c0b0406080a020a1106070f08010b03070c120201 81
    0xa58000982e503441c180140040c5500840040900e4441c090b00c0e242c540c2e02c80d0300c03d400b2520404583c0310010038130030006988503004203038002405002400c50391025006070008489078801d01071490303018804030b800c000a04008803011340003222808158250300d070160000b95540c021841041340280c54264000006108500b2500508000f0740120380d1420710140e1a0f0b6104010350b01212181e180900c0050040f07405e006a0307001c0d5078031014024054803031030385070714179061505014240e1080811200d012a551481401d1000e40f08101515015045040242900005a01c11030611201c50b81040302d002d580ca00300c50709a9084038000902d40c50790f13058a407500300c50410080d0000113480c8160f000039050004116000d2092a1089805032101c404180740d000b244100001325a900e404542070a00301d4000d07040d0107107185009882451030003452450140700f65194008a0110660b6020965000b03186902600342c2070308081c0b0714205007500602c0c0030208840a8146100c034000006440d100f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 221012059 1250 221010809 221010833
    0x6010e0f040f060f1719020d0b1012060b03100903050409090507090504080c07061805040b010c050106030605070f0504080703080c150c0307110a0b04082b0b0a050a08060c07 76
    0x1c000d036883e0026103500c01e4109200c070388001c1400134802c4016041c030046d0a00100da4600c1d0f0301400404611106a03590321140d200035082d0203c00b209294040b61081c2000c001602c11801010b002c28119200d8050504048000da0071040c1c181c201140d46001c01c1d00031040b20304890708a000051400c003c1d0400504150294001c1440c042c00c290502043c0440f00020f408110810404c0e1801c030750341e03140180d6250200040d42c0700010b002200410151a0590003d85281c0c1d044c1482070fa03461480e614682150f84682042340d065982d10140f0407a640e01000c480810015070130101c0c640750a1440345959140c140c4402400a01c002444800000040c00489000943c0184180c62810840340b8129103400885450001541058440d80409000241c05100d41d40011600205880e180c13944d1105902c105400d02804614420031100900c90403400201c0304c040c40381c002007010a41c5c0070802d0214050380414461002c00a00740701c10b403000304680d074218001d4529107903168001c0c5465031101c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 221013309 1250 221012059 221012069
    0x3060102010b1206070201110705100203100503030d060303090501030623010203120703091b060e010c0602090d0f0b090a02090f040606120302030a0207061409041806060b0d0506010e0f040f06 84
    0x5042140c0800f104001803014000c161a400902150511810448081c000d85802920130743c0704400c0c8601e46810740d8015131708944c408002150746521840440e2030742d4002d010403485103507510300c204241980144154041c1c4801d2030203014140c9030116825403c0b06020080e4007110080c200140c1d1a1300810032101280d40c02203110055180085018008146090054070218080042d02c0e904480c00c3c5035070000d582058a9000e2075044410045502807100c9808681d0780d5400c01c00e0105943c1ca0001c015000361080d802051301360a41d03c1e01e4410380310051f18022155214160303800040e0b8600502c2c82e84440107068009035130744d0384e007081c0e00581000c0d48031100075501805000181070340800108401c490030303001c8411035603803280226156002d4943c0e45600c1d400500c600c65084c5081c0d00845403041540685025030f0309251520301c22500039a101c546400400100f41c0707121011401a280e00c48424203280fa48116404040b89900000000b298804c03030741e4038040b41413400941d028501805c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 221014559 1250 221013309 221013319
    0xe06090406030b0c0d0605010c02010f030c180807080f0703050c091b0409020d1401060f121b051902030f07020d02040e06040302100609050405030d0504080f0307171501080c03060102010b 82
    0x402d12580003d41d036131280c0b502c030305c55608054002c2000d500130f46507101c8e0580e040e1f41d08501e50b880400114010800d2026440811030424a040041c3c008081c0d5035000d044010301504400d071a1001282c0351014960121200d50040300007000401c0b80070030004c0c650101070300d482545507506a031116012503051803454442e0404900070070303040080d90140c04d5181c54098100490301280344203c0401d0360900c00d0000040c4000303104801d10b481a004a12a00d080900c042042c0d0009008001c0d04102d54400000085000c105001e117442d550b4031840d1410081d00185240c001d003401c200c580d170701c0f9608010740201140d41e950340854417580d200e101885030703180c00d441c21030515160094170795031b03d400804510b0381085404100728940380300b0710b4051a070000c01140340820203941680500300080c01034851280520880300b180c2146401141325401c01c0c2c3e2400d0395070b070b0141c10604425401078245181c0e09980d0203006102e98010501c5170300500013030000c60310303a920a40100d000d40100b002d495041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 221015809 1250 221014559 221014561
    0x7060e03070c0324050910020c0a020901170c060c06070f0c05012c070b03060d140604050303041a010e04150e10020d0606030b060703050a031104030b04061b0e06090406030b 76
    0x3100b0510303840e52051400c4c040d1041080c00e10744100d001d81d0010740d6251066003000f40940c01c0750465a00030b00512000c54159160055035800240c01c0c51000d1b0b01c03482004040d0b60501d020280107004551030030400b01d84450422814081003a40c4102c010040002c2c8090340c0c0158403001e00441d0100d00c00d65000c4001d100d01406583c100383c00c0d02c0d40006011010030800b5a40d1000000400e0000940c3c1c2d04000c01821565021f040020700704159009485000c07501d250718420b1030082c046248224020720007185e407803c003841c00f1012218400c24500d13604134a80018807071074a14070745490308650004144c401d2210321100010013040640d00f0401c00b0f00c00d0382405e03400d01000d500035140d4041802420010150f035600140e003a00d04002030142e0000c1d0070003517080024001c0e0f014044410131407600140c01c500f200c04001256000d5041079681c410510100001c00010b406004000d4030b0010240010104036640500340000c0d04c0016845a01c001c5001426038695a00c1000119040500542c032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 221017059 1250 221015809 221015813
    0x9050a08030a0c0f1103220305070303080415200702011103130503010b090705092103070b0603010c1716050f03040f03080a021201050d03051902030a03180807060e03070c03 76
    0x500d2800005000b04040540b07440c04c550140920b100401615005940303804038009a441380f8a0b4003a401000e5250042800300119030f040040801640c481c2d25034256500707003030030011015130444204581c030034184904010600041441841c2248000c008242c03516110b100503110b05641c555150000c0c880401e80c10b059000f4601021b0869000b90000c0059148100600024580c110380301000310300100311030704003414152540301184030102d40c0280104000540c0f1800d513448001c040d150b8619820502c00c3d00c1c9000c5c816054603030f496081200b401c0024840194041c0401090580340078190000ca1950502850440e0404007141c90070b00c3c1c0c0c038501403404907441c0c0401c02d420f40004003801d000411545041c802c80f0f104ae82c80003c000c455a01c0c1c8400c0021042082c10110108801071210b003903118240c0b01c0404914680f0340146da1104c841d00802422115100d1004075070500422918000c01c50960485460941202010038501c5041c2020703450351092540c000c100240d08080002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 221018309 1250 221017059 221017061
    0x1902280309020904120e0301150b0307120204080d031107020918070f0314071d0a15030f0b01030204050c0405010522080d02032205030316020102010f290d120309050a08030a 76
    0xb551700c80a8032440c0b4240d120400341400c8440942c800102924008018840c04d002e6502440d4458264030b000c0724850a0300c010241660080c0c0d20400c081d0f03028000d80c286c0150980103080f01030211040c02c50901846400180b011407010340140c804424042080c107404105002c284054050f0340b2107488150742d03c2c60070680070b40c0c4031009228540140440411a168001c100703090400e034040c00301400740c403050b00d074400405800111920004895100000003421039202218040c02009118401d601d54010f21082c0c4400400c0012524405c1100f8480c5a0300501a190080d140100142503a0240807080c0032014403078010703411030300c5910042c00181c0c1d40000101280c0500e07a03002c031824504411902900141401480d905da0410721800c45210100710f0b009071210f005100200b40c54549082c0c00c002c5400c2540c018202c1c2103070a81c0e000614004c105a0341c10f503682603c00b01d645440790380341c20888cc030000341c0d09010941c07138041c1a01804401c109600150380c20500c2c05a890415030b007104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 221019559 1250 221018309 221018333
    0xb1f050d0b0307030506040b06031c030b01030c1b080f16080a0e030705060a0302130e010f05010206090a030c0803040606030602121501141b030715051902280309020904 74
    0xe510241001c10800d500d050201d0320800301c82d808401020303a502c843d03480100b902401080c060b0140326a000360f81d04c42c2e00c6041c234550004459140000e140700c0100c00141910348880b0420f0030b010781d117031400807140c00c140407007901c09030000b41c125101d01e20b0b04001e000902c1340701044403000034036494181c2442503080052000724655154400e02004070313002e141d1103028911549511035003e2222002e101d0103074000f841e00d0035034001102642078070f51050f1380e0000000c0c2c01c1019559034401c800e001d02c1d43c0400c0307203907000401d12004101402060381d008211004014000341041c00110100d000c00800790001e0000c0c6601400541d2a2500100401c007640c904865840d41c40c5000f4094116550184400c107403000780d01c1c042c2c075140011504502c107500c0740060358410188010455100416440d50f0700000344c04104401140a0902444e00c81c0010f4103c45100221481080303181480750358102c83d44a00f03020341c44451051803901360150020012a00b000e504070701440d0801c03040120101e50340c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 221020809 1250 221019559 221019577
    0xc08040302040c030605130612031115040326090303040303090201090b160204060b07050615150d0204150f0e040c050912011409030a080103110303090a06020607090b1602040b1f05 79
    0x6e0000703604a1f0032040682c0d0b503500c40e640400510411240200e413003020212070344403d1a0449804e000d084204030091441141c042d000103442c000c9030346101c0780c41c007a159604444035020140a0030031a80c80e54680c44003400007814555140c0c82c1000b1a4000d20340400284103c940c0181c40e00e040300380344115503600760000ca200740d19060003c04e0035420031040c0e41c0c42c150001c004013001d5883c082140d588580110a042e4410b8610301803014650840c0300505c0000100c0c0400741c0c50f6443d085109218008d20b82c1c0602c144400d5a41919480e5400303d004600076604507400b003035500d03411400ba50980719441100f5080b000302d2242540000301504000f11114605020165640d5401111078aa005070500344000034032090040020030031101200340310f400020140c2c3e00d403030040310000b000c078031540d0700480141c0c010354100425280c1000314000281107508403c0d00c0e00340e03400e8480201a46040c002881580e542e5000d40840e100c0c006040002d0960224110080350304620181080d000480c0d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 221022059 1250 221020809 221020819
    0x6161703091c050703120b04020a020109111210050403030b040c0c0201020d14040e0a02040e101e050607140c0a0801060e0c09030706050d0b0901060c260a0c08040302040c030605 78
    0x30ba00b420310100c690040c0d000c0569980c0707810110250b0317045910011b450309080c03800742c9a82c00040f0603540e034802803030481a1a000003500c3c020780d1800585000c41c0c048201c2c402c0d49802140d45202c2c10114104030a42c85009000840369200d2800794009d1400000898000f4034060110342155000243c43c10b029000740c007124405442c16404844c00c10500b040a1040c2c00240410000c550340449510340000c41c03a0750140c02c0c162103a0764080206c800f19240390150502220800108082840110401d90f103520500500c03030400022481030b1080d514004c00441e40d00c0c540d41242c1d44288415a4581c400500358642c103640d40d10814040c190500441404851000108800d48840011600400d00190140507030910b400800d954130f030801c0b10703040002c94035094100c02903907071300c03c805001e0006502c454200030002e0800000b0100951072502d42c400f6561020500d0441c203206548501c65903240c06001c0490600e80b085140c0550340c4020340081c14904540ca899030140c200009442007507030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 221023309 1250 221022059 221022073
    0x30706060b0304031701050a06030c11030a05090901061d010c050a02030f0607020d21021c090f03031b0816020f0307060e0c1f0302090a030f0f1e020901050616170309 73
    0x105d1440c1c03d0a0070301c109503004010300c0301041024013030b4101e141c1c450420f060448600c1c1c5103d0046003180c1c01902030300001440040e41c00f1a51500b04910350142505107030400302100c0100080e00913805413517807141800102e00031001001820007541174050f9000e02503c070b2046204410944d6404240c4075039025005031103440c100c8901c03a8038212046070000d030201d01200c4006009400a40c041a00d90103400c2c0301200c0c8604000c414055440c403180300b20740504414a0341e04004044424071a506a07070081d008012038174543e84000080e800c044e0100d245030002d0103054042e0700c0c00b100c00c2c1145040e4000825171000344030035940042108080d8806443d061a41c00c4100000c50180b50343e1001a6816100892007691080e400340c21718960192281d1803068407074840c1d10100130702c01801c44601d660f00c68158100316001058620f000e55580d2400943c1c1d045500249071043c1c14020360740500008602140101d80300c2c16955030040d08220501000030300708000303a405a0040707171340d0a140d10a000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 221024559 1250 221023309 221023337
    0x50105070c080d0f02040509090d0315050d02100e0d060e06070513090b06090d06090302010f1a0402030c0f04060c0507083409020a02010b0f030a0f030f02030706060b030403 76
    0x3400300c00150b544214214a49440048500002c229400c0303c150350a038280408509502c4000885000f224800000e18800c41c001d10010700f9500b4900c608120880380d035200b0050781d1242007000c2800c0e03070f0480f600c500c9032807645c00c120341301003410300e6241c1c0c8900e80c1428181800000d41c420500e500010b420388010782d9070548162890f22a2145c0c1013212002c40b04104072012259201846092004003100c0c070f007186000009510801c1d40c0e0040d04c51319604e00c1090304142e024400e01d01001d031048000e00414001504030201c00c05200240e6004075000030006603e940f0403401c03100f40c440c1c41c1c10100c0c2c40d2512020010f00c1500c0d8500200c41506c10100c0108800000080540745000d10010344140c503800c40d83c100d243c540354610003448034009194007280307036191400a01403812030795000180103030f464010040c80340800b50300c25020760001d03580d02c404520003481040043d50181040e0084101045c8100d1a40c4507940d400f500f401d10f00040400c03044000c600442c00b440c082e5441039074004c902 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 221025809 1250 221024559 221024567
    0x216061d040501150813021908012429070b060a080f06040609080d110309010f0b03070506071a040f03030c17070807050d06080a032303060607080d1805010507 70
    0x2030060003000c603e15189200041e1003111260380c0840d07100c210507050748899010a56234101e056009442054844d0306011b4210240300d45103960f10092115481000c00000b50003ca203500c3c016002d009600341842030100c0f190107108446550303102d461a956407514140f1540c055011742d002c500c216907940c13001903801c0b8006120280c4444000180c007136510745594101c0184070918084403a441c0500441c0d40610761403140f046501c00c072448644d66890042c0c003150171110464042e501d002e20700003111416071000034200094031000e450642d83c40c0601c0c06d10030b0407036101000030302456603100c041104200f034003000382d400c03144240c800b07114202c40080c0544030400d429414a600080141c000340c052440348802903040701c0542085490110060411015680d140e0000381c6a54071801c0d000e41015800168202c4911449000c003440d00002810842303d48030103400284075003004680c081c24051900c044528585a101c0b0030454002c40588280c52052041804d4480d9403a000000f0041805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 221027059 1250 221025809 221025811
    0xf05030a110607030e03030c0c0406150c260703020f06060105041d150307030302010605090906010f090203100f060305071e0e04050a0212071e0207050d02100216061d0405 75
    0x401000a848401181d0078001c075a003160342c084d070410104425020142d241800105200c100e10006001c40300f280009000581c1d0a9601068101506110b990900c990200d101112503500509400d1684042c0942c000144030b120701d103200c543d1000800758109500004c1d400011078001042d0746003a51810010b544c5d80c011032060455031040c904001180140c3d09038641d43c4204002c10000302c036900403010a240c0440d40e007040300581e6541805001c10f141c992119540b0656103001400c0ca58100618a104000644200d80c0714079000301c0892152200820000040c1007403070b00481c407003503807024010090b20044d65008040b4225000e4a6256094068940c9110034280c40e2240850f00701000e000050200901c04c0c205a5402d10017220160440c00780c0c580030f4403d6039150580740c034500c0c2d0103070707103250424281009660040307030300700f00c143c44150a06540340e4040399041c074954166042179040c541d4103200d50000c9602044085a4180c01195600041009a11505007000c14800344021110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 221028309 1250 221027059 221027063
    0x60c072405090609011218030306090c0e091509070503070e010c2d02091302030f0114070809151f0801020f04050f12031207030c0c12080a14040c0f05030a 68
    0x1c41040200307854244040145505030040c9030403042c05100c0c0d03418004490150340c81c188004a0700854206242d450b0081d0409000d07103c0d070411121101100290054040003d07041c000c0d151200010801240013000c403000301030180c555911032230305100041199004891800100f515032130300ca4100d51140c1560020544d100c010f905030648240941e100c40846407031810352000c801d002540040c0c07243e012140c02004020b40448003c1040d10401d41401c5000d08200f0f02c6a1400c01e403003408100c00c08190f60040c5444c10a11104d8444015041c10044101c001a00051004040c0007403084208a803a40c14a15203000242054842814a0030b03480303844c100301012401800248510b15244101410713140c4000c15103515034445204d03103429074209000c01e6854801000810240982601440c44050510f103040440d52442d07035642d4841c01907590b1408100041d0b5000624120855449a403403111148440000c0d450b181c640041546040c0c0900d640000e40c015000489060010b0408d032026 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 221029559 1250 221028309 221028317
    0xe07110706050c030d110c0d0804210c05030a09060906022103090705130903140405091b0912211c090501060b04060c05070b0c0a0f0204060302060c0724 67
    0x50300d00314040700d82d6000b40300098454041044a4412203d103407141c218030144200c0003544400300c0302c01300c60074200b02801c1c07031041c00302c5c00c0c0401000401161101002c441400c00c01a2400c20014080700c981502103001000d81c80000707003c82e4810b40010310030003140c4040e6104524151601412070701c03500e2003505400700080003901c0d42e1038004001c015561094001d8100d418072559a800035050303c442c1c800c00001d00d5610700624090552000b8048034128949624505c2c181c0342402040c840d0500401030301c442804649400541c00520f412030740ba01c98010090720000c0b20715901c9503111308848900c5641c00c0d400e011040403601801054a100728103421050502a00350040e10015140290049419568684d400f05403904864041c001905071641c4403100c88401d440c0541c0381c2100c5400c03204a049081c0a4002c51040002c2c04001060b805040000d030740c0c0710b81c40410302411a41d00020f42c885c80c040b500c030101c0c40b000a16202110350300940b0b4101281c1d5120225400f22180308040009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 221030809 1250 221029559 221029573
    0xb0111030901080c0910080901050601050406090b070201030902030d03020d0e0a2301020403080a0305040203101a0114040e0c0c160305070306050c3603070506030619030506100e0711 80
    0x35600600729140e010484d007980320b28204244001030b4440d103030b180d005001b103100c103020b01c038035000c091260550002080c203045291505112010f0100610740c0b18140c80c1c03281c005541011a4840d400180d23134641d01404441303004100300030250282d081650401203180c503210402c1180407002900380320281d004121001c5512120f0790488201c0081050001c0da176400f04000000502054001c0940240310f640026403410b15104040c104104903d82010312402e18600300c00d03202c20342805150407a03090071b18a0000503403c0d000d2055018680c86817250310192402c006034140068001c02c6d90702515000c0d5169050003a01c0000394140d10b02001d8680e80c03002d407045c000201075901c500d400801414507d42001d04050a00c0c00e48281c0b689100704000500350480032081000032014000c0c5c0c401c82c09003114500b81404940b0034000202005c0c82060054413192140903510405c00240da008001e031001464070600e488081e04c2c240c8118041020700100042600d8884c001070850044450003034050307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 221032059 1250 221030809 221030827
    0x3080904050601110a05010c0807020313091d01020d02030f090a0b0f04060e0a11100306120f0206070203100207210512040516030c0906080102030402030d080702030409060b07060b011103 82
    0xd00e0010002c9060000349001001d12107010800034400d14810000411a021704c210021303c1440d002d0160810b652091044040010800d07600900780c1d1a40100045c00440c0e08580503d000c55040c59000d1652000542c0700d4000f109400461080b044101800300395243d10908642d21950040094502901440030070081c4482c5080550030900500010a0000c450303000603041200000301103d040442040d0804103040c140b2a11400c400103040810840c0c0c0307030402c20310030058154401401400720f00350000031541c1e240c003501c1c40d60340c001c0c0c100d03040d40c40240c0180c0c00a61024038151007100c03072040140706140220a9540d41122181c2c1c0e06802d1680301d909000e00500c0107802200c0728003903030b0240d0050080d005003600c021401a20a00d501600e0102030f5001c6501036002031840d070340104200400b40c8c800184007400c454062800003401e94800780d04030700f0740c010394016950762400d08600040303400c5900c0140c8045402000100004010030006480308001e40540d40b103550018000342c92 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 221033309 1250 221032059 221032061
    0xa08041101090f240e0f12101d010b04021303030509030a02060a020127021c03031107080912210f0403021305090f06010806010e0a0905070305030c010c030603080904 73
    0x4032050303040c107200c0142e54680000d0201d81420750000010940080d0900c121888609455892200d8508000114000e5280407030398600c03044070707414002c00d19041c0390ba00302a0b00308040c09120f10001401c21a60400301c01d6040c4050700454803500c150b0030501000e40c2860075100f10333606c84c0a92090324845924542d000e03617268000d8804140d050041c1e629100250725100c008242400703059000117039450300b20540c28062002110203140820b03600422400607281c810401020500c602c1802e102c600380c42c54200c0140250b408807403194140401c0100811017000044c2c48010412a0701d4500c50625400b07041e901d4440c2502c2c0d50101500002800010703902500400c1c1251144566a1520f41c507030b00841c103410f030200082401c2683d03030010404107110a1280c015207040c0440a84059498400610380e1950103003c0e0006081e1040c01051014405a06c1600a5540007080c0c0c0d045e1980c0e03003815074880d007182450001c6542800b034026031071403080c0b05080030b503680169031074103107010181400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 221034559 1250 221033309 221033333
    0x509090109020306040b0604060f0b070206090a090608060106110625020a0503070804080715080c03060a051003050103030f0306210c030f0b06180408070219120c1a0a0804 75
    0x18000c0d5030300c58455001d03031020b00031140300780d0181103024850308200c01032104548140d4052084006100018440b50980c2011a40b40a40440300740303441b0107030000020030b0800e4039400894414500040003802d02c001064060480e00702d40c80d1519144100e001168550200b2600b0762101030440c5548032043e100900381d0b440c0c425a41c030454482610075651a46940d01010303040d5822000483c040011000401c6800c010b0802003080000e861040070b0302412480c030240c0041c034400d2000c400210640c4841c2c12500050000911641202c0d41821016008140070300040c0c0000b00f0381084503103283e009029803000c0316411b03107071030304000816000740f0150744080b1011500743d04510000030100320300900801005000e840c07030452074100380041011400d281d140d03c2c2e0422003008108400f003a8070310140c555464050b42c109802125803010b04105a405400c00303030084d005510010203010854175020148c440b803003000c0c4410350100354000d01c0f90060181c0c010018910000140015030105001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 221035809 1250 221034559 221034571
    0xf022511042f130e06120102040b0a080903070c1511010510090905161d09010501030201080f1816030303050c040503030f36090a0b060a030b0609120601060f03020a090509 75
    0x80c1d00346019440303881c40000080e44820301e02804d40f01072003081d140c2a80101111303148070000318600340c94100f01c07104a010759910401440002c8000440c81501402100c001f5607006040d40405620b40419181c0c2c1080c07440e40b0b0340081c074511603080c109141445044d00a04104c419400003a1624051001038010348904483c5401138490039003100d0a00c61414014001c0108126050305404040703c1c81100000c01d2040740b40c1c10b2000400150742c00550f4560400d500b1014440315a481520200100f1b840310701800c000e101e4040502c100c43c002c0001314090724425a0180081c0c1c80345000306155014500400381e0542040100d81c250350b4210006028151800d0081450380ea48581d41142c50f030080d00000e05003100344d098200561400b200706a5000000400800480c00200c0100f00c1c64052140346200b850f82d0340003079a10380d0f034900003501c0c24200e00500a502c04100c3d09403ca484807428894240030541d24200007c01030300074025640519401e9030303105501c618200070004191800b42031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 221037059 1250 221035809 221035901
    0xe09060307230a0605071205130306020f070b0c03180105011802220803190507030210050c070602030c04050406080a08180a05030102070b07020d090302060405040f02251104 76
    0x11480d42c68650781c1d50380c0000c10b101c0c1c9881d41c480100c0e080c55462031042640d01d1082140810544504900d0308000d2010740c0c0d0082c4c80141c4078441106008118480c840e009040f4019030003c1088041e90740000318412640500d13070106085001c0c51890a90343d0a010b10803e41c2440900547c0025882d03018020413030200381c80c1c000b800c0b4000d4981c20300ca4442e41020344e8540002410000f030103803139811109400303060310384145041ca403900d00035110500b40543e0b04c105034a0f5804202c4ca944a00305a486680d040b9078110750343c0c01d204c000301c3c0e266401803003054003403400c0030b4000034440300c0460030b0074020f604040c605151042000f102c81c021400c0c842d40c0c5501002d07181010032252000d201402e6414482e43c0c00310000d003014900680ba200c0000f0504040103880703e0140010385418040e10100d60701500c01140450f01c00035100c029025480f024404001c00d840464045000c0c4880c00010030702805030440b107240e01c101480b0a442c0040722207505035560000105405205040c2c41000207980b201e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 221038309 1250 221037059 221037119
    0x10605060a0203250c0914060d03020307060c1e030e06070801061b03030216050c0a05060c07181d240411010809010906150812120609100302030d0f0e09060307 70
    0x5110100c0110941251b03403076590701e652602c4101050443d6640200d012240c4644120321994001e640313105405008000e545c0b20308184407024000d201c0b40d420350440307444010079a246184003c0c010607407603540700d050b0b10070034010a64642c003070000c0a058500766038610030000444e0243c110942c50800080301019420020a40242e041c07214804040780314001514014410104015040e0100d8101c588107480400c0400c216450000b020740844140203000c501000541000d0b8000b0420100110708440451040641c0c900e00031a98022400400150b1202c001c2d40882d60320803500708403401000500b4030341607800b0707940c05050b0b5543d02100b440000709003008140c0d110002c0c1d41d0b4200503032188014200c030903c81c0090038000c0181001c1d9540889042400c059040103c0c900094902402520341802007100410000c03c5a4003458024007220b01c00000c081c4000c5c1196031050ba0100000c014658a1045180c414201801018010014800142480807100c4c1000300d080c2c140c010025200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 221039559 1250 221038309 221038313
    0x90204051c08130b04090c08010b030612010b0d08070b010803041a250501020a14070f030c020d05010e073b0a2409111201120f06021b010605060a020325 67
    0x201c20f00301414840c1c13201601c80386011a1441034441135055007050000590041c030442e5516404c0c0c0c2c0c0c0c007240440300004c46c1303954000d080d4014040105540d40012240000000340880c0301c00a20407284940c00035980d90f0790f640c8400e6102d01840c022382c1c4600c24000c03141503541c1680703005040340c0d028203450001c0002c256507000102d19565002180c0fa44d4005c109181103e0708001c1c0942125045121186400043c1c1d544a00d03030482204000e090002d0382d40094150344030b6001c804069607002c80200714050384100e4541c0e0b104040e01c151a0064050303401040525015a2421044140000c030680b4860141030391181c00c1030f00803c44c8400e25950280c00f6681c0924448010b02d40d49090752419140782040340079029103100c1c8002c0e0710420410442842c0f50500002070b07a04584490b0840e16600c00c541c6000260403201e4080600328500100d248494030070401314000200c0c264900030403216584005129040c021244400c000d41c2040c03200c5044442529003c640b112125058101c12050503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 221040809 1250 221039559 221039587
    0x801150804030c0812040606080118020a12060605060a0c0209060d120e060c010213031a010f090203061503011d0a060b0f07080909040503030703050901060506041401120c0e0901090204051c08 84
    0x40358141c0b110364450034108040842032142c00b502d80302c403151150041c005500440c20b00c370680e100d41010780d81840c1491050260650090014160007440f86507200c0b850b100c010200c1e1041801a4400c0c00800042607091800e801c0d11006070707500c5016105652003000065031251500320005030411000c0040800302c00302032000300801c0f61a13608906400d415800d01400c119040f203020200040003100611007210300c4428041152101500503076680d444401140d44010500b0344111a504040b0002c2440501000c03c041050003003001000d0943d0344141e00825100c2c1c0348103030041004e0410030b68000c3c40c808402004c1b80f50140704014501009007020035000b0000316810b0310140c101200340045503170b2501035a500040020002c0c07186c54100000250a4461403107102003001201c50b010751036900550303403c4100380c0c80c51410400c00302d5000b000742c602c4410a00b02840380603180004140301c0b03450b10030b59096034409030400c40f0107100e8511270307803100d00d40c614283d518520510540c607080d624 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 221042059 1250 221040809 221040811
    0x1020a0506010b040806060306070c17040b031302030d080613090302150c0307020d030c120209040e0a121412010b0f0f040b181e01030b040603060614010801150804030c0812 76
    0x140c003c00350703960f80381202550170400090a0148241c106005001c41c00b54000400d515003a004071401c554070300c101c0b210185030700c41e47d4060720ba0b13000e0103c200000b000c0106913807a1624000c2e82901d4081c0c040020403942d110301220071a5101540046680082d000d652151401522034012202043c01003001c00402c00c0c0308031103c01d56680000100111540d050007046070700150350405020a40d1004800790050340c54500b100f03202c1d503011400c0c000641e241d4200e00b5501c000d0400742c40c0c1032503150604074045002074103c0310101d900325410962a41046044840703648a1810710300080e420214060300e0303540440042401103c00b4401310117260714041c0180003c0950880150740c511160007030030106d2010030589031040f00d00001c110901108000007036054842460f00181d01102803000500400709508050b100c94540480481c0744082d00b409a89500c000f43c80300c00035a83d0301c0c01003001c0c5d1800060448002003841d0013190010707010300c1881203210301c10351000303040a600010401d42d480c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 221043165 1106 221042059 221042069
    0x10090602151b0d06030501061208030c030c0702030601080607020d0309120809031b0303060f030706090b090a0504050f0a0e0c06220803031e09010618020901020a050601 74
    0x40404040000000b48494035846100860010004000751301048406620f01540440e0b0004524000414150302501d29495a594401c6d802d209070030140c08a0342c030420610070440182d9003404804c4c080c2c003c810040143d4602000000e10306038240a0550625160904546c0070910400a052025034203003860030035070301c5811816255108261034159403048040200024250100046000302001c0728a0b112001e551001c064543e00607104120200300c040d642081401001000790410705401400c2210340307641d42011500740c1d40111000fa428459400401020040c0791040c0580400010000c00c070404400020820f03e11402e8542980005d5048030380bc08952046004c4000c0c00081096980764141108a0072403030605032180084901400002000c100051250f02d044452000200f0f0742c2020303024501000358001e01c44581140103110074000411350402405009007 = true := by decide +kernel

theorem cover : BRFrame.Cov 220863309 221043165 := by
  have h0 := BRFrame.cov_init 220863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 220863309 ≤ n) (h2 : n < 221043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
