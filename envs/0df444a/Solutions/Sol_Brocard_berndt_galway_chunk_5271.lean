-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5271
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:18:53.734985+00:00
-- url     : https://prove2.me/submissions/38478a53-f373-4bd6-9773-5a0653052128

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 947841726 ≤ n < 948021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 947842976 1250 947841726 947841773
    0x15050901061404090203150d03090603150305030a0e28080d030207030909020f071a1816090e010b191a04060c020d0204200d0f060e06011b05030304 65
    0x6005000c0c585092280b90503030394061606061010700d1000b900040c010b408000f19101e13802e00703039841d606503012100c3e01076110b00d80c8552625000500760b40c50328010341055014208200b001403000810b46501070b0407410202885030380c07800810010407002030700e44200c40005010b1880350380624118804d4401e0329080d07a003020110b04098050b4880d040008001607451340c410000303580258040d0050501100c01d40d8603100c0c203070301c3d2003003402c442c0c5a601082c151407000780315140340c1007100300100d108900040c0640380340c824007007442c078009442a081d5640c1c48800c6007150807c20740c0603800e000742c014a049200c000c070f49041030340d4800c0350050844c2c10000f4001031841114003402e5404544540d962803840440a078244186002e64020490304207885001d150080e403840d03034030411440c600c0b11545480b09070341c45490040c6c0d20f030a40d075844202c0c0b40943c00e10160340f03500d901543c000320a003400030540800c0903040380303540307102c0101900500000c4117200c10003c231f0300d800030301040c4d00c40b001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 947844226 1250 947842976 947842979
    0x15040f050405090a12300b01090503030a03020706090f0c0e070e0f2e120605040203011503050402060c011a100e090f070e0402040801020c060906190209060c0115050901 74
    0x180001c680c2e00355010700c2241e10120a00c000a80c8940f072a150300110381ca011102d5010030300000c400c8040c400010301c2011802c1d00038000c540002d00c07840003142001d20300f8001c242d1914020030344074442c02c01a0020140c0000d001c03801d0015a4000590b0580e01c120351010741c010900384107078000318070b010b1042c81640d52000b01d20480d10035149c14208220060503090516121010040c08000d00ca00c446080d102c102c0944d41340351072a0043c0c1216854035141c240010f1704c0500c3e4030044906a0b08030a2050b88140010302004006840c000c2e80c4603080d040000b40c1d41c88900025655000b03840510220790308110b004049503c0308424101411400ea6440e00080600d50080e00c15505141c0c0b2150051000c00c005a042c44072030482d2178200c04542002864004500040b1301641e2181d041540f451f9000220000a02010081079030b015441b80054525800d00504058001d424008402c000b2900452040b155a54400c101d030054210240200009004502c65441e80703031080c0304051140340e10340c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 947845476 1250 947844226 947844229
    0xa060b1b0601120503160f020306071107080d05030a0507051309150905090c0904080c01110705070f06020d0e010203131412010203060d02040e010b0a12051b010903020d1115040f05 79
    0x1c0c250303c1164004055400c0844100480c0d01051160b4002d407100b85040d46500007603102803182e140940d44540d58051006250b00400c0c2c07030840c580c0e21002156010f189081e100310340c8003040d03940041e01c0c800b020030326840d00e8500322440e01a4080f428a88041c06200194000781948052821013281d15030003071199481980c28122107003101c0541241d0070045c1120313070a2401640c4158800e2103550070b28184810b6003100ba00310380309200c2c502c0d843d0f180090900180042041080000d01042c07241080c8507040500003510341017889018801d0103102071030211103a0080c400d55a808501d07001c6a01100d981c1c00c0c42060b2010100300440c0200c1d0560313060b203080701c0103008583c82101d000d00700c0703d10328070f041e030030b0100030524401c0b881003d55843c80000400d40e6211608002047e42000200740001c082c1041810403540f111200204000a000300d0f050341d800043d1001265011994074031805541d040c401c2101941c4c0004d10350280c0168007104405080c1c0b000713072003900c041c41e103142d00c0e9544400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 947846726 1250 947845476 947845499
    0xf0306160815010e010503190f020406030b2b0804030b160f090e15040f02040306051f06080a0f0e0f01060f08120403020d02030f01111809040c0b030a060b1b0601 71
    0xc2d40c02c1c00110050440e010700e5003e00003c41e0031200d05020b145061403001c00c01d508449440c850740000d00e40021b402c100340c907818001c1c08288142102e00c0d050f80000d80840a82826120b650404030551380804601070110303000c161002160070003c1d6032894500307400e48400d40141403803060046521514110b02940c410415841650600340d65900c050302c460508070079207003401c12100d03407094451400403000c443d41c1c00600021031051801160b2400c042c9010022000c00c500307800000c221620040210551007000070360440c0a00344009101d001c1d21700c240014016001c61106944070303581c405082800b056100800300e580c10110900040d0726841d849440b10100310451141c070409220900141c83d10402203c64203100604455200303040000782c6003501c0201104c48042c010214401803414008011411403400440354903226107050703915842d000c10240126406402d02100141401805510440113442e0080520391600740780c1420314040c203103600c50b102440c0210800040c054004a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 947847976 1250 947846726 947846761
    0x213030b01060c121101060308192003030402130207020d032c1315050d03080a0506010305070203220b04030c080c030309010507170423180601090e04020f03061608 72
    0x403002000e4a04420401c0302d40b41c041c61700510140d542c881c8000300007007506004283c00d6001301c80b40981403500c0382c0c002d0001508140020b800c2c1c9145203071109211000300803030354060ba0440781c10110820800390580240206180290020074400070503080c036801c24002504500044a500502442d014206801d01074262120303410003110090310404124a401100d80010001d842c488010340da000083c48118040741d094001c01d90010910440000c0c1c0d0140e2580b040702803c1c140314504140c0b0001303507a407080b00c1c034844042c115a83ca031003000c890000f00034003d0918803403854a540c0c40381450480442c03103124039503241c1314041a0300d24900300803043d24280c000c16112641000c0348d949811b04646c034581010482d80100300001b0580683c0c6c142340898103208031045070401c010400500c078501b05400450340000603400c00708800c80c1c1c1c2c030100c0700b0107444051011024507141c0344040f48401040c0b1550f2a03041c0140c40401c10b64903081c09103991910000e07a11040180c0782d010100c110034501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 947849226 1250 947847976 947847983
    0x13060506041a1512101502010c0806010804020f0405011d0a0507020331062c300a0b0702160e150d0c14010f0e0603010512100213030b01060c 62
    0xe42c441e040c40f454801800d451400c186694035103010351803100b01c0c4004208844001680b03001c0c08050001d002a00100800d03404a80001c01c030303100f0010030103001084010324032070410030f40e400010115122442482200040034009001e1540c407212107007465520307001000101110705000450b00d044501515016080f1a0081c0d85412030001160740210401904080c0d8140a2081303034191000d10700d00d0300b00409203903a9082281030b4811135003c4007e40740400c00e200c11200341c280d51840d6075250020f084040c0000c2c82c04200541581400c0300e04142410050480c0142400f03170b81401071003403519204007426030989541440c03040c0602d01c0b0079482d02810058951100016009480d20394180d13411082c014008407094805a550000700e244030340042c4903d02e40c00021440755604820264040306540c10000709a01001001ca40310f4001403280920074844004120301c9a0b0023840428050704203040103541e079005c3e2a6600c1c0741d543da030707102c00c4550340c00c03072400094110321075040300c14810790 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 947850476 1250 947849226 947849261
    0x90504020343030c0603090201021c08041514070e040e07030b09070b0f03061c050a061a01090b091c20090105010f05090114220e180628051306050604 66
    0x3401c0c400c034007c2440358803c80c154820315003080380740450740c1160803a0081c01da481c80103920300303490080e03020409104403410542c100b42d00701a00031940441c0c01e50240d01c41c03504158000445000a001e045050084604d40c0074846000c811700070300d66003080c4145128401c03507040755560361031b41e0141c0c451070311000c0e5a0b4400f8000320304d583c6004000d021080c0e540083c03d4241c0000c0340c94060a05a001d081220402d07910300300700300c04803036100c60452042c0003400d015034020710b814426141344c45280c0e1094801c0180c401e907a01c41404950a80300e140380c0212008071301c00c980c0c1d210141458000742c00355101d8000f44000080741d600c1203014a1052140340d0f05d007410800705000560b18511000380007450205c0600c18012210101c090081c03080c10790641220000b03142414012030301d10094601105104d0020b000c034000c0000040d07440e04081075413469400c24500c0c0c0c9a00c0007070bc04100004c4001390420050018062074101c2e9182e40c40d000b21410480b50301c0d00e404000865a40188043c072119 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 947851726 1250 947850476 947850479
    0x12041113060e04020f0f131a15191d040504050f03070f0507270507020a0b150f030706080c0f09031903083102010302190c0c0806040804090504020343030c 68
    0x6080d80000d0714040040d18155201240c60740012150900030b4265184030101081841c0355034095200128407890f0b60030070703024241508045159812f80602c18500030b9807030700041020441e04001011903c080030b002d8944034a41407a1030001a055080b00345e80d41d220f5408041180c100c0b040c43e150903420080a024030b41e601d858550000703840020903510a50180c0703440703940030030012a0400e00c00c02c2110120101001100e080142a8480a03104c4c0d02a50242c603061213103d81003c02d99411404030403219840d41d0030761800e107020340306107441681c044c01360065000c0c00d200709031154800f00d846510349046582d45c49411640407407010102d50f040449451030400c540204080c1654070500625016180540e0805115903542041c40854005400d2003c200c0078005043c11540c081c0080380d0251141d0300b07194483e00d81c9070080740141080569940b0103e021940c08016801440f00030007588a109038403c03060350300d8503608101d004030360144000412680e90011040005480d0b00081150007503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 947852976 1250 947851726 947851759
    0xf1305070f020f072108090d0b0a270303020c12070303051e06010c03050903010b15031008030703120b0607060c121a1302031305062a12041113060e04020f0f 69
    0x201e9260080d80c010b20201700007c03d94841e47d69466150f030141840603040e080c444d4000044461010041130441c0c80640f400d040c84004616400e80a41c1625015803075100071101c02e4101241004008101840050f40504040d05074100501c1881c0c020701000200400f40701c80684138a04542a50014a100310106c000038001e4000d010700303a50241c000103030b912a8401103813504040300d208031000c0c0c0001c02000304038025a20950003030312a0201850070040075560113040f40164504107416107444440c0348400e9100e68040e80c01c0c10f500010b0034000034490541c00703080f280b9012811861141044d0304c0b00700c6170b6249007403540e15400160095111000044440e0000d40001e003160a00d580d006070000c1c0419010440d19000d42d450300a200c4484485032122103007403403280c00180d95448144003a950340c103404810b10350701640012050981ca0078a038001084e100c04499401101c91030250b0100b08503c901d508203124520940f03500c4180c080031810821015484508140c0c44540d065284560 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 947854226 1250 947852976 947853029
    0x1051e09040c0b0a03091b21051207030e0f0a1d0c0d0905060f100e01050409031e0201090201120e0705060f19030b1c08090f1305070f020f07 62
    0x180682c1c445080540c07034104180e1103074010b040b80c0c00002d40b903561060038004841803040030003614050619403146400c0290981c4c11030b545501c40625003001c0301e0400c0c084e0030311507040d0203404021401e50b56031140ca00945141e0080e074519000d40d01d600c100703405608042c21421305407002c461100022100002100004c80e00050800648a005108078804011a8040c42d10010701c141c004d48024504810201070300742e0010403144030200380790b13010009034000b0030146055450998002c01c281650741400c1d01c5410004402d240300550604200c000c2d9941988110074440c800d90724800700b884113080e910309582200350a001d031900300c0d040402c09031410034003c2c4503145900002a091001c13800c402e201c10803040f203504010a03158005071419181c18040201d00b00c0071900c1c84d40100380e070740e00c4614050203900e1a040c00f56541c5043d080e07c580e11451601846044d040040c001c6141c5602c0c000c01c3d1a2070140c40b18098412040551a908004200d6400780d400e991802e01152107103181032090b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 947855476 1250 947854226 947854231
    0xc2c0604060e0a0c030b030328020a0c03030f0507021f11120a030c110f0303010f05120709020a030b0307031a07020d0212030406060e2a0a0504090b0f090f0f01051e09 73
    0x34150b071b4000541441e14140080c0015885481c0c1110084002c520106406803c05030315404640142c083d440014655280703242c00d032a0146003145005107200300c01c0d0380d1842645c0c006580044000300e60ba444415070102c00381c4551040e80d41c03014032041100d5860b074400399610003480e581400e204a920303107486584a0900100207140c0b90403e80d84250031141040b800c003510100703903000040140101c1845100c5000180b50694440010212f0f048040d078443c4080c1c0580300c14140c0000b41c004080e8826000013007111401400d48005640c0c0e440e003005100110740500c0f00006a1a00050040c0c6c000710f030360004498141c028104501c5101c1d2846410340c070040044990a5455501041d8111303400b207480c8c4180d0b40d03c1c2d9110250079260b04d440c02941041202c44801000800000081d141c0c440d00303440071610382e6100843c1884440300051a0b0b079480c0c482c2d594000c840c4108005003a5108500710780070703510f8104801d10903600c60701030203600701c001c0c003a030962014444016409424030103919036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 947856726 1250 947855476 947855501
    0x1b210203100e04050c09070f050706050603030417060f070c0b0106050c1207050c03070f06050f07020d0602032a030c03012601050112150e12070c2c0604060e0a 70
    0x1c950b41c85015460b4001815501078401c1c0c1c0c018800d031030300c50401c418a590482c0c61410301005403200740400915920030003100404242d02c80c1c01103035560300c0410a9801820340006642221200d26418694400302201ca0400c018030b51300c042104540a60010403425802c4070741124035a090104c1511154064250b1401030311444240801d0207543e80060050a846070003e8680d1481c22410989051440d4206d40540341086c0d908100843d00b00007240c00300d22411603e00d4480f0b005000140300f40000140260a0034000010446010019031110145110846070107078481c801e5140101a8002201d01064034102000148400342da0702d40d81c1c2c1a108913080c0a0300d5000c200c4003856084d20401c6e800701c9071600100c891201004611a4060707010508408108803c2c3c582c01e03000303565040030201d50380540310700003000d00c10300401c80c1c180c0010345908510341c001c0c003a0140700a041e0344000c9001c010481d01580c0070079410321f854081c3c00e00b01e0310038260744d64464540c1350f01107004011070042c80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 947857976 1250 947856726 947856751
    0x504060c15090606180b01301109010f0908060106080406020702190612050f06090702071505090a051804080c161412060405060106230c011b210203 65
    0x40799030001c0e40c0612515503224000120300107140c14101d160b10300e02404800300650a007803104040c0d981c80300020000001c10f00c4109040580d40e48040c40b50103103607420003074241c14000c1c0c10031060006070051002000030f80c1d507981081d4a00380125000d801e41e000c1c424407500003400400c030703d0344150078198006000310300051525196900007951040590700d0341601c606003071010000c0d40d420003100625144801001c2c40b81c0c2c5040ca070791604041e0010316240c41102420040b400c007a100f04039440c041c0280d001300105040c201a8058a5a0440f05d022132051882c040046074904180681c020700501107481031004d51141d42d510603164020030501450b82c850340d0007480600c08402c0da0071000b0711451041c0b5050803902e2050002c2108107076030300e0089078008800d02c000128002109411915285070882c0c1d40207503046901e0100104c0214410798800100740f40d040034006500071a5184d5100f820900710209851040ea5640500e06030180c58241c02d01804403046075507001561b0110180380d0300d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 947859226 1250 947857976 947858003
    0x4110901031a18190c05060903120d0212040609021c1e060f063f030e04020403021e100e0303250507030305070b06010e13152105100c0504060c 63
    0x4640c9004a004c007030051801c4c0880211003400b00801d010405003e041c0c400c54644a08840404d5458003050100d003004000080c1c1480b4581c00741d4140c41401040da88090070b070f810542440c2d0050300c000d0109920400080004500701d2144c6141d03448a69841f44071110020040092031203441c0d103c07501034139100e0f21403191248030a824032907035010b8000008a564041040c195407404071070010801c1040c900c444845200030b074051144502c80c00e9141c6414020404c2601c08600a400f0342e50009400a012180da421000300c0c0d440f5118003003405862803d4003e08034401210405210b03101e07180c040d0010480c01c0400910502008600c0072000d402c0f600c418442e03558940b40082680c001e4001640c0821224100201c5d00e5025822000900c0d00c222101c001c4000100c0194400c0148411030ba522010021000011b050100082c8064045480d400002517621115644e141904032031900644c484010000190310440110b01d50a03550142041d080180c00d13100311280391429294510301c0420f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 947860476 1250 947859226 947859271
    0x703360603180c051c080408010e07050a0302010507120311040b0a0f08162f0105040210081905040204140702030307120e07030b041403070516090c0e040c0e040207060504110901031a 80
    0x407c02000002d0002074490500d0000d2803e21049030003da12425141c030003000036030ba0080c1a251055040b500342d800082c60460240d00608a605614100b8003000c28000360310803082001c0c2c40444480c2e1207107034802070f8880382200c44102c100d0f950a14092901d506070346140c0f14402c1c9108850042404256929051306d0000628089030340f010b1490391140c00300011401c12010807072142180d4101903045062801d58155100d42d40c01c0001c040503512400141550390340d81200302c03040c0c2510f08105950800201c000d440c0d501c00c44003100032801c80c18944200007107502c1140405410f50f0081c0c40b106003190b0b40c100500c98098000c0e1041e60440580030200e8505000800a0900c20001803803a0702c10300b456000301100c1e0341d02500c1060318200080240c540c2044502e840114200c138005595101c040382034922400d0311848039041803021520718100315050b0f10442c0202d000d00382ea030495544120411021040901000384502000750f0b50b15600c0d26140700c80c50f040015602e2482e01e0183c0b100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 947861726 1250 947860476 947860493
    0x27070e0a14150304080f0d0b060a030b090c07171b070617160e0f28050f034b16080706050703360603180c051c 49
    0x3040300c0306038008180c00c2940e42c9000c40b02d55101080b160b0002d030840ca029111100309010b2003944030034001d070005140c04105100d0b8022003154000800d4517469103e0f50400400500d494108280904845800300e0900504842650600c40d8401a00003401140815001460300b042102c0705002824410800e81080e0511207103005c0e208a94880d42e0900c59000c85100111000d00840483d0804142c080700e42c030b40c815071040300c4030403d41e0321030382260100f004a6500241450791220341c080518208000010215060044400c120b981e54045c070320f42420941ca80c0e42c01c41403900745842c0101c407402044210138048070314041c80d42c400380c11085454030070001600011100d2038250070107158243e54012001d400d0300940307002d8000703041e030a050403006445803145003030150500091413000c01c000007102040c00d200c842c1c1000a90386003503144c101c10881c0203a60042c0f0001c2402d201c5407005012a041301e482c426504512042c440510301024044400701440c2180c1e01c00c0070000b124004034040c1d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 947862976 1250 947861726 947861729
    0x81306020307030f0c12050a180f090f02040b0318010b0402160210030905120d1d1609050c040e04030c05010903020c0f0a03050a061d0a05160527070e0a 67
    0x250007855541e0141d2a0040c07040100c50980c1c3c1c00d02c10014005400b0843c2d01a10450503400b90811030b981340035102c4181ca540d06401c240c075034600e421481c040754610184181c0800c03559204420b10080091102000a902517400751880243c014400100e4142d10703d043d4290656203a00000740c4044141c1c0400e0580e84010802b46c0e048281c006100708609203a00d6449030010940303401c1140d00d1441c0e5816488041c8060b80644e1079102140181da05000d036400400303000111050994032410031084c483d103c06200c00040920b064805001441103014019648114a040100c500d064104007000f40b502e0340150055007004801402000059800d01c0345120480c002c1e00281040e03840314040208000c2c034280002d0080940d8041000010300c000349000170a07621001c085240f0034503242e03e81450101d1102500c46100d140c0041c0c040c03003004100034040f268031007c0cc102184d1900d0034056032007450118201d07504c4040701c1c00b44000100d000b045401003000c4c034120740c1025108002426a814a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 947864226 1250 947862976 947862989
    0x60e0105032a0712200c01020615130e06010e010b04060c080f0708071a01050a051302180303040b13060302030601020c040c0329040f140412090f030303020a0801050402250813 77
    0x30b2000c102440083c11181005d4401c00c80082504030ba0300c000007521a2405413005c0480441c4c40141e0f280355a0b03035803c1c07143d0517404007801c11100100305600c960b2040281b0a001d51034402c10000716512400c40115410786405031610050840e40c0d40d10080c09a220500c0c001c41001c0030b00c0444001480c000040c02c40c2d600641c000c0340548201050358201d860182e00c000d100c0c810000c410451900c1c0c411220301610031200c0c0040e05c0310900c4030740180811030003003841c1e0705000018001c00c810740315401802c000302d000041400242d4883c40150100d210507078410b40075038015083c80400e4030b03007600b1071005031003985008900041d941c6130b14801c20001102c030040c9130000e49501449810a441001101000b80c0418407104c1d100b243c400b80b503004083c0001c1c00c040040310140c404d140c083c140c880020300001c031060640d07540d1b0381401802900a4101e180010703a41c00c00000b03940c505802a2150700b109030280c102c07517404608281904a00940301260010b000348403001d960b141c0c074462180103211 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 947865476 1250 947864226 947864237
    0x2031e070f0b0a09080303011a070501020c0303071101050a1802091510050c1006030309300f05160f090b030f191505010e0703050a0f15060e0105032a0712 68
    0x50000039104c1c07070607030300019810b038014001002541c00b05080d1440404800400c56618030780350921502a100706071450380b852100000344142c665205400d50307503c0240c54020005078503541400004c5e540340204d0001d000d070300f209480e0054907001c8106500446a65400b403214002c850200b1220502c0312162008228003207540940410140580c010310f40311801e04000490070360303401801c0f11364903004050640707200c030031907007082d1280070350107035030300e00060155001d900b80c2d032814000c1c0d051010812900750082e041510305052100c080c000903610b40d038110f81902410020b02c100208450702c0b0320b0b64141300d039008070440c2503403d201c1e0480340748900e080308504102c642404c50584005442e050343c081d20304401003103034801c4c900702540c11280600e00030580ea140c0441c0d10028080007948518050b18010744601602c954800800480300039880d07110780c1d000d02c2c40055a0354001200e0041300c1f40494001401040540b8240c1c00307114450b0902681031100503160000c0c04d00758401c445000c5035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 947866726 1250 947865476 947865487
    0x17030310062a050319022a0109030b01030609020406080a0201081807050a0b0d0507020316080a09032a0605070c0504090f0507080d02101e0f180c05040b0d02031e070f0b 74
    0x15243d1039684180314075000510081864420780410031a60360500141f4a0003100301c1d00440e8840c80a04005540280000c034070341d6144d0400d0001003603c0c40c07040303100301d00d01040051a8040072403681541a0161605a11030b9960210006180d0300c541c1e60300170034000c1c04008542d541e00c03929000042d01c202c420f40c607111174201e00301d00101c500190a4506542c001d010841e1140713070b20060040202c0d40540021381300e001f49101a5130910b8079410042c14000940502c000d40d101101a400d4050a8181d05441d11350340c0d9503007901c051040150140c940d202c40c030030501c110b05190300300080c224442e00700d1072012451510755500303180c20380c2c11086440e0070100f8403440da02c2d8104401d0512040060701002104aa403d0700360754054000d102186058840c03030800d03180503003940120104541900b20424859241c43c10641b9034955018061040345041d501e03c00909003c0030b40203030558003070001c1101c802c2846080b05030752200605006188901c81001c80d40d0020980804020500100702c41d40304c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 947867976 1250 947866726 947866747
    0xc020303041b0b03071404090e10050c030c0d02070f1b1419030b06041e0c09140924030a0c141002030d090204060e01030b0117030310062a0503 63
    0x100b5500c20030041880090280718811440c0d0032240c00803550f041c2801080e490384001c10752401940d10010301181b415803e84402c03140403540244445082d1400c0016030740700d050a0748580030a81d55805400c1050003c09400ca005074001c00d0600e00640034441c050520707644454501c110308100950420400f801044250211960000341280071560100340e043e80741e8088000e0f03a09480003400490035140424842e40301e40d4003803080381c40c0b10a040750076802c040e16400003901d0031401c3c00c000142070410020702007400c5111b580e248a40105442050303156442d0300d03600d0481c540d03d40ca00c4410800b5000c1c040d55820031091030414425910000c400b0b00d0a44107100e03c20b132400165004909245480c500c0b00e41c0403088941c428981200000c0e4440c642c000300340200000d4114118441152002005200c2d00d2194103040301c0710b040c11080c6101a182c08151280400c0d5920790050480c900301b809a2401121100c160100890300074400300002c0d90003201000b884c0e80160b4142d0800244403558 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 947869226 1250 947867976 947867993
    0x5060a0302040e0a0908032e08011a04111b1510051c0c090509031318240308030a11070b010e0606070201020c0906120607090503010b101d03010f0c02030304 69
    0x5981000070010441c05c0d4461900e94440200100740e0a1560011004100b00802001100d07840344400c0d8090306499003032190003413145466510804410f107000500d6450540200020280041c0f03100f410308020800c4000f0502000104159074011500c41c1d14a140c11101020300c5500500d40c5d45200610309400e02024680244136140c13905001c691850205000383c0c01442100c0f40c40c0390014103695900002800c602403071020460700d03040301c04002a6104e038001c0c0c0107050044050100480d05c0c10403401c0301c00c44840300701009004034408040000c2421000910340c002d960030030200b1492107520140c2d08651011101312881200b40703005000c0c0300803002015600800548155140591070780021b9545d10701d00302510f110710252000548592100302c0074007010310421040ba541810400006411401d060142c240258607244030403c181c03509544c0c8062406482c1c581c04145a0301e00000a41140002d000d2a0550748403440c684514a01c0c1c0b060343c1d01c46800e540a551139040078902002c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 947870476 1250 947869226 947869231
    0x80f0309040513111e0d0605040c120c3308070906080105030c0409140604200a0608070305090f031303060b04021207050d09170a0f090b0313030905060a0302040e 71
    0x41444603000144c10760802d001501c20888030381e46082240c0740390742d42240c0098015900305c004e525400d81086840c3d000180980d04c10106200d805454100c016031024200c0b2019125074101101000940061038051064001c600803491950702d0ba130f1480d102229110190000298842003000b08066000442c04c2c00b8010602d41001c155240200003543d034203035600c0d080d02c0343d0b5607407148500300440412148058004501034a0b5039240a00f41140d54003c0d0350001c012060703c00e8050b03181c074504040418150b138001d480b40070a0351105082180240002080e01c20300740705401e18600100002c0001d031070222101e0f104010030344d0a41c6403010968124840050007280140228a5030030722000c0100c6c0d00c8007031450016107540c034a4020a001c2c02c643d01014000701002459004240c1a5000400e02030b030054440c4d88400401070002c0f140c80d8018400d000a1020034404a005a002000d006401c00e0003443d000002545a8001640541c0505010300110364009001c00c035008155001d1907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 947871726 1250 947870476 947870491
    0xa03050a030e121b01052a0717030603070803030f04061806050103080903160b070308100b0301091406030a0f0813090501080309010f1103070308061507240b060d0510080f03090405 79
    0xc103050140d4007030701d225540b10030400d4501d03104c0c6180040754100425a180540c021101c0e401404c403a00c03a158858ac000c1e210103010b8000c0c07a802192003400041200c1c0208800c803141c0d240e685d5070382c0f00c4c43c0080c800880204000e07002001e102c1e010510305d0144134065401000c0c819660189a01014034140408110900c2c2220b22002041450f00c4403003550001c1c3e0301418010010b985403501581c00b000e66411030519480c001c000450f1341300860b40070300b208000714210b480c8961180d0b420150394904103c0000d24580c1e040052a00044064001d48108004035040f07100c5551601100300540d10240c003c03040340e500105c0c0002e40c960340144403003603e9a03c2c1c2403000340e03004081c820740d8480c4940280502030000b000041001c0b5103400002c410104204981c564940c5094a0070851003410400b04052014012041180c00035252181aa10700c800500241c54241014004005040b00508042e03610489940024040000388080002c41082c44051586d4210b490200b00c02c503170000e031200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 947872976 1250 947871726 947871731
    0x11011e1101051f031412280903020609041a060703110c0603092109090406141807050415090507051905040f0618151107050d050a03050a030e121b01 65
    0x100042c90045040f50242e070f0b04100381051102c0c109017002e2a01c104002c650046413030005003c2ca0783c40080440c00b140c926200705203903400b4803079181204c09891a00010358840020000810580741603400241c6812031910502e005440b200002241a00400002e4000c43d80c2c1c80403520307000405001d05451041c003110f43d0303400c60604480351a034840c1d036a0300e5041d0315401da0405020b1038200d14152840c00c5402041c010140c54145440710241501801d01c1e00c280014101050f0454680d41140300300345200e000400070145448200009010b0300881c241d80a0b00040d00484d003035065009040c426074280d01c400750348608049180388003880000b0b80300300308481400140030b1900000115011503015103412100b11b00c850b091050201c43c598014442100c0904d5250141508103107200c11200c803640c1552401e0782c0c1d61043c03201d04d2100c120000e099410000d214800030b400f983c0580b880c0541e600e0002065032148800034500440c00406142c0c4c900c01082c0894035555002d6400703441c0c503151009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 947874226 1250 947872976 947873011
    0x1b0f0f0406121e0c050d03050c030a0519020a0308070c020f0406080c01120b091306020c2d061905090a050d120b0301140c1b1002040302090f0c0711011e110105 70
    0x84213090b00150088600c1070300501d4041c0203151081c1c00750f4043c0c1503940142d82e40d130000b03100701800e00d522a401342c10f0124800119244124008034082a020343c05071100a500d9891020803241c04481d5101240d01030048007010b180ca480c0e901c80e5001a03c0c041000f041440d04010024199007800d40b04000c800b4180b004030071050300c80c00c104a07000403405181810100c000c4c90b04d1300290185210050341c9200348044020055542990080329949881c03543c0d541405c0178803103e440e07000840351414521300c42c800818160105501803a4402140400d4808104183da5401c0c2004490301000d40000d84d41144004d81c07008034841e1000c4043d044000b08031500c00410b0401044400a0601c0300401000c80c4140d03454050103111b0500d401c0650030b6940c83d03400050100d0003500705020980c0a10480c8c03002814a072481ca07260f130300070705141d845141010700da079440f5003200000c101b40e1303810840308900c01d1900f00481982b510701c00c00f468507400c800314602c22015003154401401d40c1c4264408850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 947875476 1250 947874226 947874233
    0x12003040f0b1e0901030e01051005010806270606041211090109050106080402101b080d0e060c072a03080712020705100809010e16060f021b0f0f0406121e 68
    0x40f868941c019628000e85546a84c0b0060b0000c0c120f00461f088254208010000e9280d501c41e142c10545000340c82c1c5865035110003040c02490703050400b60040700ba1070508290039000920152540c0700c4002000c045c9003d0300c88800c074076960210a011162200c0c16000324401d450105d45880c05001e001d00c04020944c90b1820041c40b408015001a006001540050701018429004d420f414032545031750031442d8085140c030707412960089078040030b442d2034a40007034624200840c0c06070040c100340000b00e0074010942c868109a0140390a00d10b429809014005c035144c1c004054600150b010f43c220b5601e0701c400c3d052400c59008441131040440d0407408040c0a203984c0e03030140900036015494142c0c41a40c0d01c11003540100b090405c010200d200d80702000c402a0000c0300c1720340c16103c0950f1051003400c0c905e4000d90342d0350300f0410241041c562500403d0303143e003080200c1c8080c0b1f5000500302045013134008003103030454905400074140108400c1d0f02c003041c0041640404000b160003011420b903d0540c0e107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 947876726 1250 947875476 947875507
    0x7030f300e0415080303010609091d0d110a051006210210030e010b040f02070302100501120605150d11010212090d0b2a0a090506091e012003040f0b 65
    0x8001c0c1c41250703101860540411800b24800c090034018084a60340e5031140d9028007400068400c00c034a01e414030b50300840210140051075184100c0c00e00501a28031001030039074021011064414040c071594903081d0209000b0440b2a886000e0203c001a600342028041c1907590702e00001c095600b14642c51800c01030321032180c040c40031081e074a0005850690103000c03e000d40802c040303413a441030512030071011005080d401051800d01c02e4080b100c0c5d0403401008030342514024807030040e0b000041c600c142d010403550b0300711951003002c4002c1d03403001031403040001d04113145100c02521818070134080d1001a580420906080c0c80114007000d080c2100c0390005500c14194000c024020801c000102e681c61004403900c0800b500031004034082015000c1984d052900308115110002d00039603400152414103404441d15404050800c002c41c006030410041c168200b0710342181000760100300d24443c5058030070a0200390192001456403903280c00340c115440d00c90f54210000d14181002040012903604 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 947877976 1250 947876726 947876747
    0xc0905060d120e0a1d010e090c03060a0f2304171912051e010b0c01091502030402211515062b0c0203120a020d09050a050127110307030f30 61
    0x200d01c7e040b0360f9503ca1034000e003031078590103c081c0c040c0b0401080c0400921180c02c440d900342e5130100104038441c1c01030f40d0003015007202e00c280c160b0000400301240218155020003807941103001105407825408100c60019121200080b600148a028130f011880c4001d0003481d401994050403a94038010300c1900c00c801c250b0620507450034840c0050303543c14403542034000100968110150444106015054030302a600c01c0714124818440010030281d80340401c038004000302840030040241d1205290406259040544020340020514891010070b9403050018404a00e600c91811501d030140300c000000740a1201200321214100403000001caa170010541c2c0d010310b00b80788400c1c040d8541e4a844402440350703201e11410300e4141001d15062140000341c0c2688a8400c3c40200184100804180c00b0b001c28980b00e0070b0344070103804500022070540018110b85813802800c2d10320345640ea43c3d520311070070300c04130048407642001c011840103006812080c490801000104400700380c401c110040580c1c55070b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 947879226 1250 947877976 947877989
    0x25020d0507052103010f1211040207020301140a0e010b1c0209280c020f06221e0c0302010f0c050d110c0a0306020c01180c0905060d120e0a1d01 63
    0x4600030303050140810100859030400c0281030b010480d0f0345903140159009000e4001001315002000411a0719600b4a1803419013000d400c00049480e0410000a540b002405a906640341c3c4000e01c40c0e00c0003685c28074010780356079000148462058143c1406d5035040000203110318064485920f030301401130460209243e040740c50811942e55200b040001010084c80c0e46022203000c10350210130711890b80000c3d030802c0e50340c0031a07648a40c89140e066580760101c075010508045250403c00302000b01c2c90842c003242c482d006180b00908a83d80c40302d58a20012000d0301c4007505200c0c104259600202c1e101c80d82c6090389000ea01424507500c5e11039450000709105402c005280202110428080c401c0702d880520040050381200e60341e04140780a500040b00420b103d5103880403a10740c0125802010848030381c824141c062140c9041d00007001084000c0105030850a81d00c1801c002800d055002c3c81c100060340c075643c44010480c4240040400345030452100c81038107040341800707414188500c5044a04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 947880476 1250 947879226 947879237
    0x2040e0c031009060e010e0f100b09040204051503011403030412030c0c05060c010e0106060c110607050a080301030c0609061416050304080d0e090a0c0c1106120f25020d 74
    0x11400d41200584400b036000001d01c3d85400e00126801480c80500e6040303505441038805240c43e41c03900c0d00c0071030b5020758810004036800700e0304000c94800400500103108000700b00608260303441001c83c980c00103511844020050000042c4101c0e85403043d9949007007010f40046040034104a041e01c000800040c01030240306841c6000300c200901032211b40042e00b4050000d40c3c55a0140700085d01030800081010403e50070800c0100d0400c1c0b00301c605800c01ca4100390590000c9010b1400d0100c6075005840030f0f07a0074041d5121140c08204c00d000154021481003c07011501c62030103800800700743c0a40c0103c420000180503000c0405600300030303502d80700b41d80090300400f00301e10f24041d443c41c80381e0703840083c441c0213102040034820340240c880c1d008030720182d0301c00c00700d070342ca032000130040704c68800791440880c94042c4c034403000c12078186461142c660082c051902c0c0c054800300003200481e0460f130307890441c1022010010601046828000251001c0b400c0342041010403002135100c4514080703280030001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 947881726 1250 947880476 947880481
    0x2909060a031116110a170a061a1504080c010c0b040212011e0209120a0314031308072d0804050f011202030702010603121d040f0902030d0e1302040e0c03 67
    0x4003503000312202c1a109103d1600c802030580707856210348840f2203070107210b4144118001100341c001050046444104809400200003c0e030710030300105500503c440001d145280c8040b19620788408684154008900c1c0d1500c0d40e1410000b54500401065820b0411019100c00d00001c0d10a0080e5a0043d03070403100780c5241e4040403e154010003c603a4428540c01e05000d084441c01d5040c0d004000940096a12460701e0b403d1821040c1d441c0c441600082c00508205041d0102500120156400688040c1d0782c2d400d040390b98030f400d1103030303040440d00741c920406141500603110560594000d20042d030030940700c045486621030400764040d1b4800c55009620b080b55040c01c07680704218465440011110840d12410a01d01c000d00a140b1400100c4401d0f280c41d0903040034a000d0b0405203481c1c43c0d1240c24805084024061201810107a0310645045e074503000d501c8016a018004240320160302c1ea6104d084d0720b044010440c84086440348403401c07900c1007009100b075080c000c200d2540085d1030310b003155503074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 947882976 1250 947881726 947881751
    0x180c090109020922021801021b01030b1504060201141f140607060608010501030c1d06010c0201051b1c0c0308010306020f0c160302011706010c030c020402132909060a03 74
    0x2440c050b801005103426200b0030104c00700140d4060168010f110f4914100d0b00041d0300117a90314a1550f180000206440559212542c400c1d0048110b082002c0c084519210100810207101d41150f044500980d44892000c0704071040710504030f0380222841950706045800b80403041144a85008005441075080040780702900c512080310326096210808100381551400303807900800c07003070200722204c01c2c0300a00080c842c1241140528217411520b49554180c49544c019505400c1e01b10717040781070000030b0200d0f00d40744001c459180c0202446001400e01c8540300c0c5404000e090b40c810307460040c0046403c0a00210368820a00740c1500d0b4807090050366030140102c44440d90103581ca00048510a07440c0b20b047d000f1402841000300e80c400e0b200e02c00000030406aa0000440c120395107400601d000f154040404d22a09404500c1c600140005282c02d0807980c10100589858000c5010103c2d80368141c618501a07004090094180280c0c02c0d08100da0b1100140c10b0384101d05c00002055100d00c00080407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 947884226 1250 947882976 947882989
    0x108150405071107140a14130b01030f02030903130509070f03241526041e1b0f05090108071503023006040b060a11071706180c0901090209 61
    0x420000e01140c04181e030750501100101040541c141c00b81d0b02031b81d00000d8590b07544802c030396000b070000c2160400e4140445850000c22406002904040d21a10303c12000003080c4001c5000c1c00c0d402000d183c5d100249a46200b0040e9941e000d680075002d0a000c124131191f021700380e071940c19100c2c1f0300490195001115030440b08591051048003081800c0001030003070440019411100c0d082e00d688514124810201800b5991441d40c0c0c980b0f500741c2e030001400550b0040ea000200400c41004821040c91601c03201c2d10301052a10540c1929101e420a10611040d003080074000c010071100e5415540c144001141c40f481548120030b180c481103400740300c0300c03030082c0c055480000f030003202c0021001d124024100d41e850341450070400c5404142c007081c61401c040c0502d03040306101a207017925011f40420216555482e02203501454058040003144100708480381d0710604511800610442c1440c440e00852038410032071a64403a80028070407a03007621240800390444000f55001070700c8881c201d000c43c44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 947885476 1250 947884226 947884247
    0x105092412041407081002090334081906090309090504110f04090309050906010516060e0d050a02070b030601120c021b03070807031e14030307030b010815040507 71
    0x10842004101d28035074000c00c0c000584558083c011400310f1114201c400380d150072030350003842d2440d00040300810308010302c1d400030100c0140213001c40c0c00580000c40080c43d404400702c80400300050389080c80701c4032450000b010015181c41c6000c0c02520741d00041e11030305500e40036002020261a1900309044c076000e11141001000e00c207005014a140500d49540390383e84c0803590900c14900c100c0c9056441c140391080c10b001a500da101c1d028102c1c20704d020041c525800400c3c960404c038040040300d504c0c0c400107108000c9a8451140403841c0103402c0c800328140302440c0821020021f0a10404600030344c0060410200d644001c0a02d03640c1d00d4801c0100d9100094083ca1119181452075082c0050b034000740c40c1d9494889941d000380c08400710010182ca9102a22030311034590f00903032081c0040342c1c20201c0c0c40c52240700640d546c880e542c02c030b503100b0b8442d06500d6403222481d0008820400c071184c01d4040c500a04509182c49089031074144003c910695138110788501071341d90360000403003e900903030314001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 947886726 1250 947885476 947885539
    0xf0313060b030a140616022d070b030f0105010507021804081204200a060905010503090a050d05040303110a030807030f091407090e0304060509270403030920010509 72
    0x856002440c204160b013240c1c0842044458413925000900040000b0561046003446601030b0961041e000a40307151848005030f2260001d0304a01071031240f5104122680041c401d20070620b441c0d1904810740c25028805a1140c0d040c0501044040700582ea2020076025142e6642401c5016842c1c5083c0703180a030044115032541501074005200622032484c0c20602c00e120b100d0400c99405ea034240078800d4110f8184941000f10f50482400c0c07040b58010310145511003514021100e0300c481d140c403800d140c1030950015402049001074148241580841c0c122024956440140000310499030020901840107140c40101035440a8140914900360840c0d04065080809078030401c07200d40d400d5803034402621404144524140b80030a89030000310030f07102203504d981c44050500880b03000b44294070403060550560444055580720800c594012200d01842c0256800540d0780300c1458918100181004904071a54040404201c240e80c001c0c00c0b10400301c826144001c0d0403044070011079082d000759050781e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 947887976 1250 947886726 947886733
    0x21020c0c06250b0a0b0d0b010611150705040e0702010c020a0f030e1503010617060307030210050c010f0501150215010314030403050312042a1a0c010c090e0c0f0313060b03 75
    0x10b6050140c10307840c1501480841000f00300d000050b400b000403403110800d00400d1400702c44e00402c08940a10107a00c040d24000040c0c030401080c618140d0007070103044540700c5c0805c1010030103002c1caa00a85005911240500080241d40400c2d080a076680030801c0006080985003802c03802010b1107440806003c0030040c0590145114911080c07440c0e401c24062440000d190000440c08080c60803081405154040c000d009850b045030244620005106030701c1d0103219042003400c061402c2441380b01c15045100c803001401c4e50420182d4001c8a06c8501104e085510240101905c020100006811641e00210125481c2109100c2c28190b024035400500240400308841903a8003840302658030a0348a12848108910f072511a01844040c100204080a8684c1c10034070024582c0d43c400f0381c9680740e203015a420b10810904140c00d54007034070b403220700085072148204524140126903e1300010107202c030078100301c003030390001c2c1702804001c08003008407448095620030f11025034002c0d2001c48002c0c080c2c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 947889226 1250 947887976 947888047
    0x306020a200f0624041107020607110f010c0b180f12070b0a2306030106030c14040515102a0c1502030405100503100e010621020c0c06 59
    0x65118102c84001c92954010f02c0c00080300d1358410322209988034040030180100d29000d030240401424a8540c80490480410a54001d0380e54080a040c06038450ba00c2c6550f074030709140520080011a1000c1c50601c40d0f400010b500290718011070700c1c4e018000c5c03138142401c2d03000c4a001030701d0134150300500089401485000d011080c0018000c01060f80990207001c0e9075140c6210140442e03280d90810302d100c80207903032406c011050100c1125004040100045081503e03a05ca12104274155400340c1d819810300c2d080000c180c01c00380200307a400400075461110102c860700c041101d40a204000c5001c200074090451124484544286546a0605a9400070f8240c1d4603240341c40c00d00b44d00554015022070352461645a1000045071705542000c0c0031002a00c0c000f5005441c203402c0582205005d6a02880109410607640003850080040750b49132040c107038001c0036203d84000c40940c0c4044140c0100300e141e003028070001e503103004102d040c0e60305699079903442540030078034409015981401c18200c2c3c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 947890476 1250 947889226 947889287
    0x90403080405101a0f100203030f07031401090506010201050a1a1210050a020403020a121e150504080a09080724180f14091b0c010b0d05070305250306020a 68
    0x1314640091010383c1d08120000d03083c82040100035018a01030010ba00400c0051030038a10302041a4001d05503080c04540001081509800320000340c02c1070446590301d03002c1115540e424096030380c12030080d0f44100091103c0d40c22044017810744500440c011010312602d00b8030060200001c00b10059200d4040059092843c0b602010703600920007030348a10f00351800860038802d1140e20055860780525030300c0d034805451602c1824021030072400e546050806502d0b901e400414000d1a105910400e07000c0c1d501c41e648000a030003d89a0b42240c8000d40c0030100078000030b01c4081c00d2032106030a080426908800100c3c003100c1c0c51811800540120891100004560160500c580107a40604c40c103038030300304020f20511002c2c400c2151107a25503a6138000c84410246001d00400c42801450000b06000c03400d000400c0c0281c420302400c941da40d109200800920406009128007404026030001c008010507042104800c03043c000909a554002046606103000b00c0b000b80101c0d10409504d51500030510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 947891726 1250 947890476 947890511
    0x6011b0c0e070e03060c040909021c06060f08070509010b0310120b0f0705090306180c18061c170c0705091e0106020d09120804030218220209040308040510 68
    0x1c2d01d100208080e50005161454041071103031180085503013041c2005d2034030050701e0261407104403e982114a02840801c941041d007410001540600c0d030200c1d50a14007100305481c0c40407070703002c2c1d8400c0e089141d0034080340d070340c500c4414112007403806100e0316501c1d901c0d07002e007005c01990b00071503800d118208010104065014510f2240001e281140004d540c3c0791400d4a2500c607a0168641c15082080007a4603910284801e0740d443d0700b840c04a610400699000c0385161150000f2460b12843e218200031480c80c1c100c490307002c100b2401000502140703d0380e48640c1500654166240400004160015424400c20040c001400020311040031814948051501d0444a607034a6194091100003c60345c0350000a100308a014190303030300e0b10001c7c5060700fa080041e60a020454180304100400800350342c6440c03003980e4801442c1444c00f402e0401c03144885214030002000c8180001280060703001d6a40c5401143d032094041c1001d413559941e42c5006800e0060034090403501c6031510440264804080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 947892976 1250 947891726 947891731
    0x40909051506100f1803050f0106140607030e090a1104032109050a0603020a12020a1119080301050f03030702180105041508030a031d01020d230f06011b0c0e 69
    0x4856060540c541e882884000c1ca2500b00050204d0150900718180a1203032401000c060b0a407000b4204094403680d8103030800d800c803804540704d691564000d00140074000c101c00c00c103640866480303242ca04603030380180440344290810341c4030300103c3c4001200c2d05981c0e00500310742d4242c10003240e0b4490310780c41d04984c0d00326200c54040080000d040d400e240c00d409031260078140c8400500754280d191600304210041e40c080e03c0100e0801000340e00d0b00081c40f09900207041460040c0c6c5a4440c8401c2204040e45041e0440c4202c142c10002d03c0200004201c5010889054901c159406d1030640c100b800800d00c3c503c1a002c000750403111003081002032690035140b66060b20400c450900c44101a180c80d15003008c1c031805040300356001009140c03001806680b000e4400d0580ba4121002c007141e03140703280d08a8008911130340c81d42e6280c9030304031040d2119000c214800c10400030555113030b00b0590114007403031200901090600c82204400600068100c094580c456448540c0c000240c0d1586072047d04450203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 947894226 1250 947892976 947893003
    0x20319050717090a09020a0309020a0f0303080708191d0a110a1d0a1d060103060207230c12161e080c2b02061209061005010e06090604090905 62
    0x40c2100d40b84401840422140e512800400c0700000ca8140300e2400000e600c1080c0d442d062542e110960401600c421180500401c210340104200e54914240540100340040100d030410004104101d402500001c00142c4012020000182d80102808203c0f411204990312080707485203600318000c00112680045115405444807815143e8030005402c28050700c0034903c0184480000180a41c90761741d001007848403002d0000d140005200b2400d0b03042c20020380041e2241c0703400281020900c003210144610f244100f06041a65000310030003292115410100c0c0d07442001c06807031402c08c100040210800e0130410450380d40500e07030303a0020074101c0001c05902d08082e000032880015107a501150035120303048058881380d686229079080e01720001c55140360f045641c5261020314050f03200d040150048102a40c0f04004030300340400114541031004007100c1350b12000d4501402180d912a491004462045c4c601c2e686451003040029107a009a412600d40b941c0b4222022091110000c0c52040e441c80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 947895476 1250 947894226 947894243
    0xf020414010f03152d03150605010206060604030803100819020109050f01051c27051b281d010f0b0c030a1d031c0e0105120f0402010203190507 63
    0x490580660543d4003200200d9041540b044040062408081001000300071901d00501c02d403c41d405c0f110408951504141c88040c40c0c450a036040c24110310401021b40800d00051005141090005010744601e01000305180c0300800450071140c001324200300a4910301c810307100c580000304440303403c0c0340c0c4000e8140d0009010510003d410304150403c500640c0c011b0b500d091400c11038200404513802d1000c080c804045c1d5501d030450110201414076a80040940904c008d020041d00b007151400c401e80c800ba000d4503d400403040565a1081d01c81d000c514801c84040f5141014400c00c00f107190f5091b445110310384081518524004404008903050396441e07004c0d403940300e8813401c1c5005107000f43c1d95000c0300b940c0100580d0349403600445981421110220180c180c8000300030119040446542d17684503a06025081c0d2405c2c281c00c41080d5405490a107001400c04405687e0400f132910050084c08101c3e2032880802c00350391013441150101d07a00c41d07145e80401d85a6600044c4a648110403c1d1131054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 947896726 1250 947895476 947895497
    0x1804032105061011070b0d09021f08041b1a0a021c0e01181205010b01031d06010545060d03051c02042303150108070e0a0f02041401 58
    0x1805445002c0c020600903042032100c50642d4410f482d601d8070020388043d144209240006d01a41d0303100240351030642200d0200700c0940740d00c103016103001102e1242c446085802c2941c111580e0005116900a4001844081d205c085c0d443d208082d0403140c001035650964500301c0c19000421070000c0c84200c17002c0d03007201c01040103108000390824022010500241004040140c1503104102480c140340c2c669880c201186c1e521010b01010094041c400c0714183d458007910301043da0903100f8000380300c0184491020000070007000d540c650320140a1248103441110328181c820380315251006804000d02c1081e0107213481030540a68500c2400444016100320400054260400c00c0f21020030a41c95101c0c00e0034400050191410345081c4174421407159424000066207258002c6401d03620440c010303a00d030380e41300c15000b41402c0441c5050650b101c5803074140108009100013900c00c08591000901b0050360301c4004030b02002e000140701d0040700500200740400d6a4007003a01450102c07000340c9480c2c5503072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 947897976 1250 947896726 947896787
    0xe060109090206040905090327030706030213030605040f0203120d0b0307050a150216060e01030609020708030609040539030a051b030c04090606170318010c02180403 73
    0x322070262009400c000184010844540240c10954011002900707407824101d0b42880140ca285005c0e80303003c1c1c0d9824800b00120281020301c10400500002c4c503065140c01c5c2005103401c83c4240d0791100400c415035070000182800304405080b4511540103041e030340fa190b11004051116000103019802c0f50313290805c40c00d014640000d95408485014165849140ca0002040b810043e1411008194013802400807254940d200b450000380204e5140e5103214040c000004007110055007006015607c10006403011a4046003038070703482a400c4075511035076560380c40c1280c10303c0314941a8280303503112007101030404800c0014203240d4050941c00e90a00d60154410140c1e5801102d50142a9801940315004044801d415410507d0700140c22036450594542c00308007201c0f600e81d8251405680c40005025400c103201500c064507901d0001542492820b0071281d68220080310040d040c00907101443c02103458260015810a00070010103190f4078007400e001c0d10301580703a15894601440300840400c032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 947899226 1250 947897976 947897981
    0x4170306090c070203190326011412100e0604030e0102010c1e0c0c08031b0708120304030e272d060d05100f0b060307050a030923010e060109 62
    0x8400c0144001c846450740407209600364400a01682c1601400a10741e5403100441c0c042002c252280d0b5920340d12042c481440204d245480c61200411230701030004019805444924450030503048401e18030345402c1500d11494a04003901c07500c3c1d8582460031820380003134049603a40c131480c00703500c80c411284000c4004a08032041d101203e000720f01d0100c0d0301075048a41001132030080740641014002c10065403104218100c5607440b9a40552000407421103c217041c0c00400183c051403001480d00301d0506a05548908818141144d00000440080d061601c10758030803809110107000300224440d40150404402d0ba104010180c001e4031802240d020713a0000039803000102000600300b1810075618481c0050b1401270002940714412224400100d403090180380c900525039000080c0d150141000c0c50141e40807503013001d110340414010480240e4110b011035003030b9115071900040c03107490f034900348240800d488150014618448044145441c055009401000043d800c0b100280c1c0e0300c507965805e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 947900476 1250 947899226 947899231
    0x21b010801050916020f030f070515040c0b03150a06030c0306061e1b060c08010e0714031f03080f1209030412021003020c0a030915020c010f050f04091103041703 71
    0x100312100ba00010000d44c65204080503401051041d6241c0d040c400300940d01d16000981d0042c04194006a40da0070800100140c0c0104014421484614540703600d1750b003000340c454490181c150b10000005810f071594040c40328481e840c01080c44011030b440e04c9000740140030003110000440c1c40c1c80d2020440038094100d803200c110042c480c082e0244101d031400c070b644241c0c504941c84174607071200d000400910a4010405031500c81d6841c12030640c504500701089071405003e1909216043c120640d050745e5881c00c49500c42c044c015005000c0128040100e043c204962000c0d000b680041015004043d180004140440c4258144402030300e85071002e640740e100d54400c06450841100c0a0001403c01c05044600f012807800c0050400002070b810500701014018220700141d0303040b506100f01940028000b50f80038451005040010440c0e00207884010210102014400041145a400b05a500c00c0380d015045030841070000752054100c001607a0411b03603003103500c1c05080c8580320350044140152403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 947901726 1250 947900476 947900479
    0xa020a031d0318010309020a08150c0306100f170a02030a0605040b06030406050c070b1306050f0f0f0a090c0f030c060503070203271e09090d021f1803021b01080105 72
    0x10710f0f20311203210f8290244981c420316814161100368503000369a07680301b44001450003602400c44100f1003000c80c02a107000400880c0000c2050043c001c0c1900ca0200941141606050011404420304d90a641c107640c240504444031801a00708911848140c020358007401c417501c401d001140e20351040106a0701200c490740d811280a000140200b0075541002e50480c0150705194a0840c031510b540c1c403029021940c1c2869055941010010043c4601c521540401d080040c002542881107900c010b10502034425620341c940c0300d000c1171400c0410b0303000480e1250b1000d4001c21083e903400d08804102c1c0c1500c01506c0419240e10000741e01c1e400b40c0116889440c1e80e0380654900090031454000003a202c030b1a9030205a480000304c520b079200c03030904d04601c0203d84c0300c5050a0364010100085820700824009460300000e00c80141983c0020b00c0708800071203c0030150320b100c202c1118000505a40c4940c0d1440111480c800c0181500815400d2011000c1c8904a10100304403005403106003080c410207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 947902976 1250 947901726 947901733
    0x703020a021e0330120603120c060720010e01060807080a0803010b0a09180207021201020901050d09063308010203010b0d020c10020307050c07092c01060e0a020a031d 73
    0x2c4d1145400810309203040c0004841e503a4a03034040c24806504d400c401c3d00e03040c100207000700744007252404201c0c6030341c480b0407c18543e16025001c103000f612400f019154030240325258044031001102040b4551a85501344020000d8420f15110070f8040c080900c10305081c1d001e05600480d03000008543c3d041c0c05908041d00c03e01d564070700741c1e00280c59408030310100104280c0c4207000c54810484a64000c840100714005078a4144600403c40036506215000304560f00c1004400416600101a980a0070742d000c4000f1b8000e00303504210380502841c1070b000c0b0240300181c001c404d2000c502d25015600b0500803504449040c1c4903080d075402c0b8070080c055400d25140900c0f0701240340c02c86070001c0031000500400c0c0d480140821042c1c0c01a44c005544002c00f1800c04510f55801d2002040040c0c003c00194200340090344481d1620800700180c001070522a040e0000003e059410035001400240420070082080f032401000000094100d01e11400029003080a2000d140c1e149150f4401302c1500070024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 947904226 1250 947902976 947902993
    0xf02031311030c1008041403041401030c0e030706030f140a020a1d0109050d0206130b0a0315030b0103060213080703030e12010912050c0c0616060e071802030711030703020a021e03 79
    0xd0302c0c0d1700001801102c020040400840e1240010700c050002030150500c07081e00131801400140c207448078900041f040020b282e40701c4143e643d000465000312405400d00085a8102025a2010709190141c1c0c003400700501d410300c60707089a20360080c04554003d40e10380101828400020100d40204000c6500049403423100340064648052411400d0f0302c001c00080c0340400d510058145100070781e10540c010b000c08254690400d4060080c4501c000d4007410034510507046560303a41a140041c00003400c19a4007240c094441e40e508040180601164004c80c0c0d0381c3e95407841e0040103030100c00c18260040040070800410040305014131200e540d404052035280c04101a4100c1d04c5401c202103d601c548920f00030041d036603e41d00001c121411125800c8032041029051039010b8803e0340307051102d40d6010060400200c141000954150b268100000d6078984401100700d410100140f4103406034000000c80408058000441d0302d2007034425201000e0724400c41e48203403030742c00c0611300e40d6030182c01c052038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 947905476 1250 947904226 947904259
    0x17010b0a030b2d070f0c140706080705040315201207170f16270e010e1b070c0b040b07060506090108030706050a0e07080a1703040c1502010f02031311030c 68
    0x1c0c1c514000c17546160400c1e81c07100c903445400300540b89210220180d0401c08041c001c1550060505a10000340d0421601d001d1556a03190840d0440d20005241e4175514003a540c244903a071161032070800c403050342003500c40700c0e106030034018010186d60300c40c0400c0c4c41e189030501403c080d85209204404982e04a61566070b903007003005080346020825410030818103c4880703110784025907030300201712601c810301803030b424021210704001b41a000b030320641c0d5840381004145c01c0103910100e001030709400d40c680c80c1d580619180b030203418a6040440c081c480400c01140304400300d8094118240100307802d000a40f100d6080c0701c02c002007802403000c0da402c204100e10110b41d1030341210350001010100040c8915002d942c890a050a0340c005c9181c5402818025090020040600039101e80c0c03207101603d0350406607540014400d4070700c81d1820344000019001e0010b030007075201c0007010070101001d46d540e00e02100c004510002c0038104842d480c41c020000b04d840d060001e1005030180010305180103c0d0b07201030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 947906726 1250 947905476 947905487
    0x140a03060b040e060c0918010e0c0c0a060203011205010f0603050c0f06070c030b090d02120403120201140106030e070603110f03181f0605010f0917010b0a030b2d07 72
    0x800042d0401d441d00f41002d40402d041060314032500c124111036807200030b00780801c0300c07020007001e090411189203401071006800422101c2d8000e00c0c101c603a15524140c0c0c01c0302c58117040100c44007508151000c00001021029000081d4680744100001c01c000a80368a58204480d090701002c0e1107a40800c181485904203000e60100e10703200280010b041951a9450111000301078000b26010030700801440a001c0c410000314104140318000303020000500003629400e0b014500c40503006400c110318000341d03e4000c3d03100000c0d030103444003420025038403820050094201d004a28880d072003a0800050744038801d20a031200d50f4000400a03140c0000c1c1060003859070005004001c4041180f540358083d04020001061300708241003003603c20108001442c421900304ac1d00240c1444010480784950941c03103c1981c050b50300d8000324045251003441201d005203a8a15420381007061900c02005200c01881c041d48200101e8031110800269100100311001c40b8003071180a840e4010041099180a031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 947907976 1250 947906726 947906741
    0x40c03021221210c0901170c0702040c261b13030f08220509010f1809030e030a03051201121a1302131e0c020304060e030c040c18140a0306 61
    0x805505040320f400507514000303084151561121218000360308001544c11000d0701d81d50045c803500001ca03601e040580c031550341c0700f414002441241c1c3c5444610001d80190680401d0040214031f0351140185010b6000c520030056030440c118240e0b078044405a01c05160440784401d610b040d05440e01491580d03104489440450b00302e41c0d10405200150243c4213485030200c03100070b014800e1059620702410700910003810380048038a080340d800305000010150011403d04503400c4800180030140741002c64000400303400040e03060060159807814958018003030a654035440e01141c0762039995280d6170312a1407034884000c04034082e02400d183c103084028240d95101124000888904682d47d00103842c1d18428601040f1040e990b0520780c440c1728840003003141c06003141d4000c1118206034200030750341e1701841c490b5004120500c10382d41160f84041c8040307103016801900a1207154250074010704055150340742e007021a48030000c0001d80b403101c1901c041c921079010b02400c418604607241d1901a0040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 947909226 1250 947907976 947907997
    0xc10150605030a090b071206060c03140d11030a0b0906031507051c0c030204142d0307090c0f080c091503090a02120f01240b21040c03021221 62
    0x2c440740c0c000810311148000b84031b13501c141e4070442040150341001c0704030340480d0040d001f0880c0d20385c05800040c1d080510103412a80c40c41c6980d85031000c2c5601c24000d002c2c90400702e02541004000e100c0b81004640140040100842e5044503d070f840609140e5282c1525584005602c62034011404071406000246484250b079122001d0b01c80f080402c02d0160b40c6245449000241e00050412011424251041c4075400071507050264028070040c580540300c040c081c130241010344254416482d80c0070844400200b0328010180040c92207018003524514101a80f64045515078000690030070148048401030040181009480602844541d00907040141402098412031441801590750001c01e0718121142100510140100e000c5160070f40303030029181c01c2d480e600200e02141c1d48034514100400c0c1c40c07600f505941c070342101c1485041c8920044080c814454004001c1c4418080311086140c140c90099a40743c226100c1d12341829510001c004100c0754054ad03101c00c40000d840750800801444be071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 947910476 1250 947909226 947909231
    0xf07050f070b0108070303030f1b050f070609060b0f0319151409161205300708370c241d0106030215030a06030807080c10150605030a 59
    0x1c0d15590700021030800e801071070490348051803c0040680c140a5040c2c07405000d0403d1200c00034054007520a4405011100309001c80460000400f41c03010040d100542e40004007408042100c3c1400002041d41c81d4080380152603664542c3c900e8100001c007181c1d001c02c03021210012092985821001c0802c0f0180018030b10346400c00008211060070045005e040000043d082c21021482022445070b4aa40315031030800c0110b8284002c1100031078211600c14503140c5541c14078100d8180c130320743c0180c012500c170005400401d80c481449510707005814140e40004e400700b20300003014110390100440445e010303101801e50b162141c00b64802c440c4684540d201c0c403594810354903a144076260240d00c1d0008030740b43d42c0d581e46101140c2d0100114140182c22800c008000780750554020803010307850100c0420386a24000007081e000441ca80c0840011500a40241d0b2101c03410300d4411030552009044140d40c0c81000b16080e1803101c18425100d0001005042840c035500c0d0002c280d07080d81006052100265 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 947911726 1250 947910476 947910487
    0x903070807030206060a05010f170a020f190215240301060801020d0b0f0a06021e0c0409060209180f06010e1c1a090a05070501051b0d02240f07050f 65
    0x3690030001d03010080c4030b40c0291803140750074410700210810310b52016040054400f00075008030340080448921201c001218999503460540c2400641b051030002c6602c0c2000080040c4029039168591341401626401e48515115040030b000d2103100c140c4e295808007000d8200503c410451000300215034902400119901e42d441c8004c9089801200d071028140e9180c0301510090310344880c54280400d41107400015070750070101d0003943d5911744030110400600f030140000da44041084540c0806800500a02494103240380480c080e400048045025000b0000118030399028500c0c210b03c62407050746000201d50710a801111a0032003026010b401a030340d43e81d0a800e044c200c0001f101c186001d058009a0170094100110203144010420b28042d04a4048403000036004905c1c581296405d01c0d209441d81040c1106014020981c1c5800300b480c400d20100c2100c1540200703a0f8031a081074100d424200d0086803003028095007007200d44034459a600d60002d9089802040540a001032541040703041c407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 947912976 1250 947911726 947911733
    0xb090f041503150605040516050a020a05071d070503150103110d02042c09030405041508100c03050c0406170a0e0607030203041101170403080603100c0903110a05010206040b090307 79
    0x81c505401c00d842040460740310320f94500082c00b403000144001d0710100440d00d000380d500444c030840c480c602005c2000001b01b5452452080102000321900807060b6000a41e845117020403402e6064103591100c2d0001000805860244054a1169080c0e01107000701100f00c000450007443c42c1e5a00d1400b20300e0074401d50481040c02c1c8041c1c0041c2610009110700080d006040d0950f1950b01d4103c0c0c0c07600c3d6408001c1005a4201000781c40880b02c09490101d440c00840c2c14000c03411640380c100041c540f041c100310030007480842c0c200c002c0440240d1000c0003142c0f1a03240701c0005201d140642000b281c44615600c2001d0501c1079005d41c05407100f4000100540f1964845090240541f0300c0340000c0d401105000a02102c9003508030308210900300035100890f41000c5080300c9000600150501043c480001d58644081c440b90b500740642c1482080840c4c2815405000ba00940c001601c1021442042041c581404c071020410307210143c0081c1103503600c55440d4602c13090002d20122850009110342c0307000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 947914226 1250 947912976 947913011
    0x503120702030c2d010501050a140d1403130807052110090503181903020405090f01020409060f1211090a090c0e0a15050f211903180b090f04 62
    0x113240d4041503481c0344002c843c035070396140f5005800d83c8190380d2610004220940d122806a007c442c0c140b419400d0801010000500c5031440c10b40142c568408040841c0c142d903401300060130b85682c404a43c460007500c41d00407903601e00c5140036454000c0325003205049001000200c02d241d1060010445e030585600b030440b01c1c02c0e5012a03c4c115910b501c0072810311889680258146450340c1f0a8031040d6415100b1003006c087d80d100b070f1001038082d66980002c14800842440394028034040c4800039540c49596404040052106101c0d04000d04608140031807000503134941c20b00c80607004a00800850b4070041042a40c1710054020a14030303a0360441100024485810710f0020b1090a980e5105032900e03058400940311f108080400560844105001c15544c0c6040452000d1054920b9a0001102c810840d20000400c1c1c80303020900c2210305c00e10340004501c45000d401c5102c1d80d10070321a070446803c0c4042070006800356514804082c880d00c105c13420807500042c88401c0c02000482c400d424844d10070324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 947915476 1250 947914226 947914243
    0x1f0302030d0201150b090d0311160e060a09090804031e12050d11280315030602030106020d0c0f1509140c0307140f040e0102070804170d0c0503120702030c 68
    0x540d440c0c50b14000a00300d20070f03801000382814944181b80c251000000358100d12400402010b0001c05000e044e10b80200f0408a102040030103801075480d51100546808604202c6501d846103042180100c1c0310041c5000e196062030340002600d007807c0c00d564038804108000451a094400881103c401088200c2601100c1c1540d903162255501c0780e502c01c05c02550700000d42e00280a40422140340c44070600720400f60140281340f2890030106000604034003a0810ba2050901c00a1401011080c03041a500440c12150075400f105c4892004001c141c070403180d01c400c09000d580c405c508481c0419042d000755a9980440000043d04e021030b1380e59101e0091030492800042e62114103001c0312403c0c10002800900355070680740003503269080c00a1500c54141303420b40d00843c2c071156103000c101002d4052b41c9105500c031100c40d0700c81380c0780c14556550460203041c030341c0a40301d501180b0700d03594040c010b60050b09400c24090342c500400d00c8210706003a00c0c0545040c00310710040040b104804c405110164 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 947916726 1250 947915476 947915503
    0xa020a020d060b031e1c12021c14010b0a0f0201091e030e060c031c090f0b04110a05010e100e150a0212030603061305071e0e070201060b031f030203 65
    0x1e40e50301643c003810f240c0f0030007459a40602d00000c00540341c844000620313140b94032941c2500410f40d140d4460454000c01c2c80302d04020407900105644a141e00c1d580004900c81c00000303000c00c035a001a0400a442000a1048000ca601e08100c80d1014511444ca60885500e040c00041100308850740e07280001205401ca0b940c901c50108040350030140e1141d106050701100711421820008c0a01403a5104d118180420f045003002c00c03221070841d000da0b049004070f10340144401c0034400f170341d08000600300343c11a000c0341d000040c0d2040e0700c00c61818540e000283e900603511540f80541000510511200e00d85110080c020103001d201c99075911004041c101c2c0803144141c1d51281d0b608240645032a46001116044050500400003180c03000900b00e0b912018048020108048a061042c100396031038020344800c0912410850501541c2ca00b00003c40385110309186240da01d628089089030924040c2d8a1031860805c0864072158a81c0d264056003500801082c0c0d0003941c3e41d002a10b4912195030b0031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 947917976 1250 947916726 947916731
    0x1603030626060a1401090b0f0d03030615050406051c0216080a110102070f080a1707020105180a0b0f0903040503030d151706070c0c051002010b030d0507030509060a020a020d06 77
    0x10465034414414180c03c80440c0c0c1060120000d030519003890440b05018207064a983e6400f042c02c5a9a183d41052529502a1005d8000d450504004002c1c180c140607030140400d14605014001c3d11540441c0c0c115010781d034455007404200300302c0343c907102c1e46080b03038102840d0248014103221102c102001d400390311502459540345141a005000340d01d003900501002d034818070418020840942c5c0860741241d00081c0d803591b0707181003041603841111020b501d180784c64003c410440d000c1e40550106010320415040002980003000368141d849220500081c281c10801020600c040c2c40744201d80d4000080e282a242031030f8840c004a440e581010b243d1040d89500d507443c00c0300101103015620080e001002500b00c001840708442c40e40e500015210004004442c0540310610400210f03034009800c00030488440e0f01d82030034000b03019020103004207201740581c1c80c40ca981c0c1c900178070480c2e10b010360640744c0c1428000400f0030006541c00c40031240d4150b0054890700c00040c1e940e5214201c000d403051000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 947919226 1250 947917976 947918039
    0x1e0e0a0b0d0c12110d0203040201170a14062b060b06070b061302030609220b0f0601030c090f09022d0408060106020c220b03100f05100b16030306 64
    0xc3c0014000722101005610381600800c0c00313084081158990820050f016940e92154030040710382c0e02a4504045c50000c000c018002550b02381d800c14038446064015142683d1680d1042290b00b900d00058500c0e0741284a12004024414005510301d5034000c0800281001100001c9000350f8003c0c0012601d5006d12410803103585000f204c1d11030000e012003000c50851070080007142001901914141c5885080700c2d0300d600521301500d94940d1144d1040500c1c910b070401e94640e1180e40016151140801d0901c0700481e08d041c811000f000c11a6100282c044c211840d24801400070340c0070000c4407400407109a4190080c455401c040044840d202e03c4452f9958a88001103040007010707084031085402206000d40b10381d8a524210101e1007140c2c0301e604400808040ca0001041842000358240c01080101c1340300608580c4aa031801c900220140040c0d5503c03c02c0b140090f41500070740c41082d00c180040070382102c40c0b000c0c070034a09119050000c0c0094481402c040cc0c605c0700203080c200081c01264 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 947920476 1250 947919226 947919251
    0x61805060702070801151520030a0f02060f10050d02010302070c080a030f05180108090f1b03281202030409020304080406090608151302071401060905071e0e0a0b0d 72
    0x914801c0000c00b40340041300c50070003540e44c007d5044d901d0048200070800c1d50b4242c00c50050f000c220020202030b0203c80c1d5540d480c10020744124648643c9001500540303001451a9010b22a014801d006113941501100c2c1404200441c003102404203074100f40e400d2280b100040c01c080c0680e40604401c0e0014841c034075580c64020281d0008170044001c00c44c0600651000410480c0c114802da4003d00b0414880c1c0d9482140c24038100c00030010391182e00c2001802c020407000d50303402c90000b0a06030186c1d184542c900140c91000c2c21141a40c3c2c8030701c115006184049002030006288504461044d6480c05580340c858500f43e0700182e8003503030901e0b0001010005203410054180080019040250041c40c01e130910098030540f0303112107070041644003002c410f24071196048032609540444103405203902c41c01103500a0405020b00c80b102894900410070b0070b8060120314407520515010304210403030815048803407403c890301543c1c00680044010032400315201c040d080000c3c20700d50023f4120b80d94403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 947921726 1250 947920476 947920481
    0x210260a0b150a0e012312190c02120a020316141005091b041b03060e01051203070303020c0a0b010b0c071a0403080304150204120c061b061805060702070801 69
    0x52281c2005810070040c403880b84c01450303a1518160900b02205680990700b0703541c480141e584610b44540c48002121040d03101e02d5100540540c13500d4101451000614020358205d8059101d120090381c00904060b01041c9000e0003010f41042600c1601d00f442400c0784d10555a9200d000102c8d411200d541c0e141b4140101042105a0800d0310310003841203040c83c40c0040d403240701c050201982444496200402d980b00c6400a0240c42d06444aa81c0314052628000380246018020b05400500c00000040c443c640002e038030f0700b40c204101c00703146031541c640d4041e002940a00c61910250045d05a4040424003540e086d0f4024600d01d41140d030b4540d03900200300d082c44243d030090801d6040300d41038013842c5480b0300140d80030750b640920341039a661900d0821b400d2220b58117900c41a15400010042001000500108509480b44400c6190b25031503d105444402500354141600440c5a5003a0003090321501322070206031400450000c0f104240c0c45150a020302245c0c144050b0340041c8042051545c06d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 947922976 1250 947921726 947921749
    0x706020303010303110705010e0d031103160204060b0f0a20010203070e18071b03020309090907061b2001170a05060307080c10030b01090902070309050a050603040210260a0b 76
    0x240641b040340e04000018228049910b01140a00780d00c107100c00070903000303d407603140030380440702125190594000001040b00001100302d004134281000045c40b180400255100181c00304543c5083c845891000c88089003040c580102c160301c051070b60b00490b8000c0c40114080e440543c0da601840d0b03101e5060180743c0b00c3e40c0001d08000d800400030001d40640c03002c444402c000203800305035400541400c04034510f0149048840d4014441070a0080403100000d084040700c00940b1030452942c5000d610300303042e401000c0041c140324900341c03000403414401a0028031007441410521101801da03590211a160200c840220165807030083c03040c035180400c8140000c00e400c000034680948000b0115003900c01820280c414941c94200e5182e0342ea000311800800341c445540115111452402c00500d4908244289030241c0c2907034001086138100700003102e21803500030300000038101c80303620200c0701202642c40310002c82d44101e40504402c079040c010180200309801000c10003000036010411b012010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 947924226 1250 947922976 947923007
    0x20304170702100305190608060a060b0a050316110d0e0a050f010c0204020706140f0417090121021614071d0a0b0607080706050a0e0c060d0b0a080706020303010303 72
    0x2442000d00680d03406071080f0141c1101e181c0030a9940712201c40c03094079400c100d803981c43c06d03041003c04030700008001641440b40452030404e0150a9444c01592942c0c824059090001001000000d10f141300850101c0c06090302480d2040140340071a00d62401c00d82c1200303480e40000c4a600301d0f18100d1503e298240054801154402c0101d803010700040c000e05d9140900a0003160045060014007402e036102500c80030f02004200d00503d020740301e8405560084808955640b0360101d02c0c3d240300b8400d8244c50b180d020684605d205102c100400e002844840d602e043c441a03020404035803c0c1740d004481c0d00d1414458107000c034411a1840301c09092403856003080520602007a21029105c061b040041d8004102440c0090080d52110224106100300c08000c2c1003480c0000700801004407503482107200d00c0407040d08112108144503055141c1c07040c800d295600060a201180e904001c5e94007500c40404011f0a03120400d6650300c50509058240e400840940c03c040300400a00d41c006d0007500e01c0018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 947925476 1250 947924226 947924273
    0x219021801080c0a0807142b2307030210052803020a1101050417131a040305010525120b04060f081b1011100504120f080c09120a06050406020304 64
    0x41c0281c203044480f80810180c03144140c90341d040001024900400058441d0907044c1e2148c00850501c100104c2c0c2001c901e1644a1002482201144000c10b1366401d03640d00a009045500007a01c003202d098015401c0140203801c032042d090001040b500955082a400fa24051389800001c5405428491401a151001c1e4100320800000892820242d412002c3c200b035016220003100400324031a145a0300441d035410521101d9400c00d22403034014204891194009000e16a115003c900140740d407504840005c0700c401080c2e00c0320754003600d40510f008800003000610380c12264005002c3d40c0c01588041003400542200b8410f8200a1201c01d084018001d90b5681c40c3e8031050104d010b440d4600c540108000c0315000991a018040c0000c0f42d098580010500c1142841d041c9007210a88c07248044d004035540c00c125030201c42c010904188114820501c540c03c01e0f01034000d22040b0210075243ca983c074092512a407001500324480d01e03001e28050440141c407460300f880e10403d40702e8a800841e24810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 947926726 1250 947925476 947925479
    0x406060509030703020607080c0d081008030711120a0503030f18030408150c070f1112151f08060a0b031e2d0109030c060b01030b010219021801080c0a0807 68
    0x202c0c0025040200c0340c1c155400c95840e055030070070340d0590058070b80c50f5060780514084031a10325404254540180c89409240380c000d40d40b1580c5a50301e114258000340000b41d20f00c141021417502e00d030b080111101580588a160200d03589075801c1d50300445481d80c14160743c00c00e000181c41015019600380744120000c1d07141034180441181d58004802c4820701c0e42840400198131081d144042e1081180c0c0505800d030b008030f01c0d03d401a500b075000c5161038082e509090301a82140f2002414400c5424090314403106900c401c104200303018200181c6c0703051030008440c001003202c4c040015a100c0c0780942c0300000d01c802078108040c02c295484141b0030215418101d12609108041010101022056503214840466820340401e40101c8140c56410b07519102410342459088100418002c1c85880c0420409040340d005400b140c0e010901c50340140d21055060003000855000107040500003000d6a00348030305404011580c032400d8115900a801c40d00109141e42072151404024018420181c11803d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 947927976 1250 947926726 947926729
    0x100f0305240709120302070521060609010b04090e030f0a0906090b12010b1309020406170a20160f0c03021309080f0f0405030304030f02011209050a060f0b090906060406060509 77
    0x81141c09121301500b222220082014000c101003002000081d103010035171044802054800a0300c0d0310000c495000380170014840307150050601c1c1c16101d41c914010306080c280801c110041c115001a9002d5100801002c5001e480c180050114901140c0e10000103a0810b03100805400c0e903035100610716070041c802000030405416015054a070f4045140e0b8960040c020214440e49140e408548030303d03c00900400c060780c1c0300d00c019901c9503c809503140244c03103808241c02100c0141201d1910180d0b8003401c02c030180d805c1d900508000c4084086c407011920661145200c480d070b0000d048507002c0b40310008100714100300044040c40c0c2c411141c2000000355545951413280b06946031405400ca00003501340c43c0240300f030140d6003e000094126a16252285001b01503d0880e080c20303808291503040440407805030b8001c2c1d0042c55400b03005041181e0b0250b44440242c00380248900c0c2941d1211381c00001c64039020b01c2503104900040050a182c01c240040c8402c46820f50810003c200080110b821039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 947929226 1250 947927976 947927987
    0x70803031909051509030309070f0302030a06050705070615240c0209060312040b120108070609050f0612041a06100206010b03042301020d180506040b100f03052407 72
    0x490702103280c0840d40c0596890403900344200715022280303400016051140781000003014511500c008421908101d494902c4104403000c0340c44000e525512980401c4c3c0003038615048140c1180d040d080090410040359150010b503140d1400a00f9801e2440008009000c4009550075241c030003a480400061581e4070020032240407450003074001e03892000070820380e403020000e0448a1604004003034903980c988038250380303a80c05904105003003030500c000840c410001103101e40480b440b644845814a14200500c214129540c1020f036008030140000c809031246d220403184036610400100350305503468000300c00c0c07260000d04103500441030115a0100140c001a400d41960804410b44e9100d03900d510b008400511054960360644001c21219500e1082c15000f9040226000b4002d101900c0480b0681454581c08040500181c1c0400041808070703000c03141d42a001038581c0700d07c410352501ca13145640750782c9441d44100c0c2c0680c020305603104031600105040c030110443c105444100d041c1110010071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 947930476 1250 947929226 947929261
    0x906030f06050601091211040b030d02100b01120e01091205030c071103010b04020a0804140114010501051e1309060e01080312070e0306010e040210020d1b0503040305070906030507080303 82
    0x3029a80c002003883c2d80c2c0610201d5004040104076000c0351055807403d00c110b001c0d1075a0741c038000d904112807021180350110b59290032011175401440b916205000e0180a0564044c0050601401e1074044000b07000700d0081121030240351001144503021482c0c014480100e01c2c2440303003000343c14814485406070030000c65881f590021807014610001000080c0105010900035031302c01c0c1300042050b60b00e03400c0110107204a01503107008003000f1603005824262442c084490454240340c02c0103000e158002d10103402001100301d514a2814000c0070015044c0c4d012508003a0031802d0325604100051460240c580a051907107a41c0116509d40114241e90780a10803280c4080f81c5010b0018108130721640d418500f082c402422500a542d403541c5091001c88292802d0380a00024030314006024000103503540d08659603030301c01456a685c210448454030b802d0400300d4160004201c0000854010402d00e070251000c050001910b5207580740081c80d105403035000e0560782d0018020007601000c018000318 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 947931726 1250 947930476 947930483
    0x280813141f030c050f03040b041203090c030f05190c05032401060507020d06020304060b09070804020a06052a10060503420411030705011d04020f130303020a0c0906030f 74
    0x82c1c001030040080e04d40d03010351540010700080c080100003d10035240031060249015035024010084090011401d56842c0d010103403c48038190030400000c0d86d0b898450010030f010700145c41c007401c40e100703942410401c00349085c0e510004000003445a440c050107810034540c0c10b0030080710142d20b51203000c0c0d10090b05105680074058041903d00030f640b03c0c8240c89881a0b4401011035036480c0c10300c0c01c24010318641e207c0d00c0c0074900c52400280c482e030003a11300ea070040790002e0107408001d05d0078a00721101d80c011400e01d1501313061207040350014150060030814811040016102110f8a00c0c3c1400c125012a44994400c0d404600c001c00c000000300c10001c0142d00c038007009d00f1a13409118001750000001031090300583c54170310401080c8031102e0f118403649403046058805e81c0f903607039004582c2400c05010407081e00c035401c10074201e1450b0960017800031902e0580c003e41008a0100c10320041c083c15403003600581c010425030000c10020440b000042c2180c904104981030441d250030b030030005e180038000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 947932976 1250 947931726 947931731
    0x1005030c010215060102120409020304120c11120f030706090b06092a1201030b0a1a01091707170f0d090609030204090f05121c0509280813141f03 64
    0x1030907a442400f007900d0421f500c01440b50350700c1e0f0700c00481c8025441110b040c1c80c0f00000384082c25103d441512041000e070340200014100e141c25000f0010902c62a2138041c81610581c854034443e110240050010b82d800340350009041a400e06007000940c0c0b0080595104154110070850789802c003040c1d01e964036501524403e03170705487c003020580510034403800800c06900c4500010800c50850111407180c80c084100b841440c44401078142c802425208403804100585820700079425080e64603000305030f00c0c0040301c00480d034810030300ca10300e46950b207000d015420170620f10040500821418000212030310f4442207a40c40d20000070200c0c4e0803030200a110782e458484032014403180e420100e50454010080e1000c0b84440c20341c1e40c000ba03010010703110449504041e0118040410721459100310310202c0502105107020204030f0f02001420354215050780074204410200d4030020107005d054407000010400705052018014419414603112441000e8403a000c1109449000da00b0341540d00d2414003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 947934226 1250 947932976 947932981
    0xe0309090f04111f031b0f050f3903070302070308072a090f020412020d080f0a08040b060d051c0e06030a0204050103050105030336090f1005030c010215 67
    0x11405410030402400e030321154aa81084d00d44480300310460762840c41d0f07141000280b04011079044d5043c0041c01c2c0d03801090021b140e4468460051009200385e8a24110551234046070850207000382c603a80844001d0107000288030107103007640020140b10292414019410041c466400a5940c40203000051080001040d00401c0082040f80004c500101c01d841c814154041182c0005060b61441114079480c141016014455030034801c45054034001d071000040e0507026001c0c03207401a800300084808002c20410603543c00e50000103010a80300d680d41c4d51506003030034180740c00302c0c3c10042c0001d485a01020b0601001690001d181c01080c091300d81d0b00108001340d81c5040d41e00c00902e41c4100e400c55400001c0009003a00380c0d00400075250241c90402003030740c0302c009150b034030300030010314080e107910070303c1441d41480311080321111710510b02d801d092443c190800480c0c6001015503028024807040b0080c4030450305600050005040d003134000700640f000e4600000d55591003d40d404094601d00c070302 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 947935476 1250 947934226 947934233
    0x8030a08181b0f040f05090706030204140f150a0503010303080615030720010c0e0301150803030a0209040f0c030f2009010c020f0603010803070308010e04030914040b130603060e0309090f04 83
    0x72101d559000c010000c05c020050048264007800c0c04031981c034441d000e28640403c84d00e000e4400e85094800704840c07d0559440c51052018200c4000003440e401f8000407144412054050000c200011090f680c06840b0351440c074010b480071902601161082e0781c52101c4804080d0f1240a89511090a240401003c607600004c0c3c80c03000c0c03802080c10840d5081c040241031054201c0d8400008560541c001c0000710f40000c041e080820041c0581510b030b4000b08081204110150090400304400800020300085003446500c101c174070000c02c200210340c94001400b0030a07264450903860003000d400020103d030305014841c04030320501c0000c81c10712410f90401e00039526003424081c6058800340c01e15a8030358403803412690f00c3d040b07828220001444da40c00818075150440c5454040da6040d2202c100c0103040028140507001e202c447d164003d5a1075100c4200e9640b0884480b078803c810b4000010f6080c01d5092510941d0b010100d100c8241e441001000c0c202d49440da110fa501c20481841e2140f50f0704c6516 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 947936726 1250 947935476 947935489
    0xc0f0c03050f0a14161802040e0a0b100f050a030218060d1d1b010305180d05130b0f0f090a12060f1b021005091608030a08181b 56
    0x4001034403038802e070340c0040d220000c00221441e90700d01600c0100d001501c0910310a170b071604480f81d0a03038802036102e401c124403510103403a2004950f0520001d81002d44400c107070300d140f10003114810390064072000c140809042c07007a0a48456459440e024a591358104805000c074890440e441041540c001050303246e400c0d8224181c0740c0202e0003411280e54055459503a4040c200c128001740c11080300344403401d00c150000601100c1d01403140d869850f5003d4120041d0000e00d0300410b101d021000b0341408488110003446003c1148a041e16015124000380705000c44803c8030703130040069420b080141080d12403040c0181c50310b403500a010070f0768450307001d00800d084203055800005031024440c111401c02140b07421207002038400800812844862441c0c0c0720311a450704c0c2c0d94002507002020180601925034000c60f922100c03603000c5901c540040320708102001500d40c0054103d030004204014071765408803410b43c1082e240190340129114142c0711a461b040300104412202d48100d240001c1a242c00e03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 947937976 1250 947936726 947936729
    0xa0c02030a0c21110d0609020306091e0304080c0d060902090103150b0402070809131e02031e040213090330050901180204110f07080c100c0c0f0c 64
    0x15054405071521031401d440c0340c102c24080d010007000d20180110024005100560016401c1462010401074840600c0b0003c280944265085515024005d000d0385003000842d00404024004005040100701d0100304841d007100303007801541040108000c0103c000400d01e82c414400c50720b8070180c254a14001006000b0b20800a40000c42000000103001440007202955800b4a005105c0c004010301001704911074108020300901c000c2c80400a6410000c0340c41c662031165135030008007180c0f58006080d20311344200c070000820350000300f0000106a41603621003586a041c00c07244441c2443e50008800000400c240402103a407000000c0030b142c803508040700c01806191001e001e03a2030a1080d2b0440e004481c405800c0e490818001c101c3d001414801c1d00980c091440c0a140e09010076030801000c2d10780c0c3c0000b200b48900900280099103584001810f13014454400681c0d1011024202420484202041c0350300c503140c01011003075a50059000400719900101070050603a02d46412284503006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 947939226 1250 947937976 947937979
    0x2a18170a06050f010314070b0d090c0e01140406050a06231e0c0d0c0b150a0503060a02130608040201080a1d07030c05030106171209030f06160e10140a0c02 68
    0x2e010502c6140d905090402d4140d0703003c0c01c0c070340c1e182c40c82c1c80500c2d9656000034440c0d500c240d0010400501c104095501040c4203911813090300502076a40d40500259840030f8101c214001d4240398191082c1c60280f00e8400140303029030b54492114540780000c0c0490810203c55a03d8a20001c0d406102d55a803104864800c80d403902c0d06c00d480a81c0280140603034000b814865940d104000c04840298041c5c1908404c141c0d0040041c1015943d082001000818a80c03e140d0003141d800c00109281e5000d20001d0b10807409050016103030001049810741c0c40300d0031b5010009000e40d101c24480913036880b20b685031740894030b810045805a00d004d0b40c103204020341000b400303080c0034840c004010003031841c4880d005c50b00101c00034008103480307080700005550190030407492030f402040c0380c01c40010603201400b4086001070558141c25000250142010012204050443d4032668251000c13904005604640d04054505161203100c8440283c44424208001c5038180d6000c030380b030740060b445506c00c811300075070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 947940476 1250 947939226 947939231
    0x60c0a03020d03050c03060907050a030608060130120e0a03230c030c0d0605060301271205030610080402031207030e1c0b0c090d062a18170a06 63
    0x5038140251900c1c080707220b01000078144004030341d1800801c01170300d0013035400a0554060f5210800240e64603072007244c0107410b0545500000542e50b000703100c240d008000a0f1401195150f85000d8800c4014500074a01445080d0300400340104114860310050400c0710f05014070300003a42d0001441460956000800714400b842103090482e503020440042c280c200f20450702c050340d000041540351940d1042064004a81007480804a0140d40001d134000101034000190800c20050030b43c0f404a0410110b0000d0a913480041c1c100211b48010348100e514520f041801c5040905c00508900b216506100030802502c01280039540c05005080604010220703043e43c0d40c20718a0050116032128811a100344d1403580150100c01a02c04607a1013654072550003c003070b94581c0342d615000d82117800b03800e170841541088a000119184210070640714100c1a40104c0a514080014051001340d00c0e101084901d02d042404003d0704680d080541e520020065000003211380007501d04070240324090b00c1c050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 947941726 1250 947940476 947940493
    0x1e0402041803020c0906010e13091509050319030902133308010b0603010b030f09010609060b0405040f06030816050313120c080303100501110c10020c040b03010524060c 74
    0x140c00042200f0f903130700c080d9440c0040c0e981e42801900c03c580c00c140c140303070002e00301c50720315240c41056409030109610624401405404252020080f07488009003204c49910000d040480800100c51016441e007a80c50f051103080c4160b40840c207644aa82081d1015503103628455500f050405a91142c0784c2e644c100a0030305000d0207042c00b195103140d1180c04003551030024266500d00740f00003180c0c1a03601800785945503880700049440707400c40061000c4a0b035540e402010640c084503008540044c200302d00326540f0b41c0d0a083c200022034040e500307000145807030680c01f00005026413055404000003031058207042e40031390900c5030551103502900300008092402c00300b4046580300184180c680142c01d102401c507218450541d8a200650705c0c000c4810005104101c5588a00c19441c0e000c040c40b81920500328980c0049007032851000741c9a009030b0080500c0c0c0301d07941001d01c6501c20b503920440080c0020b041c000c000004403400c003200e58010703480105d1000d146031908402c03544034020803401c803000d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 947942976 1250 947941726 947941733
    0x10060e0f03120d0b181512060709240c020112091406040302070b0a0206041205040308070c06020c0a0f230306090a02030c060a0e010e0301110d020c070902031e04020418 74
    0x340c3c04209103c1c00145400c4070210603003010350b2914135810200c0d007500c5a50f29083c501481c1080341c400c40a52260941080408400007441041d004039106d4952891040c1019481c10804203210b2200e004040a81112030f900399110f503c07600f00503021b00b485044c081c0340d100307901e02400c0310103005801044031300b2200702054400500707503200b40d010740c0c281d03500d441e21101c90798481d22800749004010380c09140030802003501c2102381122000d19090140c606a40c035551030000390000b00080c0d0341031054180c10881280c062284601801d811a541d5002e075041c94503c1040c510755006040f242003030090b03102210b008510000c0ba040b00014111101803a14802c06a990750700000c0880c024001d01d02c007084103081480c11741d038190603c0e445010181250720011150403030f80c0e08071564559210382d020310f50703406e07440c00507c22080c1441002d40c2d83d40100000714603100d00d0398000c010741441001000f0700c1050341c0004c1d58441d2410a0410354a0700e80e40005005042051283c05160201306141c1c2e042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 947944226 1250 947942976 947943013
    0x60c030442050a08070e0d0f140a1709031c0309030e01080907090f06050303271f08040f0c1514070302070b0307020f01060603020a110f06190f050708180610060e0f03 73
    0x1e01d21809c8094080c4800300085910b89089000051020000d80c0010501c800540702800f10542c0c054121118061000e800c0083c1d48019143e95011950b50040700742031642c41213400000d0711003801d01c0350b290309016114958801640c4075031100365a031403040e8201790074150404002042c006041326151f142c5a421200000701894001240720500d001c0e501d01d83c20006620125401084150407110140160503207050070014005ca034400030541c03140d00011200c40300704000e040040c040640c2100c1d20400542682212042c035400060140805000682d00003480800d60300c800002a40341d8803100000d038a02507a100d082d100a500341100481d0003903055020303140030303061561030a03601e0002c2841c803900c88546496145031500404000b0f00800c0c0c40c00e02c007114400e0920700011700861208410030403203806646140001e507075074080c040d030292180a1480f0070b03d00d440181c005420207500c0c40000071a00e12804060100000b0241c201c0d0350307050344410f2000805816502410300b030072280c030003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 947945476 1250 947944226 947944253
    0x121104090c09080118200a0e0601030b0909030702040c05040803030123010e0907051e0c0601030b0f0f130206040305031c110711060c030442050a08070e0d 68
    0x6044150000d0900c03c1402600c0c1d1081e10b407040300740c01080c0c40c0c03a01c5e000c1000800a02d05c403504201c00302200c0d5151416640c0050180c0075954089040030310004040d80d041d4000c140c41211408280f040c1c08801104803004140d048800090702c030f903007900543d518065035000b102c85d8003010000013228144c400c50090181000002c81c0102c0ac4200015200c2807400c9003040d4002c3c0d800c83c002070503103008a005091094440f03440000020b000c80040e5a41e030700c6039407150159000b441c010000c102c40090181d41100420700c0701195860222041800e41c0c0c8001c10920180020b501071005645401c41120050364112090787d03600d0240f40c2c4960100341c0b01c5a1201d0500d031810b420800310201980a03188059400300f03d140a80360b2980070003040e0b41002405800c140070030003002070110f0349040740710002d405522007416a50210440c4641c403104102e0714070041d003e050102c8481030340c01400c891658110b42404070707140d00c40341000c0b2141e144544406810010076030001041c0450f1400581 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 947946726 1250 947945476 947945501
    0x20f030307030e060124030f020c010c090306050c07081e091201050403021c050412050123070305010b040b0403080313061523061e0d090303090b060d021012110409 72
    0x84490742d0752003140c003000d0414a00860543d030400040c000080c030a404c4018088c91484002d03041640201800d401c58426440d55030100309903010130402c01c1914050613038000c3c0400b06c00760030b201c250388908a0342d00c02d140c005804402d0b00b09102000030110020b03124030f014044c1603101840c41c0f000c5524000c24003580c0075070151180400381e0f4004107100c0502e400e110b95a07502c0f241040e01c0e10040c540030b03600c03800003125555220304c034a07045a144400c0d04a4040c0c0f50800e48422801c00c034202400300c03030040c0c002d080500000c000508c100c810031011501100da10041071540c90766200c40c13020030261610780c01040e00342810500400c1d040105034100a03942400368100c641c60b1803460404003444581c1c815600320000f80031141c4440c484c6516040006002e0340501d00e0a8229100311040350076816085001c44e40d10314410092194000840e80d014105481c8007280004940000d00d1200404222104100c40b9085000402c1103d4010034820300044108680320b41c0c80d41c0ea070f400030340603c41640 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 947947976 1250 947946726 947946733
    0x310080f011104090b0f0d03020d200a030e06132301030203010e040b040201140a02010609060806040b060f0a120f050c01080705040317310f0e010510020f030307030e 73
    0x45005a2041c420320b01d0602000030810b14052614181102601035505059880205041036414035144c0c003100c200064440e601500f1110b1404802820007184900b41e4850401c03041100c4807000000925443d071a5054200404c0204d10792000800c01e05c94004407481100346614000b031074040341580710140d0b0109070952200d01c8002001101280001d11030f48001681d10404100815443c8000c180c1042c010302d0701c4d21410110f030701030075202c0d40051544d4005030344d24101080382d0348251003448040c10601002e40b5240c10302d52107800e011000900000d1207820b40b9026a1115034554054200500e120030342c00c4000840b81c00d02c2132400f484020140c58501415030b104042d988207108041c490320031a110310341000d0540d11041802e540d22030003402680400c000340c02c0e15450401040400d80c244401c540d082204031180d5075010f502c80d60080c40b82400083c024804800701005042c15030301e050300c0304002203010300001c1f4a0314440c1d4030440c07458040081405a10b80e4503410000c141c070301e502d044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 947949226 1250 947947976 947947993
    0x161a01050907170a0c03020c030a021c031407121b02160f0f0311040b0406080a170a0509040e0102040e041a07020c09040f03020109021c0b090c0f100201020f031008 72
    0x643d1803460b11250000520030810000e601d0900552014132142c4152400500b040d40c1c042c00300d440d541c01000544096402042d142511a40028540c880d0583d50301d02485110070b012200040210054040018031070311006072520007686503c9010040d5180040940002c03003803101a448600130084030030b201c0c1da141030100f004e0407801d01c20800c4070092424101c40d01c0c80c40e1078903074544c2020600c1c1944242c41d41602042c0350f840f40100f5020f0310114000e400000d45a02d0414541c80e580341100514070028803018030142d810001b614190b00b01a00d0200d42440840c00d02030091084e6040780c0c2d9028031117001d120034807500d00c4038410060071581503440c01c0d031034428041c1c1c0d8980000c0380e10b035401050040001d0005891415030f4504911034000854120065400107038480e0707030b002c1d00d90240d0013039024000c04d2141c0303004000d42020504011740803074001f2002080d402c11003407880ca409464011082e0317100510035411600b55840718407543d41c580c1000c580f0890266264841d03040c031842031085 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 947950476 1250 947949226 947949241
    0x81204150f0c1d0d080706090507090501060305090a031b140d0302031603060e060d02030316030f0e0a12020d1b060c0b280f0e030c06061023161a010509 67
    0x1400220044004c0003122160750682d0307151919405140100c80c4103464600d00d0340091000c100440c0607014034140031a40e5810040003c003210802451a011035001c61211808240c2100741c5503000300440710603400481590030803c251000110704020f8502c503007801e004843e68158065802185041b911001714241e004c4100c00342c0f503080c0a400b03011307041d040103d101c3e494002010680c20b032029003900c0c00c001510440c0c1501e10b030300b5503080c2d010984040440c26525844014400c0044c4201c1e00754003c82d0408102c030003c00403040000f4090b503c0c0c00c031400d0500c001c1090246503007031912101c030b900503240c0308000c0865400c1d5000700c0304107205102145400d001c1d915400070519010052030341e001071140f0030700d0240009140d000503003640c0d07034140c0e01d00f08800d00007004c410754100000c00c1316050010070300030101d40a5854504103d50740a0380001482c070104101c83c03e101442c03000ea20b420100c1c00f011480e101d640c00052004030403400f8030f01d11000c2c1000b03913412900100d50921040c1c1d207401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 947951726 1250 947950476 947950517
    0x10b03030d05061507031b0201090b0c250b030103020d060204050d15050f06371205070b27030c090403030c02010e0316030c1b0e0a05070c081204150f0c 67
    0x4008007c00c41e4403840241492084051291a9005161054085503a0055861158040300303451125420180102018103151f103109154940705480000e159854807055035070501043c00001d20904400032194107001c62030701580c026240041158081e04c4171460702441c904403400010b8085400c100006465000c0b0031821840740394082c4c0b041c0035070400502c2507090300e8030510400c408180020320740031006641c03041500c050250111681000c0d8800d0415a1808000e903201c12000d03101004002c00c0c00c103d41417841001c40c1c00c8180700b81d110700072000181c1040c01c21900c0c0b90700646042c0800040c15410303000150b000c407454000b0044540340d02500c0340c584c407605511180303640c0c41203c00800039108155460926001e500e001490810366070310f090601034242c0c05180112070391004d00c000c07048c03036100d4981c0250441c00d120b524900d0a5440392144c1c02110807084d5044107440c0000c01b4020913001b0051401c482030401c01024204070320240040c030650060301d001880d62481c0200492104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 947952976 1250 947951726 947951737
    0x50106021b010e0d2406080c0a050402030702330c1209010903050a050d0f0603030c03081006080c030c0c01050c03011502070b030c0c030d0212040204140f07050903010b03030d050615 80
    0x2500f210100903558585100e80b59842a0300c098001080a05e10003410441c85082c010780840c030060000050290100070b0300c1c0009030015482288100203010b401500040e0110317051034a40c00d03041410003d040c0039658003005170508680304c19454200182f03030f001e6100030101c0d40004504105c664888001090032140c450400402044040100c0c0d8000c90040e0098441d04480c4440440e900b8800c0c424003058502035403045010901c001041c4082607081800340f07903c000c0c4442e000b9100c5145ca100101058000380c46820144000400310b12240700c0c3c94115207481d00c02c40001d001608048101c0703110b6510921404030020410401851000c1c40450b900085422001001c3e045842d1402c0b17204076a8000c4407852101e210800041a00590074000740180e980364495407070b02440c2c0760042c84241c41341e24241000170580c03141081190b0301c1540006400c1481450025211400080403e0041980d80d0060b9403611020600c41c946503010b81105100e0b42e401e07141c1664a0b010070143d90058010b8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 947954226 1250 947952976 947952979
    0x1d01140121170903032a0106290d11070f11030706050f0d06030c060f082203030c020c040e1c050304030807082a030f090327040f050106021b010e 64
    0x24500c031007180b86000c0043c000034480181503a160441e103c0000c0b10110310300340150049510b01c00c4000d0600740a200c0c100040035005e1078841034000d200324030080e800e145281400c180b41c002c180390609010b9648903210101030100625541c100c242082000510030380c00c122000600800011101d05000c18868101c9001362280c2e8180744400404030110340101c1000700c0320503640d12000000c111120402c6c0c0060000c1d884a507400003482c40d00819080004002c41c2d40c1840124011411501e04100b0440f02178140ca000240840c0000080f414a42c5007000035030b010381450341c41e0b0302000021420101c4080072880406003615501010742c0c0c1400100c401030007048000c0d002650040c05030072000d80c0007580e03941014a01c880d440c101d403803d0640b198100c031461400300800c42c0d0312a0103080c45410414103c021401c0131300c1d6424441c8401c03509a014000d1405000c000c40c0240c6a80e0010b000b4450361250901c4150f0310344100965803103401c420b0505000081c1000c00d11035000700303950940ca020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 947955476 1250 947954226 947954243
    0x80d050f04170c0307020411070606180b0a0e16141c0536070b0a1d030609070b0d0621021302030903070f080721020f010e030405041d01140121 63
    0x819002c0100134580c01c448008d084804106142c0015081e03c1014064101500b002c8909019107150b001140c0c1203012050050440354400c0c0704105c1c15100c034640c003d00d002c002e603c0120a03680100c402482c252030002e9003040214050040c864045414510f004004104012564a14407003094010411225005266001c082e51441040c03503032a20070002e038440222688295103a0b8440a55031107404840300040548190003206c2c4031006d1146040503045000704280d0500ca10354940750401807240300680800052008481a002e030170110003807000e910b61345045d0940006003074030022929400c03441580111582c420007651842602c0c000d41c803c030010b6041030a15603c5100320000c06209449480092240800144810f101d03200440300101900340d1303e0407424000380c035051200714491138590502e012144108400400d46088607401c85001c030700b102458a50380e200b141c3c0d81d44021403650811400601244c50b0514440c100d0f02c0c20300000e0303c44403440c501c090103803400c40f070020079804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 947956726 1250 947955476 947955487
    0x111160302100207030507090501240f0302031b0403060e1606020d0819020c0f0d020f2d0a031d0f09040b180312012303070e04080d050f04170c03 64
    0x40c1071120b0003948807240100c840d00c80d1a61030f220704d080301a030301010100c1c1e00c946c01070001100ba01c520b4044500c43c114400d8410f1a40000608040da282c80010205940030001840b200541d400d4081c2000e148000545d45e143c0303d060041c050805540580e40512034064940350284c500411402100c1c4254040c10242010400490340507201034048215001444102c0d88481051b1000340300e04101c5200400842c1f02010f581400c02c102c1c0d02c000015504050300e42205858003060140502d508141c0120610203552810712003c3d1803000444a41c1c070490110b01c04040d000000040030015950021500100000400c040980640314841c0c0142c4100042800544000b4003160455560070040c070000c20342c1c0c078913a49950000300b800b6030200447d00040041c0074945000492003041c3c40404c04a801f503200c0440d0341c0300f100744144480d1140500001c0d00b400120b1040d0791080210360320511050914892105070250152016102c482107941611080301d00041107909401c0c40002460504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 947957976 1250 947956726 947956729
    0x100e1206190504050c040515030c0604120809061b1015030c030311010e0d050a140f031602120a080402030d03140c220f230f0402032a090111160302 65
    0x405003c0d100700c8251080040c4601ca80c2e5560250520a00c03400243c54106034000c0101440c0c804040409809400708100510540c00001d4000c0030301e81e00804405da5804080c40403540314401c0c49520078501044150808603448080381b8049980d020f00310a01080144480c4107242e04203901c002440104400800c10001f0700501d810041c8481500000400c0c40094641905001e42c1034071510000708001464a043d90b0400c000c141c507101d07a011b085080207444541c41a01d0300c00980107900f56001203440c1d2070014070070806882200d41251415440300a2010040c0000030b05540480c07090041500001c1e84a10a12400156404006038482c1a032240019501150312944031804510300316901100b10b8a546c0304c400780107102c0740440c42262031422000820968050a01b031007400e490704044100307070782c03003600d80e48058004660059a136100c140328044200345415030388a586455903000d05400842c60003400c0d8005081e20303640004c003500c40040e5107070034a80c0500a4070398000542840076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 947959226 1250 947957976 947957981
    0x14121b0f1504060e06010f0f090e03070b0903070f0c0302010311090f040c0e0916080c0a0507030f0c21080c0705070b0714100e010c05091c02040605100e120619 70
    0x400d02500f00050240b00e1500050300303042c0260030086200154507810080c0100141201d00181660841000400c030300100c0e06449108070080a01041c1d50702000c109030900a1048854065004142140b40d00e0701e45403d01000441d84003c1e40840e107403028943d4614034003c1203e01308900104500c02d404030301e90801005101c0c195850040101d054992a8551180c140550007520050500c01c3c181c24080300c01003809000406885041c40d0501240c1c00c10340c0c020b41503c1d0100c3c1c1c58102015a0560a5000ca9130390b600c05038003500060710b102c41040303c0102800b45c4849100366540b1328805a5440403c0030843c071651b24028041da1010400700020382c44080600b04880c81030b00e41030310100021200e90b2505840c4400720039500c0d82d9403c61101600d0034880e4010724a20350a003241065500000030719008900100c08841034813800e4001d0441d5107651004001c0c00b4000c001d0303c1e8010031294001c11000040320040d003e000e40040c010101100003c04510400030024080400040c0243c0c0401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 947960476 1250 947959226 947959231
    0x10b0913030e131b0c020306090c0901090b1306030f2003070e060316030b1005090106120213080d0512010f0b0702061303051c03231314121b0f15 64
    0x90964031207111405039481130b680032105020741d84d6601c0302401801010b0030700e06c018020713510070f90081d0f020380790700c1e02e13040c04160444845c607a001070b0f0480700e90081000719401c0c0120350107107850030102104022010a0311000a8020110030545001080308864a0901013002c15030607404545c00b040402040e441aa80c00390000d0140c0d2070b881500005c4001109464208071451484e0608100f114044000c408005090440d65501c29514020014125007202c0c0d034100750040c1c000803088244000803001d24020304402044501c0300c2d01c5008001d01030b4102d000c0c8100703c0c0301d03420000504030356004400400c0c5c1d03a80c0510689003000319820801264003850321a5800702e0354038000004910140101d540c071506203103006412420b5204002c0c1100d08100c00034050b80340b070b002401d5424040781c192590203c48101580712021150800809210001c02c1a900f1889410300a01030208100042d02407000d000105048118100e09190b8550b90f402042c0071441d48000d5108090307002c070011142c5c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 947961726 1250 947960476 947960509
    0x507050f072d0302100203060a050126040c0f0f03051005040323191107050f01050c01050c0406090f03120e1f020f10060e0c0723010b0913030e 63
    0x1960040065039164110707030002e070b00c004005400c010714820702d90180400380705200600d80c214514901b071400201ea414240c0034030360400054100800c0050b03c0e101d804420701c40107110444c2c44c0e142c2407a103000009024000c1c005020241880004c504002c00c94000a4a61002c003401040d140c89800c035000b888010320580c200005445c0100300d6041c603c882008411180da42c6950f1021600c06a40c0d078140a040f0200810400c00718420a440011544a007030300d80c1100c0c400c001100003c01240d660040c603900c45d1440d480c1000f400554030302d12000308110703906034480417a80c903034404007240d4028080c440a0000c100c0a80540c02e000d00c1002001c80e02800100003020280c003d4500d0f5044040c60486100560702c20f819152001c50200000321842c1c08001081c80042d0400300d080c0c5140c28090181d4181d602c02082413410800c658100602c8032513030382e100c02010041c101d10140644000b80d03032035004e00301810120f13550413085001c540c901ca403d5110080c0d0503951005001c010840e446500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 947962976 1250 947961726 947961743
    0x5130905060a1203080a0b0a180905030d0c2102030c1206010302041703032e03030c0203070305010e060103030f1422080d050d0f0b2b0f06020c0c040507050f07 70
    0x20407081a11070303400107060300039a10740c86035240900c6c01100b2950104461445005141800c0104007081c1d00d540715110400000405c9100b1589421803850041c000351124840c03d184107001c0301e90b070000000c1800d5a80c00e580b0001c60107586101001c900c0107440840c1c3d5444108208103920000c0c0e0403140e089a41850018034050351030310f003000f4002000302400407540000080c401c2c400035118044820801d4050111000e103420b070307202c98180b20a0b200c011700b40316500740794006560701402031000444d0000005d2044d4040b0741d005035181c203424081100499030214501d482c05100b56882d50110445a20080c1307412170745034450610740c1040d4a110221302c0c62031004508850180711055000304192074064441003420782c01401d80707a2001304460740a01d0b081d1822440d950b1683c4000f18440800b032031070b81c0e002c1c0b1620210700c05000210081c002010603680341082000650090102020400585000b410342c0d404020681d8000d507500c500003501401246112500c84000f006581e1181490 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 947964226 1250 947962976 947962979
    0x70614091f0f0e0109090f02040314061f0f142d0f040506100302130305030708071e111504081b040e2a0a09092105130905060a 56
    0xa1450503420845507a0308811840c945100c940261500001c100300d420404004501d010008020034154440c3c00001512502220f00070341140d8100d402464210301c1c08ca104040080d06103a5401080e1414552403402079025840007032000040e209444036218030094203071800c04000590700e1005c441652001c40c411410038417446202c100515414a035802c1c003051050341f03080100c044804444a0700031401e01d010095240c3d0360310550f00054055050040c2c4880460254803c000da05420090252000080080c140101600689003140c0b1804800d9007002e481d44102c481c240022000a040410f09000c1140c185820560f1b1900e091408405505247d500c0d14032074038200f40e4140071040e01c2c681d0901c0c0b20302820140202d20b913280c014402820f103416007000c06803051050725a042e000c10070140c44500d059035802e424400514241800b80f012140314180b2421142c1840030741c074103817041800c0f8401000d0241080d01c05042c200d07801d2400c61460b100f4218050080140503540c0100c00303540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 947965476 1250 947964226 947964229
    0x4120b0613090c0f1a030f07050403050d1715060d090228030b0906070f030207020103060909140606010f020d0813050706091a070f1e06231807061409 66
    0x5007080c003e00030010100303214948104540741581c0764110f01c034154651002680b80404550449400488481804000d80c1c0d80c48000c03151409242c00041c5203001d00840c6d841050b0748240b5082803061a845c1d00059500d0b0b24610441e11184948060303040081400b10300600c88003a8810500140090b1201c242c80201b142c0c08404c002c005000120b860002e04014428000182d640582c00003055000b4686030508407805411403109055a4042580000b014011640310360403000c020100c40b80c05005194452410403003580081c103282d0f40510070b0300c000404a61040e56003201840103900581600340c10010308880c1c0a400900b42002901d41c402d140340025010495840140f09907a030f004959400d08c0c0460080741e64400020102c04020302c40c010100c7c04070300403001030903031040880e00242031542111906000001c0080d0100e848c0c070340c00101e41c0d03104800c1002c1c0002c01e282491682d0355018a00c8114441d0030710444007036445403406000c954044c509248604058035006400d08003901c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 947966726 1250 947965476 947965481
    0x608030301090903020123010e19110901110a020114071b0b0309060106090305031c15031101030c030204140f030703050d02011506050a0f080604090f080702090c04120b0613 76
    0x82c04607460b982d0303400090051580c203116081c0c00c005007074840c01103610381801c0c1c44101da6040c0105024414280c0200c0c2c3c2221419400c90b03000b1502382c40600c8103045c01c8200000d580c203da10640e0108042c150007c46c045004540215074690584820405074501d984408070707070b000751004490032a2140e04000e520185100c4c0030006141e102004c1d9983d251169817a820000184e000005101000000780300150000c4140c0d481381d0444d1140086130a08608014041c0446010010718284590008014040003401d00400c1d18400c1c2c805002c2401d032024110201d101d284100249600600352000451400164240d040e00e4020225a496516621068200400c4001034000340c5c0d52100711a2007600d0b440503810082c1054207082c1d040c5403441c0070280010401340c07440c1003045820340020702030b5a103d07808282610f4000d220351180e4280381c60300c407405500194040e8840c00003440010345070b811100c115425600041d501104038202503495000c2600c000e0000c42c1d200d1070f9000801ca50010703c1c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 947967976 1250 947966726 947966729
    0xe0a06060b1b071d0402280603050c0906030402040e01061a0403021903030c060507180e01210f0308040507091113173403030f03061202010c02130608030301 69
    0x6881e4640c1d0798407048038000c0c400103040c0e200d50494001c0ba404000309803049181d203111600000b83d443c1150345610010b0a0402c0140790303004022501600104007002d0300005200307030381c02510100060f8a501c84c540c01c0c2409a9007295500c005c0c100005001800c00d504560a20400030340040b030520b8030341c8101c0040c43d0147d07460307030310a00e4082400c100b50715000c0030080001155aa940c203000e0700710780307004111f607002002c0075200c1911540481d081901c2015892090711680c80901caa49485c0e00d12244d508400703108000805609200032a01c403c0100354402d40203078040050800a6015502510600401401501c0740d0103045400202e054160003107400003090740c41d00c00d0340c807002c0c0e0300381041e61402d82d00004d480685201c07805801c0f0340002540c030385248551440300b04401c0c41000104694101c8940c104214024140c008101900560500d1600d0840d86090065944a8004418104200e40041d001407602007030f80300076007030144e440c0c18580d403061070210b80a03031140181d03441c60380203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 947969226 1250 947967976 947967989
    0x4170303090d08060a120f05070b12060306061f05040b0a030c0f03140c130801020703200c060f0f0c070e0601022e0203132a05090f0a0e0a0606 63
    0x30004018001d02c8100c4100040e410102401e09018000c45c1e8841698000c10750b021181c1909001480b20704400e1504456100b401c849142c0d4484043c442c9942018500d41810191100032070054640818424400c20b0083d11341002d20052800b1a040444911100f0090000800c400b080c05003144004160680300e41e100860445060382005044051001011003010310305035000400d56042d0b00140d41010344480c4068a584c042c81d02c072a54403089a000f80c18662000403070390201a00321200d003c2540d02082d94194500e10310103d01e40b680181109154000f038100306030100003a40d41e002e4000c0c40c40c004980d5060400c00c00409142903c42d030420041c4801a60801805680c100042a072002c480c43d02d41c1b1003404100b01080c80c40d0817440e081d821098011002401c050500a40c82c2442d54003c40320100c00c0380c20541c10f000c4c07126403100b8200460301d41d007808141400c0c80142c43e030141e0580b0300c1140b01950b075460800024001c02c0b6102d020740c0100c50381280491142d02400740501315 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 947970476 1250 947969226 947969233
    0x106090510020f061f05030109151506050f180907031b02160b161b03050d0806030a02040911030a1b0602010903080114011e080403030507020309030a0f05030417 71
    0x900081000410381d00c0001421544010a1804600070209005400c480030503100d080014001204160401242e0400b0740c0641c84c2041c498244a000107075041079035481c00c81007220a91a0001d140d6411460007081c01052007046050408003d000007008604007140e440340d00b030252800040c0300800203458080c00a600c4d140140c010501c0559042d0324000d0500040015514030a00e9151800c81c2c3d02ca01125003d000c50107600002d4050164441564844d00c0342c1e907110718002103500310444c580001e89031031140000070320f10703503028560160098800070000d0402801ca9401c11000d0304203031100f01e4595000780340c646202c3d1010081c00000038465080441e4a1002d44131101400c0401d03031040d0b085a0515102070b0200713421a0310346054800450300c0c80c1d00c040c0320030010b07a4030004e640072414900001c2281d5907950381d8400f0f9858085c0744266424441901da4110072039482c000d13600b460f641900480d041d440081e040750a4100c2d503a1050b41628105655000c5210350540040c80c803800942 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 947971726 1250 947970476 947970479
    0x60d020d0b24150d0608010204031407050607030509090405070515090411041a0c19060b030606040b13021b060a24030c0b090402120103030306140d0f06091505010609 73
    0x2600111280c09002c81e00d000a9402c01c800b030000307042e04141d400b0310540004006501c0030040e010b60016000f0b000703418001c1d03544654a00c4d040544075070051140385070f401000e10126032864030380100c5080c1c41e019030f01c80b400c1c2100751341000482100540300312580d20820b0400950794852180101c0c0c07604042c0c0c0b0450300c1e207600f24248400c2c0c9100250100490300100402c0c00090805610786400f8813209560640b07030000410307414039089101d107180140c50302d8075400c8400c1001c6500035419550080c0d003690800e85600c3d06120540389034152042d8402d078810b4003d0b0f00288a50301500c8403014200c134610102c0000c802c1030b41420000d441c0950203035241e41c00b030b4080c0010758007440302c06440c3e51285244039286031112900c001141c09110046900000c0703c8409950300d030152940c402c000079282c106942d5a24001c2d0040c1042d10903810024131010f02da00142c5000d0250400f03503508020f040c00503c955035211002000a100b04813550901c8208045c5001c00900c02d040c00303000507841306a00c0a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 947972976 1250 947971726 947971741
    0x8030c10020d0213091d011b080714030901050103141603030e04060e101a162603102907060504062c060f060d0210050d02120103170301050102060f060d020d0b 70
    0x5580407200c031b955a04003c0c1c116003d10b00748400303240b03c0d055807a021329140c4179828121980e5482408081c140200881403100c4241c0642c40641240d104072100448046112075141d1503220380362000703014410001040001c01d0280c074000500c0c020090000480640700e002c182050320b42915040c822261020041c061340c8500c886544049401c0c020b8242896040c84c1403022041e60a00020405640720400f9103014030784503030820121034000c0c8669120b00c1c1009510303c140845100d081c0710443d8081502d281e0b0a1a80b18491a020410307401c2c601d020980d48403a400f41c003010f40100d500d26500c00300c14030386904007518913840205c01d0151800c00e20301c4000d114941000540300709071540036001032181d59500c550b100c0300010f078103541c20f2040645051081e5503a010760001243c0300e900000d0f901030480400642541a24411012131100801813201c0b01d90314042401b4541c050382c030603800b05130a4039100e9159079002178010080d610a4043ea0f0100720a4a0605c00c01c0392440410030501108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 947974226 1250 947972976 947973011
    0xf0706050604091e08041a0d05150612091905060925090f1401172517010e030a2604210207081207030908030c10020d021309 55
    0x215004950603c400021600c9002c58100e6040c00004440d40001c62041089024000d5400514801030081c142451250b006042c5500c640000010949070000250b03244c02c40003502081c41c140500043c0c1002c0754190405504000074020100c1c3c0e1003444062481d023014201c4841001e4422030240c05a8241964010720b0310b81d4850741071080c2c52340081c007040ca098840e804d802c201d4506220100d06043e2411700d00005010b0200030400d040c01204c004202c03080f8070040e21254095410494803042d404c81000c0c81d8440c54405801d00040e000d01040040d100881c03041c10f98405004000144046214207091a40e0720103002440400c0b850400c2801050020b0b00c281c1e81d000150b0701b6006d040c0b0706540c651400d860010b0100b85c84581030102030014074404c101200251450508075030062000c8142d28003d07411140c4101c00040400d00f01103030b04240801640c1d0050000030081c954503c0c0001c064000e03411055003551499424003819045401c00790080000303210a000000e9041d002c018803c14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 947975476 1250 947974226 947974231
    0x221070203070b0130030c02040608010203092401050409140703120e0418081b010501090b030c1f0521070309050c0d200a0308040303030203160c02030607081008030f070605 76
    0x41d148402d45c0e03241c0f0f41c0f41d0103188408203200d20144d000c00d0315440c040d6032804d11024042d4100d03140100228403204154002c502941c0c4d8801140d52005848405140c08040c0e07040c04003000420400400c03103410f1980007000054828101d9844510100445903c0c080656206a9044c3c1d4103c50240e140707900a19614a8140b040e00e00740304800d107041c81d440b020150804010500d2800250304140e4040b1040d144030840f4804000340701c10751396410000064003155402c02d210323020302016400c182c909000d0b000da400b445581c800d1034840c10000180e5098121402e81d64500c654960b100c812841ca0844052180105441c00503100c40542809850103200c1918a4014038081200c5c20204034a8080e0000d03801640103131300c820169400105900e5265544000c00c24000402c1c00700805425030042d41c4100410084c040c17440384620701c01c41d0130504000d40030790941c11140102c1c0103940302d001d001e03074071450b0344142103460381d582c410941c80d5901c01c04601150340c00200302c0307030100202c030701440b40c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 947976726 1250 947975476 947975489
    0x3141306080f0708150316180b0409051c0203070609030c05120f1e092709060106051803011d1011090f010c1401020310090c030507120221070203070b01 67
    0x2c040340740105025007507000143c041c010300d142007440c0c1a000c1c2d4040000d034841220303088103440007942d40c10100b403400001141c2c3d049a035040004801190800340320309081c1a030440c009007060f491051140d01034240041e000000c600040009101094150003119905071180c0e40b00d4a0300051420084c1c10b280c15001da26000c83d604010b080420749028051382c01c00c0d183c180c462840c00d130751031202075118403894088540062250819007203800c174803045c0030b060000014848140c1da4481c246d054441c1024040c010109605220306445080c06401700190ba4501800000d8102003820300e52000324134082201e59a42e2140050045c8000c044c09560110302c40003480500b003050701d070005200400410746150400c29401c03096400e208494000312245840c0ca80215660709200e640441e07400014003894141038103100301c49a5040c420b12070030b03118484642d60407804d6200207000704007070350055002e0319079958280b5000d020f240080c20701c1030113242c0c560000e607a41e020501d4003400001050707100e01b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 947977976 1250 947976726 947976751
    0xf12030210090b07110708070e091c050406120902040f0204150302030f0711120f0a0e0f0a030206030c070b01090b0f0910120602190f0305010f0501050706090314130608 74
    0x5000060b500580c0c0b44d0850000c0c140102c40035070585915103800c038107602c15031a03841111800906040851105401107031500e040d10081034003100c400c550180c0160b001300000d20100401c000c1075225148500d190f11440740301046040700c9400040c161003042e05101c1c0850790000d02006154481c00c03c040d503841c00f605041d41103141c010b4642e034001c80000d00700c005100d41044503200d901424080740426228003c5819126103a4800c200050b401000383c0b140803c0c80110352040904e44040300c5e90490100a05031007005080d5800d0003599000075111441507502400b10000166042408034068219900c00250101041082004486160031818002c41011051000c0c2e003404008180540f803c203001100030031791031700d4020000c0c403c003c00a1410011502c15108456100090403070109440e41c041c4200d9884900403c3c42c00303803d104083c0031580030041d9000054441d0880c0304424000d00b00200e40c20400e160421813940a410080c040340d410f510180030b0306401c005141d13000007a0f1800e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 947979226 1250 947977976 947977991
    0xa06050a0f0b25030804020108130b07030c02030903150402090115050d1113060c050f011107030e0604031b1502010605090406090c0b0f18040c0e15040f12030210 71
    0x5052155054002d160128500003510045039842c10040c008405a52030028507020309810300400a601c00e99041740010504000f09035801404069100010b420209510031612100400d030024403d41e4844000d500061001041c10342c2c0c2408003021061400004a11501d811f02c104440182e050300004400a070700710079808440d0340b0000342c45404002007000100401602c94602c160b004002ca90f48000a6401c0007180076039100e401c1103011441030040f0752a0503414160076090b103403030401c00810f034481405070002003480b81c0c2200c0716460001d89407a1500c0e48a40303c421103031004101c00685403007920002c000d20105007850000e2140c1520003046403038140703400140180b40161000c2d0240b512891804140035030311081000811151800b590703910603085281c400e17900500160f603c4801200d207034480302c3c10603010350001e012030b56030340100c0150701408002c680c0071011885800a801840082210508506200041d0180c1d00d841c008060f51444c00034a40142c1c00c0103445150f007440750 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 947980476 1250 947979226 947979239
    0x601050301061203300c170702060601051b0d0206220b01052b03080604060611030a0c0c0e0405150a14160302120f06010e0904200111150a06050a 64
    0x42c1d031030f841d6042c54201116503500c44140208101c500600020f0410316550603480203003a40800d00031030043e1560944c06d655501201c108103000c0b2254000340c1c00000001d0b0056103d80018071641c80544c4540b017045800105844c9424210050304015034440f90920010001030341860340c0b038406000004c1801d640669a00d119804103105490244c8181c10101c00d5540c40ca4041c60060240c0d2a1042c008889505008052490546a05000302d01d0840085103261250600d20124456035000310300c1c1030101c000403150031007124019502140029070101c2e103402c103590810f00581c020001007001807500c0e04000e01c040b5024040d00c107090319000e41d03030400a2100900903030101100400304c2895010a00c00d401038030407060040b4180c0303012800c002c1c2d2040a03000c5940101c4c001c0c0d80c0c42c00f108102e502070080c1a2001d84001c0d001c0400c90a8491140350703903588400c20248107141000e1802000d112a0346003800004640403101100d00800c9030380c2e501d51194100034641210b511000514064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 947981726 1250 947980476 947980499
    0x13080a0b0619090b120102190914221803050915161719050c16120807020a0f09021801140702061602090408041406190f020a23060105030106 62
    0x483c10031010b03210950f428003079542ca0390b128461500c0304006c3d542e42580c81080b0343c100c00801d0004011030001c11010414030000440c0346110349021340500c02510900040c3e265a00c0071003184022113885041c52802e0401c11140801c04d80d01c01d885580d107031101c807410403040703c0101c080b0312010f54060044051100c0c1c981d0309510515000075403565032102400622005101d1f00103400710320300c040b0a507060030340d52110040543e0360207601650482210180c42c00c8191250f88503003080112480406808103040c00c0c0202640c51006143c1d601241d621429103a0384150340d4070100805a0105d48500103095a485441942809180105902200440c1407040b8026144d020780540710104031245000f040030702401c15981c00034040d030514900740c44c100c5095406406442060881102c2000c12070601c1c100b99001d5840e510b45070b80312b840d212203085604e1704400646d0011031280160b0b000100d07001c06514007100042040300f0400d00800c1e0f6003185441c4040c0e0006010ba03140031801c22036074900700b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 947982976 1250 947981726 947981729
    0xf090a1e0201140307180506030403091e051f020d110613110306040501020a091509030605070201090614090f030f040e06031f020702090a020310051513080a0b0619 72
    0x24024a2600911800122689102c40d1810100c90f00000140942c160b08450040840142c0014a046298913a414000701d8082a10700402280300b8281c00d205d580b1104558648207081d45820f128040c1d95400059003405010b20075400d041d82400c410403140f9810700110342c0704082414030301915003410202c50790760f18004118003080b0784403160000c104400b4000d00e200407034000b0121041c034200b5050881c001c0d8014101040400d20a51000458940f88014a40d60305100c3d112028980d2a40e02c0e80d80103044d008214100319540c5489890006a46104400650006404000c0146040f24429281240c0190405603d61051240340c80c0c0002c1c41044070282d4003254012032158480e0004240b0303280e01842c600303200c50308091900e00c410b19268050700070305008803191017440e240d1005280480c8001d0b55a03408141c2649818401401e01c00040c001d51990080c00500d004200d9a00750b0020800d81c1088945800440e840c00c00e10004040640c0c00c80c108071014603e04c81890300c2c035081f8200070b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 947984226 1250 947982976 947983013
    0xc031d0f010f0203040306060308030907151b0c0504050f16020c090c0c0c060c100606030c0f030b0a09020f180103020c0307062c030d0e010605010f05031312080f090a 73
    0x20402c1c044895482841030300d0003036a0110b410702201c1c1d120f183c40301050704100e914181e5803040110002d540006005c001100100c81d89030000181808001d46562103031403a070945112a849500060035142d61040c075103c0e001d0708401000c141040300020901d401403908900440d0301100d20080ca503075451400c190800031500d42c2950f01c86800c8242400c00f44501e14141c0e000e075000c90211003481000c03d91b60505002c0802c20004151500020f408407480e0f54010400121600b819606080c004c0d40045040c50004240c5540760350b40d0700c206016a0b00010710f01c40d5104003c00c107020b908941040f540c000906c01d003010340c105401120701a982c0d02030341c00c010301015102c0340c4102c0b5444201c070b81e1026100c00038290840c45510301030030a075294000340030b80564502e000c0c00c2003580d14044c80754002b500d405035101703118034010041c00c80711908003a0200203001303100d90b648c078000784086000300d42c09034583c0c907000c0d0140b82840840510686c01003c11002d60000b07074041002802003944030303440c0c42d40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 947985476 1250 947984226 947984237
    0x120711101e18140d081b09010818030406090806060906180a110307032a051b1c020106060f0305040b13050109050a0501051006020f0c090612030a0c031d0f01 69
    0x10041a000d11902105400f03408401c40441e50801c41401098444003000341d610fa1041644a6500441e2900921004180c511005020b000003c0d8850f640041d08032802e5404031280d03000c0c061256041d607200f5030040000c1180e060080240803003d00c50254481401c47d014026860030030082888248480140d11074200c16800181c20540f15900c42460a8500701c401500c901d05a080a40280a42e00a9030284100289040c0d804828504503421200e110380e102070501c403045034001009048660541f07068040e1600845200040c1301d00c0030705090040d07001181c090311b0a0009001c0703411340402c800c00c040c00d1200708030120700d0b10700c0040e401284100441d04000d1107800c01754010306004c100200780740581700340d401c20b2103015003020740586061514190382d159520030581c1d940d08680c40c83c5100ea0886020440f80f40703042d00080c0d50180f03000c0c10b803517100445c2c1402035085902c030780a02c40105115079101010300d076104940c03e0101c1204548161200040000035080e4485000201e0401c00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 947986726 1250 947985476 947985491
    0xd0e041d0307081b0601090b04050a0e0a080904200406081303050702010c02131505040c1d12160315060506090609210703060b120105070c03080c120711101e 69
    0x51524405442094520207545d22940c503010440701510440c950340380300c1c2d03080c0350100b40360101ca4880c80410400510042c40140d07030710740c0d44159a41107224402d60013a507400d5040000c442a90f03803d80d44884c0016050344e11418844040d0a5085c080c124041103282407040d640040d400c901200c251a8090030f28020401241c07001403510b15905050490181c10302e40201c210030a24103541e4155001203400b4040102c0115080721a589280310507401090742c203091454034107000b016030b410075001c002070302c0358204403180300d806054a9510840c2c0800140d03855444800d000e100703403400f40804070b981610b020007540005100b4043e00c11000c1c0310f180342d401840e80000d061403185581000e40800d5400090b640d003002c0d0300401c401100a802406e002c0a0080c001c2018811503100d1030081d00e5000018100b510101d59025000f06890a04c807001c011001400ca0040c0e4424070030491907554880600c034025565040c00041d08104e00040e0402d5103030807c00c00300024981511240382000500e01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 947987976 1250 947986726 947986747
    0x30803130c050622060203030c0906071104050c030f0c341e0201080a020c2a210f0106030308010510030204120c03020928110c0d0e041d030708 63
    0xd4010782c07009500510019462400d15140100c0442648100d00903448281d51980140e0303c1e44000c841007000c10310200220040e41c6005d0f40a030a00500452100c3d036800006800308040700e409540c0b00c0840728000c402c1100b04019140c0c03c0394405110b800d101e08100a004074501218048610203054400b00500440e00782d6074100f150350031a800103024208030745454060340d880100500d003a800546601c0c0000c950041a0003201d03d110000d0004242d441c0c101d610302c104401e020340d582d001090f0400124109550323404100e804802c50712454140290030101a04e28040581000c80c046904292041000c280c00c04c0c50641120426100c00451011000003103000384a05c0d0030441c003500b6070a00a00c04d10121100c54010781e8429503014001d1b0f10381006800782d143d44c142e840c0201109400007003610000c1500714010000401420f00c0c10308403c00d1005003044440d0b14640f0020303500070a99001c81c40e0500074070224220000058420040319001c0607168482c0e0f44015041e20400204111003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 947989226 1250 947987976 947987993
    0x60504110307030b070f0306140402071a01181802090a050712240f0803030403120608060405060405120a1e050403080c060105010f0f05070f110a0314070f03080313 72
    0x9000741950401516481d1040e4030902c20b0b15a4000540b180d645007815600900c00d0700f094408200141c03c0c113401920030003019600907803040301c0301795080d4030440e00400403805041c06000c1d0040d02644011000705120108c42d42c85e41000c00100c1080c40319005a10380745000c1d13801c480c1c11400400d0a640d007a1003500c115162869036036140d8a07142d0100d502c4c091060900300740141a407150103069035951005c502c0100799005018240d04100041790000c4d0058007070762074240c0c0342031012032030540e901103030390511008803810754581d08054208002c10a06009690a0341c070101e8815007806940e0000070151409110490074030b500640f20955464001d50945004580c09008103688045004803a40c64030820301c0740901180d0100075503103126010300180e0015000654030142010786c5030325510385880103210f080d80d15500314207940104e40c40340c0d000900554001c0b6442c0080e01c0b039080303145140550307a6101908004420341c0601c00250020210394010700240c1c1c80030710413101410308902 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 947990476 1250 947989226 947989253
    0x80c0a0c061223072f07060503010f06180308070b1005011112070f02030601031a0606040303050f0307030e0609011401050d050601050639060a052502122107050a0507060504 76
    0x3091020700300c90345e6044c0030800f05070050b00380300300954001e6640c0340d009503407601003030141e4078203540304000c1030003014855014016510903032040b83c28070f5640c94480c01d9090f406648252080030001b030811032141c03101e40400004040a10b0110018101e030780190352038407440c400b424501e440010341c0105200803003072a99a1b164000701550410350796450003e25607654810301c01401081180016007514001d4196405c0f40c2d05a02d62034540900004e0700c01e5617900080c0318905069981511450300b000400c4014421600000006240c503100d008044080c034050703002d5481a09401001000500d0104455045840640f02c107a11645060700c0c0444d6080b01e03820340000341d40414000f1040804141e08034541e000f8540a032050390721581c3c2c030340094079022941c0b01d140d40710105442544008259140d0000007036131060f912000040807401d001580100c500b08107a018a802d5048170254409105401101c02e040440c64001c60280240c100e0080000291405503030310001030030300c000007002c0e40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 947991726 1250 947990476 947990507
    0x43f0f06021801020601140603220605072307080f130305010207121e08060121060e061804051b060405130911030c0108060d080c0a0c06122307 63
    0x64940c6048000b40440b400600d980ea401486030700000107420003555048125080c0c090140c034a1543c0d803601610300f080168269420004100d004880071034903034407495020381115a105141c0100481451080d25010261000f440c5020040c03240003030016012a254402c844101c541c41e003a000510001152290380080c00b654000503020b81002480c40d4180c08003062502d42c0c2c02046e002e08114441c11801420207001305000d040400d1483d8041c0b0700250792000a1110040b10065072038081041d2803040e072110040781e2003041030088501d85600440b0f5246d058003101081440c0581341d283d074445040307295101250007058005026141c49085801405000d454420074100402d0307414000c150801060364021201d074000c1340a803230042824068178805035180f210302d88641d4100100022030350001c41c1c0b001001c02450000807000c5c001010414010107161803017514212000d03001076441e41340000d0140c0f501e104941c0020101c50390850200f001c95141426641c0c101c401c0d02c1a00d80040c059 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 947992976 1250 947991726 947991731
    0x103110111031b0d0327050c121506091b0c0102070206030c07020a0f05010f080901060e04051f0c05031f030605011211090c071203090206030408043f0f06 68
    0x201c2d11140215a0091070310030500485003030301c0342d04008604586800010710044504107848a840740940c0c01c0d200c01b41030095050340d0b034007004507000030f000200030f642102440c7c0003a5000a02820070b0801d242d4005001c1e200003806240004041c1081c07036550040c103d0313501010502c60817402c404d40c1a148802d601502295403410810030440f0310b44c002542c1284250042c8001168213010844580203c03031041c1c603481d65010003e0403d90710400000d051290b82c0d07581c0c0100003906110300000340c0c05180202d000d04507860300c148030740e04000da40e44810720013541084404a18640d000301120b40c000d0000340716070011042c2c03118004180c01198800750146082c00c0c00482c4c500340d168039140e0807a1048200220b00701c2c0103400d000e0011800c8949800e40300d0180080303404031b441002861011300035480c0003d0702c0001c1d40d00142e61500b0a507402d82da0104049024080c0c550302c03029104504070310804400941440d9802c400507030a02410305e07151041c40c2500c0400300244880307001c841310b5101070f09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 947994226 1250 947992976 947992987
    0x91109061204171b16050619030207020d0305120708010608070e0d150e0c030c0a0329073b01031e02040b07021008040b061507050303040521040e010311011103 70
    0x4203100c24400c844d00704040d01402c3e400c8601c0011a41c442c0e82150006085542014000d543c2441c019440c54000d0081c107400300554001a920359100119040c482d031682d50729800421014083c4210003850201070140700801030007800d41103010f041e400f003002d00e402c0305440300e07503004150040c08259006016aa0400c102e0040c40895040107450764444411110519005010140d4038a01451100e40050a00d42e060001c95603000c80400c030119a08100c540d4400d240f0004a41d10380d04031054000186032000394031035800c103044101031492265046034040303c43c0072030030380c001882000141c1c1810380d81d000c022940201040c000300c451105290440d1584c1e41e03601800031a6115031002c80c480c0c0041405090168007805c0500d0103241c024581d124656108828801e9a0a031b8000d54819120103005034030010b0000c01c0110b200ea44a4400707071100030304002815140300f03035104140310860010700040c0035404104904604403500315661506880c080c8005070340ca00b001c00c1c4100f070580000100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 947995476 1250 947994226 947994247
    0x702060a030e0f1507020d05040e1017010b0901050a0501080f1906030b0405010f0527100627050106020c01120b030319110d0f030b0a09050a0609110906120417 70
    0x18a00240413541c0842c00b400d0b6540c10040341c440900d41c08001c08550b050200740240c4840807000342c1e00c00c000220002113151181124544d81035000c5c031448042e034494041e01d81c03500300303600041e00600f030664110f1501414080080c007407503001414444c0001c091000544200f003003203e4954440c0700501c08012003a12428403045074101240c06980541c20070b421100880c20600c1481e20468565003030700201c0f0807208a03030140e84440d00d418109849403d084010200f82c034410000100010001c0d414500700c0540f04034481c1c0b02c4101d406601e0703071801004104264011802c40031418092070a0b4200d8040584801c0c01450110001509480041061b4125000001001810310700300d0b26151540035443c00301c0c566680006807078100144441c2e084100d058040c0d04084030541c1c000301040e07410b81c0c4682117181207030b400703d0b9002c45c0d5075101c0e0800c20032407540744500200048010b000b5841c0280070400f03c0e860b8401c000504031000f5503c00000c05009081186000114540c440d640d5200320303018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 947996726 1250 947995476 947995483
    0x91805060f130207170a080103120201020408010c050910030e10022b140a060302030d05070501140403090609060c23030f0d02130501020d0c030503090109020429060f0702060a030e0f 80
    0xb4411510007940312541c05c0b10712103207000e4814051683e5a0301c0440d030309507510072070420441d00ca040c044d503400748000f00f01e824080c01440e0009003603640f081c0c1c55841c17a2007080f540c81000c110400030b05140007111014048041019032100c0040c00700980c0c1c03860030010394400e200502c10364040e100c104503c215030715001c03608000315802440810107042d44810034217208482403884025416441441050b480d5401100645034aa000c1d000003d01140c0c90724070b00d48150401c0390214005030301070005001040e00303c001c900c0984407038504880381494030341d9007000c0001350f05034604608000c06500e59070300d40c040003104e00400b000c0c4d2600703031104100d01c1d190340031f5000103910048000800d800414a54400110000004e441d5a03804100b20369548080e41da540c000389c00c0d030045540b20714018000d80ca460040c0d00f540540f013003944a001d41c3c1102c00a08840d144075145106600c10005490b01c4800841a900140d4045451079501d68288a0550040c044d000900d00240155001e0790101c01003c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 947997976 1250 947996726 947996737
    0xa05040e03070c150822120e28050f0a03020a090e0d0305090303160e03030403051507030506010f03020307051224300c03010509030a0f091805060f1302 67
    0x100d44001c1c03e07a44844508041e0600008428001081c207070000341c0e04d00810020742e14101008889140c14856034503503405030855142660045000c0c203191480320b042c0a1a681c8148242e035040c1c8484c5401400500c0c2420503a04c00c60b13200d10005003180c1034540c0c44c0d030300a4000303680c000c04885d5282d81c0c40c114000a061450809a0140127940600916500038010180b0548102000c0d624560b0f170103c18211011030082150104035600e082c10200b510204020405580100010a90000c44001310f280f41400208031078109403c000030300400713980004805040c102035050250301c2e41c0e10305500f2121801900030300048035000c2c40a0220200055007805041007100c03400d013001c1d09100d410b12002c04100f480010f4540c8200c00081255902c400c4810500d10700c400c141c850103051200040c1c25074005403031400c0740e40c00003e00407203143d4024004501c1c00c0b0450a002c14203e00c0c154a904032480700e501c0d036403010743c3c0300c0f8000389280c2e450044880c03190b04000c2aa104004803845428001e4001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 947999226 1250 947997976 947997983
    0x280609080d030c091206060306020406120516050403080a120906020d0e010b0f0f0f030f1c02060403050319090210050c1218060f0c0106030f02090a0213050f0a05040e0307 75
    0x68154100c074991280c041c80918296945607195885d181504110301c05d00412001c2d550990360315004400581d03507000400081000382e440703800464000590b4030496001910600140c00c0c044c01141036076800c4420303142181d8004203510b4440c04009000e55003407504001202a103481d00a4007070822041e98094952044007502c1006038050100b2014200c810150401c4d80c060a4884801c80300e00c2e04a000d040a4100604903850b207408200120b440e0030b950090b802d40e250005010a11011154400d902504203144010400c504060300c010340f55200c054081c001040300080020805800c41c4c02c003881c0e6607400f400e5481c030440022001406600030110340420340c02458031500740040b82d60217440d0564404008800d2030410242001f07284e9000030407040c0000010310103035241c25028885c2c01d00a40c01614032840141e43c070300c10001560b0005100c401c44a1040c1300c0e490446403559059000e0300d03000d41e48680c42c1c00154000032a107078019403290382d1050802e40c0c40d40c030000b4003101504c81c080c0f1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 948000476 1250 947999226 947999233
    0x31009030206010f14010e060c0c0405040b09010509030412120306150c2105190e090a0b03010b040c02060402040504170f0c070911300c03150907020a0228060908 71
    0x201e0300200b0103a41c5030340c040e0b14001500f94401d1200703403410380c0c0141903c41061084500000b2b242d0041070035544120b40035a012080304080141207013003801501e9000f1150006146841d0801010b807a01d0b1346c1001000d0032a80b008c8c0923641c41035001c1e60150340640079051040c41d4404803400c0050013410040d84c00c5540382445c4880044115200211200b0700360181c07515414005407640818600e9103071078642c0100701035400400345540f030303e111443c003900c407006001c01c1c7c0300028070074503082d588600e050500561030490900301283d4042042a000b03a41182c0104040d2038906000501c6104072241c42080c040c0080d40019211341d000003080c14018203410b8810072652010900e044030291041c9001c54603082040c0c010307405421000c0700c1c003906d074002d00390f040d41c04082281300e480a04840204084034008140704000601b0710064103c103000326448000c0b80b90911000f501c0e42c0c00404000c0c01082d01d0018040001d031101e01c900034030108180103005065903a0001800001c441c49070f54660300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 948001726 1250 948000476 948000479
    0x90f06010e030c0d081c0501060c062004030605091c0f0306120b070525060902031e100b0414070915080906060f010e0d0b0601030b04091101050306031009030206010f 73
    0x100801c5240000000034020040c111068030303801c21701c1d44031505003643d84c1a2003c07050758154452082e81d010b040613030340d100c040c04220300d4101d0844604038900d10302445400300f045411142d031400c40f03050700da0065003c03a81d500c036007450500d0f018803c0ea805140c0c000703460051b4103040c0c2c418400f044032019541d0510107156a20218054009820b802030104c1841c2000501044c0c000c0c001821440000103c6440ea0041e41d100c13007148a00a25040b544c3c50384841c580403d61504001c01c010103210401c501004c00d0700034501a44d10111921900c090710340307c0c882d00c8510740c0c440d4081380b0041d1031034070003060910381503000500140c064060481d845940748107595509100f852010f1040b82c020008000585603002040079a90741d0b4150700e410040003d040812984803810600001403141010010074100302001400307851407100028000c5141040c1500440d442c0341682180c0e40082c20180d6403500c54201003420700b61008006043e25003010302d0030041544c005400d9040b6080c2c3c403800c148a9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 948002976 1250 948001726 948001729
    0xb031504090b070302070c0b041829010e01200304060212030c0403031b060c170c0c03090d020a0e100317041409070504080d021609020403031b05010b090f06010e 71
    0x407507200d1005441c9501140028515074060390051141c50700405000980d6559224516010b5200703411603409030289025000c03c0012a0003110701e100685507070050a8111a003268500c0c11060f5451410000350342c00000a90340501d0005a4201201100300201c0c1201d150707250b0307281d100d485690014030400701d096880c1955001920b00800005e0f620500c0c03e451610125860000440e8031043c0841c1d48032028001039443c0710b100a4498561074200b901d8a9041c8100d0070b40a0060195040c1c000410020344513440110407105861422112408200d00034004546401290b4100b40c166895610601c6200719052520380e04880c4103442c240b41c0340f800356600360301d1401540f055011240100e92030250624040141c2907208840b480e0180c14665545030b4507140107498140c480160300301100c001c41a5548050348805003502d620706620340391a540d0001c043e00708480000c1000c5680c14003d05c00c1107003c1d000242d017010014404403443c00c002c40c180c0414102943c0d00350100394240c403040e907107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 948004226 1250 948002976 948002981
    0x6050f011b06020a091205060907050a080d050c010902061b2103040f030212190e0d0b060603100806100518040503030628080f0607050423040e06010b031504 69
    0x441c02203100656a0410b6690001940010003001c0034041118000704030602460050302915004000520075410001a05420711605802c0300740158040001400020000151143d104150346040b5650300840c0a02d980102216400250f1210001500c511071290801d51075206100820a880354000618400c100c4c03007101d1407007110280001d200280104060728090602c0034001c0c0143e421000c5050840910b590100b61400d0808062024840c84070f503001d50181107000041d00d5940395081162501260100c0041100c0e00c07030315002000411044145104800030020502110600e040c03890605034594401c0c020303140140441d03924004108542c6400703500039500003018518584031001480241513482c221300019110700e1b081508100e07210f4032550300500300e070400b4003115100c1c0381c20030b41000b001401e81410050244414051f058001e03504403a4401d01c2000c03118000c8003880810301502c228121010503004072800002c01410140c02544244041c0714074503031100400e8100402c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 948005476 1250 948004226 948004247
    0x7060201060521011805012310031b030b0709092706110c060f0115020721480e2e080a02090a091115090a030606050f01 53
    0x5005150103481101030b141e151554020183c48800869203c03000da801c0d4424800c410340484450b1741d10702d83c2c1480941200040c001c400070301000c4045070b0501d5007454541c0074a500001e800100c1418019051250303058000c03000b1580503580405900d050ba1016000c051b092080019250402009000314095040580840b114810b803800681009840e00d030300810000418500e24502000750410540082100502c138541d00038210319658100342c0750304207884000d8150019544054020301c19944036846400400c0007180e0410700020702400d20f5099400400120b00c00344103a02441f40039004001c8040b030042a0118001310091450034420259000c01d12034500000b100743e0102c1d8814a060750b10215102050010290503030325580f1190784a40d49500001e601d60151162604505010900b0395100030050310400086407039423a04800c4052025a031486a2102c05400318124610000d45200d00c0c0040e0010303402a449103880c01c02090302d03004443c404e6254000703c07a07081d80301c6d148010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 948006726 1250 948005476 948005479
    0xa11182403060f10051801030225020f12120f0904051509071110090c0504051e0109020a080106050c070905011203020709180f14060403210e0d2006100602070602010605 74
    0x186006c0141190005503000e4903502c40c1015004c00210401740703c00c61440c00d00c3d21004d502e0310301c01005881040300c042d00312140640203030b4512540400321080405c00a0f08203149520042d603824401e0441e1f1030b9841038140050b4010b18003000c0c0080d01c4486815803682d07050a0b111501213031175220042e02c0211480c0b4000c05154020140c4201030200e41e000205000d10440640006640340c0001030300303442c012240841c880461160026200410b052410300400e80041c04502d02001088010b05402e03050003003005010002070440c0b00440704001ca10001c0480960230407407540c4904441c10840710800090340184540b0b03a01089e5508180b15001e00100a040e1402ea24511a52425104255107205640d154045d08e009103041d00c00303200b81441548207564244009408142c02040c000b6040f034070035001c519003a01030b03c551070000b85064080c00d0608050241d6991205403000103000c8141c40a038500030b8009100c00024142800c005507207241e02541c00c03868a0743c00480c200d954030310505 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 948007976 1250 948006726 948006737
    0x1050603120a030903020a0501050705031015020d030506011e0e01031d19030c05061009060e07120209040b0d111c0b010317042c0a11182403060f10 65
    0x10101c0b070303000b940000305441c4240140c50000505456960846000300d9103c00411400010400a40c0c0d0550300400541199000b0b0310f2260720881c002965500030101c0201855600c0c404944168010300d007a2800039100d5505640076240c0d45801440d90549403d5640840d0400800c400c845c100604031300c42d04403d0000030528a1080100c0e08600c3c4080c04e000d409101c01124a031020550a001c1d65100d00c41e07020191688505d020700440460321581d0050340380c90300f20401d01200945c0491600c0401d0a060000741e20f0741542c0380010300610032402480d501040300d26402d01000103d1800340150b00d81106c2c601d96030310a4094200319540301100040c240300c0d00d500144001003803183c1c4914550040b01c599828292200d80c0c62200c051070925200c0400c1c48000c0210001840d100c2c9603510a51202091001d0020700d034450700180139190040c041d210104941e00d6040e11030b00c00ba6102c0d08150b02041c040c00d4030300f56413210a41e10030354000c0c0c0940041c0d01c200f00382d030078840c80d41d005061103607a44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 948009226 1250 948007976 948007987
    0x41e140109060c05070b1902070503040303020706080f0103081206040f020d05011d0702060a020f0d0e03070b070306082d0a03050304110a03020612130209011502010510050303120714030f090105060312 88
    0x1281c0c00e059841100c501ca948e0078002000440c20410240c0003452184c0c000f0840030303060602c05044120010200407040340c1000051000400c5e403800c5e503485400d0552125103d440d0031000a000e020185030010f40380b0310210b45074541401d241c01103812200b42a0407103a0314000008000c4c0e00342c10072991600964400b0002c10300d070458544c006c01880396400403c50415980c1d00d42141a20710030220119587d06c00f0a94030300313000c40080815000078050404101c10761030461402d8a45229480d81c00c9150154450032928884040c024070f001304001c802e4400c6004c491070301400c541c00070348056505800f2995039040a00b05000c0310000e4940003040b0b01d0030540080c05640c1c070104010604403418000c1d40148005840300842103020303041c5221089491107481d180207085605c02041d003441c400d00c0001c00c000507100482102c040060701d4071000d0403a500e1180507105060514500f803c00c4500004202d014040541c07224001c1001100a000c01d494501c02c151380d80d00340480480121100300300c1e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 948010476 1250 948009226 948009241
    0xc04050a0b0108010e0c07061a01031a0f01110f06010b22180f091a090c01030b060301050103050403021603081c020703090b0903010b031218030a0b041e140109060c05070b 75
    0x10030a0340450350460540c41c120703290f5100701c240c1d104556000d150b50050b27001c074903da47c0c05000f03200f00b40301840c42d000c07502c1e1740c2d041c00075030210310780418103050000349450038444100501008000b4042c02d011135180b0b59651001d0580342e80110800704a1403005c0040114003088c5800100031a140e26403400301204005010100900401c056094683e030740b9100d200005003203002c01c1219125280c0f11081d1460076135000303030810002145039410545400c01c02c1c9420307640c0006803410340703c0078600050701d0396a500c0d00344c0c42c10111180c40115880020400000c028004d0010040c1c00809000308a03c022401c10700d6050b40110540140482d80f0f1500038050b190b02480a4001807400400225801e1650000b203400d041d100d400348180030030002000700d0551240003501c24141c005400401e0b1610340c9446820300c600300600010000322910a001d0341900d404007a12840079008641c004010b22022a010300a1007404c90464055041c0030404181c4d074000c3d01602d15079a0400388440c038a60320001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 948011726 1250 948010476 948010499
    0x30203150709060302031e04030903030305060f03030d151212120614041a04020f030603010e06070c030302090103110a051b06070912050a14060717131b170c04050a0b010801 76
    0x9116061420900034052587c4400307a00d600d0050380240c45524509007582801800d88000810b2280605c170411441e4680317071400022580d0003601150005502c0c8a49803000c0301401403030340b0a001000001c1110802e00c0074550745581d10064580341e00401e107503040c202c401518080d218030803802070f43c1c501100d030906184d0012000043e00c41c00d0040c603da80c100010b030890b0844c00d2410060180801088880d0a0911500040c0383c2d80304002c103d6442c140704020704a4411020040406030049130305542640a9045444840300c480020fa1b1548051500203005410011117106080c03070601d00701088100110342103005540d01d40d00c1201d4a400c01c9078446101e240c000040b541e500c1120b1032100424440c203102c07a40b4402c4103000d0001030074104002000e503248000d2411a000803172061000000f00380801d0000307550301404070016485000c108004131400ea034442818501c8031005900445001700b1312000e8100c04850030029a1928491482190340b101d041d0380c041a00d050042c40440c2405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 948012976 1250 948011726 948011731
    0x215030712020d020c150903091302070218040201020129011107120602070b07050f0910050c010e07260a060e120f0a0f0e090612030f04030c03020315070906030203 72
    0x90900c000c40d8070190141c1d904990280e00315881041d030118004c190303003805000c10500d20f40c0e02d5a403c6072608000141c117489114034002d21b03104600a041c030740a14156030301a1690309800400c1004603805080d01c81d00c16140480f01240154030b4400c1d00a101080040d491340f4001d005000d84203100002001582c0b050010707030044c040707817207815000034030a14940401654580b0802001d42c4845e410710b41590341c0c210103001c40051120500201030a601020141c4080200c110b8540c60301340e0760710f041a84d00d4401c180b81c5403099420044000d400d528002890f008031003c03907c000c4110b0a40580510b0801d030b280000d4021900280c030800040390964003c1802071054000b501c004080041010303d10782c0c00541111004503001c9100c600e220b410840180c1c100c4001e081078201038900c840000c0000c2001040a4131030300310f004862541043c00c0068540c408447c2d4401c650303a50300e03420f09402044491200300c0c800e1252991030710602c41d842490301d00070301c40c648521f0742c41418504182d000e900300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 948014226 1250 948012976 948012991
    0x91212310302012f0a02030f150a09020d02100305040b01050f06070b0a0e0a0318050906030a0201030f1e0219050a0c030e0d0c030809010801090c210e0303090d120504021503 76
    0x103450344d84203003ca84030950081840b0701d0001c0001600c40e2041c1418410401c815121b43d801403401c41609c00c580c000741e01d6010b58030550010781c00d00380340b000991068610720003070341082c0c00900c0b14105c5900f6a000070b0240380140e083c0030f400da0340c5500f003141d0900011025034004609111510000361707008203154002004c00400310f072030340d001c0f0801490b0150045069001aa045c003010006012401d85c80c07003e01401d40d10701c3c0703440c0303051030200380d45150340c00303009040581d281640840d00319142c1c05800c03000061406100d8151100c5d550b000079402c52206403c02a240010b81081180180b00300c0344408840c0e21200710100082c0c50644401c807482c0b00c41900710100001c2080040c00d00c1044c4409140702c6c0d0700e4181ca4986150004280ca20160010794050307150181200ca030903041541c0f41d00360000300210030110311642d0140006401c200c81060218400802880f00c6004042004900c08803255240c400707c40c04500d40030b003929406d9030083c0d00041c800c1020000b0a24807001503911404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 948015476 1250 948014226 948014267
    0x30702120307050d18050f06040e1005120c0a05090402150703050408011d010e0610150e0a09200712030f020c0d030608120f03060609121231030201 65
    0xc0e00d0300c8460900000030303140030001c0c0c5000e0750742403520412650380c4050542a6046003004041f080420000d1203035002d169420f0101000103010342c004040341e01d000e4007024048d8035030407100e03294281c1ea1350010354683c1e103d4580900e010501c0d06141141d44d12554001b000b0301c4031a0180840c8031003943c4500d0081d0204541040042080a03090080001c011b4803c00b102103d490700c0e5100b60f0071104407001c1e0071404e8104105101312400046141020345401205c040d620185c2c2c4141a1020300114040c1c0d6001081c0d81c00c0024000c801d68041c400b0100b05030441e01e00710000311840c0074180300350100148451040e6032083d080030b219900003084c9007406c1000500c0c000030805185d103401d41940ca00d0700020703200c40301800742e142c081c481b00f4400d16940c10b0107820651462611082400300400b124018032001c6030070324060355205080c4ac200d1b21036100365041e094980381c2c6c02095034854400006518003148081030f01076002048038415400180b89003504038290360044070b40e842c00c107c03007218a62 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 948016726 1250 948015476 948015487
    0x30d0807030e060631111b0a1a1e0103050a051908041514031003141506040b01270f060c0201020c01030902041d01021b07061e140d0203070e04020405030307021203 72
    0x2040740c0b01e08034141941c0303031b0190b8031180441844440d9040c2101c01405039003004041900080c4608824101051a01154029990380480c8150582c80c0348a0240d84c01464000000c280940814000029805401620911102d00600e41c482c0c1404541c010640c420812040045412200b00790389203a11500d0000116400200d24039008d42050f1100c160440550408004000e80316508080ca0011034001e0081900075850600e40da54000f40224010382d1903068003051a88181c140c80c6c08442d04150000220044581d1230004900601940d0b070039203000b00340031613054010741c0f50800c036550503030003040c1c1c0c1e001040c0110003510301d00038102d80280d11504c0d40540e8600448040f000280351130001170319031340000125504611030910302c00203070308141402c1c04040c0d80400b0400d150140642c0d265100b04101008a8a00302084010007101001240c1d080345404190010340c0650850b0b60f980f003201d802001040120301c01c07413060962641c002c0000d87c0050400c491540030011a441c00c0d00c0c1410b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 948017976 1250 948016726 948016819
    0x81c0204050d110102010509061b03060f040c0f14090607110a0b04060c0611090a03140f161412031617070b040c1208160809030d0807030e0606 63
    0x1800d02d0012100385158107585102075034248111940b100360a00285901d041a40705414805034900b024414100d0000005800340c580c40307803c17030309a5000f0b0400c01076140c10020003041401c1414107640041d5004c2e10041a4444e1402a07810340703000103004914003c1c1740d944080705402e40710511078000e01120030004078180700001a00c0101065103541500103010300c1c05208588102d030b40c000c2005000e10a00d411601c61240003426030b540f0440d8600380c8560b019040f40741c5000400d02030218400c1c1050013107800341d050154011118600350100c203e924040c10061280424070004103d42d00a0042c94468000182c1e0322208034010f488209521811036041210f5030310040b4162580002d00040c0410030507005099401000e00624003040031141d580c81001174403c004031140c00c401c0c0c0e0380030072013030000100460b550380400904481d01340e180490080c284480c21034404001c42d1614280c8260b010000c50010b104401c0203085103d103078503451100d1700240942e810000410350000440b080f2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 948019226 1250 948017976 948017989
    0x1d1e160b160f05100f06061b1e1502040603060501030c020d0806010e0a1e15020c0d0312020d090201020607030b1522090504021512070819060b07110d081c020405 71
    0x90581380c0c0c2d400300350401181c02d0b45068aa181c2d103d072080190789030080034040aa010941081980048406c0c0b4125003c0b0700c1440360300e00b40034040c060000a410034012101d031a402081210059241444103c0e0f0300e00055045954130421b90001da081340d880074850520400440c2e51024050500c00c00012140d030109a4203001c540145012200744408a0300030000304004600812050b00f0180e02100c03543c0f8025240e49c13071740f5251802a502c034000a802c04d80a82443d0481c17142d44402103407210f00b401907000c0500108001680540950000300c2c40791846400b540c0c051300300140c40400c46220001e02a040c030790100615030004c0310495a0351840c8200941c00c5030041900d8540412107060500402c029240c19000003c0b082c0010401003a0b5200f021303503055406903490078501030319601d5040c0511074040c40060446031501e451000710380c0c44201000b0708011402880024604160441881200744213150081c200682c188900511884111018004003100356000f41c100341e620404207030f4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 948020476 1250 948019226 948019243
    0x501140d05010609020c2a0a03031124041109090a020d0204111201080f0d0801060503070e0a08030d060509010605030c0a030b030a210807121d1e160b160f05 69
    0x10700e80c0210034002242001c03941000800c0c0306040000407c0720450700041c0c680e400c184801802c0c00038038000442c40c860180545810a40c040a1a20100345641c0000a40a4046500300e408244c03031203c503d81da0a200d440780c0d114040000c0182000301d0070b60200403400c09090b10480c0e206c0e07154404040100300100141c40515203120031a640c550600c2d01d41401d03d06400c0043d41b43c6e50000d44859101c0390f01415560448046003442c59580c1c0700c0480403900441e011040c40e41002c0ca045c40010744540000040404a600c100d00300030450b210402c00100d90000c0c4510710000d8001d0010401c509844401050604414100020045d82da031003c241010010b032801c0c3d0302a89520030965050000d02d00c0824100742c40d26010940346084400940500303001071080a000c0c2d502d000d0b0301855001d221400b002c00071a442100c500b1650074000c00ca00a46035294174000b4001c92148a42403000f404205040c1c81c14a85140e0401c41100c60300c407215041800700b92041c503005403804000c80c4041c0100342 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 948021582 1106 948020476 948020497
    0x10c051e0c01060b0a02010b0103020f0a1b0b271c26010f0503070b070b0a050613020d0504020f1002120304170d090501060501030501140d0501060902 66
    0x40396004988020500d5031034480045008403ca00182040a29540c0240040c8001500450907030150400031510340e0418444d00c10414010f041d06907100e10506003600c80f01e020b03910f0b003c0100106484003030b81188001c00c0581c0c0c055000c060b807a080c9000e00014a00c001000f6080c00f02000000000000c10542d10101c8034a807001741c81e014400c0c00440704101c003550712642620000c1181c1d1003440d10034400d6901c0007480c16013480546400756008102c02e5050340c0c0b14440031014090003000c10380d10031201d81aa020200203031014103910001580002140e1400c0d00c1488098520004410301c50131400000d500b190794005001c0c0c00e040030b80c0b400551139072074030720740b8440c56035180403082c4e0000800706840215940941c013030002030b40128000e000300c6980d1f500650803034400f030140c1c0005007080c915200c100e050543d07980f07281500c10000040c08941e1800b194089800c5203090b00d = true := by decide +kernel

theorem cover : BRFrame.Cov 947841726 948021582 := by
  have h0 := BRFrame.cov_init 947841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 947841726 ≤ n) (h2 : n < 948021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
