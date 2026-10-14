-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:29:22.939986+00:00
-- url     : https://prove2.me/submissions/cf3cd4cc-3bff-4870-89ce-4611be3e05e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 365107913 ≤ n < 365287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 365109163 1250 365107913 365107973
    0xa0c020d030b061602010c05010903080403031406032122051503070c0f0204140a09061a0a0302090a020f0a0906090515070b04050336010903120318 65
    0x1040c454040c44001910707003482181070b032800080d15845840725480345891109041021079002c0c3d6200342c10b07990410b0003080801181d01700501020401c413022000a450102c02c040441c401844003400b5030f40190050019240203002d0b40052114500c84181c010300510200e00030440c0d894101c01d01c000203c2811b00c1c258503042c00c0c480800000c50030032012041c18401c201340c0d5a4015071107580d007a0041100082001c050002c1002091003003070a2440e2a000c8040040c5c0d1807540e0480302c58603100c0d520400a43ca618880c1d0b183c200285008541d010345501d60800151911524494102e0500d9400518101ca90300c1d0068855000281140200c0c005441c108180c98000c1a000c00070103082d40e010602c09603440c8034403080d1281a2008090110000205d01804010801d03544144041d1500600580c6541801402e051000583d21029064504001d4180d441800c1c03400499501a0400c02c818282c2d1000340c1c082d01d4820404100d9030038040722140071039610b4940099481524100c1218281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 365110413 1250 365109163 365109167
    0x2606061c0e07050108010e07031a150a08010e06100c050708160e01060203160303020c0a020306010f03060b0d03050702090a090803070c030807022d0a14010204230102031b0a0b0a0c 79
    0x50b40d07071080c2d05000c000720042029188151603182d115805143c005540c3c0100300503105080c0c20448a5030304030003403100c04440c0b041c00030000e10f140c1e00c0c0c503269081c0c0d980c1d8a0314240100c1703c04642e41a0001c0c580c0e1103071807610380a203403410b082d10f21a5027514112a11007030080d00e0062030b40301c00b004d0510410010403030b03050078107001409890300344003651402e000f200b054507034070342c0d4000000c0406500040f20000303940244103072104294014141d0380c8950b076031846102560070a000640b01180303829001e5000703140240718800201c0c0d15031034007810205242c0801410100c02032448a1032501d40c0350345000190480000d51140380715441c1e001e80b55526050040c46940e004150300e0a640c0694846038280070000c5c0010003040d48240700400350a0703086580742c106481c44c40c0c010100ca5214039080580401900a841900c08544000041460442c000085103101c410114050f070070400500c10043d88000c241152041000308481811080d613607291000203003194180c0d40c9958ae4802048816 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 365111663 1250 365110413 365110423
    0x21c0527180106020613150e0102191701030b060d0b01030b07080a051306020a02070906030501090209100e06040507090314010e07060e150a0216090c020d2606061c0e 73
    0x180d1801c119202d40c103043c0043d40d5003001811240441c400100b1000030818a0380850840d4134241005020f4030440d0012107000c0d4202940261405c145400006d146610400c49140d41d0301d0700108118003a4031b143c4400903d44400f40003c1c0d00041440c1c219404110a031402e98006c5105e00312b0b05c840e43c40c0520380180400d41c041c110010b41400c00d020700c6208109503c00c001072035040200107a0b50304280c80164904041580080101d6040940001c20b100040d80700386285802901c4118142d0740b04192422400258040c000c1d407002c1d1302000c0380b4941020341c481a031065480c20502071094881d141ca15000d605402d4141e0142c0d121a0f488101410600c4000c005103070350305081c1695003902d000546524210700d102c2082800124100c044180300304503051002c0201c0b81002d8201d91521056005015400040405449117409041c3c1161280c10300380c21b804000020308031001e19003000e080e81c0c054084c2600d64003640c00d00c40b83e0320812500c1c52815000c61100307800a40440b440c0741030342c105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 365112913 1250 365111663 365111689
    0x20a0c12061109010c03080a18150e0606100e010c0812041104110a0e21060406050105010815040507030f0f0f06080606012708010204090507080a0c021c0527 69
    0x21602c24002c403251079812030b4400702c0f403a030b06040500b81030351542100c400410729128100c148040d1204501c003400a0a01d03c038a400c040c0305400d011030b2401d549425590042500c50503040149105124840d5104544041e4130b82814500240c00740d5494076180041e070000020911410070100610041007441c015160685600b66014010901d4400c000140341c000c16a0324400d00085080240c400c5d41c400e1160300c0742915544c8600300304000f040c0c080341e5600080340c08846051a220000c00c041d0700415000b1322845c0080008842100c2001c28403014000c0a00326409242d150b0807400c8642030341b80580c1c4582031003c42d00085002401c0c80380400d841050344500e0842c0c211809001103640d109160644007520515020b072508206a007c100c620180d80c440800d5502c0401d000c112524a030300f00b10b00a1209035a00b16450b216610400111041c0070505400750f4400c0841044145014840c09640c6c006424000d0820009044011007801c420210200050040f250030045117481c004142c41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 365114163 1250 365112913 365112941
    0xf010c1728020106030b0c0f0909040302030304021002070b04121a0117010609060b1e0412060506010e0303161e1b08010c050c0709051b0a020d0f11070e0601020a0c1206 74
    0xd52072540d186c801c92441c5c058540101c4190010310391445480b1402214450300c1c01030507101c9146000c1c20000c0d12500152401c0748a01da2455009109c2c03440015001e0a44049400003442c1070b1030500c1600781d40780036000458080c03178444880e1000300e2501004a0080c501c28545a104c0c0b07851640c032500715000b0b0b130003140c09146011414003200b1044000d894114051080000a40c60038050395140d0340907542c030014140f02d4046130301007003210640005001d08001c0c2c035180780900d108001c0586070301821a0050310307103042100d400b010640d01c49110304504c8a44800d491001e505845900720f048030b503148503841501c64001045024024807400d41240011324086081598031000e4030303203034405c501c40c03071440740d032907002251001d548681031004610629003001e80c0c03508000c1c8040e440703000540140c00410042502502c03101c3c054120440070300f90240c068283e45041115500440101521050461254511000004000c00c030a0b4002e003854a041c8241d90102c2e1600801355040300b0340d8406e0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 365115413 1250 365114163 365114171
    0x3022a07061211030c0703090e150319120309020a0f0b030907050307050109061215090b010909050c0d09110409031d0d02010801030b04060e0610170106050f010c17280201 75
    0x440d414003c42a01c2c0c00603459640103540e0702e540e0504544046e07854000d00c0080e84542c0030f01c02901030042c00700007007031402c1c1c00b44d508980e05018001d03000c1038400c43c050040411030b07140141040c40380e40b110b00e60a1004060300600e07a2140e0042125032420703082203080e08000014881c102d001040f03498001c1200310000e1003074038144800209881b10314450f04c4184000200300900d03599058200440605c207002c103826071180d40300c001002402407000c0050104401000c00f0400441d00c9c05058402ca0022015525251008140c00001d0020000c183d0300c800c0e0f0040015101e550724080d15500c07a000f90b5130020805245030070030003a103116180007031140c2d02d041e141d400180d0300404a141101d40101c1c91000035500d40c2010009409008071030a030381d00a09080040b4000042074541c04c1d1185420925250088004d05d1401c0300c0c06401041d40c40315002c0706040c0c140d80300d80e000c120034500c58800b11422a101d2103030013035682c011041c100464403840f81c124140810118518401e20007500c0284 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 365116663 1250 365115413 365115431
    0x1a010503030a05031005040c030c030c17150d050a0308060108090303100312020f0a1b060c051005060312030f0f0603060403080115050714030405040b060a080703022a070612 76
    0xe60359209030341c00392061103004400a6050004941d0a100608020b03000788001604807100400a206504210011915000210341414480e040b1101c0e08251203e889070035460300050442c4409280840c1035005044030680300000d1410701000c0790345846501d500b0030b1403c203c0000b4204107030042207062203603c11700130003a00034007400a40c01203a130060a10f580500703141d00102e01384130a0640c0e08202d0b102c0c400101040061031290803200f81c1070342440008041d00d4060031141e02d01006000b900903802407a02c01840c8180c0c0c0d001582043d0300504480080700d58201500c3c1e25001112512045041c80c0308012091400c0d41ca070a50100d400c5000c2e058900d415a0003621081f01801641d06c5c00d5102440e244000740600c044070003058001d42014040381180b103165589500c0350003143d00550400c50010780750b09020041d81c0c440c007165110340e140d0f82e03030f0110110005e4000b07152000200070f1011200100c3c1d00030390841040e5061600240403c0390034410060052010034440c003c0d0686448400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 365117913 1250 365116663 365116669
    0xc030411010e04090b070807180b1e2b060603020c1c050c0a050c0a050d050a17070c12120504060e0d02150406022103010302011b050a0506090a1a0105 66
    0x4044220242061a030041140c800309008004644c8002e148010345801c0c4034609030032610345803041400d6550f50422010b07030051143c821007a4440c6801d0f5203000d202c21403900100c0034402c0845456017a055080c40c080d00c0380890659040b40f0a9000c0e03201110303d4407840312030760150601904d0076090a40c600351105000c5130381e13404445414804911080172000007944120f0071200c101504008880c65100baa04096840e41042981d0307901c01d40c0744040011711424203015100d091070300000508071203072458642601c8500791610300800000100241070000d44002c0c401c1000c2d20103a080d81040a00c5850410f550b24482440203060080900c410401d0a40c403442007841c8441c2655030540002e00d502c04103411401d54a40d0703010f5004041400b0a00302d03030000d8243d01c9400904600189542c0c1c0c06030340b001c684403c0c04040d00040e207080c0c41081d503441c111190303500603100348200d030780704111078542c181080029161140c150b080160814240071000d15100c46c1452100441c22165140c5000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 365119163 1250 365117913 365117933
    0xe0901051003060e01060305030d0c020f120f0c100c0807030c0305040206180303070210030506010f03140109020c0a140322080309090c0706050103030905040635010605130605090c0304 81
    0x4000300e8854045404c03540f02900900010340e481411241c0702c000c95840c15001d00312004011005104020b100740324110000345c83c80041d2580c3e03224902c0c080e80e0150302080c0d43d1104540c0301071407180180c0e841d11481c07944150043c0400c81e070b0780e071005030802201c01402e68950701442010142041e042c480540c0d251401c8071146402600c1301c0784559001e80102c4c1c20340c098100080d43c02945030840598640d0180c2000c0d200d44026a190320038100b908000f94116041c039010409072500704001400401640c0d401441140c2c82e1a08840070045950b540d047e4100c0102141c10b181d0f000420140b100080d816901002c040507a0034056400d0b003001c80d52035890141000043c440c517011804030300214407800842e4020f0350040c0c2d0070300c5150f0b140d00b000b4200c09500e224003030040d1300c0d00400166002c5038a030f10701303503139501000307540c0c1d24a04141c2d0b00030a031101c078100c81034195643c0d200001d16580742c2d901550940200040403e40c1884c2900b0000c03201c1c00180f0401800030f0401c1000000f40c5482d0f8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 365120413 1250 365119163 365119169
    0x80a02180108060406030605090d08010b0f030103020d03050409020a0e120d0c060216080304120f0c1a060102100f1a22020f0f0a0c0c060e03100f0e03030c040e09010510 74
    0x7a01d050b8641d50500054090503203540080c008500c0e10052003000740c0c006c00d004150010396254600540d80c1d03154070060320312810003c28a02c078002c2c00180010f24104942280700c0c0d0080c80c055080503118100d41080784d000361041c1000c20856034030b00700c1a0402200c00d01d03c00310401e001d448652003d0301e01034004501c1003801048aa130002e2050100e00021002007001034005041544910303151404039090b260104071900856101100e182007070b4400c02003d400c072035000c48000c84000b16614071201b6403402a1619040d80100350600030021020300c1809101c0781c1007400447d41071180c19142400416000800c0d001e4000c40c203040356a240000d003c038540086100c001641c681ca064089d507218060701c8020100840c001805c9240c2960000c410060980114281c1c01c860307544030015111602400582600364101100d603035611002a40648003020f001e00ac0440d140808100031821680100c0c2c0e11000c40c040410f05000038071900d2a580c1e84500321000030000360508081c07100c20400288 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 365121663 1250 365120413 365120417
    0x6050901122d1415150d03030905010c020c0a090c0e060d0b04050709060e0a050108070c0c030b100812181201020d050c03010515190f140a0f080a021801 67
    0x10881500314412a11082c660802054000b640303104900d04030100707841d40003c0d1500352064a8072103c07945850780b01240604040d40c02c07034084003910b10601800c5440940141c05055440354507002288003030140c01518040da601625100d26004200030100039a034120b0410140380405600c640381c0c00c800290141801100c0142d190850702807410f02400c1c120110641040c10841032066841d040070381c03075055902c40c7c0c681e00c0c4000103000074890008050b12079207001815400c0070a510130f0151200d9180680075100c81c920168894940c160300c07641c01d44010f0304101e00c100e01045800c0e014840d11307441c0000004023a190055103050020004806400a84108800002d04910f2142541119291010a4000c1c059440c0c0300b03514844503007003403040340e00034032096907610b20400192085031040d100c541401d40c0c04215502c400c885096941613420140501710384541e03150018080079280f0341c100e0f503a80301e0404280c428000c2c40e004025205440e1a030050000c000040c14072180380702c40781d1082c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 365122913 1250 365121663 365121683
    0x40b01082a012109050d0801080a0308060f0406082406100207140a150c060b06040e010e150607060504030320071704180b0a05011404090c020c04050a0f0605090112 72
    0x10383d0700c840460200b0b411001c48a15245018040050101c1e1003c9041d44a40b0348061903a40d030b14000d91a03144198005000500d0303400000c05030310b40501000030044000c0e00000f01182c42d0241e2070b244c00845d034420314401c024010451a14070408040a0744400140d442049031110010081c0d51807081d4081c501742d400a4540c5c0c402c03e621540c0111004090304050548070240d02070700a40b0012000d0400d8036a5824680011418104001114115080b080e501407003070303184c054188038600002d031100106628070380380940d21340e848001505002e070282d10001028101440c02500719181d640d50401189401c20320903522902840c00d480301c19030400101c40041c0101e01c07484240d48100e0300451000041070090003c03504280c0d01c1b0040c6194107464a401c5607840b01e00544008015500001a94000f00424820301805410055040200740101d0705e00c640300000042c2a05c1c800c6500039810360783c1d030007001c8806100d401400f000300030036980400c8135410081d00c8040c40703150500c0035040140b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 365124163 1250 365122913 365122937
    0x70c08040b0c010902060415022b030e01020702030a080d0f0b090c030907080d120614210c0303040603050a0f0c0f03090c030803010b04030302070803090619020312040b01082a01 78
    0x290054004c0a034010401c41c4d03101c0d20f8009031070640181b1020300300144a04040210123900a9400640000042210000d010042c0384210041c1441c400c8014003035409114040050b2802c03c01055010b1252075055150300380c004015086075051140814218180084025261101c0061035080303499404075039541d61301c41459610341070103540004203521607100449900c9600034120381040e20450011311040341c1c2d03564410700307034080f1529055003d01052410303a501c000007221603032903c81c0362058076800c1c010b820010741160446d90245012949030f40400c54100c245204942d140c02c1c0030344d020018845440001050711190b1051002815500c0101600f0b00c07805d400218000d640c807040d5141e89603160f03603080c01280c03c40e02c0101c0242c82007040100c1d800d100802628103040001e45400d042c1412035041c200c4583c08500c0c94410744c0420000007403000c401c039071020b1040c1d0042e11848a030354076240c1c000d0325003040e00f0104c0c0b14205012022030b1342c01c0c3e11907100280c1c2080900c0d04035440d000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 365125413 1250 365124163 365124187
    0x908070803180a150b010816051606050a0522030c08031302030f011406010906022508060406090c080706090e041110080615040501050a0f030e0304030503040509070c08040b 76
    0x21492120181c2c03031190007400000c210b0428000081e0065640301441000300704070054554081c1620740c0d54001d0200b142c5840c04902c1107003d001d80318003041054903262016185c59007280c13003d8400d1121580c03070380100a11001c01510b0700c45100010000070780c011803661001004102000002040c0318000400b04400081010500c03010702c0d001001c2c2c900031404520403a00030462034002203504400840000c60560140c003201c0c044030040c3c1c01401d50620f151404c03900703182c446807100326400014200418045001c1080500c202c0c8038004c00a003030306082c28040018800c80e802185d642c0e02c80a0b0521115601540c01001c8a0f202c0d005200d0f540ca461070b0260f40220b06800250b000801a510440200c2e8000d81301d0307020b04e03015202460314030361502d503014107885503000b4103000c03680c100254020740d03203d615950440e0003245800944410366404a41c02c0d41d01c10ba02c10740d0f40358004642030120f850001411b54000c0d00c0380c18509480b800c95a96500140a103129111840c40003240c0e03400414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 365126663 1250 365125413 365125441
    0x1b032301062304080d030914030309070b030c0d09030c020306010e101205100c090306110a05070221060a1d0c0d0305071109180c010c2a2c0a0908070803 67
    0x458065440e00030b43c04c1740003401044820400c2c2e072512030705541e0a800920100449016001440282c040c4c14240142c00d2a2944003900c84074607440708001b60040d0000c84d10401d45224031075925420000418010903140ca441a00800100c000041c18801203001000703025040300c0c0d520200d61040e00140c100300e07040a102402c0261642d0802040445942d445000c072016a40715260410622000c5e160518480c010034051202282c0d04110345405494440003422510210788911445040ca01c501241401d400391014070142e6202c1904021066600210031641c0c0c00b00c1c4010f00740b0803000c0300013407030003458a0700240c1032100001c0c0000034000504600362980170044c103001c50303c0c1003080b028600d0341c10704065241d00f4050911043d1040d88150203804000341c0140710441c560700c01103d440303c2400042e507011004114600001150f5503940c100d02e05114404032400c9800b4050105a0100300008003261100c5160091200000712840700751200c1e1604400724036100d07518100001818 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 365127913 1250 365126663 365126669
    0xd02040908040e060112020903070b0c0a21120b030606012a03120b010503060916050705012f0a0903060f021c1e020c0c0409061b032301062304 63
    0x40d00006804034039003d60300400b5018020a0b80c442410504040f0900128064000c2c141d6058000300c80c1000401116000303022441882802d84070200b540d680c841028002070003020040d0a00d400e011005250002c00744c01c0d030624541814440d1450307210000751116030041c1180d040c80101d10140405a08560805c43c03480310740c003a600e0000305c00342406880d14482100241c0003509004504040d03503c02c40551b40581009400505039845840201074684030419a510810000b4850040840c00034000c82c0081240c854070402d40c00794683c0100c1c1130190210b1400d03213001c0104081e125569110203503400f00ca41141002035184500000f20021b44101079051082100d1480e0400282e00306622001803404610302607400007050100c0c01c001e84c01460050030954000f6044c11203d400c0c5a04a200440d02ca0800061b18200d43c0e91000d107080d1014500c580000c0e903980048505500300e420055038408210258805980360900c020a003011020b12070700182d404507084641607038410203640c06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 365129163 1250 365127913 365127923
    0x2a15110a021e24040b2503091115030a050f060102060a05041a0405060702070807120809030709110d05060415090c2003090a0f05090c07030903020312030a05070207080c0d020409 78
    0x8812203080160b20303c09040d282035907503401420202d00e9000e261903078084184800003034070f90343e01d5550344250010420884241c032102c1c0d1103241c81420790b950000d440403001d18902d45540300d041a95035030b412104024010310844010708203106480c1c1e000110542e0103030841a01142d250344030f1070901140401c0b40111004c1e02c29500c00c1c0000c010f000302d000c5100b1100d5500700c4448582d9071901ca5075601c1c051107211249000ca0b0044d0010030781c560014108035501070f04480d9965602c841e81011507040d00a030303d41000d03003c9900760380003040340601504514101d400b03201056100d50b800d11a400c0c14421f00300303456a2000c821100c00c7c0648100340d95144250b003944091071303d50b458191290700c40703005144110704151001c20044012031303801c000d03114098071813a525952a0034a0a20b82c3c4458000e400307201143c080000166010050500611040e010343c0391203013440140304066800c081e01240941d00601c0050281d8000003404103c0544100c07442d601040786800860000c1541c0507020344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 365130413 1250 365129163 365129203
    0x80403020a030807030201051609051e030303040614070504030c15031b020c0a0b033d09060312110a060b18101a03090303072a15110a021e 61
    0x100f404841070107003510a010783c0083c0304039034980b460118004804032404003c114400401d0000b070070034882140030703140382d4228400303649880000280f95800031201299059207032104091034001003194a80c2100ca039042981c205421340e82ca01c003003003071180280c01c900c0c540e0240a5042d00d211350010315461110100044150841c20390082d103c1c04810325050080850b0000000c1d09000d400c201c03840b40c0c401782c1b84031100305c0e00c100326820704400441e80c4c040410290209c20944807480d05c1454020030b00c0200004091780746203040600020031031110024040c0030391850441c00070104035202e00950000000802e00480340015680560b4500c0c01511480ba83c02006a04049145c0f9001070340d0030760100d600321400507440d6050500c4126800051038005201007800d06004140b80c0038280c0c0035114010195142412040d4188030b005016584541000a80a483c5501c0d12030080c008031119540392500e25100000381d62030700120b061b1129100d80c80b01c03103040c005050020b0104186040d40c003c7e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 365131663 1250 365130413 365130419
    0x318020613030b1b0711010201060819030905010f0e010e15120109050f07091403071d06010305100524130b0a030f05010501080408030a15080a1104020c030301050d080403020a 77
    0x9115400c2501046850f4032000b00841ca45004032800424910000110246054003903079581d070300c1400c01d4110505540d00d0300b001251141050041c0d41c2d00746412144c45d01c1c05c4900d41001000b080031603010038140903400c41410049540550110b81c1c60500f030902c08011040703000800e20034180c071034000344030400116004140140001d64623049038071f855002c1c01640c0b1106181101288142d40b17540105850321000c000c0c0c1000c0c0507400014090080680318142c0d81c0b0031020280c2c49118400007082c0418004010b0190703050300c60243c208a694055241950620010a4000f0701c40c000282482e0b10b602d011840f038215160460b108103a0214441144c1e6903200c69050464124641c003102103820955440c004403000c1c030440b03040783e138140d4542590381c5035611500701583c000350903521025110181c000a00c000038084a0003170000200401c841c0344541010701010865103c6940308034010415045801e40000540f03043d500221201000401c8a262081a80c880c6600007034210200381000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 365132913 1250 365131663 365131687
    0x3070315150c03030b03030f0316050408061302030d0f050a0509130c210b060406050703030905010603050601050a320a080d02010203060f0d170306040e06100302040e0f03040603180206 81
    0x2500410f101e62802c2c08802c412004040e00c1c1e008400000402c0f003018400508440880ca01c0c11290f9403050a242d403034207403107044050804404a0340b00c6203e5600e00b103020210b040070455013041044529040180001140f401403081c0314030f5004401708440400c0308401c036239901140c1504400460401c001c101c21502019001041040314114070305403922500c0c2020f1400e01a0820015005041703d15007030418000703881c85c2d00041c6007901050f9680e044c010004009100b240c002e90300600040401d5032600040202c0b2804540080c07210b102e29612042c4100314803020791615a02541f2030070343c0c4170200808500c00c0c0c009640102202e20600264041c450780641c0114010b16069544858512455040c0511a4502c80c4001c04410300308640900317a082c80030145402880003000410701401c416021450a80c040d540b4486180003480200111b141500c501048010030401409181e02c840c1d0040b0340b203020350300c40c000c103050701c581607214070150b50380807014000d0380100019100c40c189203030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 365134163 1250 365132913 365132927
    0xb091212010e0f10090f11030f010305060601030b03190812070306090b0a0602100506040f090c14040501032a23042f09060904060602061e0403050307031515 69
    0x1815011503108000c2900080743e03400c010720406850580b104114a4185c601d0000d14110522241c0707030303079101c0c00d240d02040d0000065016043c0207038600341d954190704183d4240f038400f810301e905142c0f400046060b9a2004503880c1d00500c88410115495052410803040d68800d0f0300300080060510f50401c4089070301540114195000c1d071004001c0741c0125400d0140156407405840c01503031000d4403c540a40c041c0d0007459120802500129a00e0301081c2c2490940c0e0b012501100c048801c0358040c0002c0c078000201d404800001c03038040c00f107940341d41c4402002005510310b03142651019a80d003182c0200840b02007006140c10000c000d9590480f155401c0e000315507002e058401da0900030101a5481c0418141400311702c08070103e00b010820300c00e01034065100c000740c190499010310401080d44d441d031144800800407034001d4031051425040780040344403041e03c8101b56005200c24880460761210540354449858240069107a0702050642124541944400c0568041c1c0580416450344140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 365135413 1250 365134163 365134169
    0x60b12070303030b0f1f030e07060e011202030f1305151021210216060c03120207080304020d11030a03110d090e0c1b07090204030209060f010c0b09121201 68
    0x281c20441d04c503c034801c200c00c024100c5001ca83c80b58100000303a200c0007000390704e8a0150618140010440014a40c0310300708030b01c5074043c10100f11240207202c1c903960020440c018642e51b000c000c40c590314020345100c08c4440040d000d48034646031507111100b000020031060030100d40d10f001e0383d4441d180245029002001c54056402a400808010080b060046c0b048449a03070748034400028011404c00c4d12441c400506411004500c100e10740407140340e9200700d541c1d010340465034654180c11210b0030b02401440300d0101e1070800d80d204020500220341500141c0717800a0b030440d504400c04600d41420504202c800715800d5050060600e2031003010740200c000510b0144640a40351101d00003001601d40b9140d030f106803840318491200043d90b04c0e01c100000d017000c0c0c0300c0558008e0107162170f400c002d26140711508a8444a81c0c001030900551070129895a40b2807000c560000312181036800003006104200c40040141c07001ca00071462691040c000002180740c45108141c445000c4650700e54004e0082c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 365136663 1250 365135413 365135417
    0x3190f260a12021908091203040b061c050d360618031e02060c120301080705121005041103010f020d05010807030201020304032904050a050601090501060e0d060b12070303 75
    0x420300b0001d5003014025074014141220802d82008808041902c41a03802410a02c290040c0554034a003490118003540c0203500480c210328940c40d182080c0a07110341c829180180600c1d1300e0001238005600080c40c0f0726031401c0b07894181d0810040c0921000680d401071014480e0820034000b278000300030b04030142d5080b514030303a4900c01207400700c1c0d00880550724540006811107a10840700001e848051307500500862014003200d150002042031075052204000184a4000000004110b4480100320310006803100315080fa4101c0c5007100003659400c2590241c0703000e039460300001002c3c041811000804c402018000b13201c0c083d801c138203410003903102440c1440f04d03614180011564640015800c0162641070b0011340c035180c20750b00c2d80c40d00c4441d4044000c0f140c028800706102c01d0030320301040034000c40c030501c01401050303242d241540c10540140c2141030501d103032200400c4800d500c0543d4007050a03050b980030062552900740040078013070310002e694022202c030180750400800040c11400312030181d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 365137913 1250 365136663 365136677
    0xa02010e010e0d08090303090901060c0b07081e09210a110d020c330c062a0d0b030304030b0619050f04180c0b0307030b03190f260a 58
    0x20034015100c1c08070a0042c80d03004101120104002001c01005000d8010010116030070302c200040003d10000090b080000001d40300110b05040203003401503950001c040c0d040114003898500342e02100300803503000c2c1040050500010604c448820310615030521a0340d41c101c540503203504030491669010208440c0003404400002200040108800b01000850780c0075010700c242ca48100400101c1c10f00c240b1800042107448001461110124480d00c148141030107610340751103880705410303c1d80040036082502420030b810f20b000c03202080d030803a04594001c4610340325080300351020010400e040710701c0d4245c44005004030038400c00d9404988105c00458210600b2040d80e680305642c01034620500340c208508481d01c0f007480c54150040101c0b600d501013502c09414050319072014002045d401000ca0300000402c0c0068541d01d03015207803103030800b40c0041c06443c0c1c10348840000e0118124019003a640b660424008200751210442d0003105a0b80310700c03160b907445004c0071080e548600f00c0e90300840e090b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 365139163 1250 365137913 365137937
    0x40f0f06020a090f0803031f0902030f0a0b0607030e130617060604110f0304110d0602070609030e010903020d080c120d2406050304020f04021606090212120304080a02011506020a0201 80
    0x31480c444005e655140c4091400d64640040401e0b150b12044801c3d200d00360700b800049500030907403000d0351003880035001d0300005003020341e0404100c0d82503b0146000f40780400c0b0900100780c1006100c0ea184005442414206c0d8540d00c0807001061a90440000310108008000c00318400160150103014225010008007034a00d08042592042e00c0d01000200ea042c030000340814200004606202d20207005412030101e0740d035070343d41240d02c900b00884980303550b03441e5001030542c0b0400d6611412001c3c00c0c4403156604640000e8049450040c0c000c0140c0c80004103291108003d10510070b80440e200340003078981a011400f000a0f180054070060304441c48907038460002440d0300c90500316000b47d2201c0b4915200e640a03c5460011441801e0300550204040802c10031079118950919014071400075036480b80c0c4c0f04000c05100c00ca40341d05030540c000252000381e170f0000c00c202d81d00590b1040a00ea070320403000e002680500302e0210311340601030b07205000061803900800c0d4006003a06c02d1340e41d44c6051036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 365140413 1250 365139163 365139179
    0x30d05010305060c0a140a091d0a052406130f080d030e0118110d0c12020f0909060f180a03030603060b09101a041211030601090b0d0b040f0f06020a09 66
    0x80150110005140790b440c4555111b554008019402c4035140035031080b5150071040c958486d90301440c44d85541c0780300400205111074490280c00c90902800340b0301d0310f86100c0c400c8252203403035050340d8810540040c1000000e000c580c04640140044081510000e94604100e502d800d0f1821841c40481d04049500c200c005062060b240c3d21500300000c0a05400140c4460340c50303801c2c0c11805500000408003080129104c01d01420080221440740c1c0101015072040c001c00a00e6100840c3c0508100418840141030110b03015a003e0030903281d000c03203907545245542852050341c450401c10701a4045241c140355040c2c0018050b03078054203051144a07112001e112140c5011105482030702c90b200d5003404050358454040410940c074860042c10300f0344a4080814110042004a442511544606103141010b001050041070301000801c41c0000305008a03040c4403040c50002d010301c001100080805c903441020010164000522564104051030860000e5000c03800841c04101c9003580014100313 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 365141663 1250 365140413 365140417
    0x10c02070302121c0804080d1104080d030509030a0c0c0f030b220f20040f06062309090a06090207140c030a020a0e0606070f0b190b06090906040e030d05010305060c 72
    0x300300b43d10a1024001a03001220405c42c0a401110316500030003403205103940c5030003800314610a0000c0315907514601100385240040d003d400f00d080c1070500081007480c05011094401030080703130901264400309864001205c0304650080070160141c1c000c00300030b010a904440340704a10b0180c03900030468036400036202c0c0d444000030042084042c003a000b4006000c404241c11004a400000c000e400005000141581c9484030791a96603590350303c082114681c01005550382c5010000c40700030040c1d503400d040704140314410540e80242c403030901040001189a210300000c210b491004c43d142c4205c0d25003134106102c0494404c42d903114440e4030310303c00e20b4085240003205034014a1001c5003850070142c41d420080040040c0c1d440780e004e100000100d40034011894000388a41044480c600c4d20340c80c9850280001e010b50181e0781d1600c0c129600c2d540743d4008071a103500080300c0108481e0b9070a00001d01400c403c1c0e4111b0303a240404103403e4920841c0341c0005060380c1c482c0307090b1240c55a440150341014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 365142913 1250 365141663 365141683
    0x303070b1b091c060f06030302240609012903181203070e130902031e28030e04090204180c05060702031c050f030c0c0d0c020907120e010c0207030212 66
    0x403d00051040920016500c01c04000d50b201d035201186003045d00c0c0c45002121800e500a5000d81c000a5145c803c1800442500b20000022040a012414001d010030f2803494140079071002d0050b201941b81442c500b107130f0074411301d946a2080550b285051040f01e440d4402d03102c1041045d1040c3c0050740c004801a9050364801c0c041903462418483d25041000262541c40004100040c0c1c0c0d030101e807000d40c505001c005144c40b4411a1001c0280c00c80e4101c0340707402e00c022901d040702c0b400300d00078080040d040c2800707040d40c3d03804d846c0c501560035a20001a004104030f030b070002c1d401481c0c0a0810b041e80704640c2e00402403400381d1b0141283c2c4d0b507107809201043c81030b00002940750700440149030761181c010310642c840c03041d2841c110b428002d40038060b420b0342c0d100361009440300d0800302d8908120042004031060202c000e2502803040c420359030104240030300c0904200c0c123100042c466801140502e50050070b400205034003d104183ca9024040e48544c118041a40980c4148601c0e0340c09460000781d01c1c032a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 365144163 1250 365142913 365142919
    0x2007170c041a0f04020403080703050309060f0405060402060f090a060f14070f08070f1e061d0604060b0415090b030c19090b010509040e071509060203030109020c07050303070b1b09 79
    0x901c690403000c0103e810648410182d1195003440040042010399028004192084e140d05d82c0d2420b20f01300691911b0300080500c022000201d04000001c0c101043c01ca40099060356003e40740c080580700c06100340903036038286801064403000020340a41c840e5500b80c5500f040d4698000308004442240030500c86e41102a002c03190702240d5400040444005020013802004002c40c001c5456842229090560314180c50101e00400c805050124a200702c2518080b01c1c124110359006000b00c082d20303500d0040018002a54541c01c2c940740c1c2d01d880d04030030b08000c0002d541900c8651204456001080b038429018064801c40b90b9007100341c03c1011490014070301c0002804a070525060b10030010f0403520320702d035040150510900306961100c0c0034190080b010840909940750034154907084449040b0034003c01c202c14100100006a0080f084a040d075461400150f50307105400e060501e80241d90380596090b100001d000c41c00d1010408285000341072240341c003200ca0f001c60384c4001c0079000f1032080b158 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 365145413 1250 365144163 365144201
    0x1b161502062a07030503090105010501050403051507030e03070302010f0b030c03100b0f0a03061b050307050915120f07020d020102042103030f021314060c0705012007170c04 76
    0x4520031002c80c0459048100711000d9408003039032041000396401844003140800c8001c01480b400c0d520030302441d40981004e1900909003491500c840342e42d0704040017105d41d10107003440481c8005200c0d4000043d01101c01c000c5940d02c00c0c2914000f4005c0c1030304004c0055040c90b05121004902d40442c1d6580c0b1050f00400800481014000f1070300103202114a25502082811002541c1d4035100015070056005a00004d172007120b0a040c49a80c49a080c075450030402c1c20010000829005415901600b9042d58001407826040c034064980b031060b00e44807000303186d460040000812100710682c0c82665140d0980c3d80c124480082079003030740514014403411031066081082c83e407145d00142e688880c0249130214240505020840886c0c2c80403421452005000105000014065991646078101550f10a15001010804c140c80311014001d090410a54400a0180c0a0121400000850301e2019035103125681c00c00c00240f4109220012034038000c01c900200c9d145410300c20b021504000c2102d80c0c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 365146663 1250 365145413 365145421
    0x3060609010f0e07020f120a08090d08010b0d0e12071b0b040315091505010515040b03010501051b160312030e1b01030f11041d01060e13021b16150206 66
    0x804000002401d550440c414094011000c800400c02000380207c400706240d41d8100602c0014072554004001c0d0445070301aa2440000c4ea5201c12114115031020485ca5103a10700000904090400511050300c944a400d28000e26814002c004080b49840f42e01608070070b4050303c0d802000c3c2c0c40c4074404c00803410028002003001c900c01100c40b800ba0b15100d030300045c80c0211951031405000b401c540041c0680d40c0c0d0f0005114605000d0888805e0b40442c5c8038160604d850140340c500d0340e11050251504110020501c0382a00f191101d900072000507a00980d065260014126a0000303032520050321080c6c1e8030072102000e14024447c100c03284a100780036010240c0000032001050f83c60064290405a4031085219078150610403011403c014500303481d615403501000344420070461049040402c41c0c01c0c010820075402c4070040d80c050f10700b600d0003003d0200f059880d400900a011081c20031180c3d41059400910001c101e07000308010603c1403400007030311440d02d00c107601d0041141c5c03400340c2d10850100b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 365147913 1250 365146663 365146679
    0x8070e0a062705150904060507020f0705060f07050313030b0403141603030e0c130209130b0913060b06190807051603081f12030f0309030e01030209240903060609010f 73
    0x400d900404484c0149400340382e00c4d002c070b1005030741140c00380d501996403001d010809906104201e280d5904000411106003000e0020b140d0b0721407088000c04a040024840b010448140180c412840c42405071040041e524181128052400c4030200e0010740d5900c046919a0242c070140c40c00080146040036007010b485c3d078258001c013803d02c2c0541030b5100306442551250384440d0b001040201030303c8050303120300d40c55043c46004907030380c42805c03d000c0c04c18002a8031511130701001c541c4440c1446901a080710641480c8000701001d40d100c0d07030455400281240e0700f802da40129029080980e480406940c1d6200d402c0f542c600907000300c40d000d850400c1d81c100102e0b01c07030511150040000b01490f400b21141405503650300100d0f0344000c3d494951b1007029802d060700030b01c506032100c82d1030405002003901079a005106900c842000390616a001c680940d40e500c0340001c50080c203804d54002680304031460324900c1a60400101d0b00d00c01c1c854800040d10382c0c20301c502002d048079030761401b07045030908010300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 365149163 1250 365147913 365147921
    0x501030f060f09120c03030b0306040206070b1005030d090e150a060c03031503030e13050f0703230a0b15070507141206011d07050306010c0210050408070e0a0627 71
    0x111100458507440d03c08080b4001c0f07000304510b800349485441002d14545000780036104140340252280e0481300400025844050458620366801110741c1516602c10707081e951041c4941c0c04c0799405214650350030018075004910241a925814004205aa40c00350b00c801b0511400907190741200001350304000060080040c0004244a81004660035040700e102040009031035100350006005910348549505001d440d80c480540421814002032611180c2d10fa20f07920090880e8040603500d02140013004903c15030b0342044103d1202801c0d00e801c041e110080900003c0011a00c900c0c3c89140c07505901d0083c804071031314594050041d20103e49404503405407010840c2100f43c11403d0924040316406c0c0501090340600302964403800c11070880da45001186c203005000200740803040050046582c0c00c0041d01412603412036142060740801703601240c0c1e1b0f01403a80510001e224543e0080381c0100001140b900c42c91010801300702c855543c00100010b20240d0a40211086e1203503502e103000841500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 365150413 1250 365149163 365149181
    0x15030c070609050c04050106050f0306100507050f1006080d080f18070902030910020403111005041a03090d2307060902060c0a0501050601030c020c0603040507050d0f0b0a0501030f06 80
    0x1050a08020351600c940c000d48400784011501134005954a1009143c944145409000a498050708107050700d04000d009102c003a0100340700d480000441100c180c0b18004444005d68864140d03601c0d007080c40c003150345d600f54103034503406403a0816001150210340050b034003a03c400d091307490700306a48440d00341840c000d034003034084101482c00b40c0d105c444102c0108803c0c00102000c51005a60b4900303a2062414014181d000000c853b00400040021443e110f4803081c3d5448210307403124950305114019515403156034070a442002c0d002088081600458010754031a0046006603000e0b601c0900d8115a00b0080310555103240c04c0510305020000c800750050b082ca5407150500243e010301c50380003d4000d4003c10040c440315444807500e00100a801e01403260083c4080c02c00348500640707480040c0d140d8040d048200d008182c0800000c06204041004000a000181126041c0320780d03400c0161101c0e01110041e98829146004036604400c075225a50413207800c0007644420030410303074905000e05a909 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 365151663 1250 365150413 365150431
    0x6070605100b070507030606050a05150c0c040f0b090c0325091d01030615060516030c0f050a02120c010206061203070b190c05090906100207080f0307030e0405061503 73
    0x60003240c6000310702e00074070201e4043d60040400524510b002c01c15034070f8603004a40907203101c15007003109850782080502a14507401e03e00340caa400031113070186004903a2041c3c951182c101130031a200342e9501c2e440a9041c0c101074400f40c815907654001000e01c3c0c031099403808004912403030000c1a05c400300c00c8514404074985403000c0490307600c0a01154020048002001c6800e0120040081240e24452100d1490342620f541804520b0800098100e01554088414481e240d141c00c0040502c16520080c2582d07001550000b100202d0801c03e95402003a1000c90040765010491901c41c1e000285041c044030b416030040c25240d9034542407041040141c1c00e86005407205100c00e41c001507001401e50b21030000740c0183c0300d5000007884c10a00342d494801340030003400020040c0050548660f10010f074052001c3c0e0b400300d04568158070803854010154003040c0c1c203010368018041c0c8501c0200040c81440d00135a03500890300107030003c00044580960f91140c0c04202541c007140006846005158009509 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 365152913 1250 365151663 365151691
    0x180108090f0307060204090c2d032d0b0a0806190f0f0b04060501051312170324090c070f14070303180b070f080304060623040b06030606070605 63
    0x740d4405266070030a0208a6181e034003c101408032945074481c4018104d01440c050900503102141580c400d544d248011800c0c02030303114640075042c042d0704424200000000124140b00d42d9402e0360090100004600742d20174140400200030b440c08802c0e290503280c410300074007038a071254040c000700d115403045d00ea4001d584600498644040c3c5200e0301e0480e6012070008100d4140d60300030801165001d801c62810b0000a0003494480042048070070190740182031000052441030030b24041d80329403942d10048402d0300204001d0010300c00101d00c1c2890083c1c000034541c4620503010070131403440480b502009a441800070343c000c19100c59124440d240110b4203a8000d041aa0485052092540041d00030402284084040c0302034059120001c1410700300960a10300aa0380703c0000d0092500050301c050800f10228003480016444480282000000720040c40503450904001d03558074501c41340320f10b28105070100c09082031001c41c0e10401c00107217090714020301c0b13079103103402404013418081394541c0e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 365154163 1250 365152913 365152933
    0x20c0d0e030a0c080607080604150506030a06050a0303210908030402060706140702071701050f240d2405010e13060e0a080304120e010203040510020115270218010809 73
    0xf0745040780001d07049002c042e09551a040ba000362011002a0115001c0c6240c00200e8201928140712202030310012101d00340c0e00d843e201c03502c201a00240d080640e121020f03400010030903800108452105c0c98075400b15240110281ca01011a000014050803150341000054018503088004082541c07040b0070000340c0146240e40ca21941c0710403200c9a0241e0701514051180b00c203545448040c0004081c0244401c0c50720400d808c075801c4000d1302a40d940d0503198082c00044d284c80e0301c5403c1d104000340400700100d0036170806130700d03174003120058445412108003803807a0600035000350b41c1651304a0303101d40f03c01e48075403540d0201c0c0a0410b409540040d0b44048921103c0828050300220714090081242c0700d04050921075400c0910a109900384800d6940c01700d82c9903000300a607402c659040301c14411600b4030000c2640503013145100c120800207141c0700070401002051a050f580f02540c0b03170310b030701c0319031900c00d003500b02e00c9050386208104804801d2003c0d550301c9032803559841002041900c8046031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 365155413 1250 365154163 365154173
    0x2010309080c060106030507170402030706080408040b12100605071106090f0901090b010207050307030b1b190c0b071b110319030906022e0e03091918020c0d0e030a 72
    0x260a030080760006c1d45030014017954681c4401c28000e09140303411140c802d0b0816030b00290382c44120344030b01414400841d001070244584902034800178000451034a544000c2c0c40e0041d450b10000b110341340804c00325070340d0201d10f0740e1240c42910005a40b20100c1e0400e0302022040081d10b80100000300c0c2e00030b4445122840075251181c111307009140045020610081c007c00282c00d00855400540c080d600000d420030110703585980281d041031340c410400c0b4421400150300052486a00d040c2c0c4a07002c4101403503240d445e40108c400e00e0481c010f0a10080580f201c2100b1980c09001801a8079841c201d01d64200c08150002c0e148060b4440040840b25400ce80d6801a18011560901600407400b5201f04010403901408850250004082c208400d803460384108503644280d101d03a028039640d60f03525000001c4082040720700c0c10318010140070343c106c1883d03460000b00b03500d40900c051103000c103440e542c0c4841c200e00a842e00807503094007420802298a104407a10050481c059905100340091075010070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 365156663 1250 365155413 365155423
    0x1202040815180c0102100b0418110108010902090102070302010509121f0501050103090f060b0a031713090501240903060216110111060a09020604380a02030702010309080c 75
    0x101542081c1e0301e040c600706080810700c14400c1a5050140c102e507203030000d181c0c1c0c0401c0e01001c0343e554680002d0382541620205005000c1420fa80c403442c0d8621000c0d01c28043ea207051700070840f0090307a0b4544181e8844080900b81e006824403280036074030400f01400190b01410240c201da600143c001d904d00c0203031110745840e001302108010014807007801c2840d50180349020f0240941002c2c00c2c1030140b82c2444e900d0b00d00400840d040604103903512407001074190303a5004a070300250380012201d400301595040d0342a05d580801d0510345041500c010000f500c40250069504941c1e40c0510702506201088690b000700c415000d1840420512500120000e000c0344003820500b80002034114144c506403511030b1501000d03601183c140400101c0b0204608000103526910000450020840107010300c0850041d0040350040002c60074080940c12045007200c1c084101280c0b600346144403019200800c2d216440b0302261034006070000c00440000d54026082150715134410b00742c2c2d600e07200c17100c01400d00f81 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 365157913 1250 365156663 365156683
    0x100e01020c0d06090c0e060a060216030201051b0106060201021c06030b0a090c0e0c13120c050f060706020309060901182001090b07051c030213030b1b04090606090f08060712020408 79
    0x8800d800910002c1d0608040b0007012740326500040410440302030b58243c00301c80c0e0348002410030800060720841040d40c00e03141040d54130345000a08c103642c2c4030300001c0d010b034001c20510700c014045008070081c64141030180d0b8084070741060840d85a511401010000742c1251070041c6c546028184000810f1003842d41741511407418610400d481b0003400303540e000310b03446aa015003855841080c50030041440c1c2c0c041c00c0200c5008542c200400301040b004521580100800a00601c1c408002c2000441e004650240b141410340b000b040240b450a10300c070b001d618042c6016102481e4030380118021021012100c24100301410000510303075485400b07201d2036004500c11112900038851031340085040c00c01200003540c2d603050641c2445120b41000354400300764031015007507805c0c12000c1980010b10362104107100c80e001c01c2203550745444804400250ac01031007036800060588100103411424490f1040664580324090503664450240c03c55400400041803100d640d8208400100718800300701da1624 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 365159163 1250 365157913 365157929
    0x601030507030b01060e060306040e1006030c0312020d0516020f0901150314070e010c08160c030b0a052214030c07050109090c05030f1e0a0902100e01020c0d06090c 72
    0x351401c0d40f5190207103c1041e0b0140d810b0000d548501440d90380c50f00240c1390300031030a40340010112407090150340341010244140146038034205003c801d004035001100c00b903d020340710302540007406a100b00e95500c51040d024002034403c0c04000f14881c2d031800b0500388a800204071086044d103840000d81e0000007a40101c00102d01c0700060114981c0501482c1d09400c13a11091005902d420a009030031429880b0200d070401542064850030003000f03000f6652078044040000401c040c1c3c9140c0441048543e0005840c40004400020910038080c01164465007100355180c1f030300c0400c0a41e10401c403c0501c070032950200748544640032448100050822082d131640100f001c0d516020000d80104402d80007119805d05000391300d41456000310445c0d40040c140740303061426696038107400c1018003503e0742c01529401e26005003c51050306070030104200e0700840708805080c000c840c0c02d6640b4044100081e0250700280c0c4a005146002450305001e24001d038004201d00c0956030303070b54400000075046551 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 365160413 1250 365159163 365159173
    0x19050301050c0304060b0d0809010c031403040c06080a020304020f04020c19080306120703200111010c030903090b0903100b01050d0e0f0c0604030b0c090406050d15050c270f0306010305 81
    0x4241700540c060b184182c0020349031301300602c001d602d03528840e00c0342c28115814841c01e00000404c061003044080d40400c0b03251812030b1a81400e01e446001e8008500c505000611303d81c02007040088144200c03401294000d1001040c08608000d000194110900010803401040c0290320188018882003020903c1130a00c0c40d035914200c000c2054070444100c011086070310203602440050b03c90110710200c9a501ca490801c0e80c092040102d0f040801d04180c0c92065007444c6501445075095000070800620a403600340e403482c0c50342005203040c000da841c204d074954090001269511455031000c0080441803504078a0400002c48080980c0c0b64440ea101035035109281600200c2007e00201d005400f084480c036141074610b4640c08040800605022000c20000030311501a940da948007800a00001d4007901d04030125080607003540e040c00751416181410702000420000c030354001c603030b010390010546004001d42082c0d000d44d100c0484206c503400c0f41082010001e566020403160740218841d0008007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 365161663 1250 365160413 365160421
    0x31805030105131e0201020c060c07030c0602010f060530070b0f03010e012705091006081507181e030206040f06110c01080705070507030b090a170a0206040219050301050c03 76
    0x407103108284c0c1d60004134440e001141900603a804218020903440c1190195102c42104031400e00b4404142c3c0020716a0100140000fa05901034208100b2200c80c00820001300f03640d5018050b14880c2000801d4020000b0792030700b1070610f14607004804c12400d07402210711aa40350041c0800550101040c03018078440403004114000c050036a05024003008030b108c201d0046001c3c2c82800e01c03a10070400c801d2040d21a4000f5220310810042c6207515041a541840760703907a103115103a12405080c0e545020303a0420310010703214030701030702640a489181c0740301540840d250024941d481007290707408a0748203001c0540080940d441b000a030001d48a01d0703070b01d0030303000d4903183c4054070039911211301e2704840e080200300000300e0381c1090034503074000f842e030800995800c0a0302d017040c01c0c480c4541004086403401c00034000c2c1cad03400029000c1e00c19441140340e16140c050405030750400380200f00540b8010b07404000080c00500380400040050301303140343c10180064039000040d094903400c031351400e00a04080108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 365162913 1250 365161663 365161673
    0x20d110a14093105010b102c06030703020a050d1d1908041206020d06030c080f030c0706030915020304061a06030f160c0c0311090c040e0403180503010513 68
    0x1a00b0a680360f54120185245050310a03140c20007a003800b0104540f07000f8241403260a410510034000b0017401c4d091043c0702510b0103401961300158400700c0c8000105040708a0118240e842d041d004024195410742d80c440e80d0480282d03220750141820020700380112406503606005409108072a11b1180c02100021401d4038079100c410308484071045404410380d0301141020b012181034a910b80e0244071000340c0c0b07061030740c06803041c0f01800b02c505141400000034042504441000d80f03082e841900e540034a8003092654a010360088818203400644081100d10f009500400340f0502c6850002c02c20140006402e040381c00032101a15616184d007049010703050714495002c0104000c4030003504600305111440c2a2401c002c241d400b444070300e458040440b6001e10100c4000350350025000d42c000385c80e840c00000b180c01e070b106290300902050000c40d80350118582640c05071094414640f010f84d1715901d0407120041d05442002c2e00c0c1e11080800b05a03503d007230107031034400c0b50040303d8800303070f03282c40d2078a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 365164163 1250 365162913 365162929
    0x417010509070f091104030f060b01030b06090f19050901060e0301150e04030c03110f030d15061b21030203070e030c06090904061112040302010515060403020d110a14 73
    0x1068020b6001003206000140c2102082d00a41e11022800980b5020032003c6035894803031904054504082141413604011890f000380f2903850003030768240301900d076500900a19005450360513a01c0020f2440214a41c140f01100c0c4c0d6007280a10b031500d039219607031400308800b0ba0003a00044c0c00118003d03d0f844940c1424010140035074400b5501d540502c0ca0078411540341400900010304100c0c00300041c0c0300341440b610390035030890391904c282c07041031a1150156540c7e40c091a019100c0b14240b03046164190200c084540c103c400c00e44841091440300504190b03900d02d03844084850054101c01154030450400142020b03c4035074500603524284180c0203018001e0b500f401900ca90307c42c05d1090550303220003060302e61146090f2001040c07500c1d80e24040000d400060302400d2080340c040390100640c0c0740a09144d002d113000760000c01c0a901c1d00141c2019290b80703007520a401c030108010420050814119442340781c1d008030580c10381d0b00c221000159200000342d02c004000d11181083d00319174604001b07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 365165413 1250 365164163 365164171
    0xb130e0d02120f1206030c030106090209032107150f020d050f25030b12030304030206100e0103020117040201030b04050117120c07060e132a0804030e121204170105 72
    0x400034140f030084100064244581c6402c0b000e90400074002c1141c42d1020080f001c40844020000e000310b540340c600b1900290060701c0305600c81d01c100c451000021445c8200c4e0552070700350303144061900850f919021968420a05a404983e0740d84100c0c00406c4003610140c201d2803181203020030141884405000c40c1e82c8050244290b080e01169000108145218528031103c194140498010a00c00010300f0002c94403925840c075001c000f0801081503400715403d44201244500400307010707102c42480c1d501e03000900000b80842c1140d22061500384001030400c0c0d12030b10502d004640d03140c224004c101540d02c2a0f100d5030411901400000e0801411300c48060303005001d14071181020440c0e04480d5581c0c015105800a2010141c518101522041000c216246082030b05003e11000302555000b01071400d20190040d5a1000c48441c4461060b0101405180c1540da00795262801d202003109a501e9900340813881d110702840c005000c0514009032009103421507000240c3c0803d11040390a58030014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 365166663 1250 365165413 365165443
    0x1c06090b01091401150908071403061608040602250609030e0102010c0206190e030a08041a07050909091e01090204060f0e01060c0320010902011805130b130e0d02 71
    0x8184100d0b2250290b41d0341121000c014134000404540c4007039400e4107413500320510344d024418010980d88203060f41d060490340141c048130881d55400c070b10346d00074cc04078002482c00a00d040c0d003c2004079899802900c04000c01911041000c10624075603035800000b03201c21101e2503140c04402c803d0507082200002102000c0c0000c0c003842221040080d11540c0003040c90713005181131414580420033a52102d03190301c031540102c0b6521800b08074041c0030000e04503021030788400d61070b14442c441e0200075100c43c0100d240380c94a80c20481c1c1d60301000030401e0010f04504141c4038400340e0001031051052001a81d10000d80005200542c1c0d00510003130300d106070065407c2c00340d040010898910700c81e90040c112001e41c0380c1754414803114a070441e15040ea902c4400c0714130000c802c1c0d081440c1c106502002c0e019200341c0f074446000d4400c0130031142c42c507402e208a9501c255880650321b900801c2c1d4104000a0b40700528850321034900714030640860341c00043d01da500380c1c0108415502d50360100030450380e4079034507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 365167913 1250 365166663 365166671
    0x60603020301054e0c03030403080d091406010f17010605030304060f021606052a0c0112020f16140609120703020f060a020a1b0507141c06090b0109 65
    0x3404038480c0744040740308044000000e6851049120070131108526845005101083c2c00034a0b61182026560340a03418038034080c40c0341100c0a07103000811039048950040e00da9050501807804503004150952080c0ca0082061418520031101408901d0181824941c505501e0b41000c00b044038101440800060a038941181445103960020582e41150013900d850400200456000c0342040c0c1600740182e61800381445c04540c098100b40642410519840ca8801c421861450f158101945010402080d0806401540b0f0f6501c242e07644c15200c05400ca001d0b20f401015290b80606500c0b40601d4103080360b001141c80200f003002e010700e140c448011130080c1801d081c214051a01e8038141d54051100140015240041600900103940780c22800020b179402d510b81400d038130b40654020110000040c1d07809400c1c030445101c0c0c00c3c06e206501e40000041c40100d003000945401c001081140d030354065100c0780709404841880003c0d501e41441000c011411012034a0034038100901a0171910680e410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 365169163 1250 365167913 365167919
    0x6050301020f07020f1302041202040e06040b0105010503091f09111e01031a0d06090302071e0b0a031b0c0c05040c1b031101090807020306070801080a0b07181701060603020301 77
    0x11010b440415130112503020280c010388000508140b06000d00400341800420000742c075817010b002c55100a07000f03507001d0100001c1c42e0882b944504040718010b0801e00a040140103c0d485a000386601600140440d864190f1100040419508031821908220307103440c0b212040090140c002041200309413017011a00e0f00e4410f50b180b110030b0180020741010360f5080075240705000c00c0358005800402401001c410116801c00001a01540303600b83c1c09489407100000340d40e4511004cd52107202410410700301c260420503551400d60201000c4020181c40c1c0e40f40c5c2c0182030410111445101c519110102d84002ca40351216107414258011881146841050428290480910001e600c40305540107080c040f030b803500703980700054161290303c10b40c03810700c542d01001005401043d5882c004c404492840d03071004400c68051409014055140d00000010030008038002500c0c3e270848210704010342d456140c4202e8000301401540490529010f1084c1212602d5003031103075001620302c03807805525540c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 365170413 1250 365169163 365169187
    0x10914030408071712031303080c1903050a0f0e0304030b0a0203010f1206060305030d1d060c0a080702070e0a021809060f0607020a050d050d1412010303140d060f08010605030102 78
    0x280320740c0344c8901040c04001d000740018040e49810317110210405469080031004a42185c8900701c0c22804245000086825039820b441a1041000b41c1e04840042c1e0080e03d13000c4026103c0a014600004e488481658800080340940100001020011505c851860070000002040075162420b2907104000520030030010090500070340700790041d00c01a901581c0b40c071400400e01c550014056010210ba008120005038110409101e580c00f0039004030707800d0481c81d40d00c85030140c6a080340c14204102d50992a8062041140d201e8054015142c130207994015042c040c0034120703000034a42d507000640150030a00d201121030500002e603000c82c103918003200850041d10040d03000d030348102c2d8080340440c110b43c1c0e812001000f40901502085400c844d516001c1e6a032070188542c40081404030b0440750b20321100358140d91a801c00e04e841620395911b03585084c0e80d4081d0031b08000018207070070045908452010301694009219064420f0415440c1102c41c60840c0da1581200340b29900400080780540c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 365171663 1250 365170413 365170423
    0x5010f060e0d0c0905010f0e060d020d14010603030c0b160207090f0e0f0109170a2a0b180708071a09010201090c03060522200301020912010914030408 66
    0xd91078104201c01e0105140001d01115072064010000d07462403a000c158083c00e03030001c0381200c00c1e54107030100c019180c4500b451302070302c2140d0041d006081420414003515000400548a40c0214203905280c4840901282901c5291300140d0200382c081d0120320030051144030032607004211445030114800b00c040003e48a03030781e40c45580601c40e01d40b1424803900c5500d0744000c05401c03c1c2d5084500000307045402c1c42c00380000010556031041150114814030482c241102c117608000c0d5510051035000d4902406000600e050060408106907000400604188c04a5002d00165480c1c0d0841d09a40c24030b55161010603000040c0b0b94000b62020800e80c9914204103101d40086030302a9182c01c41750340105d0060440c1080542142305185001044c41141d40c082e5000e601017082444d442030408071004102190003074004d0001c040f07189400d0042400a00c0c08041c100d00500241c42c1242480001e0344055000704d000503140d41d135500400c1007002203004416452810b1025505140c03030031810980b55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 365172913 1250 365171663 365171669
    0xf1106070f02040c030f090b0414161205070b0a0c06060609120f050c030607050a020c040c05180307091b034506021809060f03100902010e10050304051005010f 70
    0xc0c3d44a03000e44954a01035000020821191b0400704404201b604048416010a0b1025282088002407030940500e000c01d070f610700074016810014402c2c2c9442c1d02d46540207000c1509851740d004949010880c0d14951005064007624ad50342c0b0300d10182035041c288100d0f031080c1c0c4000300b070140f6003104001d01d14002c1048846142c20042001085070182130003070030450100b645560500840702000413468220003e0048100c3c0d9a08403802c040a41c000c1c0400c41d4209803081010035006e111150f0ba00c02c20302c0304445071501c064191410580d0715800d803004c0d81e84001d003074480d882d40724680080072941442000c54030f5100c201a20805c0d002c0e03a45841780d004503400742d0242100c1d245224240d00d5018604d03490119070150086541d960660320b010440946911864440d0f0380c0310000c280b80b031500c03501e50101404001c000d4015850705007984c00c024130380c0c45000c90512a2440344070341269204444100015019115240d1380d141c249000c90030030403860b603801c07d00c6180c0b42c014007401d00590029415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 365174163 1250 365172913 365172919
    0x12010c1218060501081501060906120c020309090c0901020d05040515030601052203020405090c03060708090c0a1823010b031509150a050d080904020a09050604030f1106070f02 77
    0x36141000000c5034000001007405024036040400000d80c202c800a0303100c020903000c0500b916942d0b03d44008480e29415481450000f44d0f640c00c4040080c403d42c2e120f0306a41d0314078011680b40c06a5240483c21100c0200d07503040f960f40700401d00300115601031156062548240c035101d481c15042c600090207a498030300304035024400110000d410f5074052000c54440c0c40715200710084c0e501c0345112030b070344201c4640422070055007004081243c001c0001502c41c0040030060182c6003540e640c18049a01400c01403544d0401e00c980c04240c60340d922200c82d860044c03c0702662814010422040340419110051700e0486070400c2500340a004015107004141510f00a0442960304d480da218003055544118140607880b004c3c4009110f105a50a08070900c40401603d15508c0c40755200c0800c242129130f01c2c070142c6510300c10003002c0042d1402d07500074a000c00b0141000c8028548800104425400903002104d00d1056418014140800c000a0006510f4215110f07032400046540c3c01c1000a030300a0003c3c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 365175413 1250 365174163 365174171
    0x3020313140705031c080a0c03060e0f10060c050d0c110d0c171204031b170a020405060f06090f06070c180e1c050a030b102303010e220c1412010c12 65
    0x202c0103101360403032b400401110088231600d0600804210301904140e800f41180d02d0141c070002070306801412110b01c01900308001d00761801c072001c0c0941c0d15204000c400c4503601c095040e841e80503502e00490300b04583c0159121507403282010700074010103c0c49014840d1503400018a07500c00ea02e254219000c1d81d0f0f114043c9101c80340c2d00390040c48002c480d40c0160106100300c11a80401c403200040d640c501c03034000c40e82404a6120103041c491428103260031142c000c032080009200c0c500b40800d03551640b41c00540100d2400720162200740e41d4801603000300000d403814021007103207441c460280c1d141003c5044080c060081e00200408140c40e0120481e2080c0a004180ca0f03c100303000b1390065695a2001d00000c4650fa40c496000700300d50100000d40c4d19414840c0b0090000504d041e082e64140d40da240c01b20041c507200c0342c007102c800740d02a4a4040d40f030186428140005520495444000c2801682d90075050401380c08100e10422000e000c141e0036031500017003401d003070f0f440b200070307444080d000310000f03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 365176663 1250 365175413 365175431
    0x90f1d0a08070c15030c02012d02090d05060405010c091406120a020d110408120408030906091c0c051503041511040f03080301050a08030f0a03020313140705031c080a 73
    0x50701e020440d4401303640700620401e13010a49806802c5540320b061264020445410414240860386d00c0101482c00040c8000e0f090801480150b402480703069001001c1824030160f55964601d88001124101c1c0d076651100c000450703c170703040600e10018080c43c0ca443c0c4400c1c0d1103070010541f01c1c090508070041c980e4905010030300640c00c5504131405241c04100620114001c9401d005503a802803050003803520450403100400e1818a003520107580c1d414010754034125040d4200300042e0400c4c50311a500524998902800c80d20803c0000c4c0441c0c801d400b803500b501c8c0761a0811038be40034010389410481f0070070030402000840c0b40480c4104011020400113041020302c2c0918590300603500250b01040d140000441440303101c402650488900b115818a000d44594000d0340301e008140b11414034200c2848020702e00c074084d0b00550352190510300b50b0001a0b4080c0c4580c0f0704c241e007417440c074996074000c5c40041c0014101401111108002c01c140c54400385101800140f400c1e44c000c241e541915038502c44a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 365177913 1250 365176663 365176673
    0x8070f09080a050706080702030f0405040b010203040b04080d02010c0c2324010e06060f04140d0f030509100203040501090e06210607030e0610120606030c090f1d0a0807 74
    0x280000e400310000702e509003111490702d15134509050143d4004190100001034640344000102c68035880001121428030785040c048c40003500111302994107600060001154642d0140080c100814810000b0301c000211074501030308643d00c1c0b1455104001d131000074000840d980120b844080c035003504400c0481030102c8181414210101e07070170034106c08080c815418090407201c206041e1154402c04443c507803a507400b0050984915464900030003c240030070414202c10300030f00601c211018001210848103541c40800c01d20501e90708402003540481d0100c03c038200f000010052102c18001146864103010010340b0100b0f01d8440c546d1440d5002c80090f00644441c04180603040010310782e5104454088111501e401044503c40c001a01c0c001e0040740d01030300001d0050242491107850605281801c0001d40c4d0b01c841160144e400d41c0d06c8600000001f20903000740d40041c0600c07180082c0d00f02c009500802a00d18118624400040c0148510300c00400401c0841c90142d000c4901942c1d10128609 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 365179163 1250 365177913 365177927
    0xf0806060d0f05100e0f0403021f0b03010f0501090506010e0a1403011b1e09030c0b0325200a0228030605070e01030e010212070f020a060504150b01080708070f 70
    0x100d030641c9810641400803032134010210700700303035550403100c5c440554074288405d40e00041201c0140050380704c0346c48001040e4a44c601091485003d00e000304407070140030042030a5640c402c5034070724035580c2c5200400c50b0540f03d10546801080c240303003017001101a8000604118994003480d040d0080940c543c0480d56401d50009604008015031880d42c4a01c3c07160152590080303100b007409029a8103041340c4118070400080341039030390090494540500740b071117816054000a0203498230801071598030b0607a55050140500a070015034818281e00400c21824907d40050480e00c40c0d0340d40241306a50042c1e4600e003e8241d00000e01d200c60b420b51000b00341510320355200e903001402c4140390205003c0c0b81580030a00d421409000c0e00c0c03d01c02d4a0b281d074081e508034070824401d0412080c00001044040340b2070340f540300300320080e0320464115010686841d8100c41e03003030f1401c6a03102c10381a0f80102c80e2200317014282c1001d00908210040b46401b020141140c0c000800c0c0404004252040021190090751 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 365180413 1250 365179163 365179181
    0xe0c0405060a05090c040609151d12031215030c0f0906010c02060c030a0201050c030411010c020303130b0c070603060308030a0b0d0b040503031f0506040303050f09090c0d0c0f0806060d 81
    0x82141c0c0b890400045c08002c81c0c1c0140202c0c00028a001c00c040361521003103403240343c4004260307038895101d4002002380fa4095100e502c0d445c0e108655560301402c0600c2040540f5500204883c0e40240d418440060188074015040d000e0180d00031031901801a5070701a0702c540d00c00803e81310b105684e07841000407580c00c1400c0341c00032f5001e007000c00c2c205001a00000030f01014003242d002048242c50760810700126002c116001051080a142d1240ec01e500c00d40300703940c2081c800f9040728100000940301d103001800c00d4001015000f0f021500302d200c4002000141c00400a03030504000035421034540b0505440700400040f40d441c0c0710000548039031160061811440d8008140d2900740c1403902d0300366241d60058540395481100c0e0036001500000f2450340700e048501c000c0000c4c0c5018a10741c3c0949854001c440021b000300d070306204031400307078031007401e001c3c407a04440460f25074440150094500712802c601c45c0758100301000802503e11504001010b411440440c0c005848000000a20024240842e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 365181663 1250 365180413 365180419
    0x10605060a0503153a02130c090b07030813080d0606031d010b211c020601060f05030c0414030c0d03050c010b01020c09040b041b03050a030e03010e0c0405060a05 71
    0x500c0d4007059070050103035000b00c8020191403680e5200200b000001c0c90149001c03144501e1030910380f103003082c0009003184104180c2c0400340c4100c400750009803a10100d100707003840441e19403030380c680090b0380b040310140900f00c1001d105060403943e0301d00800c01c07203004020140f403e04040000003440740c00010b54080f041341100138084203407100350040140030058842e500c2100c1144140c90240010300030584003803c042c240b0011804485680303014100510a100c2403405a02a16000502548041100928150014030b255490420014a052007030408041040701c203200380f0005503041005c403000c41e0800951024040c50f0300c00041d04118101d44600d40c01216440c0e0a82059009030280030900b1404008100000310280166140c07800305003080e81c80800c8000040c0061241c0001c00c1d0411b0048451041c030744500003c180c6000e5194005890540c03182d0300c0c100c10141c0c098800302d00803806078002d2100d01e10449032031360b98440d01c42e1001e20607910f810006da0152208030410000b01002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 365182913 1250 365181663 365181667
    0x30f070606090f020a2102040f08060906060a27020c03030a060302190e0c1b061e07110613032a0b0a05040201050d050a0209090a020d060621020c01060506 68
    0x40c40d16400800780c9100304440282070140007052400c0510075103407143c80b02e440381010000d8484136a510a07401c01710b8031803426428440401c80c5100841c1e06030191502c000203144608003800480d04d0301c00010300d03d034402c255207007040c010f490800a0305511245004403a5403880405d005c0c1e10064012428400d80754400031041049403100c64100b03904072030085d60a000d0040c1c0c0c1c0c03400605410a980101c0395041040c601181e103034400a40100310309126a501e10005000034506c4034108174059559282c107000c140003051018401018040c1c00c00ea003420710f100c094070200d05081d100c3c0002021120030800303c1c0700ca0300500d03000742041b07410402508008003514050f03165410b1010b0242100f601c1580042000540801c0d5510505005580586031a400c0070a0001d01070082d10006005009150702402440a1504e40c040214002c011080000d07860b1507c0500c8a011620154005000c02840302080ca0000c010880551800d500070b10001da80d0f00c4c0d80068450140c100366200380e07041040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 365184163 1250 365182913 365182927
    0x80304050d0807030203091b03011b0807080a09030e0111071a040306060e0621030f040603020318010903050d0b010311040e0118050403020c040902010c0609060e0f060c0702040e030f 80
    0x11407203400440298960301c015440b080700c114100e01003103400c02c4c11607010303402d003c4000d4603001d074040500304020000710714280c40043c01e030a81b01d059960540480e071a141070201c495081030f151940030143c608100554070a946000b0045a501c846660511194204080c90a84213115140180440701c440c02075800381211042007603400b51000743e85452420202040c144a0780900d40d0140d03000910001340391501c410760848040501100d000c051008001c0321a8642520020b040207042c96200144c80745043d4450081d00f1043c5c507120b1040740d00d42120200040e80040603149000200100000c80c0e80c040401a030043c00d12021048104201040000300c50758104a0785040e030704a4004141c1d0f0703240c84035042050b10815900100960010400c0c410541050781c89190a180145802c800385105622458103c030f40501c001d9400944440b03002034102c2003084901c03401380c1d20400a02603450b0049039a4a0390161a20081c803981c1c031107801603000715040080e200d0900c00d0403806952084 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 365185413 1250 365184163 365184173
    0x1a0a03030908010f02032a190e0a060806030d03020c0106050a03051c0c03020712060b121015030b0402040c020102040b03101d240109080a0807020f060c03070f0f080304 74
    0x1d01c038428403006600744070340c4403108500740c000c0d2400303100405229041d0310001d40f1140500015441d07620306800c0140045011001a0035040040c0e41d02074403544000c0300d0002c1072203505841030704101c0074019a5002c1c48080e880004200601084500d030042c0c0350032010f243e450141149a0000341d00080c400b001005228020078030b04465003030007482800100a440c0b041d03c4582c2140c10140240e008a03004102c0500e8980380048074a10402c00011245c54401c005624410081140b05250740460000d07120180e040c400c0792119141445201d141c5407840d0b036030350751328040201700034041c58403100c10141460003501560f0180900b603001d01d4032464106001210004a4032900c0c1c0038154001e4008803007400b5815113405000c218040b1201c42c5c80103c44103080500d0700c000c80381088a40f2100044070304081c4031b40032a00f442402695990b00590040010524000748800d205140400001d095020300100300c0c2c3d512507000101d04043c1d25a400c2c00c0f110041c03c0f2202800501c0000100700c2040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 365186663 1250 365185413 365185427
    0x504110a1d04030513081b04140106030e0307060612020a08190212100c2c0603060103050414070f090b0928060b0f0318060402100e1207090506010813080d1a0a0303 72
    0x1c02c0029200001004c0d00420049e42c4c4d072140c0d00d401280f102c8006010040c070030340001050500d07000803289404101d554800845016920011002c01c3c02950101186000c62a001c000d025030fa000b0600703880805104d482c04461501c0091050b11030a02c4448409404d0142d40b040040150f4104882c1d8550750025188100308055810018810400305011605140030801004006405542943c0d6160300550041c440500140c40c9403000034600c0344561402c0002c4c101a144d002c90300e0030424500b6003560140d854022811344150454001c000c510307a1088444045055810742460580c9060b0388000018511601300703c000b02e00c002341d4a01c0c00c441c00130040d07001e4541d031040041180c4c030140c02c5640354030382554001c0d803185801805050942c8155004041d801d03008040382484c0031034161039803804145c0d60002c0f60144e1210100322882d03030091034440d8850901110b443c8250107994505800c2c0c4685000c04001d540c0e2421030a9100083d441034081115024180380e02c15074903800c02900384 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 365187913 1250 365186663 365186683
    0x180e131b050306010b0d0e07090c2d08090c031e010605040e250b04120b0a0b150a090909050f07120c0b18060a030f05130b0609071b060504110a1d0403051308 69
    0x1080300c110bc1c0a00f0b106810300001c2451180980120b80b105020b48203c407442c1e80900382d00c00911400d240c554007039805200b8078003a000c0c10155a0b52140c00b4103c441c0c29a400c90b40403900c22403510a003e500000f01007011007100440031f002d05085403d0801d03a40300f01d1081d410103081814045404148007600c4a100d074019402008031460350781d9031a42400a4410005446030006044440e00c145030743c030030300600960005400c002242d59180c150030021100840c0c41a2001e510090b6000d1920301c003402000003409150102030951007854841d50750032400c900c00e501c407819000444051441000c62101a00c000060180345d4071b045580d4000c014043c8051a419802e01e000040340d401280c504003030507042d910403995840da9880c041080405c1100170422014442045030030f1205a140c2c40001d02e0441c8504070005550906042072000c007016062981d0184a03080014000651908c003480f481840c8054409215615490111014012142007254a4200f00d4010414201c08a81c01040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 365189163 1250 365187913 365187917
    0xb04050307021509010e040b040b130914010c08071116080303160f021009050a061b09080105070905120c090702070801050a06050d03180e131b050306010b0d0e07090c 73
    0x1c001a80100f440c034900c640f003640781c041000407080080c039040c503070007014047c940100b0004a40c559040810b000403861340b010138070182d03100c03500f50800203001880ca80d0310035698003c01131f030142900013801801003c0c103010240400100300311a9513070100910035180043c1c2c91406009640d8506055490300181c0d6170180c1e058889400303051003403080c842912022081e0340241000c000c112081c00050250003001d03600d60007032501543c0412042d010700f00c0540180804811001e291110081000d80281c100c0307903459040c141402902a4050748400a40310100c4084c4211740c480180d0a01d001498640b480e0044050410401080c2c0c0200d1503030100c8000400911280ea50103014034100c4283d03014141c1d000c01010000f4010034424020f0300098030300e20701503a0006441e800203010f00c12080300d040c1a5210301e40c154030100400c0000920407070302c02078502c401c0241020300181d29900140a00c490020001c85c40d21407080282c4c0005000307201c1e100c02c0d44e0f0103030785801c4d840000d400c80c1034220300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 365190413 1250 365189163 365189179
    0x90612151d1b030c0c030c0a080c150402010c171c0501140f150f0c030c07030c140307090e01022104021c12080a02091020030a020604021201090b0405030702 69
    0x420300082d120348440c04841c4803a50320b1640e0360a401e40b040d030030200e09105244014040c4c58a00c0008201003034169004103081d0340c0783c84890803500c0c600300000c1c2201e0012078102044c0700050b604105d801d80d1055100020b802c107100c148100640c640116036015603078055081d209510410103900007811b0f140a41d1300211072010b40ca0a000015000740e081980041036031074a090344c075502070094400547c0c0e0508031403400c0e0a60f042a8555041603c20818941100204004010151884e10010000c00180403451022000082c0d260601441601901500d03039241c000742d804290f04590b9000c1145014081c0c1d0206911070b407400c01000c541c100c1c0a810341c80321174000b0422100309900340c075900c2402c8140d4840c070318100704d5030100c0c060f182e004c0706c640034807920409590b40c030010058003459694040e08000c80400c11541e064142c4901d2410f90010000e03d01810f50206049500a4056070026880b6140d40d0301640100f01c054005402c201c070a8050004100010009052690088a20750 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 365191663 1250 365190413 365190421
    0x3060501050105070f0f1a04060c031a03031903060b130503060601020309032e050705120109060807091e02120115090f050d03200a030311030403090612151d 69
    0x950240304d54080944a0b04201d1242da00051400c1c28a05210780b00b041d030b504041422240c10401c40d4020b84007100e1103500e031100340d2440c0d43e0521440401c0072181c08011840c201c503801003500ca00c035903450300315000055108116414081c1d00803800030308407100e403195100c1d4000b95003e800a03082c010176101c0e020b4031010030019880001a17800030b100c02000b0b0b1002022000b00d05900440040c0749002031031584260480040e2188505072054140d81c079030f41c1c0d8821804070308601c03121058003c00c4010345844414404800700103074140c15130f05c100c540040c01c2c0f20007441140d0a0140c0a02e10044a40002001005040c9244029048403441c8402410402d02c4400685009800d8064010801c442000c1005039180426080064501a040c02d0001c3c8040324407501c010212140c207000c2c1503001c10740444c10951f251046068000e620b0b502c40381907091a64000300120014460b0700100002244480c4060700d46a00440250707218142c003c1c01c05960707102d4034984001c4040d01c034221012000001f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 365192913 1250 365191663 365191667
    0x1412010b060406030c12021206220c050705061b03220c060f02120c060a0903120e07051302120a020c030c031206040b03010c02070537090c0912030e06071b030605010501 74
    0x5507104050a51230111142e82d500144003100c1c50740724480c81003508024250484803018820729490521036500d166645c6401c0c1400ca1900e1006400402001d02800b859000750392500c060303d4016840090f4081d801c2e0020341d8022802d946130101509004555000080081d00306c24220b960038099002c0d1a002401c402d1486090b00a41669000580040d03000550300c10040d031102490314032a05064030307d1912200e000040350900014014240d01500c001c0c0514540f500d0300179030b2800020780175850400d251000d0501100081e0080465640100f49181100424015690381320210001c6a0300c52880c0d4403401d110300b0055400600a07860500440a2400c040c02500c0b9004070ba500103102d103524200a004011403400204050040042044400c8006041d610500d00e01e242912440d05801c00c20740d4000c40381000c12080900541c0b0604204614021801d2403402d41c042c14103011590303140307012585a1140c00002040d0090fa042c078035020310110034100007507038029102001107070780324001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 365194163 1250 365192913 365192917
    0x24090905070e0c04031104020706020d0f0501051c12050912010f0b010c0b1b0f1c05090c010818120a02160905010803091207030203031615061412010b060406030c1202 73
    0x3c000303400c01d42000203001044040f03d2280ca500406003006107810102d4454004a80152029690f4941c8403003080c150b85480340615400f42100326210307030703286101e01d45603100880050030007842803031136052169840d4007403c141c61a1544c0600101000700050721082e0082c2060030810740ca443c034094035020170b540301e115030540740d9a0004e070140e070a8440301c0c4034113111451180980c6030070700d0410030030b601c0c03180f02c00180c0070501d199002103c40c40151450300041c2c4200030841c040c29449002c205415a9004180e83d410440c41c2d0301c055541003803001028206035080c161012048000180380700c0c0300381e0000e41e44c0300307400f440e00c001c0d201b080d120460340c3c0035128213104000703096105000c0300c8613518002405440440b412000c072603406551313601107400e47d001035000601d60200c40b4560002c2c4100c0413030718003194800701c2c0c041164905106441105500c1da00c9030a000344003942524110450940c0179030104103004114a840341d80d2540d005000d00400c1c0a0f540000b40e000744040d84200b20360003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 365195413 1250 365194163 365194171
    0x7021204030f14071502030703030605150406050703052a0d021507120204050307270b0315041a19060b0f0706020c10050c03100605120a24090905070e 66
    0x8107002500031901e466412485002c00f40324540513000c400203000c0860004081c3c001c2e61600595124850350030050110342c02c5510480c016101000e200c8100e0200138200c0e0305440190400b03644420365820200c62601996400b080c240c0780c00729003124511402605800546001400c845100d03007402d000720380350080c0400c00c458020010000c0741009009a14400e80b428803400c005040c2560fa00000b231030007400d90b0029a070106414281c816400703260b01d00c40d0301c011000e0f2060241950000119940b28070f404032401d0062030010100e010007502051401581108030507004440c104001d0540e5004000034144c020301e8900b1100240f0ba8003101c042c0c81c180c2032070031080e90500c49a034544038082e40c0b101a4002c168098070405402d503048900c41c0c0e074040c4c06000340c000d840c0c0c5000f40c19012404101d42000d002c0c41801d0024210a40c408100e042c0e001034a4800031071788050280000c03000f114a42071081401014a43c003007146070385070340300b5180e0324021001c8030082d6603038160215005c00181c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 365196663 1250 365195413 365195423
    0x2031b030c04260606100c05030f0d0c051908180d080601081003020d150219020c13060506091203130e0f01060801050306070f14030a02070606080303101e03021002060702120403 78
    0x81c00179110b494582014519a9500c1c14590f0038a007880d91014215072011412042031900420a0020064580b0501c03410b00100c1c148181303004040c4042c140241c2c940c04484041107000000180341c1c040301d1141c40e00440302c460403180c18401503800500707a1a4221500350002c0e02c4400021002c0c0030005160003282e402030300c0a4010b01d410b84941d0541c2030302c0804005065000c001040f807800c42c0050f13400120640f54094000e15900340100311050982d8408121840e060040a110035038400c1d045440b54001269804c031036400c003404413810360042940c1440d01290500c400100038908443d0355201c0c1c00104440102681c82d003c056420b10028040c81d601640500b0010703210500507100602c0c2400a400c00030080b01c02515212402ea204503115480e0341e402003075440420809000d1840034200f104051819407410401e1a00400854414041c100c803003124507803a81004181300e6805583c000e17100e1404500c48000195031108150b912200620810f1040014030b000002941c1c01c0c0c903445 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 365197913 1250 365196663 365196673
    0x10030902040b0906130f0e0a050a29060103150b0c07030c0906140904150c17090d020d0c021302070305070203070b0c0a1415010f061805060702010302031b030c0426 72
    0x11045c050000c0103e0110302007035640c0c480b51080500f0040003200b0007a0f2046004006a013018a005107450049011114412a140300c41d84411001e062245510400a10703001402e04040b0311038005e0410a644500c4510100041c0034000c01d0340070500b082030324041c8603080303821344d40c81c030703001e01151712501c200c01d9007a210510203e814900350000c1c035003160203040001840d41c50030264900301e8801d9900c071004a0004a1141c1d10220509490740c0e10060703100c00b0b00680e9203034140194075607050500c81020054540000c4c0c0840d501e1014a0055007a0090219201e110f0740c6405015030380020b9081e88240300e0000c0016103201c03034400302c0f0844a401d9015103542c0140b5070f503030600c0c3d61040481030603038050101e200040160002529008040c04440198441c0ca4003130064180b48585400c6014014a010b003481030391900c901b21509240d080c680140c2c0d0340d403840300010411501c138083c049038900000c107100080c80b025010300305940c2e0041032580155250101c00021459001c0001d11076002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 365199163 1250 365197913 365197939
    0x30c030706031d0609060403080c0702010206060f1201050a0b01020705031b01030209060c010507170a2708040f0609050f0f180919031d0901030201092310030902040b0906 75
    0x100e03401c41c94503018450603c0d064030306016107160a00c0001c0b55540c5042e03000d08100000d055200c6502c0390809040c0f00c03d10300e002c00640000352581001041e8030302a04d0180c0350440c4503160f104104180556100c003c200500386803d00704050440080e001e070043c070401c0800f080901c0c1c003154400c11020b08600030081124207000560183d00220092a0300c044207000c130301d054070420300915200368030310ba41d020001c6c101d1000d0404001405071000441500d449c0200200c8848940d981e1180a0851801640700340c240c0743c000b11510640c4c010b81c8800c801e001e40000d03a25084801c0c14255181103507110346014054090002030a00c4403000b035480700c00c0101280c0405004070319990042c10703903801d40e011080e007c28400d43d08550444202c3c00207424240c10940c0600741d48201190b0603084400041c0c070b5145400003400321100d4041c8003024142901000c494200035000b4017080c0d50081e004141c004401d420140080030080e50a90043c0d003401c0803140c803868220791061150100130424100109 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 365200413 1250 365199163 365199167
    0xd0c021f0e1c17040c090903080406150b0d0207020604080f060a0509010b0d0f0501200903100b2803150c02100c02070b0c031608030601120509061803090a091a030c030706 75
    0x4800740c01900c0080e1071308400301ba803031a10700034545041e000e9110785a49040a00d0a2001c444d401c0c84001142d205604050080146000031141081d002000140c1c81300468000a00d251081da8081d42080c0706503182c640c114600494200d201d41d08001003000703140d0300d091005099820402650b6400541da0702c0c0c03a00000c50496000d00017900507000050341138914800100480443e0a0f59201d0441c0401e0900d29440c04110a14103d01c084009000907403940b40812510001c00760031040c403080c00203c12950100d43c2450100075034000700640e00d107480c041688001001c01046490042c001c3c50a250100d040d1030103170600c600c299034003c0010030b191403c4401141c00004295215000030011b42c590245c0310000c0100150003145c4c003036602d0806900240c0200700d0031180034000303400c2104204030280085a030a0f0300c200c4000781112103414200307805055108481c0819070118142901150156071640800c3c3c2058a9451041400d003014042590321601d1802d4207906620860b01842124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 365201663 1250 365200413 365200457
    0x332120d02190306050429010503041e03080f060d1101050d0608070308090406050102070b09061602030d0e090c0903030f3f1305030d0c021f0e1c 64
    0x218100c0801410301c902d0729481d0010b858403002d5200029120b000500c4145071071711030a42d20011843c0c82400d000c158001c3e500341d40550340070f000d06007d80800024213104c00d44c2140e00c0456a000110051001c4600c0d018103403503016103d100c5040d402400150707003424003e1450784410307000122040f9a4901310011149548000300c0e541c500c54851000151150081291034040c5103c1c8107005d45a05407101400121511607014504543c006882000131811807000c031600c005054465956840040d081c52a80d1403104e6002034061003504000131407950700c141d10039030f0443d00b180d00100944a6148102840c05540c0c00c066164100f0004440804120b1008103244e001c40861900c0c41000d010300704034160304802c4000704082400d1681d210841c03950341800d91005006a08240c00e01098131400d40d2070103958101401c2c08da1341d000c4000414000c001c0030700d407503611003000002c0481d4001c5c1c100152000d000c081606104103104881c0050184040c000140719039522100555051100c9138405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 365202913 1250 365201663 365201677
    0xa090506040611091206040b0702030a050301090b0607020a1d07020303070e040b04140f01080c0109120b0a0603140c0a2c0411060331120507060e07033212 68
    0x211104110021058545d8200b04c52040e4110001d00403e1034070f41003031080604010000300840d0810000650142d812100b80d9055031015200080e1003074407100807508912032040301179400041d4040002b007400001001d10f145e0801e61841021135200c0c000140d0341c038081621110042034404200380c0e0181400c0c1d009491030040140003103a0f0020030007090300034a030240c503a8801d9a104100600081c0f80c10070000446403828a030031568540742c0340c660b181c0c10880c284024004090000403881c0c000198000070003031600107003141c56504922416aa45400d46840c07036004410000c4000b5001103841055070351400801d511010715100900d98014215000b841141e410400c07800e0014283c9414000c0c6108550070200e00794000e040048001040003030040009034500c1c4d1210134000140c24580c0e5480d10000c5041490b251007040c9040d5025003640c0c0066100740c030950000006104030050104190f6150201074040703002c910219803141c03480d4500e841e900740e04c241d50301c1d0380403005030b0010003007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 365204163 1250 365202913 365202941
    0x10030201021614061c050c0903160b0405060f1b2a0a0311060c102309070b0a021002070b04020a0b0c0a021302120a050103021f02070902030a0b0306040302030307080a0905060406 78
    0x50a000039605c07000700c50382a641c181c0000300200d14255107080401c41d6480742440052142149441c1c1140007909101e107018090243c08080740101c019031001042d1040611004240320003182d078440b01d55502d41b40c0ca008512501100b1460082001c0d180d8002e0100e0800a441002c446007940c40b9100400b94030100140c00403810040c0c050300c46010b006d08140d14560304000304101401101041c00180200040b803d0f0080250502458400000b01c3c0c108580d1841203041e00c0750009c160a034286402c20f02c01003a507500008028003080b0720881120310482c4201c1b500b0423410b8880c0d0041e202402114143c1ea4070f5442802c40c08050b241c500760111f08000b900750003624050450880e000210415240da01c3c07616110801401140b401d64017800401840c007002110404e2000c0e002581c0e5151845100c0e8000e50001c0800d400c8080758202051110015040790300d50304040c68001e42d241d0084541ca030000301200003044603060307540214841d060f008030041c540f44e1140c0d141c0c0e2004040d04038003801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 365205413 1250 365204163 365204197
    0xc1b0f050a1203021c0501080d0807020c060d020d051003050a0303020c1603060504170f070221030a05040f06020a0b0f10080f0102091f0c0308130b1003020102161406 73
    0x40e0100c042d4440802290380143c1c88122408000d2100d03c0c1d8140da03000701c1030038000188100c00001611000f009040d261040082d01c0305502030f810420300595807900010002049009411990024800d545107404200001d80e10301180c40401c0c5614040106603410500c01500800c1c886d4001d0454a0180b40030b60b442c0705000716804031520303920343c01100d10541303e004000911101098000344035041407101c0b480c00c080d401c1103207424400c46e18005d00c124052003d0804528540100d01050898003080300c1e41c581400c03201400c607070003c2c0701d0000c01d0b42401d1408980c2a03c0480d0201e40140e03c10514101030303c130a064040d00d5100100b00c40414001007000150030001004180e5030f20305014001030741c1e00c100c2010302000c121041c031120326403070407580c0e45140f599101400c2d20442d074151820a807291107581e00ca80d9a6500564050032800020051040503c0c070417a030001280e02c00d8080380c02c034601d222069a150050b601c0707010702980c50300d9207611690600d50002c00707541060501c101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 365206663 1250 365205413 365205433
    0x14010608090726010c0807120c0504050607060617030406020a03210f0c0f091508040203100c0801061716050c010b060d090212060c04140109150809010c1b0f05 70
    0x121000c6440c3c0348561680e2640c00101c0c0b409a020312600045640c03601d400340407841d0a84014041c00c01004401d500903a40d1040c00d401c240c41030043e6800340000a003003540d02c44050901c000a45070b80d000b03400d00c455540080340d01254001044070101c8801d90064400085107841c02c1d40c07008001040d902c805c005501c1a910301101a220381d41440f001c0f030300d0004a185a07441d0040c81c2c4003010700b0303100c10300c45280c1007409a09078221684100020030720304609140d48500c0400c3c10032018110703032008542852000b04001e0303000365445050b940196a10b0402035012801510f003250280c0320722903440c524448069100348940000e01034505044004121040c40e003000c00c03419071003601b200080325070301c000c403a0440c0761501d0626403400142008003020f081005c18810b042c402d030b205042d03d800c0100d40e00c80c032a9000d070b80001c00030701c8185010b400112600c034011704940412603410a07070307519068100b44090b000301e10b40ba11409644200c034514405907901e002c0c820040c0c040607181c1e441822010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 365207913 1250 365206663 365206679
    0x24070804110405061f3b10020316201c032f0309090c09030d03020a030f02030705190513060e0a091803030e03030f190f02030109020715140106080907 66
    0x3804016407903582c141d481c20002c1c400c03c0e1921b1040c0c101d00541040999101d55102c1d4001c0c030b144005000c44d1180f00041c4103410681c9580700351080c03212403500300130a400a202689068912000a004000c0034a446ca007040084200ca00c001d490b40000b1480a4140424843d14500100180d400855080e107043e0354a5258181501e18054425a10020b80a000e606140ca162600190010151410058160300180d100d4210001440c201355001c00c0c2c0714501813180d04190300e01900380700c0455481c241210300404950041c0c171440408141c6669007103040344071304e08698030351a8488102034003078188041103030000103072025142d020801c80c0011840b009544940c0c0c1c3d072001c1349449106042036a00e0f0103815100d001400c0d070400d40081c000c0220b45d0309413250090303000710701c400c2901c688004c030050580101988840f440c8024804000415100c2a682c010721856010700812a01c02c0002d0000c4016034821031850301ea03030f1006100400440e40035810882e000120074007655280e40d1698a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 365209163 1250 365207913 365207959
    0x18120c02030f0a05150403021c022415010819020d1d010e061323030c0601080102030601091e03060510030609030504030b070314011e082407080411040506 68
    0x40b621664001114040c02c00a0411000505420080681c0d10501c2c144c1c5000c1d45034400480c9800c040b12141e03502e0480c03688240510314801c084540600981c0d02d00d0300841d495200d0407600c842500718000c084101541c00744c081207101d01c45d40720ac01e4182e0b113500e00c8080301035001000c03a0080d80380c46506210745100210342416000228000000b00c0000841d0f040b460f21b00050300b84d144509186003202c010900307040506e51041038a141400590303040c560550314501c80c03d9048113081c000c2c0400842e0300c55040d0010f40c002c24007680d46501e0252280c0008a110405184002e481c100c4038004100203421030300701c5035002c00c141110454080e540d46840d800d82c1e60000c801c50029400140502c2040072114100b40c000181d80f030108100740e1f81000313142d06080180244101420030080c1c1d2000000a030b2801d502030f01d0701074180d5412040200700761b08500c15038201010b03403450140c002800d1b580700d8019148119009210003440c50300c0e003030511000700000323010250401b5078918000c8400041c450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 365210413 1250 365209163 365209183
    0x15070206030f04020f01050c101e0c021501140f090c0903070905010303030507030504050a32160602030f0d050907090c050d0c020c030a03110102090d030c0b01050418120c0203 77
    0x80300b4202c030b1500d0300c10814032150b02e059003814000c007807000844200001400001140b0596400907401c099624480e1004108083c0080d185003044400002c90b980032500c1508140841c072150300e01d0340c803082c40d00300b554084080d95800849c01c07019140585000d500ca2a04070881c10003281c0741c0603410000c40d0038921144c0041000d941c864004008141d81445151b900016a183c104010f080a0761055181d482c0001c0203046060180020110700b140a4504000c0e00d030305600c52880032005599603a11256100c1e00700c0e02442c208880024030500100c102d8500041c020942c070300c0d20b02540f90768802010060030455a5104510010442c142c0500c100034041e441034941ca0703101c1d03120080b60401d940c00c0c0707001c0320110f4000c0c0702ca00c5455200000c0c85041c0300e5040c24507404a408650000d0300a0160390803840d44820812105410f01d50800d1072094101d0044100354196a02d031401d000507540c000c0c2d0b032003c0d1903903244004804a00445070030103504800d8541010486541d0f00020715182800d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 365211663 1250 365210413 365210431
    0x60e151b03060f190e060411040603020c100c021506040204030327080703060b090912160212010513050607030e060402040e030d2a0c05191b121515051507020603 71
    0x410500013501400342c06607215508a070f05101c230f08031715400d92009000f00d106a01c14160007044204400e8170602c0402c0c040020394174104022040850003c1da290004d01d60550000c047c1808281c050605008a8083e030fa059202c0c454040f2204162900005008030320011b00c8540031004a0740090a001003402036004000105190300750804001401901924a0405070b01c41000010b060b07044000341c60141c2c260418166214820b13001003828500e5040c4004455460a010020001c800407150300065001e0001c903041541c404c02d094044a29010b985800f40d4484400a0300601d456005003a1000b4803d0070f69042000401464040d16585421082c0c5c00608401206200080c190354600940141c0303866078600e03061781c8031107031191a03a00403a1424196aa800c2042c8000c2c0601030741112074030480783c044a1b43da25810268280301040860780c1d0011001403651203c2c00f4003402c60040940c10100000d94640300422101341e03042c001d045c4078100d041c4140b4000d6541d0601030f600c80c201407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 365212913 1250 365211663 365211709
    0x20f030c07090e0309030604080a0504031b03051c02070308090103020d0c32070605060414040b07020d0c020f01120f09081305030106030f06020f040909060e151b03060f 74
    0xb46541902c1580c443c68440e54018440c1d070034596000200c4941158010804580d18400380c40125030a200c1c640001c0c194200007076580e0408400d400c8188100ca0243c0305540c0309210082c0d045440141021441c0f00503440300b601440452440e00080c0718401c03050400500d441e25202200d81a2140c00039600003080040003405030040d011401040840f0050b40806500f0f202c17a0460500f41c029114041c01d031b650355000049040e162a844446000030080300c0c8041440d2500d041c020083c0212824001406481c0c49802c600340240046031402d54014803d1080382c46031801154010300c0e451044c42210384640150045080620a05012901807240c0590383d283d19140500c1d02c070400da0090780681c1c90540c04001050700602c003c180190700040160380ca1600840800f202d02641e0042c03203489180a603880c081088503840400c085125109841c00b04a60101441c51701000b101c00d403041000350340914810500001c000c59008000409081c0c02c070174040042141500c0c0c02040e00d46102038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 365214163 1250 365212913 365212919
    0x13020111030a0516060f060e01061403011401050a090510050a03060e062110060f090c090803030a090f0b090703050601150504060813021824031c020f030c07 69
    0x44200340c0320146001600852600e048070400900c0d51191070703080149124510703100c00401556404c40071002d51210024040c10740c036070440500381d08082c41100c0106401d4070040f518803107003d0513203049503022044400c02d49c02000c01520b044e44916070940c00c12807901004034a0359110b0312822901400d55035080c1d00c41101d45c07000b90031910150491010448070004009040d0358400700c404e160b140c00c00d9200015050010740354034020ba00e103502407880d401c0c4200400c00c080b2210b224002c96200c000244442002c6040c1503515203500c0c090f85036250420400250780410540120503032621132103120300c007020703039440c2e07030a10000541c0c000d4880d4120003420828401d0400c080340c054403608200c0003045800880260042c415445031070240082200002c82c00e4654554220303a45070060402402401041d000c801c8040c01128098000c4030f0300c4504041610340300c060504045006001404400ca15004984418a44110f4a01103110b1020841003428050016005800515000f4461141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 365215413 1250 365214163 365214167
    0x3020f1b0106050f030303090703020d031808060402010f080403020615061b0d1e090510050d020d0605100c0213020c0102040305100506030705090601120506150c1f050f040821130201 80
    0x8804d12418803035030042c424070024403000310b202d00841e076044960301422401440d050303e079461941001c0780d940001110014a403040172502511a510076131701c1803400045c4030010f0329050300640c4e0140042e07000303c0c00136002080409900b035010600a051340c1c209031005842089004c0b196001d1011900320860000c1070340d80103001180c0081c0101d104220700c281e00100200601c4042c0715491150b8881c0180051050040d01150072403410f0340000e40d92404e00c00d640101a051903c121401882c041502c000301c3d501c0b80c2d00c0c00d44c219034010b00350389450703181a515102075040b03140500025542000004001790041103e1550340c580410003181d00d151841c2003504180c00c03644070750b00039616202003003071170fa074032188968811080100016041d00e420000c5804c00e84007174851384800c070b400219003040c00e20000b808001410980f261070b4034201e0501c1c000090b07480039504865601ca00c04041400105a01c4c00b4014401e020344800050381003592500c4003a0b141076403205034071880c8040d5801556 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 365216663 1250 365215413 365215429
    0x16081c0f050f090d1d09010602031b030c07030320160e010905070c062a120b04060602120705031303060b012c010e0d0f230a0b040303020f1b010605 65
    0x3404100d400c8883d24150a51a4662402519181c10006880e24424181031141c44a007403641020b05908019a180e40d00031b90ba076400501805580c0c40404581c0c00306000000031a07007030400100140031000d255035000c0d1100c85520003407200f05054201040c240038401c01c000c4441c0f01035440f030071621034680700c2e60854440c0180c01040c116401c000800130303005d07001018640400d5000c000025015694100e0404000e041d043e080d9000ca18840480400c613031100e40000c8041d65501c080210100382c004000c211401445520056000808140034045408020f0b018640c01841035900d48141d001011641d1134039034100301c8125030f4510004000d03523800f62040e01a00035410b10840e800b031842a1035021a800000032a0410500801c03400d00e507101c0b50407040107294071890450f4201000d183ca40801e0003040c22042d2954a4400321005c0000001021100540c1108010f0565100c81d20118003a43c00340000700c0b80c4941c10000005540586a003e4154100010000400704e04000410002c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 365217913 1250 365216663 365216671
    0x60a06030902010c2a030311070e13020904080415031a0d0b0609070e3015040b0a1d0c0a0603060b0910111c02100207050316081c0f05 59
    0x241c41c0c8504080140d800061144440c2d411040c03181000843d00c0003024081c081c0c001d40c02c005c5001e000004100740d0400c29014421002d07074142c0b0809516107201d8450000c003221701d080c0b2043e91900940140c2040120640c1090144070040e1809441303451807555548a5100d0400190703407030107150043c1107001038004040801300c0c7d581c2c1300140c0c0f0761900e0041e40e0002d441c0c1071281d180ba802181c03549000305103003100e1100140680540c1d100c00380c003d15024540c840c1c51000d044842507810080600483c118114040d4041c08950b035894070384550680900050502c41000d0307841400094050000801074002d00c9200010040c154a44003400400021544107009140c1084010701a0301d1001090783c0702c02d10b044d00c0c208036a0300b09070012242d02e000c81041c81d440c0d004d0801c004070840040b190390102c4100f982c00300c50700354540090941c224491a9800f0b84035400a10100d00000c1b8040356070540716002d400810f04200c10102651050503001c04068141580e801030701c415100300d40a160740c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 365219163 1250 365217913 365217917
    0x506010e060627030a0f050105011d070c05070509011203020f1c050904090b09030304031b030507031b0b0c0c0f0a020906010804060f09112107060c02030a1208060a06 73
    0x507810580d02060560054000a950012400c104042202050b0b00a03402481005040350384c150a181003094040c4980e0800b521a9403c0000102c0c070124405d000c411540c090900d035440d5542c82d110b00b15130440207408115a01c0c001c80c0341c0002c0d2643c2d010010350181c11071040c0510010444d140180c40c1c001c0c100b0300003070030740c010507681c18a02c032841000f40c0a0b0107003800c0155580314604002070040c07011400042404552009010703c0c0c400000246104910036116290088035103414005107551440d401000210108410701c006486240c40341540c181103001900780300d5030350741c45006050080b81d5890907e00c000c90300701600e1104206000e040110300700a0043d401c120b801003110150000c040905000164004c40c2c20403180342e0001c49800400602000925428903080d55104040da00003849010445445165902090103d4202481355401044e182d480e0081c1618000000001681d240c06070800d4000030500c004510800b8071815078646040d480d007001081742c0c0031026041541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 365220413 1250 365219163 365219189
    0xd11210c0d17130606080613051603080706020702040e060c090f0108010503251502060a060b120a0b010210090f0219031a0615180a0b0711100203090909030304050601 73
    0xc2400200d19040d00a07501c410310f5400302e03a1504140000d0710417580a04102d01c104020010044140a0741e2003481e4490702c00d9480e02258003140e0501142113000150110204014510020307550b03500800d0114801760002c11118001c0c8249810140215603140c1c00d5840094001c00c945001c84e000c80742c1c01024201440f49504080201740e9030f050309031600c40036070180d03070a420040c42d100c3d08600c000c22551715140e410500914000392100000d40b000c5031228102a8041103450b0030805a8800d000303155031402c0e0075590b010110b0302a0017085200c0e415405890500a020303030460145401c2903016139500c3c0954255031050141c40b0351803010b002c010429030344e014000a6400c00a60282000071408c07081c40303032214000503088020702140c1c05203000c000580032245c1010340046440030f0314115074040c001c0360b07108a08411481980c0c001031100102048810803072621481882d107c1c40300d4411242842c03000b2000c40c0164800791008000c9900c01700800c030411108120843c09403140b4203181c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 365221663 1250 365220413 365220437
    0x1003021512060f03070305030406020d080f060d0b150d080306090604090804140a0509070216150906200a0311010f0b0d0f03020f01020412030e060c0d11210c0d 70
    0x1030031090340070380310320311640030300c1c1404010b584c1c1003154078003551308101620340d510740d40d0342c01a40c1c03180841c20034000704500c0e00014400305500c400c000e00c5030f04058009054034085d5a107014041d400140389502c02200b0303160302c001030f0711148260170860b48994801c0e50343c1e08080f02007280c4480d000b0501c9105078140280100099406010b6800300c5440d0f075585540c0300c0c0020001110800c064010b40d821009038010810203541c0081c4a8000d60074900100f201142c0340c0e2840c071402c2d0300808440000c1460450100f0085101e00d110b40300c0040c03409907141500c6103020f115820854070001c00d80000c0e070160208002140284a84000174104110400c809200f80000c40c00404401002405491400012005250090000280d4040c800c0000c55560740c554810200c8045560801e8001914460102e242410044122203515400e01d0040a4000000310200c07528031105440e0b45007401485450b6030820542e5030911040200081c01503200c1e000629924070704641c60300c5810412070b2084281d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 365222913 1250 365221663 365221687
    0x221070c0b070c0807060603030809070501050301260109050606090a09111c020907081504061d09190501021c0c0c03111608031207020d020c040f0b060310030215 71
    0x45803100d0361040610500307696510040d102d91142000c00781124400007200c00410060b0380c4441e040e00e10984402000fa2a0350003801d40d60040c6010f880e002c14404c100620032051803802049000882841642c0c84920003001142540c401e403804440c00e601240901c00546800c00499900400c011020000e8030020f841d034200c0f005000f81b000303001e00d15401c0d03065400c03c42180325080c00b6401410403030041c10085001030461804580c10386003002c0c1400341581c00d18181c01484100c1d00220210116a03440f10084400844094038405e02e80c464222104040c035107051304100498007d5000684032032034030070710515134140320364811303001803804407503c4220f03400883ca02c10050b0035103803010300b000140ca401440c001ea00e403c402d40c00c100608000070030308400001003c0c1480032900181c1d46031207484081e13035220743d4802c0140c0540c1194100080320b0030541d1141354181c2c0741007008183c1c806a040030900c0c541c826601561a5843c0500910075402d180607502001140001c130b03203140c00500c0101c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 365224163 1250 365222913 365222927
    0x901020d4b2a06020d1805060a020a0206160219030801261906020d060b1c02040e0c130b030702101a030c010c02040b2101141e1e0a022107 61
    0x228070b00724041e6084a01406503a906a4040c191404000c1200030076840301c2c20080018030804039090f2094800160080d01c3c103000f03070b44030300740160000c01e0207460350107444a41a900705401401c41c03086460040b00c4403c0a00414113140c001e0304c400e6225418119901080b0800d0b038480d010907004100406001d071b0000800c0300003100512800785c0c503805d0918241d4040e10030302da440f500e0702c0c1c02d015000c0303101501c500040800c0550441000804280061450180d024500c05d400200c104040003d450b480c0a0b80100b1183c01c2c402c181c00303030305515105903ea01d0380042e1080310069211400702d140140442c03080c2c148812151007624107111000000a5546014154082c104041d14200b1021915690042c291518005183d0040000c03103032071498030765201d00502040d80d824a5011074003912a201044d004941c1508002c403a820300c2c000c44601a00090305035001600d01100420702c11f00001c00075800b0b01949030000d40d940120484a048101e148034101d4850403042c42440440e41d04505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 365225413 1250 365224163 365224217
    0xb1008210d02090109031407140d0503040302101b0606080d020105090714030f010c0221030606120402060903120a091d01060c0c03061a0a06050901020d4b 68
    0x1d025039504410030040311600c0183d4001070141c2ca991030303112002c110200708101540d038000024003901d22100b040001030010924058210b400802c401d0015040c91000701c3c540a25604045050b141d1b0350007416218039500d441520625034800e01848901402c1c80b400303003c02d90910090080d414141030782900c9024a21913082e040300700a004c1d002e1a2020f005540080c14900000c01900030b4021000e5150744420304072070024055048401c080500c11002c0d640a0580079110728208610f0203102c602014024005990245041c0101c421680c1c0802c9008400da18001e1401d881d102454400360031800c09800545807200701c1490860f0a107002070984d0304550991800308038000c414103040e0700f4550190000b0301300c0c90a1481030300b80c0031000100049950303829141c2c110b03c207075180811500c5024221072507006030040c091461080d8030075208001030340300d1600c044400c410214844546141d81c010350211070600000d01803880352040542d017596401d00c0c185000725601090340040200c006403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 365226663 1250 365225413 365225437
    0x1e1522051e091905010b130602030a0807050708071b05011803030c081b030a0521071727010f0b03010509030703121401060309020907090f05040b030a0b100821 70
    0x10000500203c901090300d41c485607030010810071540c42e03800070840c60b03001c48440310300607012100014180b88000200ca500400641e80c0c15000d0b00c804a0441d01170b8844102034441c440103104240100e903404c031541c64000801000c10450510309800509071045401110907400d858103010008240c0001e460703041d09900c01d180994400c407041d1742d14a01e101803401401244400b041c1b2210858002009106241050307030004080c01c16a5104c2c0c2d15950308581100020300d000d03c1140d2945c0c0901d4805800003902113039016242001072002003040c6c42c0e03160821aaa4450030240c4408010744100440c822040d4000d20103840e0442000381d80344a0b4400003020841505d0344544106400c0d030204100ea801e030440301c80156902c40c002405022000c800341c0c495150754010070740d031901030031060007110343c40381d03096424620f090104002808540283c58260054840350800603108085040c031400c507071030354400d8032400c0902081c034043c1d000d00503204688402d40346043c070302c1ca0705058031017601d200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 365227913 1250 365226663 365226679
    0xa0f031a031b0d05010e0714041e0c0c021009030b01090e0601061b0609030f081f09021e0301030804031449110f010203061e1522051e 59
    0x1c2480f011680e5809001540f0701008055411400310713004084036009031000341d1109220003004126280074003030745105240e40f04e0710226040103800c44042c1c1003490a05400800180c2c010410403170002c9940800200f00620900030051322900050152025a40821803d95562100c1d5550340040c02102c00b4480d03010030a04030302c100207820402007a8010001d100c00142c0c0c0c81d007c1d0a040c90204504c0105402c040041d80071841e0300149902ca103094161004024034101030701300258072441d98280b6040c0560006030788210204025402180300b50041682d50f0314600303042071404025043d540d5642c11403034002809410548941030032003c950240380c0f10107050308000760b644480500401c541807560030800c000315004400c2481c03040c110300942c0ca641c000040b446080b40b10846480b5401011450405911013500800f004030100181000d1300d682c0f480c030660300c900c0d04034400c00310907111a21164841f2a41000c01c0d5402482e09903038052000c1d60310350801c21000501219940030b1508 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 365229163 1250 365227913 365227963
    0x1608010e12092d0909061b0c0f01050108060411190b0906090d0311060907270b031f0b0f0f0931020a0509060922080a0f031a03 56
    0x240c0607140011040030221440340f072803802c01c80b407140007000124610803868080010716800700414840e1041001c2181d412500c51030840c8184503411803000780c02148074174441c0e1142e080c5c0922441e4080c088a000800c45440c0624200103030203111081c1e0f900540116000c504108030526292080e101024210307034441c01103802003a551300070004a180c0c460003003141d0009054026100c0a00d4143c2c05003036500b40d41e14000b080c0d550f100a4841c405032072511f080142000ca003512040c1c501880c0301d0b603001c610340d000100081c3c07400c0041c8600c2034104141c80e0307108003004464841d02021742400d5450002014600f0700103018004e200690750b020344071880006044030b034150742402610046042111b03800d0490300514081e18001074080340181d10798031001c61a49000d1001c0d03841144000c04500496441101116036585195140300b011b078602600f000002d400300c8040d00d216142c66980040d0000100303001410b84a6216900c01c1260b0090302076540d035180030802d00107400611000c6202410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 365230413 1250 365229163 365229169
    0x1502090402120a091a090a02010809010e0607120501060215160e04020a120b1c02190302100804030f03050c090d15060e07021c05091e040903021608010e1209 69
    0x1158001100b1552424020018032110551021100600409410080324000e0342c500711a03c1003529000c41a5019112050042d841041400d41c012041030000c01d0010312160514036010741507a5081c003240c0e88410902d4010003510a00e80100707c24801064410f45800b444154040c0c0545590002c1d00e2a10b144400140542501040c600000d44115640d0038960001400c030500e4015801859042521030450352030520308080300207030804109001000c0950802c4120501c1c404103e03e22021a20004056a960010501d481d62241c8807242e0314545840c000305004000d11202c024145400705000800900d0029a82041d01c261a2a0707c03d0006040c107040340c0d0428101c0d260480c0c2070590104110018003a10b90142c4d0180d001c403889840c200003a039041003920701d4618001340007031285015500c1c2101c2e645e88051400c20450030444000e00c041400c0d20358000096015a0000c894440701c0d941400c1c902d030050805400800594204849031600c40d01a814449510f005c04a80240581c1e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 365231663 1250 365230413 365230417
    0x60a151e0503011701060b03070509030708031c0501050405090604141002030907030b010806040b0609060406080105070807080c040f030b060f0604090902090a0b090f0702010b12010e06070c1502090402 88
    0x428248038448040002803401007481d03009000300e583c0a94500c21011882105024180503503617004811402c0d42c1d6900f508403065001071750515454410a040020f46080510003000d41c10400042000c06c03049032083d810959006074081da00861503c01044070034980032806540196015240d050f0710b642400080c1d04c0c00c201085a40c6c3c1c05031001091201060b00080c0c0d54003240e10603090201580c0e03884a03520b844070000ca0f0040c00000c807a100044040c81c001c0e220340c0c4d00c000004c4c030010b2215125074106003102d804407228004105c1e0542070050450300110301c01d41c007211400115180508040d6040c1c100f184a00c0014076825408004c141c403951101c030401c00041000d0203a549465980c00135101520007440d05a0240b10600301141009a06000340c29610002a15065203500c64410001c08231100515400440d560340b20740003401e03520b4442e0007044c40d01110000c80c0c014903d440081c184403000d800381c418000341070403980c0000c405d03008580c110300220000580b141903502c0802d02034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 365232913 1250 365231663 365231687
    0x230d030f15320d1b090204060323161b020306040f120e010c08090102010b091513020310050d0302190803070e03070305120901120c03061d060a15 64
    0x4010340d84404180b01d00c400340400b0301182580408004401c0c1c5030480000340e0070b50700c9101c0e00b100c1d955121801040c03207404480301d08040d076585803100135a40c0c0f0202089030415000080020340302c1c03c00704200780f48404155540b0290311540308081c14130302400c5c008445100d40c03660500c040621001d07081c00c06800c0d001c0499802030103450007407500c9d24140741c80c41c10f040004c03103c9580d00c00c003904000d0f2081c0c01d00d0740e26030f0060f10b8001241c5450f4036102095003041c01487d04640d01c9011091890300c480200c1801140d000400c3c0d42e450032250104242801c00c10385034020684140200201c054054071004101d51003a0f4500d0700e0a2103a00b002c034200280405440010044022003000b0090058021442008207a0311142604146000c25444010503c0042c00a91040b01d0704000030030b4600041034500c1050410400781c00f010b41c440801e4400203100400860381c0d612042020000350580355040d0000c41c161088c4614283d8009405100c282c05061408040308000b40c10040c0148408541 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 365234163 1250 365232913 365232941
    0x11407031d07150906030507050d0f0e010f1509020306060d0917070b010e01061803082d09011803080a0c0303090f050d020d030c080c0a09030209090109230d030f 71
    0x880c0f0b8a8840803043e408052070b0400000c0d207000c0b0300042c1a80b291281c0b87c003a100c6076492a10f054101580301d005003c112500c180495038a06641c08034080074403c84141018001c00410210300c4801c02c0030000c8003e07484080c16a00401c10441280d960204445d4414000a00040c1e0301d80c03241881c000b001081e184445c560040081d50009000100074040d04030f540e404844001c0d03a0700c42c00c00f01c0d424041c0710288601000740d42c0c8103100107841038010f80462072050644104032440c01840500e041c0b200d4030f603400a403000050403c02560701c22650080d2408003088809000d103580e660345041d10581c21041c00300011070b404541054031913008100c030103420001c0300d01141618101380741c0311007601841c0c401610522814140c03007402401544108601034842d00003030f80d02c1120700791180c0e0044030705130108a0b10044c04401661201300da5030240059100000f0420040d10300601d002d20009003d40c01502140d6603c81d20311000071310398241c41c80c0c62401041035001e201c4488013504084044c044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 365235413 1250 365234163 365234173
    0x306090c080a1805161e05010206240a120b0c160f02010311070b060405010602010b030a03030e030c030f0a02010b06131e05120d02060f010509040308070903081602010e0102011407031d 81
    0x85c3d096480d90414064032004c4800b482514001a61120101071600c81ea5000d604403000060400c95541c0d10403580c1c1110151450f032246805000480c5030910f0b401c00401c8030b8180301c150062005e10fa100740d40c442417400500c2e141800d0380741d4001c0a001302c041c006081020151092045900c241c000c0c40d448040141e180c0e0b2581c0f200d28010301c1d0380c601210382c640610300d800c3c000142c861050184c6030464102030042c2145100710f450480141c00841c6074220a07110410103180804000c1005080d807501e118007141d112005110020b094441d005209485001c060084100300200201e9080480313001e51442c0300004040051043d40249650209070303c91a8800a00c602c0040411055183c40080e27090351541d0769882c844140800c020301507a90040a072a0009000074090090160040d059040440004d580c9540e600c103e94459507040300e0000f0b55800890442d60400514101c072582400203119811860054900402c0b00803c07032410551101c0c882c40c440728510303050f0b90304803140e003007078403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 365236663 1250 365235413 365235433
    0x609060408250309230a050402070c0302060a090824011401110f06100e0114090c070c0618060302360a0b090a120c0e040309051f0306090c080a1805 65
    0x1804e24061481250a01000906485920000040003200400e00205041841420181440002d4103ca50201c45280301c40f4000b0015940344030141980645559034880c1990400c12014203180d5101c0781800c940a0400c0400d111403040004c0605603a03000603a26141100c43c1d004035982d945500003032355607009080d031980c416007000c0b600d58400c182048400011a6541661801d108005d1080d403010240022080aa42c940092003a402900013014542071541d1612001c5c3e00c0141383d0310040c00710f46041c6044100d0340304182c3d00320043c00f060400f1810300e10701d55030310a841281000034109469000000d00305404400403104048a8046c1c22100080c3d1070344107100e125408048524030030405018000746111491080005190b44000c0640d0594034140c8d0030030b08001c0242c03040301070002c00c24010070181c40e9405004800345040c00710700d50320020b40c4406802c550407500152140c44c01d2841a07614581c10040141c3c01207920000010104003aa81103660b1410400008020303018803040c032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 365237913 1250 365236663 365236667
    0x30309060b06030a15060e030a0602030a0b1207140904050a17041805101505070305030606190309060b0a080c0d080d0e0a14030304030f180f1503050906090604082503 73
    0x600080703c4900c5e003150b140d4860038203807a003600c040b10165140c2d1100d0004400500c840c3c002e190441c0d101000400c83e03c40c008001110702061513900b078031f00c0e0f0107224104415402d403000d200e21002c1c02c2d00c0030210341c2455100d00c0c0d1548403c003805400042911003180b504e200700e40840c1e00604044110211251541c1a1380010f4407054a010910144440001c00c0c034000711503060f8448210f58036100c5c541403c50794165115040140840d6224005000155124403074005001e01301c04241d500044207041803821408940e1541003581c001c80c22071105112007100041c030744d00c00050480c0c0b510460b400234074003101544142d4448000c2d00e41040f5400c040d24030000b903401e6842d480b0350b4440e000000d9010750300303583e03000031603003d00000d850300b0346001c0c000d00031240700c05605446135035024841d88401030140c0f607003041c5d4082c1400c0d006c090b1000344000d41c10300c100c82e0422240006081c5d5410110511a44c403140031740b020b400c00c034001030300d00e04510110424904850049444280d01c440724200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 365239163 1250 365237913 365237921
    0x100203130c1517070504030206070c08010f060e1b0c0102040e040c062a05030702030609030307030608060103020a03120210050c03041203021c0f06050418110a0b07030309060b06030a 80
    0xc54845115074004140d500c070416207004041c06580d1100010241462200014071002d8000000d1007000c01001c8050b8031164021b02c141801400110b40151800c0129402c44501505080049260220038000c0c003050102e19604200d100001610001d10000380700028466030403004a190b100180001d0300c41d982c03049040c07056004180d40c0284a030341d40001d0b141032100c0003034140c2000700740624842a54420300d00b02140ca00034001c0b01d00b000919400319190a00940300d00303911350b0012080004c016418017441000d02621800340c512545140e000c512501d1840c00028844000c16041040440c402c10421403260070010040c003076030400a91520155106035016112142c0c05403981540c50700a008581500084010140c0800d03c42104507008013910800120380c2a00d96900243d04d0f035441c0a101807841c3e05413030a98044030b09281c80003035409a4640c050180c08503540410007100c645050396013081d09402c010951503001d1420f10001d02501d00781a5001304040148401000c10b980 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 365240413 1250 365239163 365239201
    0xb091504090606032009310e0105061909020708070b1005010e0d2406180e0c0904030c080c010603020603070c0515010513021b01390c14100203 63
    0x10100500c00300c801382440041011000000128001c0003006d41c07500300b40100d000b0000d51140c0a08004551221041048451802c0d80743c0c0a51101504083d17068284207031074202d030301156020103201045036440318100061003000c0d0318950206081040c0329086040314010b40d805030a20340d0340c0c0380440356940320121601402d80081c05100a40c0158240007a103260341a410100d41c80144040b000000c51900300402ca542810791074400000d420300b08800313a020f645004a10218001c107540c01c2680c6810130090045114685200034000825004160120050b030042c003e15501c00d44640c1241c007400d56503000a40206000040242c4a81e20810114406100c0e5080e2003080300b2082002c40100b1007802060313800b60794000041d075035494a90081c0f1400442011003211882455595401c60b01c001d0320b001046031541d128201655640104003240d020035070640d91003002224402458040d1561005082d07032407082080b01082c004114081d144c001d510410341daa4500103034100a1521070030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 365241663 1250 365240413 365240417
    0x1a03120307020d05070b01030f0f060203010906080f01050124140d0902010813110609030f0607050417030c0a1104020d0603031d0324040201140307051b160b091504090606 75
    0x5507611403024450130445404a0300091460070990031501c61740843c05540c0c0e021920030b40c400b0700300000560ba60000d14020300d064000080c2c9a4580040e417400d2003c588130400840e4034200c010f1040221100103203c05c09038007170326112900391003882900c030443c80500034014000d002c1494103030005d1580012140314400e0307032a054039858450b00c001d4003112118004182c01044080007e80e0706080c070190950b1100201210f1060340004e41304c5003001021750316000000c50009091098030400074801e2040d00660004514200f80c018540b030b224030034810700030100300c242c1044d944c203a951134040e52024654a03201304180e907517900c0c01030414280c0c2c2160707405900346440901e120340b801080e10300300202c100c056481b018202e25205d10301d262006100302e042c40412081e01900d00388241c083c610400054640310380d50f41113011201e145001c10a9070203420341c1b01012440340345214141a100312503010843c292940107113400a400b18800c00030306802c40b0f0b008180052582c1182c7c11110403656a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 365242913 1250 365241663 365241673
    0x3070c0504060b190e040902060705030d0b2d010309050d020f010f0b06040b1b03030103050607021b221e02041e0e012310020a17040609091a0312030702 67
    0x3e00c2069503207004411403203003503696a8452800c140c1c000c4000111095004100180f100c081d60b0000341030740c01804003a1002c1d40081454100c21400348202003816600301e4045450a038482e0300e0740281c1c85400480b0807082402d8108850350f0340650003035086164040305507002d0a1080320300a543e5849014480c16a40c2003140d68000e03d60700d131182102c400405000246010700340b8141e01201c0d803042059150303a032141803000c0a102024005980a58400c801a10190410307420007860003042c0c0140d03c1c41c40d41d07515904510b60355808030421b8001c0d44001040742d40440b1044850003090104c041954901800809e80d908003440e5004109075820100c1c0d60700a204c0b03c0500111020a40c0200f5060303842d10340041c410b080d08020b4405241c100e07240b960045004a00119000a50003081c4c000035070311840800c0704010503007103414005150010b80c10308061800600410007180d42c400d5032840d65880320301c510007480100d08103a01c990003074100c030707007007000e45603070050650046a02e0360041c060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 365244163 1250 365242913 365242919
    0x20f06030c040519170a060b06030c07020d021201060803040914010f030f0503130f08011d030f0c1501031419030e040b180103080d0c0804120c020a0803070c050406 72
    0x482010359000741c1c0815985810301d030030a402d2101010842d00405031500d03c9100c005002103800a0321010100c0c0c0001a0581c194a843d095042d5400b582d00a48180800e00800100e1984101586d0a80d0303011502062074920702d0000c1011007803100c001c81190b500b404008100c0c114000000d004841121008100c9402c80f03c1c2a10740742002070081c903400c01a59401040815002c1911444a900580c1528a001c240c0124007120300503d50204c002d07110a0042040b2034042803149a85e0031110280c160b02420360840301c0e03501c07441180d0040140420200344840312003400c00800445020803c641840d03542c490405500741d24100d850302d00300344140062600c80d84a94641606c80c1c680c0340d1681d803003c4107004100800380200200f915002480e403c1c1c20103504016000c8140218000c00d0030756650512401540240d072031103803401e428000e18105100002d8030f8030903400340302a10f07071a0207000384110b031000958046141d4080c0c04140302c0484d1840601225111a00c100c0d070b400c0350300f04a0107035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 365245413 1250 365244163 365244169
    0x1060e010c121103121314061308030a02040302090c0c011b0906030c2c0108130804050402180d06050907140d060b0301021b01050105210d0c0201030b04020a0309020f 73
    0x15000000c220954200b66650030700c0c024109446a64124415a810f182114004108821044501e044485692503030780c4180010025040c01035440200501428507000d6200790210b09902801088000e0000010f040503440c1c1e410341c1c1c003455004040c9400740c200702101ca9400d420210780041c2c90f52a00002404241c0e80da08550000d5001da2110308440386043ca00b0783c000c20521601301e040c00502c6c16440c3e2081f02002c9400c500c480042c1c0c070b08001260800c00102800c000405081420942d10040300101d0014015282101c0c001c44001d603407a0300b200383e03a0901c00c041042f0182c000e00c007201030704100025130700424814000e003001c446043e5030b03484002c1103544202284a4000002007000008602c1e0f58000511418010f400940f420b59102c4d596000c0002e407503210707800d90759601c0c01440307145022101640b49880415030300701d107000980c21094503802042026000e00640c00100411a4041d4001c03240315a0001c0045490391240c0c0c00180280c100680700f00e10400d0b00032200e0000340303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 365246663 1250 365245413 365245427
    0xd0e19031a01120201080a0509070e1f0e010b25020901030b0405060a060303050f16050d02011a040504050304290414130c0f030903090f08160f080a020f01170a0501060e01 75
    0x384c0c0596030030f250ba40315a030803d0000d02000d000680300380a45080400d00b0f2590540e514050807441000003490315000103100e0719801641c1000f0040c40051004020145400b0161546546e040d01c00080321005545080e6548500c0c05000f50000207200000040c44000d80c045881140204181c81c4a59195513400f01241c0d0140402000f0074024065400314861002c09054541b00745c5480780c580e500b0a80b103040c03801142510440050307450315100c01403034110900074200f6a4040c0c0d0180198289070303403096120700890160a101d1051a100c2819444001003524110b20b42c0090213640c40d502c8044c09a6400032802c455401030010078420880764445101e0320052072200c0c1d4840c5850001242d04030041d029140c0309a0422849640206420b46240744000c020b0681070000c2c00e6014600c402500c100040754401200c1803e40f03541004818000315804104503411111076491000d40c000603980c44d442002103d00d060091010010b40d4111a40000d040e1180d5898001001ca26031004641d88 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 365247913 1250 365246663 365246699
    0x19020a0c090e0a050f0309041815020325120b03030703091406070510091110020703330603020103050604020f090f18040309060f09080d0e19031a01 65
    0x800340310200300d00c402542c032101c9603409031419154086043d03100c652500100c06681c0c101600002181111441e0a126110748030b501c0503c07114042049807108841c074040b601500040e950001300040d404040c0d0030ba107001d4448031860601241490410007440b407120300220078a12407a048800113145400010340e440954155543d9182c3e40c1009a082d80030b40a01ca1510380100303040c01140c0002d80280031942c41402c2c0300d000041c9042381410b01404101030340c145d80340900800114903006990104081003940d420480c19000d03d6480069040304000030a002c441d2030451803020024010107400410899000342c1c0c1c24070542e22010200003c910400390000750340e040402c09101103003021074803901001001010840d003400d1782c01443c1c02c5200101c41c201c001540140061104603004180241080c41601d401040c29042001031942c0700c0380c84c0803030001d00c4400c0308801d9581c0d5805110495a180c407004003100259646440200c0c240d84045680081803040c0001c203910a81c41080c901c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 365249163 1250 365247913 365247923
    0x3021311160212070b0319050103080d1a0d050105180f0a11030c12070f0e06060d0b030a051b0406050402190c060f110c0105070c05120a200319020a 65
    0x1400c290692101204032404078200d803c44400c00c10a4064102440380200500b201c080e415560705d0104030369611114800e211030034071403800c001840443c1402083d035900d07134a00b40780000c0074510070918000c80c002e00d20016501c00c81c08090841001410f40190380a1401c1810044030302c085103180075243e10000d91040404c0d80940098070114600200d64441040083c05481c07409e90300801050840500510f0905994401c00040203640e1107841e40784020985840100a0342c1072801c0041c1103440f0f54003140381c0c0e0315150082030b40595402d201030f118403507205044031100301c00d28003503d240360345005030305110b60301c0d080b00060300381054000c07071b0561241c0a42d00c00039505500c0003a1483c2e9007001d000e0b02d90640e10802c0d0074044c0881e21401d02200ca054000c02d03243c601c51409203094a00090114041100c95414000016000a01154503d090f44c40e001d0310f076030740008122180e00d0741e0130381401c3c101c1d00048141e900540101c0205280a0384290000003070044000c01da030ba1358401c840c001c007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 365250413 1250 365249163 365249167
    0x804110114040b0f13090203040f240510150c0803040320010e100501060c1106161a0103052406060f1b160503070303020604060e070e0903030103021311 67
    0x5580d88100c98000d00381c9030070481c950400762a035500120981055a41072680c41c40054440740d9449104d0301d00d0020904040258510300c1c0554030600095503d09009155000145581c000365034043c0329200f0341190703070004000c1c41c40c015009025078409031042e4003210720041441015180700f1604503103901e4102c00418515110343d40c007103031040201028071120122885200503150380a004e0f20240311103281c002c01e440b0340c09601c8030b400c64a06910590a100c000c0e507610b400603140c40400718810804940305a20360b55444982ca042d507242c0f5400401c040b822881941c02c2501024110341600d00942c200c6400620310b0b0740c00400407030400e80203138141c04403500107460340c50540002c00e0027681c509015418202c810380c1c15804881540000c00782ca42110308114000e0110658140050100300c0041410030f1035514044e403940c4015201401c150703101d02c068581168100010401410041c0038031859103044003030306441b50400e02040f4459429035501e090b040c1e100d0300922401d404100d01c0301d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 365251663 1250 365250413 365250443
    0x70b15062104050f0d080717091e1e03040e01090513110f0a06020c01030c020111090f060705060403020f15010e01060c05070b030a02090109090204031a18010513020f010804 76
    0x5a00740208125600d2103100202d0100d003905003e8400824180d8880c0c0015050030721018081449010070b21080400c0e4408024005100041c4540c2d46c00b40304881200711032a02135214101300c0d01c066480001e087d10404450346180000040c404c85544810ae54003a0342ca0340082c0050f610309481c58020003900103442000b2402260713030302005650040c1303204140a1380c4000b203421080e01da0300a801681061703201c1003141d609030040520920702c601c020090900d4100c1c00031603a000d0903400300e0280100403c8003031103864540c00c448000e90020100c80151819140003580c0304203035001c9007458000c85a1191740500c101032164141c900d0000c1d25040ca81c20001c0844112191003403c0d83c0c0391181c2d000005440d810100114018111103e0250743c9685400c00903000000e10350103003521510410013080410306103240740d81d44143d002801e0703100da01d4009031074040000124541c40c09502e00f40a0100480204020780c604920940e51003035000b195000541e4070150843d4094403140f0710001103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 365252913 1250 365251663 365251717
    0xa150209150d0b27060d0201020303160203040506161a0c07060e0a06090605013201050306030f061006081509010b130f030b0a112b0e0102070b1506 65
    0x103031201c611041c0300003031003000000015120305500e512000001c0c4e0004c01422800442500700c40d40008141c4044000b0203041c0d000070355910008004035041c40d440e0808146c910b10900403580200310061216488600060a6841d100c0c40050701702c40d0301820034090711056114096842c46654010b00342410142152a004064402c440840b00780e0700501801000048613489068045030090740001410360500d400f440303510380c5425012403207088024882d84049445241450407030020300e4040c3d2207841e5000400c0c58201040c0d40b00d4050b0245c0000c01990600100381501160001d0744c0b60042c41d211031058003030081c040d14286411254020052218280c1c1d18024030701481e89151845100d951034041c180c800c0e00c6604120303608520213052180c2c4e28054002c00d48200c05090764203140c0032107100b103403c5000603800f8805040c8000c0c0e94000d0381c004954810301c0303a41d02c00f000a41d80c1d500c162412070340560b01120401c020144000c0c2041450a00c4800c2d500380b054050ba07101e0b03064410b4150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 365254163 1250 365252913 365252917
    0x305030f161506060e01170103061805030a180b070210030c050f0d2903060f040c0306060b1908010b0702040203060d21030e1605060a1707020a15020915 67
    0x40c84480407a08500c800068070a051071003000041440004025041c40f0b0020071079098110f5490402c40903c0901034804c400950090449500060001e104003049035040500f00100f580a01a40404240102e40c60f402016400580c0a14126081c09070344800c031401e4a0300501c90083d4002c03c45c0b20022503603a00a6110074074110503030034414281081d240205031907a00505241014030385542280041c080e480d906000f0b2944070240b05100660601b011942c4d07094014118080e1103030080129003440303007450384500a180c00c640c040c07080b00c1d2500d407800c0040d4425403d10544015928820004920844446050300e6020101e10300d80080790302084040e400152001e40c0c08401c1540e0400040e5940800c0c041c611075910781307002b1101d00781c1409012185409214030300e51300f000e17844403598075903011100161941100d500e9100d210340c80080301c0c00071651090604050708074003800f620680001d86a90864070035014002000340d010220b85c16400794480075070300a03d01c84804035504a100c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 365255413 1250 365254163 365254177
    0x311060a1707020a1515121e031404030b060f1008130303020d0509010605090108010b0904020103110c010908041a040e0106050c0a0c0303030b090f040f0213060509090601060f090305030f 82
    0x811592551285c0d12040e001040c040c0402c0c2144c0e660304904030341110403103080300c002e14100084801d440d10903119041a134540000c2c40c0000c20250700c0e060b04240c0550780c000c208200e144d643c0c2c3d0322940c884c41c03c607241c4130341981c12501c00d1590644040041c502181545110049907803401c4807078890102900c00c060500000300c05043c2c00b842803c05464051050710b100748031200022500320300d80410700965805c1a04203203040d074144031802015880380760120303410550a10340095407041144003c05140210809801d0075402d003455001070040e000b001c0c0003514039040000440e00004640d03140948158407c261907600b45070b004120301030180c070160101d0040b290a454480302c0542d50315070420026003003240825a00c0840c0716080c1800c48900b54818004840003c8600b096280d62030818000d850091040c06901261401190260001c0c40140301c0038044e00c3d0a810100c2116803241001d00641c80028401c01c2148034862150780c21000b142e4000020714039048900c441d900d40744c2c0c0142 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 365256663 1250 365255413 365255417
    0x1030e0a0c06111516030b180c090429122e110f070c050d0203061b041a0d150e04140102091002160816090b031203100311060a1707 58
    0x10504c400c80c1000340202c6803042070501c802d00107403410488050300f01c410815409005031010480380041c00d208040d030b0b94209240604480d114001d050001d0043c3c051a84082e6a1710b400704d140d0510f0344503101030f0119211742100c107508041c0903909082d5540d0840e01c140e4004103200800c0860741c0c420020501c040c000b640d10b000c900110040e1414100340e015a40e003920704400042c2d880103002803c0360030805442c0c104e0321705211907520f4001a94070701c00030b0040016800c00d02c22001c02c085401049030001d2600700030040c00e6420b0142c0c0d019054024143c49402607091020b401d0441100c10b40b410252802004044115119500e85012812041c50744280c2503608100440742036595842c00b11103852564000d0801d01144080004041c0282c1d000380200e0b030005480c45811100d1900400965521480000b400c070f2007000004d00d420311078003c80301144000018042140e20b002e043d03106590040020314500102c4038107200c4584522147d140021b00303143c100d20111f20b1010b62164014210b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 365257913 1250 365256663 365256673
    0x9060f051e0402130c020a0c1a0301090509070807260601080a081305031b03011506050904020f090d1a010f14010c020d150e0d050f070206030c040306050f010501030e0a0c0611 77
    0xe0103568104d808405c02000540d000203407000800c51402840c5001d003240f41c8840c032410740403415040c450f000600032888480c0c1c907140041c0c0d0800040002d407005003c52030803504502d80d00d8401c4d01d440e64800d03451f00c040110144000c08503000c00107982d07041b1003055004111481260f2111105600418100e080a00340031000159a070f40800c81c0d6403600c10742800c03420000607244101801c4540c9410903114030100c0e01c4041120316040410348030784100c03e6501582e82e0342060180c880034860f152250398421a080c00020512042071031070225000020300b604082d988030848000820210310902042048074048060254820303202100502d01c068100d0030194929501d0705180d2246030360510200b41d5078206140400400c01116a025416043c0246401802968600140f14000b0f01a008075070000100c2d20f00c3e00342104a80055030400340422007400c102a03508400f410070302c10640060705000102a031081c1c0821200b071031660154610412a03c1c00f003058400d44940a481c0c4140c0c007034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 365259163 1250 365257913 365257939
    0xa02070305120108060a2f030c04030503040909030f0c1203200d050601080711101a10021f0501060e0906030c03120304020a080313170705040e0109060f051e0402 71
    0x242c42050341c0a84100e2020f0030075894480044000c40d180d60040c2590301e4080404011407103c619141d00064269211450f81c0381d4440b00248080e100701d900c0100a4400002d0000f8038002d00d81c072099140c0d11a030755080828044443c2101d2001480c3c0340a400e00490030341d1010250b01039406030b07801c4045016014000070817040d0410b17051f082602103100c15030711035080108079a44011403a60041040c2004048002d0f103240007507407982c80040c0066220f0340c400f01060000c034900281400c440b0b00502b0560007200e9014000e403561390207603803034014050b81c501c01e0301d450349903004180c1030301d0027596041c002c03503206800c00c18112000b525007030305800344c00100c06564078240204016101c150112595906040c414809401c641d075002956980050211f13000c410441d4007000d0464001034a414480040e01d0040760a06020340e2115a025207800d00300400442c064010401e018098442003000a0944060100b61101120059003100072100441e03540c0403004076040c2c00c140050030381d0011400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 365260413 1250 365259163 365259187
    0xb0a030603061a120f030a030f0b150a180614090109082a030102040e24060d0501140a0f1e03020d06020310060e13090201021005040303320a02070305 66
    0x240f0301c4510400c010f03442548100e01e040007007070b207a0303100b8210006140c881c002046150303c81c05504650f4081644407548d034402d15005c1e030810f500f003010003042015800144144403940303900c250f40900c00b0403182c9a010b00c450228055201c01c80d40d4585a284181c02260000c1005500804c112814020040e40100c5c0751002005282d080d4243c413501038007506040803502c88180010907010380300740e00400040c842d60080c8200590080301d41c0043c0c4030110f411228001c03640b084425510340100300414460f101040302e8004904840e8a41c9464403001595800d00200d12082c0c051989103083c40070b42041400a138210f403152035420854000901510307540003d403400c04800741690402e03008010703c440410b1011407000200f190341468030007003140c0b80124420703035011101c04442a540318803000a690007802603104420114504020b2031420b4900078005019401407850a4502c2c41000c0110854400b48640011244101c911255441c003510401a60041908a080160034080010301030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 365261663 1250 365260413 365260421
    0x60f040503071b170a080708090d06050a09020405180d081009020c030a020c03070f0e040606181506090b041a041205011b05070209041202010b1002060f0609040b010b0a03060306 78
    0x3070400301540c120520b4904000004d6040e0903219032980c105c1c0d41c0500009110004440c0e006a1003211991640c400c54000344081c014520702402d041d0400080191281e10340c3e01444620780300700c808000390b846e811002d02c1c28281040e41500c203a40151180380c0c0c1c980c01405966840341b643c00c9440c9a035911030032140c00340c2c1c224820010382640041031a00710240c041c040c004a0001c140d0090628524101580320f0040c1c040c8506007101e810345012806004154202c2005030403c0c0d28820b0aa400e0810400010441d444881c50f80c980e269002003185845044100c0854503d8482e9030b04003418040c807449445000040807102c49e904000001c0c5000d049410410494080c03000010b00d02c0d544142e01c1c00c3e00c0308035054001040400c005401c01640c54400300c40e00960807070641c41a91044c00001d03801005d81d0202103a110b03040550301d0b04a1030740025214480c0c9403c0e020000c10b52641004d00c20810000e84004007031400810040c0601000000984940c1403d80b8022802c2a580e031a444125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 365262913 1250 365261663 365261693
    0x150c0714091e0a23041a01060203090f0f040902030712050c0306070504030303051b03090d0e030604050705092509080f0d080105210304060512070203070302060f04050307 75
    0x2000124100a00ea00d80200541d5200d62445150044400301c0001d641d44440010009569140e8404200444203a0644503a156008001d44160f4604041c144805152442100b000008540900100d2460f04c00700c195103d0040143c1040088001607080090004124400d140c05c02d65a122000c090b9404200400091070b2411050b003019802e404c0c46030074803c0da411400e001341e024209002c511680042110b08030380e094500010701ea01e6800380c000d0307190b003040f1400000c1400807090099114012840d0006240c21752201c4164001030b000345521100200c401034030503007101004021509062134907aa20410b0b0043d20b0541c00443c40424126510041c049000a044280144042c072400c1000280ca5070040b001018240b2800c2c03801403561034140603140c092030300010460481400501006914040c203410b4a490b241c07a140002c2c41034106202d060307071000000010844460000c02200c11040d0180c0c064020303035841030aa01004e440c0508200c40f184000c20404012620400c1140b280d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 365264163 1250 365262913 365262929
    0xf1b032404030207151209060f051006020705010305040b0105100210020c03130e04050a0305180d081e0309030a0e150d0c0e06040b0d09080c03030405030405130b090402150c07 77
    0x140d41000e003402840c22480c2c1c1c104a00b900d807083c02c0c0000b1a80c200c0e02c03071940071240d0880410b18008905c0c1500240c40c00710500079195091209000108102c0105482034901d69403c64000c40d540701c00440c00e6540a0754041c1c0031011120052190b4109014200701c10241c2c2e00440720007411000160040380e0064030b100303100703800102c1c606134202c0340080e03401d0003001400596003482c1440d444950f210f114910008043c0709000504242001650340c00c0011603800810109401e510f50804000c1a840f11045043c04d03c00c920503030040711507440035640281140401103003800c01e8120b0035a80303062000e001e10351084109007030113140c0d54000000d20405160000205480d000e05c900075100996001c0d1030351203940140701c2440700d80c12400030b49500305c9441b40e0105d504101c90510700aa8401c50081808034040041004240080007001300b01b02c0d201590985078541800c0e00da541100e24004045c1d80c440307040f0000c6030162900032800d92242008109040c40d14035114403040c60410346910080e8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 365265413 1250 365264163 365264233
    0xb0417280203060604050f0708060f15072a030f110418150c0c02040b1903031d03010605010503060405040606080d090801150317070501021c020316020f1b03 69
    0x10840c2000d1145a0300b284e81520107100d5400c0005048103602001003030001004504800200e2a5450b9000404901d4010300460180840f4201c904010381c45080280c1d41e80280d40e8400d00d00b50341a1181491054003905107008203421599005a4021100411344098039800318400c0f895541e4410401e4085201000c981e0039059840c3c04c0401d1101d400c0c800d0040c1c0d14014004e04040c2e0040d91044e62968101c800040c180f5400340040c207420091041035003004405c00d00802015000340e048c00c15500c004030402200025901007500380c0c0d030740340611400031f5018401700340c0f6810580c0020360028070071030700030512980f24003956150078842101d5000041c001102040807032828490a48203409440c00340403440d0458846403010380303040740441d400d002c00142030f01c1840700a5040d104080648509900045680560b004c065041510381c00902d00031501c1901c5124000513009030201e03500405090102845034540d403c9116007441c3e01e4040c0182c80c0c5501030750120458107141e596140c0f800784 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 365266663 1250 365265413 365265493
    0x5030c06190c02010b152b0c0206101203050a021903090609050f0d03080c16061409011505040f1401030503130b0307080a02031305160611070b0417 65
    0x2015a0200d000c142c1c20359161415a46041d100d03003140782c0075820035108440c0c0d51510210a450703140324000b02da041c0c840041e00f03201d1110700203402041e198040c59089580b541c83d401040c400300f1416101d51645250032014450000c0d004401400c8a001d242c0152001a4002110120105034441d004c90016003070001c240706880e040101b502c05044141c43c13008085400710041000b4017450301010b01030184020015060412400860b0000c10000815160b503504514100c0d010b40340c0c41000651030862000061692034051080748280301010000f402d6040c50041488014403441030031801d21511602074814441d031856885000703610420085a0b620324141051080348103d1308040700d000003c105108640707500440f0650000055a00145c2d01e854030515000360b403242103c020264001c251119840d841801d042c0021100540c40b800700d0080c0d003c0040d80c8801e6540a4074411400c00c1c4410f00c8422b4468074130f8040304813a80200c2d00004000b11180040201d031010611069850324412 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 365267913 1250 365266663 365266711
    0x61d0702070b070503040509090109020d1a07110a17090307030b060a06020a02030706030c05070209040b1902041211030708072301050307080103020f0a0b030a0e010e1c080405030c06 80
    0x800041c40440401070800c03e0340d40e0703041d0700d0788100d128280c0704034074110121300054006e5101c00c800580c010700154024580e40b07820b180d6211851200c2000b40410350006000700e0290740e0200510000ba800f402e0305144940e501000c0030008030342d10059003c00d10105180f07440400c240c00140d030280400c004c1a151030380070000c04075001d0304904115000302d0f180c0300051700d0000320303207054074030340d0a0208030b50450344012510b0b40070b41c07a00170354091104000e22060104031840c041c06020740c440b01c0c0403292020f4010300203a225501ca09032201481500d1100494024202c0503c0410010191069580d4980ca0240f400505411503c00c2c01c02c07109078540c543c3d2505e43c440081030310a0904604501d010000600094014400a4080d542800b01c0d0117081c1e841c80800800340002c01400c0f034603810b00c0040c01d030050000c4079240206600c0c01c130303190200000c0000c101350b0105481e6400d007080c41201070200c0b007080d0050011201840140b0200c20281414030040d442502050440210011a4202 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 365269163 1250 365267913 365267923
    0x20c010608060916030b15030102070f060c081005010f0215100509070f170603100609061415030406020901021509240601020a02040b010c0f200604080c0405040303061d0702 76
    0x2000410340c0300050326002d5021111040041702d800c0349496509507124074540b40190920b8440c0303130b03165100240321401c00c0030742000000c1003401207034100200c1c1100e003015229441e0075a00080021260141001290311a0140a070141054815506001498002d007400b0704000e4a888808071011401804582483c0070055030041852804003007401142c070010b080c0d04140c90298842e4800d610018460391030800442000a244a4040200c41d5403220001c008251b90b014015160f107004d9204291032410300c20321444424954503041c910f484079940c0000070351040c40840d042d8007484403950100e4658120300e62080031030368043c160a81c12202e02100c400e80103a07140c40d80404503818000143d07400a01091001c1e815140002c012500a0041e01c0c41d4901d0300e4001c1006204607210010400c800301030710f0848100345c402c028540c03040030400280c0e00840c025902254800d8044c80140d14281c0c0015802c58000e050000d5015201c43d0700c0d5503081800c103120004181c8101c1070041490b41046 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 365270413 1250 365269163 365269171
    0x60314060403081b040909140a060e0d05130b1303050609030405031002031e06150c01091202190b0c0405150703020606010e030d08100b1b060106091202041806020c01060806 76
    0x25108034841c041c480ba0304c0140542d009044a255a40043c18108510710030080a080c80d404120340b42e982c25880c1101c042c00c900400503c81e809070076110708040f070107071064403800e034013084100001720f00b4040c004000b9000107011b00c07042d50043c0000004200e0a20142d0300442c03202c001703190740c5d508000c00e16282c0a804045040c03141c1c410400c128a02180343d12034140004944d41e195625102e000001d4140c0010400c02c1040d84000211040e10080562080050f44d00c69201d0040141712040e05a846024445003034000464810440c0d00144401001d00d901403145070082c1d04040d2030303030003140c0d01c90b030b00085180209800003007207024960100144c903071150342444c0689a010300c1c40080380d114010800f1440078041100c012410804000107194050000a80769545440040d90101c2c01802c455200a01078001c58002240c0749210f1a400020b90344040482c2011192a609000c004e26035407850f501d00c0c02e68115007100140d0180020001140704ca000403900a04012845051201c003030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 365271663 1250 365270413 365270431
    0x80105011215091b06180b21100e040614090c010203040911040e040c03020109081c2601060917030304020d02090915040506070906030903120b0406031406040308 71
    0x210100c40010741c034011000210042c1840480c9040c081c0c07400302c000d41c407804a000b02003001c410000c00c11550015504501c4040e1905840c0e0982d960040c7d12518459140000c025080c0c0e0745064864101c00d510b0b085d00134a80d02460450703660f0741c9010511402c020b45084921603201d605070340294220385a880e030041e07108000741c00314564200020b540d034803403072140039001c0361503540c09180c900000080e40e000b4190100040b03007515041c50311040034003140c00120702240c4584c0300440d0039031700011001c0249000e541004d8185000381c00075541706680100f2034402c103540c55140010a581411158001c15003a1100784c4c07600d007042110440100a00daa028459205004020169440c07505143e251a0141c0c0e11400765100c000032a4103040308180b54040c0403825074280301c20400700160a41c41405107070b6880106a84840e011070903641280c101400007550314564062a83d440d0f4400c40803054024000581155690ba540003071202e074800c200e541c2d4011100704170a141e0401c00d203541c885034074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 365272913 1250 365271663 365271689
    0xc06160e0d020f0415090903110703120509061c05040c0b0c0a170c0d0509010e150901080a06180f0b18040627050a03020c030606060d0203090c040204030c08010501 72
    0x1100480c0e1116115070010784160f11142280483da11160300401c2400840a8986007054940d40c189004d080003007022400245009030700d906000000c1440410341c1da011002c00c0b46c40c01980c4c000c5440d41c003e890a03641c081001c000b60907040706004d9009010441214000c0341314601810f00091001c4a076100d210b03410020400d80041c13080103c2e0032080c07146c2c81408200d003010341b00c4c942c0b40c0302c3c01340b100e091403d841803c20880c00d05070081c0c0a0031fa014826a61485001c0c489004c0c0f0000001d9100d040e042000103202511203036000314566988010b00d0200098a50f580e854109411148103244503c0b440e95500501c0110744640031f16074a24600b629101500112001c2c140034401d40180080d180950300c4c0340b014004145103c400040001d09400c020282604d0304009444664450088000d4800d40215010034100030843c680310308001403002d1300b48507201d142c09000c2d500c000e0441100c0c0c055500f0441d010f94552001c0e00265008a100310b4a541c1031200e6642180d4044e00400401505 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 365274163 1250 365272913 365272937
    0x402090a1104091a040c350612010f180201090e010b0417070e010b0c0c0102010b1003090f02060c0a0b01080a20061201170c1f140f0c0616 61
    0x600c00488084640d03030f90000450180c1116602030604a140810b03521908182c6521b4941d9030190038030b03504001142560080125500c118010900259150030541c0d500c000010418a00428004180c00158001046448001040c0012100c40302d500350305005030085208207551b404103800002e000d02024a20352541004031201c82801a03100b1070480c03214102d0035a0320302d00148180c100030507800e100f112042d6113901c0e40ba116a00700e8125040b55102d4a41c0320400c6610500074906030b1880945405a0b10314055012000341c81460030548807070040020712070042e00c403d4020950402c21a0213002402c005181c6042564810b9100743d2050388840720180c08142049041068142d140e440c040c0e4080101c004501c040c01090000c0c0c13200000c2c00000603a0340c6d020b6044403640800740d404c1d1740d00805014200728814220000a50f20b15140044d80f00c10302d03018414034894900d20340d800500b4400c0f500000b000e50750201c450ba41054100009120941058156020304142141411544401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 365275413 1250 365274163 365274191
    0xd02010501120f0302070306020a02031e03070c0320060901020d14091c030e010515010311071104020a050702061c060f0302061215030d1d0a0b12060112090b0402090a 73
    0x140c01e150240211203c0d071001c204260080128a0085038080c9080d500c803036900030041d441c1d0700502181e402e1840761403000030a51400790101d0b0b01c43c180d507844511000300307180c0b0100c46101c40700c0c0d0122000d070034113044c50311404003c015551042030b9050025039203400015605054641041d20a80a100c044003844602e442c0819401c070a041400600c0d040e04413141412009455000f100695651800084c0030781d450780440500544102a01c0c00c1c00420340449640810307218051026107091003441150340e441c40c2c0354004003031202191800c90b040483c43c1e000a00317640c0c441c600062100d0481d08a220482c1d000d401003030010940d07100d4400802d840c40e00031460b0f510a5040040d41d1f0450000007038130286c6c2d056850305503a00050216150306055a401820700019030b990380f1059844401005c1d200d10340315148100740d40c080e00700079003802e50791b04803845a224007418041c1402800090340003080308600c01c100020b4000c00203404e007400c10380140801884081d04e495245810306600b04a244 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 365276663 1250 365275413 365275439
    0x70c1716090203190504080a080106110706120e030f03190c08040803060d1b1d0408040b0a020a2f15041403210408190203060c09040f06170d02010501 66
    0x740002405039803955241840031341d04580f400c562001d0780ca020188000d02c40108050040042c10741c40b0142c0c03990700e8900980d00b00702015401a001e80c0806001c0c090a8842c5584c2c00807018200340c0456181d400322042c9086401036501d03240a0a07001c801c014104001e05000e101541c8901c07010410103180500c024082d54000b48080c10480e00040401e0494554500f600720440e00061212615210034201e0782401d240c61061950350100c8000021406103052012070107103510180c0d50385410300c0c145a540658001c0301888065028404420002c036001000340c1880701240c4142550408640c00c1c544015a805550903000c1c1200d040d1040d4000b00250413a820f451040788155801070700d400000c1d150429046100441c4a18451a04015840003002e44141c50146007520b0000b05243d02c81d2074000710010300658194002408030700306580c46030040c074035506d0240c804500a0403003480381c02515001c0e40b2a03801d14000a072a000041003c0c007510034001581c0c0b0080c005540b610001010b14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 365277913 1250 365276663 365276669
    0x31002071208041109010b0a09080c0d0611040b0a030606080a0506091b0f120609070206160e040b100c03020c0111030f09010201090b040605100b0a020d080c040b070c1716 75
    0x3114000020038180505484d0b04900c10b4401464102190703199580d00100d41c0000c0700341c0002c6200c903500440c04050104010b03450b4040980b079040c06410359221140600090310902083d042d003000041754120030180200340701d11582d02c0110b0950f20f048002441d0b0380c0000c0101c9076991504003402081d5581842441d0408440c0711103110015000c9108140da12510f80c4a4083c0c140c00120b80481c2d07004c09001a20449048400e010300b0303560030405a807111411111036140d5402c8440d0205c0042c086d110b030009040c8064000a020080305000c03030a0688808071000c00f0039224803084040550401015001200078a840400880c070020038a41c0ca0040041c0030540c12801f046a50469100754003c0c0701041d04a56500007505240c102140281710a4a10703020003009007002159000c40803041355030b90051640104130140c503080b800c40364201c010701021040d00040200040c092054000342440f0b50041c61408200c078540076000312a0325001c85150900d0308403406c1d400585e44a0301d520412 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 365279163 1250 365277913 365277917
    0x21070b0408030d0b01112a0f0105030a09060902061b1002090609061e12070801061403010608190f020a08100308030c1c020301060c0311012f07050601140310020712 72
    0x31399454100180ca002003640e8121503039118507058280d400e0f0b1800c2d05a001258440c1c20158101d2951050101c1c462152003013a003c50001c1000c501c03988042d0307000c03508050003100005400202a4002001a03004a4041c804140308401045c0040c0d8140320000c200c0320b000000714504150751021038031900600071041d10800d008038118031801000314829199186900030103947e0f500301c01079000c50f040706403030160026260000200301d0b0ad000d000c101c21105150400700d4110fa11301a8104c07444c4000910b4014030386d0b00c0d0309921071041400e0040c07000d0075851020250b02c44d28401c0005000a00041c07a010840604c00410800b0540680480f40c11000300001c01c1c2da54504000c030119030354103020b0113032076151000000003069548804440e6125120750b80712603030000f01e465805e090300c0c0810800180402d80760140500224003c807032150721200d25900505002864480e907081000c242d00500c031841c403040c014449071600303000316410200280001c50a0000b1515106800c1c160040310703c3c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 365280413 1250 365279163 365279171
    0x6190903030605030102040306061701020a0903111f110c09010323030c0706020c0103060b1c0507030f1505010824060702060c010504061a06071509020f21070b0408030d 74
    0xc0c18840c0d00b0080142ca00030700250341d6941d40c3d14088005060070b21500000403400042c1034100e04043c0211107600c19a079031120066401d607102c801003034545039074181d07100c407190040717a850074017040d1040803101c020380700c6080a80c1a49030841c01c1c00f88140c00d00b486040b02c040103000080c2c00c0080c10300e01c1e0b502c1740140120b4500041c4900d2840c880c60700b158540d44105840012455030000340c446c0c40001c00c1e64144500f43d6550368000f064001e086101c260b01e0740c031141c44004455158080d541c8890103280129201e500020300c0001c407020300548510406540380c0c14007440d41c010201d140c100021003000d0f4440081c40403400016003550342400d2042c04001501400d40d0f0b1500246c0c0c0c000b84845008000e9401c1601d00340004082d5510711814420360109041c010b85000029a41980c3e00400d2031410015a05201e40041c034550808076401404807042910507254045003094259031544544680034504044a03c0c10301141c1c0f10710000340302040184040500482075a0030b6001c5600086 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 365281663 1250 365280413 365280431
    0x10207031707060b0604120507060903020607030f02010209040e01090b15010c140705280b0a09030b1e09060103060b0a030c0308030703090818150f0307050310050627030619 76
    0xa015041c00f6103159404800443e0100364982c04800c984d01ca180300d0411910700d992b4409040e20900c69921001e50301480038403140010a02070f81040100d6103c0348001841c1403070440000301200c4020800016030384d52035040504000700e920000c3d8101401a80607108100c0300000244009110040100221040d42081c550072b03400b000540041c160080c41003581e031a8441c02e1041e448034280c80d01c41d031003040d03004c00140344492b00100e520614696507030888045c10b5441e0242d0340f0300058451300c0c104441d50002c104c0c0d07903501200da50151100c400944403035455070900703000390b407000c030b8486201d000040c20820014018000c0441103da1010000c4e40340e56461406400034103404102403c440c030005404c14080a880c108141410700403030b40e03041450f20185004038039000e0b2000600000e8801c0001c501424010006142d0060f4802e451801680d118000314100d070704000c01450f000c5290540b61840c650940025691604003a03004201a18001d1040d0040d070307859001c0b49242c03542d11103001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 365282913 1250 365281663 365281673
    0xd1b0b060d0c0e07050723120f071707150e0c0f0103020c0a030206160305010e01050603040503040f0602070f09090507030312060302033307020c1e130614010207031707 74
    0xb0030b0080240b00d0b50b5a10502d0412000740035036120000c112440700c0004002100a02c1d050089070003122410f005009200381c1c0500e446240e4032151041c480c641c1d080c0050380014a000c4490300b400d0047c09001612884d4500e0191588100700043d80300032414509050b038591000148404040000ca8103d41000c0e08800107900911a0502103d01406043d25000c00e00d03400144181c042d00d41c0c15090200b00210300002c900300d550a0041803988010340d8010820b030f2070100043d64000e03002c3c10590707282a40d2240840500d000c42d81c00000560001c8508026104288d0140e50042195004c2803008526603650300ea20b5072030701e010007014404000030107040602142d000303002555000e011903844250160890270030240c03801801415076150383e901005804132113203490060f01c06070003c00b40c491090b02001546885040c3d406c4007100c04100c009411399825881072160301c08102c0c0003c41ca410943c180c01c0501c20300507954150f41c040081000058042d91040840084003140e03151600c1003032030b107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 365284163 1250 365282913 365282933
    0xd0c060605180405060a020a050702042301060e0120032d0703031a0f01020d0f0201020712030234060b0a150f020105010503061b1305030d020d1b0b060d 67
    0x2075034200b4500d0342241d2118038003902403070103a801401110340e50b50310f40d81c40c00c0c02d034031031303082c10200091342403040070014140b9401942c0302c1310401007000159196403035a0301c83c1000c240d03c01000100d4582a2885950f0019000482e04009503034883c066412070500c60395903c101e16031034500c1ca00300c2810610982005851011240c0c2403a142d03603507040310707050017009481581750802100010700b45151042c94980340411107044184c01804000140d4901030f2518085240c21300155502081300700c0010b10100c808020740300c2591001030b11a101d00300c036a645040141080402241c0c0000000c0341505000943e000c03071640450081a950003d40124241c1034040e80f012041040c48042401819080740c00c9000740240c1e039000b005180ea9807000c142c0c0e1801c1c152000e001300d80c41d00c40c3e030507043c0a005004200440b88911115039241d03035800844e02d4600300904141c0140c00040c6d000400541c0304140d001154142420904005400e07292401c00440c090201881103120780d00d03070802c004441d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 365285413 1250 365284163 365284169
    0x70306050307030b0115200f10091a07030b06120103150c050f07030c0605151201050624130e1807050303030a18060c050403060c052a0a050601031401060b04080d0c0606 74
    0x20300700f42070896441f0b0069940c4032007903c201c1c0398002c0c801280320303201d4075100740d180d01500500589900f0b84c24400f121503140004e09507504043d25401d04411a480e24801810302d1200c0c0c50800400c7e41c950b0500744651190311502d45040350803c60085459603100054541c11079210940503034030078551400b6030b030800184a005140c00d00f4042005840c00c01c5100c0d402004509079103603000e64001c501341d43e00300e480807500301c0d503c030445103440d40184d1801007248414102000300540f6000c2c06120011800c4c01a50010491900140030080b4507029414000c1d0302640400c02003001ca402c01d400240c881c0001000c6000c81c0b030390b85418003010690100030300419a00501c0c10041010140c80050030b039405400b056610034104a04012014412004c88001180c42e40d1300000e2113500420242c0407450070b205944044c86400d40301d01c081034080c8525070086108000c007420364001c9082c0682500c2c4981d1000c034640d4004e10082000007800704000d01000390034500300c12846114641080208001e0b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 365286663 1250 365285413 365285447
    0xf0207031703010630020702060702040e061605070309050f060403120c021008040803070c02060f0c0312010501091503110d09030e19210f050a0308070306050307030b0115 75
    0x101c04410208600c80218103a5503555201510800c0070742060341c85a807280c0c1e440050340f65000100c00407145035405042114402440720740341401580005d42542c1545141080341d0300003400340001004003068a0300003140c18280141090800e0b00c0140c41c042c0d0341e105450060319000e80c00031140d9076000440707001d1640134040203803507030baa004018122040000203d00400000c000c03111810701032858a0722880d0300c00645403541d602d45a0403144465074640881c1c20000600c0010340542c40c0794007030102d08005038001d507280d202c4000c880700842c1c5c06171702a40c1403015503c0184003404a81c0c0409210201070300700030403900740d40b51400b0f0381031090b220010f098500d03001d16030040640c81000390350204c0c41103404800c515400044544061040c1c4208108607208410130800d1510300005000303d50700030f90244540cc07040d41c03980d03410714005090490000d0341403030820290a8052066a001d020150018015141581c0c0e03a030088000601600718100c42c2424a2142140300c1c81c2520820728002d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 365287769 1106 365286663 365286683
    0x207030b0130060603020324010518220501090b07080906070f0e030709110405120607081503010b0a0b04060306050d0c060305040c030c08030a0906031404030f020703 73
    0x201004803951504c03180000b004d07980c240441142d0165030078480b0641400d11401c6021410142c01c1140b00d10501e942e00c007e21110701030b031150b011050075503103440300e0140c250000c1e20803001040204250300f08130070300382041255010300d80111081d41301e40c200f54030750b10100c0e0340381c40d42220b941d80000c10100e04000080c0c4219405420150050160b412403510740c90040f09942e2480d03403d4030301e81000603040125044c05100410001e02c140054040e500700200014801100035101c0f4141c01c0e0300000f00c1e9069503085d4490241500c00800884019549412048040d040342c4242d9010919180000070a802c0100107103d80a1340903107003c0e419810000c080d40204800b0707206a0741802200700100c00542e90405001c044c0868200664852a14440003840c040c000d4020304100340c101a0010400b50187ca031141c0c101d54141001038819201c917404a19007401da52014000c0e403a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 365107913 365287769 := by
  have h0 := BRFrame.cov_init 365107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 365107913 ≤ n) (h2 : n < 365287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
