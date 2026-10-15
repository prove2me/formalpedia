-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:50:33.765278+00:00
-- url     : https://prove2.me/submissions/62021ef7-ff94-4cfc-b551-0d2759338c23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 922302158 ≤ n < 922482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 922303408 1250 922302158 922302163
    0x1181a040602190e0a1215091e0804030b09060106050304030e13110306010809011808071e03171506030705090415080a0c1401022e060b09030d081909020a0b03040501020309 76
    0x540c00700380f003528050b6207040055141c40c3e11084111107a11f001443c05001e00b00404c0220302d2200404014080e900d00c6000c110111016006980c01100100d056684552720107664040a010341c4010500c1071000400192180086450248004c0c0c036030001503402d03070306000c00da0b5411201d1955542d000b10030002c480d688140300c1d6902243c07101c028420080305a440d514010324000000c0d045100001d120824010401c110010003446ca114560094405082c004c00d0003c0c21250113510610000214465001686e8070700c13440300009194501e0b548600d40c083c1ca03039a01c0f50f40e015410035194000c04600c0c1c80204c80e1100208051000303403690000a00e0400302056160300005906030441281c0701150742d001410010b4800021103140446022003410410704418054014642c3c0c00c00c0008507035959240d000d881400e8058003111181041c44c00d00380c1d00d1850445904145078001011042c055046400601b4000e0016004042554483c00d2030581680100e42c03d40f000c4e0340000504c40c100204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 922304658 1250 922303408 922303429
    0x21010c090e181e0109050d0c0b13061506120b0108090a0b180f1b04020a08060f0d06151502060714030c0f07030905010201181a040602190e 61
    0x68509161030034281180c0340303600c08001e4285000c81044034605800c0160400032120b22a0034203036290a82e031110b41c1000d02902c0216021102da0281c51003d050036809140d0210407903a21201f07401c03503a502d07481604641000c0303080c1a074a0a80300c40780d8541140d0914801030142c1190703900c0c4080c10729801c03078070020b603601442203d0420110320304106070b0309400300e00945201ea000c1c1603c41a61101c1580204000040c0c402410500450150001d0040c0c0043d03e00c3c5403001c0354803c9004442008100822801406613010200d0686000680c0d181752001c0c01e400116001424007e986c507040d21240b089400f031828080c91103004410a00c03885005144600150526100501c0c2a02d46203c00806800c0090880f401e03c850110100d900d2071b80c40c10940c7e21021004100702d4541ca01070500070040409072040301d0140d4689000b005607040d00e5008070b50340350f41120007400b403004200741441d42d02400400a5808640c00d000c84c422203403004814500d100303569924a5800388150b420420200310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 922305908 1250 922304658 922304681
    0x4091104050c090307140f090f01050916021e01110d02091305010503030d1812021b030106060f120f090b0f0601032315300d0c17092101 60
    0x74240f11480c107943e000611181a00c0c00c820140420010b0300010075403101c00c1d1500715a000c0602d10400c035900e0004070030301b8120b50003200c48a0440c0c039200c800c59043d010100103600141c0201031448031080b011542c0903940c40260700001442c01d554002c1d012150001c3d031b0f03295080d980004040c0c2151508400c2c12000042a14040006514003c0042e43d01c2c401c2041c1d1040c160b0710f8a06c0002c2001d0361800c91501c59411001d58003071a40c01c003038025112180503001a10125000c0304003009400e0500c961070030b4a0300d03030f1140d50f904040814251126036a10160441aa407240324990344605540a4241c003140309001407449418072090341010340d0f03c02002c1504040c6000ba4280d16030620001a5580c0c00806c01413078180e4584508841e0280c10314480c40e500305030312401c00f028010001e0300c125000740e4a01c108550440c0580c20389901c40c0320300e03c51000000c003868045008100b0400403240205031480c11546091610401707c0c4d55883c407480740c0b000c1c051120f2086407010308280a400031400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 922307158 1250 922305908 922305931
    0x111060105030618150403030b01022413080408010f0605030f060c030f0402010c0b0f060114040b0a08090a0c0b0304120c0b0f06010201020c03030a0c110a050c0f0f0409110405 77
    0x1030401d00401d070ba42d0001400403000348040040d034800301d402403140008020410280d4003c503e0705040c044c001e0009401020300500c51503820700c0307007455000c03100030a03504085000700c1a41c581520f00c9181140a22060f1201202048005041d1409118140307141c446d06a001c112a847d0401705418000c101e07100d682c0d030341c001c0001c124003141c0300c00449a20090346406519103440d1800103e4801200c02c40040030003a200c8244402550311841d224031a0b0350907a5075040c003a00680d048103860245100d1580401800e011046105000d02c00d0030b6840601c000803074090013000d41b114801404141e1210043c0a400010b00080c03100d0300b064448010134a06000c55041d8880d520044201402002c40c04250186004111285e100390126450021840110394480c1030891242c8010540d03070b08020041030b015a26010302e054007190303040707a864124000d44040d029540c144000c44401188507684a2407914405003135580328030a25049501503000000380441c40c500340801ca6101524184625 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 922308408 1250 922307158 922307161
    0x9061703070303110702032d070806160c050d030606020601091b0804031803110a05090906160c020d06140702010e120d0207350405011b021906030209011106 69
    0x4920000480340303215454540011000100f24420401c0e00a490f4000e501d80a141d61304100c14103010405032040c840204044c015848882045589902c030348540040c40c0c101c100001e022885442c81042210060b007440d003030904143c0d41b410708022542d6078043c0070954601007404925410400c850241201040400c040b0400315103100c01c1c021600e05410800c6800700c00601010702c2031039117013502103180d6500701200f80c0780e151000b50010385825160254510540002c0c0394034003190242d0244000d00c01404003074441c03211582071203a0140000060045072203540300142c564054100b01c1714020f110000d1400304880240c0188200904034404582c14200303030b00081c00010034811500d800c907041c102e55408845580002a001310070019202c0c580710f04090354080303c07088035403032105400c10707614100e82c140680c10030703050081c3c0c0155070014100c91981c4288009801c1c1c5840228002080c40680b80c22030000c403051352815803c5880025004913000705030f942c01c89c1c441103c1103c69000b81505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 922309658 1250 922308408 922308449
    0x6060f0e0f0d0212010b0a06020c0405150a050909030702060f1b071a0c160312090609030c1a09031b15041415040b04060e150a0f031505190906 63
    0x11601810300070f40304030036826091302d80c500251700c04518400c0c09407030042140d541c0c800107915a01d130199458065800e1500107001d94042e614800e00d042001032040200508000920119102c010701d064507e220810059003d80c0d1400041c1c50039100c1150025540c0c244050350340008034103146600440d0780304030000d20100e00d01403149c074007041c0d4422905464941c90510705182116602c070007005e400e0590004070900a800c440300c0c0780201d060b21954156540c0384004c8581205038032020b80b82d81030440091102498218141c10305a810400702e50400d20f4481c00030f41440300c00304446501998461a01d00c00341440302240c0f20320b1890315000d0341800e2a0588c518040d02e101d800840c41007291189081d85080c0b83c0301614040c12203400e03c1501c807a1a642c6c0030b84540449031445200d1040c50068206007240902269004801c680d91129858182c000540140c03a058245015080d507980c1c0104081e06c0301d803c5806091a82d0820030742591400030040f0848071507400041407288114503d040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 922310908 1250 922309658 922309669
    0x303040f03081f03060903110307050d03200c0109440c0a0317010b0403120f1229010504051809010609020409021b0c100e120106060f0e0f 61
    0x5016030107051420640d07884010b0143e8000900b0200b40107010510404028400f40354803241c0b07080c0c0b0a44400b1280c0e00c0f1071104a68a0280364802803003980005810001c1500c250071032800f041c4000e48424107800803d1040c0403641000c00041e6050f950380000409212004845010503188200c00c2c820345501350a82c11965080c984a40400c010120580c0c0390800c00d00d03048035010007109007640c004240c6494002d003409a11200c1d4216200d0140020441c1c02c207070400c81b07040b0b032752001d90040c0c003461400042d03a4401811000c5414080f08081501074004d160140740700072020144080342620b0386001094440600000003810407030244024481522804030009948030302010045aa60300e1000c114050300e11a00500549070000c5400110300595401030205040031000c03091658141c0b10034140e48804091955602816a102c1c503414540a0019078017440d002910401c50961406006401e44406a03c520300103503a1000010003240d01a103054601b003000c451040c001e000302000500f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 922312158 1250 922310908 922310933
    0x9020414061818070f0807120c1211070501140c070f050307120816031a060f040806010308070b1f0e060f030a11180609130314040b03041103030304 65
    0x41c0110320025225011800c001c14003290014000d00309400200d1500c500c2000820540c1c6050100e0700745501100c81d04c0c059040c0138424402696869944900d03520100c01601c5a10b0540c020b102d040e014102c5c4c03550b414014001d00300c4095802a582e0f0f81285041c0e82150400c2015201050814040c4800c440303080c1c045440c29600300c1c901c52031920050404034214480d1080080907460f1001c0c0001045070003600f19032069443c2c000703031040d413000058203034242c4618010980881e0041c6403012442c0c80c0c580041d142d42c011170201642410707150b2410514001c000e800545850202050030400c02c000c00307010b81da011040325002c0d002c1c04920101c81031420305602460100d0300e034080001d00d458645604070080900010220341e9154a1800c0c819032201840800a00942d0401c4203200100200020140240d40c00707800002660750f280c403c4640402501800c4040085903416001e42d085000050800f50402c0c031502a940d09041c541810103101412a6500980040c410800413440c690b6100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 922313408 1250 922312158 922312199
    0x40b0d0b0606040e010f140306161107122d0c0b0918180115061707140c0c100806090a0f1b0203071202070e160306050603090f0106090204 61
    0x10481620744034000340803030007150004d280400e0500f00000d428040100402c1c1140c880c0303822840c041488070141a2a400c0c01c8401e240c02c91072103a0b299111510802c0d42e0001c01003903009440903030352201c0c100003c00c013001a0548240b00b040300c40d401c0f600c800e40700100c3c1c1c0344030b92100019801200d6513618009a014400c641c0386170000f0610382040e0320390468810341c10f420300c4400d0101e0720700040c01c007901804540c42c1450030b602c2c103082c12510100a03200c0b8010b42e0016200c11032a0541107000d40d01c52640208200300704805d01829079208000c60b00a4041c6032590700207401c4000000d414840d4840c039255807501004119811f0145503240e5150107600400e1102000c121010b070303401c0305030141c0b4104208401b0001a00490883c1310380c08000740042510a8010a460080c0b0712822079598101e40941c0182d820395002141003408924211100e0b605181404a2090b40d0781c030000390b81d0b402c119001e0000d9000001d01c03a80550f001c1c0304110180034049002c505060600800c03801c00354031010310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 922314658 1250 922313408 922313423
    0x11119140a0b1501021207060e0c1504050402031e0123060703120222060504030c0902040e0606160606142727060a140702010504021003022104030302031005040b0d 72
    0x30f80341503442072154208449418810715900c0a2074900a801031005065038485405020806030307852410b201c51419480c88042d000c0e0515080ca81000001d41c4090458044800e04540090f10748452003034190082154030030074600c245280362126200301c1c25100031849864104080c60009420503080b0311200004500161107074100301622a1b0800070000c042d1400000f41d0700003c0c5668000020400e0360700c242140b40c1504e540326140402d074029800303045a0791069800188590410202404075200e540d4810410345603151120411200b25801c80c0e030380b102c0d05e0751001c2c2850801d00b4910011002050112f4003140280103a0b020030703000901170f440d14500c88080350003010040c11007150305c0c0c55800d05070741c0c4078100740541d48020b051008141c0e10702207a820000c1c007114018450148500d4010348006500c24407071004800950000000180e005900c0710075a0100a0303800c0c1c00d51241c2c0c40cd89006030389060000030700f849208168081442103080101007010b9031241140b440b00b10342d02800b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 922315908 1250 922314658 922314691
    0x30203042105010504051f09051002070312060f150203191202040305070f03030e0901030803150a030602030a0507080a150315380f0d11011119140a0b 66
    0x645003024480760700050600d40c01c02c028082403100210711607141c40c0a11a4041001d00001e81d4001510408400a0000d03084100d1003082e84096030000e021441c800d18000d4141e540d60712400d41100d9454020048114a4040030303c40c0c1c000c4411340c244210398a00046040043c0c01104011408812581d0020808510680800e080d00382d01601d016503802025030b20a43d440300c0f503000003041d40d8401a000500c5400c2c40d000ca40c1030012910741607a401c0071710280303150b43c1c9120040b40c0c22240c414080c1c000c0640c240010204246102442c01941440408525070801c4480242140d81c050b0030319141625106039041110f49170481d0b1002c40340d0200200c1e0044005c444440001c1c401007111204210262461210010f4209a052a800580311089405105140601c2003007003002180c1a0010152203181c004603002d0017100224103414074101c107201403402a41070a01c815450410500b640c0c03c0803040811141000300d00041c6050002000c7e8400b0316141e190f42414083c00c0301e00329480462 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 922317158 1250 922315908 922315949
    0x9050a021e060a0305040c0b040e28020c03070c090c0905130204090c02070e0a020a080a0b030a0c0609240e060a03090519050d03062d0e090f0d0c03020304 68
    0x1d040d9000440003403001da154650200e020707001e000100c07021608450002e401140c0e14080d10140c400713550b01c240c2d00740c0117903544076032681104d101200c40c0607210750050542051111f86000a0804000303403409540c80e01c4a514103500001200e4100071003890404c4110401d56612180c403000b140c070101c80480888243c0103400d0028030403a00210101c5081400e5104480e0300064000115403404420403000d50f61064548102d0007104290400100f401c07011036440749403504000031149009080d13442e10b096aa540304074200e4590302510110350b5644040120b01604412000d840140c4003014802103000003006016038079403502c00d07200b0000032400ca50041e1080c0e100d101c295500800f21f0715000440803500c0007a98145100b02c03601d03c1080100342c0d805103c2d001d0842264210138210348d10149142c1c1d5024001c0441900c45c4950034440e000040344102d00c00b065014100300406842e8110300905840d0400303203013118540611003944d400c0c2c800260b0000484046520260003484d2411414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 922318408 1250 922317158 922317199
    0x10e100f090c032418021011060f090d080405030412140109060912020a150f0e100b04062115020c0307061a01112104050a06020f010f09050a02 63
    0x880d005420014800000310410140c0d4000d451461460044d13a4440b11303a14031580150b840040700c4820540034645980010305207150400c2d07810b0f4081c200340103111800c1c0b50451030440211018035408410740c0c01c3c40f1100500303015402c040e202c0e5140c403014034509a21355513541d01c22071040d0119849501030791414024202ca00d802c28400d45e030021302c550041d0f828840d000e00081c102c159002450110300220b076030700004d282141c2d07540c8000000d40045040c02c071b520041405070802c11140761620440c03207124400b400f4842495000500018814140c54280403c0300e1190300030314001d06400303569a80d540036007070081103006d6200d4000c0c0c2255200c0a00302c4064000c00f8002c0311b00b80302c081909401c0184640111112003400040401d040317400000445400d1800100000d140e00b28803d42c070024130341810382d00c100d80500d400e00c40c9000ea0b1032000ca0400d42c100d41c070040c010317000743c0304a03010000217000c0c005101c11502d806000c482d0381500e6040d140d0030354000c003c6c4030324528501000e102648 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 922319658 1250 922318408 922318421
    0x120c0302060705030a030b09191d0d1101061a0313020102120d0914031c0b03011512031202190e0a05060c0a061d0601051504050a0906050f0102010e100f 67
    0x74056030340380c40341498000e56a4000c922140b020034204041e02119052011301244100c15a24201382c8405c0c084606400904240c0c0051118000040e15100a407104002c005e000016a070783e5550140d130f9951500f400c41d141d9400c907003840c2c469094010845580d80040e0385d008008100082803003005440140e251411021070b0201d620b4010510b0b4145055680c0401e030a140540e4040308501008104640c43c0e00c140c01030400d0321007203480ca490300201c0551202001c60405800013440905600c030480300707581d5561101d0003060402d0030400402d03610580c0c1d0f104040c2c18403000d509200c824070050030000100031405003041101d80150805542e1540188014a009802965101d00520742c1544801c00d030b030800d560490402c081303a40760986403002c0340d205011000181480742d08200c200280d107181700da52070580781e50074070020801d0354414072200700504a1000000c0d4251a04041c440008290f04855055916100018120311004070700761495004c201d90000703a580002a205009003407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 922320908 1250 922319658 922319663
    0xe070515071209091a0a0b0c010b0402030103050607021b0d0303020325091707030803040b0c040e0c180105160b07020f030c0c010801170307030804032d1b080301120c03 74
    0x1103040041c1c418540200f10b800a4540c1e5040910001108503018090408660419030700103d40741010000740885c44003420701a00c5a800200b061040580098141e030801c2c1c0040d103064005030b052000395034040015080c0440d80381142c1250090480003d1041510550054280340d0004000307041d0401c01c404a40140414140f140f6070f403070b507070705006101c0c040b00e001d2190702c400000100301e410340d0005181811207610000c840e10b1541c0c2d40d5910a1030040290400417146014800858440741e1200c62038400d901d002165034680b039580c180d0311014032041000c3c40c184082081215400c4003994143d030352080d0420300c00c94041d120b0748400c914001b2080c000c0000b41c00b010400a41888000c81e000340d002c14240d80e28105a601d82c500020301c2890044851151380c410015480060700034006542d0150103414100090089103102d0f03480942c10b10019001038490000d00350303286070041c0d03003804800c0c042240464503170050f039110600c6110600504442203002c2c1c4e800000c00c030f02c001c1124095507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 922322158 1250 922320908 922320923
    0x111010c020a03020706021603112d100302070206090f010e0a0603150504050108150c041d07081513052703040602010f09110402031906080705030609010e07051507 72
    0x4900020080d15001402c0c0c0403801809603540000322244001000000c408a240301c4407045072445d035071002c40c4540421415003000050a00d801c68004099802c802c110984101e40703c5204004200036040b185a5161402c1c184140511800340e04c400c0185c0c0c032110000d9407108500b08003e40182d8070710341c2c00707400c85030300040300c40000c41d0a80c1c0c507802c0608440c14a05010980940310010041511824098441c050740f055a40b50300d0080300c110f8107a04040740c50092450300d0389802c0e0b8014540c032154803180710102005c05004410b0f43c06004140d201c0c250000e03c0c060b0080000000d4648564808000395490315039020072188100720100841a00741440891003100f415013880b916900130740300d4070015510700080403004420a0050641c001d50140305540015034805c20040250001760144070024913044206100c900c06214210103029420b0080a401d0301e401c003018a0003100800e00706440c6d04118a202c4081d20020f035a4040c0c1e401100c03a5038010b520b46a9403e1303e805410302c05080035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 922323408 1250 922322158 922322171
    0xf050c1203011701050618040b07051603090302180f01120816050c090f07021018051204210507050f060d061508090f1506030c12240f07030506011101 66
    0x40c8144510310003e404104001c0c030095035003404000c3c0d0002c09502d0340f50300100c07400000c1c1c005181c1d6078000e03a010743d460515a007400044602c1071052942e40e10100c01042d05a5018019454400f006101088400c005a449441c0100300450000e0061065002c64026000200200b00c415010740f00401c0f9400d82ca04501c40135800c20907515800c40b40090b0240da00e00c008070f0582e01008801502c1400a0740090040d2006880900001c083d82c05d036121a40d8503172914000041d0050155410741000403000c2501c617800e120020601041744000e0340d042030f1f0140000c1001542c041031004c100c0308200c4030768a803d000e0300c0202d400c0c2d100d8031404a44480c64950089070900d90f003d03294044a0031039441d00b0b01e0b6510000110390b22545140751801542c000c4039030303200c2c6201400034294003540c042c0560b0b8090748040c01040c3c0e981000c0e14041080d1300f08004c904031a01d8071410701c0c52070b40d0450103424105e040c202c80301440c8503006041c0c20b04064440380007450070390041c034807070403030054043c000c00c100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 922324658 1250 922323408 922323419
    0x1701020c031321050a110a05030604030c050105060604080a0b040f020a1707090e0309120f0d030621020109030f062d050a05064c0f050a0f050c120301 66
    0x2400c2d007070044501c0c1440440a01c00d4601d00c14221000d419070080003059020b82e283c4507100d81107085c2040950140d0001c0c0c0200310794806200d00340c012440b948944251a241e8504942501ca0081529008a005000030021860b000480041060f0422005049910703141801c0701c41d107241900294204961880008418200010884541c22a502621038150315190020141c98079405400443d034010300c604034440c501030f2070300908a8601411249440c422039a40350034081000c42000c086556142c0402120100c980a50039891a00b0304926000303e0950002c0c01c02ca550b4000980902004c1070039004001e0154441242614007a84003440d000300c202c8009160f0310501c0300c41c3d410a05000200f61845d0240c0600c0340100d5000301030703540351034821200044108035802102c0300640e00b1030b0303107190150b14140803164080291607003a803201c00b00207010f881c40101c0c0300c03e038082040421074150001da0064041c81689220b00d00dc550301d4101d4400c0300e1070020607001c489070031038002000145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 922325908 1250 922324658 922324687
    0x9040e070602060106080103080d1a040510030c0506030603120c01180b0106031a0609010507020f09072706020d080c1c05012c0609190507050405040e01151701020c03 73
    0x11034841d9802c50340705a0f00c5440841d444042848001c1200c0f85c24040b0102d05109a00599008400c460700c80741607051100004081c0c1e04c0c15940d45007003640e4203006205100d072214143c80542010f0340c040d0b203141030400110780e641100d03c1c2c0c485060140071a0f800c00000080d003180301c2141a9003480100602c807810801c002100a10901000c2441c0000200302904412160301342c0201c010007160501c80480010b55440e4802101280e00c200600c1e80c2031500d9446a101c24002c0110780e441c1d02d03030200d5803400d00482d10740101c00c14101c404808010806540e001881c985504828505803415444551261019000f0180440da20700300081091940105035801117040f108248108900302e5500040704141c042907071210342041d81841c0008506081c0f0340d80e0150044521109017044d16001885401215001e603103090000704000350402c201c1c0f505000b0f0400c8843c64100801c182551007048003164041442000480c0340107800c0d280b02e441c0b0a40c1501d07008444a800d49648500e4944c0189 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 922327158 1250 922325908 922325923
    0x21050301180b0a0b390a08130f0905040605010806090601030627030e03070b040b0d24080a050d1e14130b1e070201050f0904021b0318011b061109040e 66
    0x203d06598a6955a02c0080305d0684440c0c503c0d40e0050a0248581c0c0c40c2d0545a912020b031850581d944c01000040d44444c03440c80c00000e00e102040010300d0b0a00e49040001c5d154180e103c0300896110009000044d4004203100c0e046a50282c0300080301c00c42c07207540e15980f016840001c1c040c8248200c0c400d0526801203c030b0200b005048082e19a45510f51620039000e0241c0e00131880401024056500c038401075034070032402e4100ca90340341c0318807804203044081e0100958001c4001900031407008010072100300144c40359040c007800e2420101d4a0381800440206652041c0c03010085030f80c40221502c00940d046840c58003482590f40c00294030758409a020740c5c846040844483e481c004412001e02e85201070747c04165059680e107141105101d112207058102c101003a80c050f03402c2088081ca140c800c2207480d0f2001c1000e001c3d64560b9005445456074040c1601d601d418401d506224000c042c40b10250440d015a202400058240d540d260b213600d940190065550044c0c0351007081459110001241c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 922328408 1250 922327158 922327207
    0x20607080c040b040e090a1202030408010c0305010b0a031a04050a0606021e06071202120f1f0302031e01090c03050606120c0d0213020d060321050301180b0a0b 70
    0xc00541d26520318006140c4101d2040f980e658401340300c144440740c44c070002c1c15008403000d0100c8035000459191028240701554444003d60302c0040c080110000a000348081901c0c50f0800b00210f6150149155591103086092820980e80e448050030220080e21210700030900a0f200b04094601102d0010091a09025003c0540324115102c4400030040340390001d40c01c0c5680c00340c1171a031035902c070540f59029884031128025809000709014460a50b603000d04ca02440711007000241041da90002c200d002044025596030031040082c0b0160b1400182601c3e840c40caa4040514981401d09182c01017021840062840008010010500c000007800341d021323410890751800722400300c841040d5200704109006821148051503174000d4034040b00040900b03034070700c4000f5140603107200d506800c8404a4000302c812004404c9540b44001000205815185ca2402d065146504024203008030b9030f054252131919035140c0044860f07545800c45180001d003600400a52100d51003810350091561450f00c7c4c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 922329658 1250 922328408 922328417
    0xf080d05270609030a030e0a0b07030c030e01150308030a140c0a030c090e1506120711010f090803010509060613090f140402010c0303110408030c281502091f020607 72
    0x401e04540200342140212082c500031803511600000c10b401030404445040414041da100303d01c0440c1c0c509004600c241000c0e940020f5906400001030300700c0308a1401040c0c60f82c58081c1c1d1060741550922000306883e004002c040e207951b00c06108401070f041501c12200265505c0091180e20b00c0341c000502540704c00c54609110611600100300c484d44002d01ca0345ea10800d015001c40c4068811901a04c1501c00142510f40b50034003904030030354640f1041d500103000650b410800b081880007849545988a102031082c0007801c0d21b62100c400302e0006000e10b0f4407861200000c1042c698400c41100d10620040400e0403103d0340d941c403044000c0500e0500c3c02540b0b410a05c4418043c0d2180b50030f01e00c181e90584600f02000b0072600c0450041041e4100c01c5e0240074104804901000b080003c1c0c040803104000808008180b045588410b660100d03201440104800200700015031711134180d1007591160300d0050700c1c0e42101c2d00007844040544a40c2140c00d09100c3c80754031459010078003600c60307c415100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 922330908 1250 922329658 922329721
    0xf111917062503050a0b040e060601020d08090705060c0c120d1e090e15030f2a0616051204030309080f0d02030d090204060e0112120f0c0f080d05 64
    0x250105034191040019403110650b031003045505000380e1080b5008034078402c0c0041c1c00a2118085012910740785041c040c190310640401040790380c10081515190000d00c0c0010540c10031050880c1d6500190241e1403007904082010b1039045c00c20420f02c0403030f0f807006002140b24404155100c0c1c480003101c151000107064003e03e4108a1101440e40e203140e001ca903900c04040b8a45104090410740140003840c1050190f405041d595030304102d400500c16130900900010001004900fa2499421200c14548110001d80c3c8000e0b60b10710055038051908050040b5580c80107241003424101c10854040d00010b001c1404810300d0b074031205201c180d8001c0801c8504020307040c07070320b0381c4d441038080c03150001607000308400c05208500380c001205040c8041c0001c14021f8840e503a030356003a1400d810103082c411074502d0f00014080d17002c822100110450070070480400c10260003c5c0900120580501303c1020040b55204020000e02152420048004100020b050035800401c03c41c03104150500c1c000c0c4a0b18 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 922332158 1250 922330908 922330921
    0x3080408121806030411030f0c010e2706060705030c070302040b0d0f350c15010806060d151803030c09050a03120207030f06060e130f11191706 63
    0x40b03550030b004000c000c00802d40c40d1402c000c00c03644020b0080b921b101d1402c8035540325840401c106803281c5500702c0580300416025000500e0500e51507803a0b846801100055425a040e201200a0f2600c02078080702860782c0344404a151845a000024558032001540b803c105002081020550740f08540901500c01220200074084c41200c0d0060400442c8641180009401d0845044c1e442c0d24000e61a0200d84248800c2140303018291009040e400c1c002400070351024184101272140c00f4004000f10bca5043c0852555140c0c0020500c40c05110303041e494005200d20441003944903896500d05200c04c40100c41d100801840741c010841c0813a0500b044441e1450040c000e44050b12009040c070701200c1e10b1a1948110565603440040960103603860210118004c00c041a030240e0181c64007041c110f20b000400d0140b620300500c100b9100c03105001d94070000752540e4040d4141c13504421401a82104040000c240780381141c4a584030507602c050010b40c0180d491844090311010b582503c1241e030b101d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 922333408 1250 922332158 922332193
    0x114041a0130021f0810050a2409051507050105010e13030c0f020a0609080c0a27060b030a14092b050403020402211311010f02120403080408 62
    0x8400a107109030759008410303a8031140540424040340002e00680384003c0206071052180844c4010400198072038042020f0900b0541c9110002c0c007051b03494102c00c515040c40202c040c0f88070348011105903500c0d80c1741c0310624803461120020b010020008205484100d49143d1700343e000360002c40d03581d400d20000107402850313650494841c0781d81082c000c400038115501200d405e2201141100c80040d400440800b58885071184409040c16454464180e4240307012149064030030201c0d240302d800340103014002c5100302203c085500200d0180c050a02d1120400c2074041c00151f0441003c0f03402c044100700280107681c100110f808a1030b40200030036180d00300403c1e2140c01c0b1028056901e81c0d64008403524a036031841c0208071000914005003450786950000302070742c0c0b02101ca61400c2e0b0f015044480b421216184d4070340c1000440803200300c01d218650b5942e05d2034070000b04031410f01031640c1d08484401e0007484203000c42e0405803a213507500d645902c1d2164240e00940039100382c0c0d200e410944400105807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 922334658 1250 922333408 922333439
    0x40603021c050928061401080709060605090d2402190e180709150c1202010b0d08160b0c040306140f010e0c0c010c0815060f0d0903020114041a01 64
    0x1041c0501aa154889205020042c0c0c4001e40b60480b60000d0743c1d14017141303541c403400785104d0a01240800e954500f094507071410417650020320328a803521800b00102c94008048802c0c0e128283c400361881c11407401d1400c0074104000000307000d00d1070000c0342d598820300703507000f80803011241009404000b03d084040342d000d502c40c000c1e1900090100e0081145100024203680c0c414402d16207520039540300e1503800c54030b8880301c5100000c60034080400b0100245080c10900f001042c0c4002c20140d008100011980a1645005030a1a10005400010181102d26003545c07641080406c13000e420701e806051040d9000784000d440292602d110f00e034010140c8940b060090340c590203c001c00340d00f4010006000300d005810314103669000c00c0010f106400c203000e90320a001307580e150103401d80784c0114040081090011110b214070010803110922220032030030740302200c48100e40080e001d0a5032600b80d00400c40c1c0e45000007e031506000700020016403400c001d181e4030341c2072001030031a6a9460422442d984 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 922335908 1250 922334658 922334671
    0x906050a0605180408130b030103021806010c140c0a0605030a0615080c0313020a030b070f0801060f05030621240f150a150207230a052202040603021c05 67
    0x41c180301c403002e2080c0d0f40c84034540190243c0403e030301e03004821160b618600c650f544003103020034004c0010005c5d494480b010140701522541200341d00d2900c5000240703e2000321100501c80d1000e198030030000b6204001b9505400c50182c0300911540e2181030107089034204403144070b1818185000410b07420a240b2131218454010784806c4041e80b43c86101c01d0250300000d1421845555030b06942001d40c2d0b07582c0f007110013903010382030222450901900c010103aa8141502d80103210f410001044130f43e40c02030250070000c01d42d00e8601c0e266201c0b400002d00140c5044104601d076480000c0003586a038021407400c660401954024a10a9041400c00c0d4085411284d51361340d46a403600003100345908030011010b021006202c0d400e51500c4254201d080d0344900c8000740180d00081051001c000600491038103140320683c020141080c0100040341045a17028042c040c1d12540f070706039010358444c4a001f2501d540034a01f0b40d1101e0712444000c0007904420280d03030070311032201403a0b4680d031610703c2503134041c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 922337158 1250 922335908 922335919
    0x30203011802151e0712030507080408032403070803040806091b09060f03010509060601020c010504050607060b010516051501210b060d050703120e060f0418060801020304060906050a0605 82
    0x1009100390700041c2c205022a800c04036550820904d848034500c02809141e01c20410700b010344420301c50060840c0c0c0c004100390305110b0000d0074800032076170303800640ba0301a0300564646040c4507000d40e4441c540030404001170701403044141c041580301c000720240082d00c2d05036084800325a030b23102f81d0aa484108000d06400d401c10f544502d05542880c0720754592025010380080c1480c500300c0013003400c40c0e80031505607600d90410403d0042944c0d044c042c042106800340b03092400c0c2420314002a01070301c00e681005049558816110748542d001c3c40944482000d5011040d2407103160341441d903214030a107400700e64010341d00390000c6140150a080495160542c9001b0254804c259035403180c1c0e00400780c0320b1540803025a00703c00000701c0400c0f088018501c40c0000d000014541c420140c9020120900544103202c00c2c0600ca21110407103003540d0846070321003c80050641c05040b0000201855000401030b540000204000e00c96140c0008180e54401d44041169030b60b18041d01d001c484050040b1071303018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 922338408 1250 922337158 922337179
    0x91510170601031107150b0f0f01080a020c07030b0901090507090c0507241a120f0d2109080a0908010c0e06030a0b0603090a1401090b0606161b030203011802 69
    0x303511a0340710490380040f001001c5e180101a4468040520341d000581040d903840308208805824040700c0d2070b401c542c0907101003030804001e9001030100c1100070043c80880d503022980031581c0c2400c0010000464005a036202c050800b940024040d200031102034074244500c1500203a640054400c00c0d01100080da038450030003405a940507021640700c0080e40d90400f0242c8040d0991a5620440706e060701d03c2ca072a010000c42c100d00340100c6810310310003905a50030812004400410101c0c510300000c5852404040044a4944580e07041d42d2403202c2a42c00d42c503100390f040410030b90030300402409429842e8211034907601ea441c50b09950f0141c42401c0000d106095402c1c080c10180041d6400606104011540c440d40c100824000d8000721524641c99004100003001d1202c01081a03400c454000001d20a220054542c41e03200c80000c1c100a0284a000031100d8200104d80444000d540d40201d0700141d0003400d40d46508024014041a03100394079088000140c000c0c00e0303105a00c515806011441c06 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 922339658 1250 922338408 922338421
    0x1c05070204020d1e0c09080109020d14030c011107060e07030302120c0a020402210a09080702120f2a09191112070309290c0904020909151017 62
    0x650840e000105207141c03600aa40060b01040300b01e5030316114916800178085205000080150340c8030381c0324074400c1e45480800c001513211000814096a0000d50b40e942c420303900c0c0d019074914030410156907099440d100b030071000121840020220140910700c203021070f41c0040302d03854568211740300060150b0300911103030b80e80200b0b8030007034075040c14550291440b10a854001c00d090764040310006003540e00360401120b034020524100b03508800620010440c00683c3da403425040e01c20b15201a2041c0e0142460070403024080104496038220729040e2240341c2c0d6400300d402101e4459109900191001c15a264010304012510500c84d140400c203d801c50440d43c2084001070030307403500c44809039a042240303d14035003405100310b000315040c0d50001840c1096003001000d0320703210740c449690034040140f07240304400d90821a5400c421103200280d950030180300010020306c030386180c8507001010001004091080e18940d0580c4010a950f85084d402099030215401c00242c00304000301407221010444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 922340908 1250 922339658 922339661
    0x30b0a060608071e030b060310030c060f170a11120403030c0e060304020d020a050a0608153106150201060306110309060408030703140c090f0609030a060e0a0b01080f1c05070204 78
    0x44200e03032400c000a1b52030000300410b5150b0300c22150503000c503040b000100300f040640014a40201800d291013143c549045000030200207540d84070a40c200c0008000c6031171507245600540b03400d0144507415654a05200030b2416045045400360003180c80e060600103003d0294012583c00280101494030b0341e5126820017289042c150707801e03a0403014954011036180c941c0303481c0d40060300303454840031501d2409142c1c00f500582d1840c280f9014810100601e101018116500c101c551030000e480c1d40c0420711a00407100502d071070742c40003003110400044082000e40650041043d44e001d00b505000740c400140c0114014481a501240d07140d120600007400706010314007460f0007440d0f1b4540440c14030107540e55140501016a440303043c0207000240c200b020325010781f40c110800c4095030701c0c0f070601d40384900085e00e8030120076010b04010f807280030010349004140481c601c460307400b01c2c030301e90701e540c4488003595035015588000f44d25100c0c118181600304264149528610342540d2070b076203410490350a020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 922342158 1250 922340908 922340957
    0x5101404050a0603060212090d1809020313080a050909061207030b041b030c1e0e18010b0303070303061a0c030406052208061e0f0c0a09030606030b0a06060807 70
    0x701d0b0165106008000120280010240943d1600005000e810300321202800c2000203000c2000780181c2c003905024100d81e0700c078240101c031584400103072269101c44580c0c0ca11141c4a40003007803c400001c1c046c500035041f0014025000c8142c4811061b80d96034410300c51941424001403899901c4850208001610700c00003a40c0240714a2150045071501106a00e003103000da042110303040c030207220a200300c0b0041000e00c1d029010358501d9030300d07151070949600010034000e400c2202020540003000b8156600350499a102c1101070102c030390360001410020000c1a183c001d8203010410b038140d20b00d510745840c2c00d0314286000d01c0c026518051811400b502c01e136101c000c0748101400428103840c41d03841480c00e10001401114042c00383e620700b001e0300c1c5141100513400008005441c0c000c0c03102103031000040b0f9034006285401300c1d66a41c407403c410380301510f5650008003464105000842041450701c440382c05400302c030005200040e1111300c162143c0c074044400400080a021684c80c0300405a003041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 922343408 1250 922342158 922342171
    0x20c0402131e0b031e0703090b1501142712300a20160e0a3e1801080a020c031803160f1517190510140405 47
    0x304a440d41d946011403e94008803000018034100c02e020700f0426182e00703941903010381c09180402404100e5a00e1403000380740540b070700c6034888681c20403040b242d00641a5030481240081c2090300e9039240f088480c6215412034081105050100e11541c1d6810540343d038090303a11440e000b804c20b50386c0403181c100580b100c1c01e04c0d01c1d00311a000c0c0700d03043c441e010a070300500b180ca410f030f0b456405400184440517240940071030003100e15400381540f50140d1a24101074406d07180c11555500f015112190300d0f4000e40980c80403105103401d4404c1c01d900700c0443c10304035443c088007451182e0b00c61119105284c440d01034005401c0484d00010015081c6600c5941c04991041c0b01100050a024408866034515040300091600d9104100440e81161070200490b400584500010300d1380c882c240f0700322450746401486080342a02d070807a180192240103014040d14401903e00d130151614012440b8051140c03285800710b0000c1c0b8000214030304410f44000c4c03005a0348039010703400b22008a10b00740700080000810381c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 922344658 1250 922343408 922343459
    0x1d0303101a09040608010b0f011107051c02030102210105030312070c0309030b0c040609091109060d0f140106031407051e04150512070305010321021903030606020c040213 75
    0x240c240350f40c3d5104401c050402c420001450035051018440a40940c4008a06100d5031902e08141c1c00300c00200c2d0001c1c0c8500384ca43c182241c1010380390380504102028004d50650020484000701041e03121180700c1501400034150441e43d0312424551248030b140c1014240d4140c00c2c00003115a8051016203240620030b1900d0394590342c2d81c1d120282c001505403a0340700103640008081103903540c0f00617400003800589204104840c5025001205c074412b4061490203000042980c0c0c203902c0380d91784215114001504280090315030655112404030090058001103403030a01030041660340300c20070303500c64071060f2113951406400c03d841d1444002220120100c0c0e420030403000c50145814840a05200803030785610fa20b42640f0b450111022400030181d00405140c0b10040000c01d1070003000c22041c6003001d003004440c640f244c50480c00c001d2560414016910341e45010810503030305034403e40455100ea420342d281c030a0401d00b040709034881c0f1030b00a801c03003440c0c400c184030841c441e1444e10017401c820b192 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 922345908 1250 922344658 922344667
    0x4020111030c060a2012040618060218040c03141b0c150105010906080405030306091b22050109050609090901060e0403020106050103060e070c0f060b0d05011d0303101a 74
    0x81c428a8400121500180562100c0044440c000980e031120b17680c1d0181c451550500c10645005513040c08000c001070405902d604400c011503010113841008260805000d41d6100d030192140400c00c64100142c6000b11f00c2c000c40614898420320410030203441640724040305444101c0800c043c09161210007a81080811104a03010b6081000002000c41d84040d04080d41c902400036101001941c0841d040c805484100000580080102c991004086420341031035213a82e0303880740b0004c0482c1c0c42c0360984080000c01001422801c2030300041d442e000e0b207200100a490303000446000400b4440c0b5500444240306080c0b49207040c5198a40c27204203000000389859442c8801003c0101c00d64003540540d640d0041030000e942c0c14021035010b0041d51400c08000c0c28002c50041c401c0d00603031005008002e004c5c10603400c0115907042601604c80040140440401d03c0c01c1c520700900c0100b680383c96030018109605000b000101c01e60303124084a0b1090b88016141680300360803a12651241c44020382d0400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 922347158 1250 922345908 922345927
    0x30b1b0c0a060e0709020a05030c0a031b02011a0f03120318120408070b03060f01030b040e010f060e10140108090c0a060807030b09220302010603080d0b01081803030402011103 77
    0x800700d0303030082c020030010600c1c0701c01c2c800403428007440d0b402005c016801017240c1940550814102da0708001c800d804260b8a610038042240107000a94009002c02001184200070b95415044002c51041ea10383c45404a071032281003005246140e40036a8058105240b4850f20a4800015591041040c01c0e54184402e124000b54108000a114019541000324042c480c2e00c10800c0b585002d003044410316803840c22311200046400040e2582c0504044d29284a15100e455680003480c007107a05d10024000c031410311183d60081c101c5070050900829070100016804035440d55094100c4581c42c01c02c220550f110001194405802800c43c4024814a42c552405413175440e00ea00c01420240c0c1c8802040c104a00c0040c1903d40004140e40702c1d0460b00305001500c11b408505c2500c001e80358045249450141c0390687c090805035001518204000c114200c080c0c890790021141440240c3e00c80300c1941d43c0340c40c1c0e200807400c0c941c40002551b10a00000d0010b50081020709448030800080341e06044001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 922348408 1250 922347158 922347163
    0x6061804050703020a1b0f111206010807050f0316060507260a030f05060f090a0e010e030904140118020703030222150203040e042315040b0a020301030b1b0c 69
    0x50300c2e40000268001445903000794081c82501180c92903100303c01106038951200038249441e40c0e4050204100c182100d01c480d40c8901c10030440c0704558041d10019a544c1130b80c0e64803000c80e442481e010700003003030322a0340c6403074040b462005d1108560300180145080000c1110190400c082c100c030501c005c8407501c03000c4d010741c680105130810350024841e5190300305200241503a04500c1c1d40e9428604160510003e0b5950885601c40c501090f202480c05942d40450a0054031f130241c0c0748142c0d9403800b520010174020120040200f003409903070501400c80c0c0c03000c82c0c22001001344212540c65031982c40c140009035058000b4248640285005424a80c3d5549070b030546507040a49042a801125010080d804c4500c0c55407004466900155040901d000034402c221400100300070800045051181c00d81010803a000c8003042444003202d0041040c806000481d880c29a016140c60410390002000c0d911503000b228184c81d804203404010342c8600b5504a590020b164041407403200900c00390340040b204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 922349658 1250 922348408 922348411
    0x1a030a0b01030c05060a020a061113080f06090606060f090d0b070507060501080c0609090a0912020a1505010308120415020309011a06090f120c0409120201150e0606180405 75
    0x141604000e551552074424840c5040b640524015082404082d140ca500412424400781c1c1040001c0749404680c03800d80250f215403600490340510101c00401c0c1c81000040c00004032018400302d95a54850f00006c50740c8040494081d644041d0401050543c5800500036010001007d020f51020b01250380d07a289200700c0490380800064070101e040c1082c0042070140c03038010400800a0848400088082040e5120307408546015029034004604002c80b030307070321a921305030308040c945040f00c82c3c00c0002900c0c1d14803400c0035101034010403200c1c0f4a0b10880d2103170070f0480e580000b00602d00000301801500d0908010006d4440103101020301052142500007984584003c0d000000e1801030340d0901600c0c6281004501e01a03901446401059111550b00c201c0305503084031445071400201c8030f0300d03160441090300d00b0b81290404903402d0400c007a5403ca181c03000c40540003441710390b010069540030b56016100388a0320802c080302090590030140014021800003050200220058001190030703500c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 922350908 1250 922349658 922349663
    0x2070b0307080a0b1e0411091215070207080607081509251814060706090f1a04030c15060906030803010501091d011a0c06040606081c050d1a030a 64
    0x1400c000c00518241c44c0c42180000c94080700c84100c019000941c0c04d2034104000381880c022aa0b402c44c00841400e03c005a4801c160000c000e9981550600c10054403007080d10362001882800c1c102040b007a60002c5110403d4448500c0240403543e03a91404480130a0050316114400113042e141d2207003621a064198852248001c8110320840324070255803810250f2480c1078100110303080d000382c1160202c44040b00f180c010301c0110008000100004455200f080401441302d482d000c008001c01c145850103441503170107010a9055003003408070300791715420f046400400240401c04000000f4407000e58001803020710480019488e034840101c07000702d510a400607109440b001c00100b0003589c0c8020341c8405003e000c0700c0803008480f100040480d000c03043c0910b003500242d2052120041c8211001d0325a400501412241c0701d003880d0600c13a00604030350140544600a080d242801c080030b000040d01c400c100340c0c0d181407900514400040052520301c052460f5201c00210800199404000240d41d0030b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 922352158 1250 922350908 922350917
    0x1a0d170a0e10020c1f05090d020a0509071d0a120b0a110c0303090706090b16060b1806090105030303130311160b031906030b22021002010e0c09060f010f02070b0307 72
    0x3c408020012072200304082102904480c04205c210190b02005403220030800f90781e035210804039440003421b96000c0b60001a0081600c02c10482c1d240d0b8000a0407402c07048009140000c4dc1d02c2d0307030502c040081d1600400c02c20a081c40029800103003100d0190741d01c605e0311400094035206c11140710040782d10600304c0c0c4000764004014814908414030076100104480e0400d00401407030040000400e0040c001c210710800d400e09480ca040c03008070b8000c191003040c014400d02c00d0115409603e80c0100c010b9a1031405400900e0003c2010b04000003200d00903a89158084000768103aa811900b041c500003084c10180a1a1007402e0682c941c01150380181c0250808181c4038602811400c03020484c02c481d0b401000c0c01c0007400c00100b100312140320380180303030b40181c10003c030981603c104002036804002508015428401e041440d41075001400041020b03054849613021101040207600c401e07a9555401000001203a100d503008900400b516001d50058400980d030341c8106248940045900e4000708 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 922353408 1250 922352158 922352173
    0x11d060403110c0a03021c290a0b0913030203040801020a09080d08040816050c100c1407231f021b012303090a0b0429070801060e010504050402030108011a0d170a0e1002 74
    0x2a2130381000e00c2c9e8002c400c0201000710391041d40000304051005804c502080000700480c0382898030a0044034090501c43d4001d660b86c0c5c02c4640000c19440e42485101e0480c020300390340e052a03611502d801c034041d03500040d9440c107040c541d102c0d40400c0282c091080307e41d44900c550200c143e44038242034146c0704060381c030340d8032011a079801d0003022054a61302005a40d04003620070700011110207140d4490280c0c141c0c1d810004981c003408564610751070010040b0100c01003030102895540000d04145210200401060000c500401504c10705010444020700303030300c00c09080661043c40805141d000c42042d08440380080d0741c5e00c51f03213800c840c00e81d405d843e82080414189000c3d0750b120200c038491009030301042101d19207501c00902818041c002d103020082880383c9540241c0c8100306441c041d1000800855403943e550060350700800204c0f03504d0340c0c01201011244414585410032000d1640c010b00407201c40c03204c1100182d42c0c0d034046a014003e01134451500d000b603840e4642e07003042c008030640040616 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 922354658 1250 922353408 922353473
    0xa090e130506090304060c0b100803192003092701140f09160c0503040b0d06260a0602030a09080406050705100c1b05011d060403110c0a03021c 63
    0x104040102202c1031135104110820a85a000d902c0c41042c680050000d43c00b80c031244aa04808251075002e07480c648404102ea00300142310485034a40d01d00140c880c01000001c0c003411100742c02031812200303000d41003844100400e0030045062010480a0152000d41e2174401078082d031082d00c01c0e00400c07114000c620000d4003c0c01c103403170072028101080710b0f0505035291a0141c080342107800d6086208114010701c5980c10030504105540160007a0802992512444042e2a0081c2560700c01e0090400d2405010341c18070f605860300c0814030f0384450150031000c10139160362010713500150503200b140350fa60b110800801d0442019002810366076031100c2e44d03581c0ea41001071501c000911000b4140b86446828858107401c48120384c2c4174034144e40000444066800d04500424407d607400c00e5040c0d59444643c5100804500184554425180d10404000b12406240d80744074111042d038001452180c14809032030680e0403003200a600e5411220590034030b5039486040c145012260a55200000300301c0c09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 922355908 1250 922354658 922354663
    0x90507090b0a14060d06090518070e092505130f050709141c0b04060629030708091e0606040e030309030d020a0215090a0212011b050a090e1305 63
    0x14030351000c94001c0b0010381040350744181d10488400d0a071003880c00161280c00008942c01c204000d042c43e03401089079140141d01e441301070381c031940000c01d28004c0b84d00105000c0c510180c814000c2da043c6000b4401c500449607600c0191403c0c000c00c1008940c0900b000a00c0e581d801050211000142008141c0364029107081083d87c5c2c000c0c100f42e0030711140d40c80030300c180703000e40040c803010340300403035036545041486a0002801400c0c81d00182003550800100001c0c031040340c020404031609070395031b803511040f070550003850100780c00541080c1d03001c20808501d286200c0c080e2684c20079064415185900d2500e221481805c40c4007290700384640008041006030b04c2c0a102e2015a01010b001031031944c508400243d451388509020007a504d940131944440b442c2c0700300040400c0191500710201e03e0300b44039040c42d54420315420202c0c45031031982d100c0a8090010b0048108440c04407040c54500f0b84405170a0b2465000009610f0410403004400582c91214401490140116010340081da000d241000d50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 922357158 1250 922355908 922355921
    0x2803150e04050a02010305190f0501080f19020906060c01020a021f060f2610060503011b0e0112020d061e05060c0706030b0d080301080d0917120304060e0109050709 72
    0x284021542030420001c24004505008183d83c24030740041c540e91203805042e400c414113001001441c0c5008030f500d540c807080703521042c140e9408400720740206000f03d20705039a80700600c1600750041d1707680540400506110001c150405001020b440c10070400036242c50880c0c00540b908401a8000034940344041042c18000c004000d070b02e10b041c8005030134034100391401c078264880c2200380c01c0c2e10030000d1804582501404c40d0b10082c4000e8950401d603546a0501a15040c052039200b075203012028408400048020300c2010002d48a465070f034000c0000650750040d4030714030030204a400300207804601c4110704c00e010103841140100c04109880c40007400700d0024a820040c0284c0040056086001e400034051086480e24038000c81c40005403000f2a44200c0070a000400070704003c000441e02074800700f0400329065850381c822403110354520400000c488015400710050b040b002048913081c0303450b001107038441d00489020a96151038031030182118060707081518150003c40040c00b4004c21806070f070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 922358408 1250 922357158 922357169
    0xc12021206040e07230a030c060507050d09030b04020d1703100f0518010e0406020c01061823152704020a14010f0f021f05062407030302280315 63
    0x10101c290924000707085030558181075217203901c43e200c81316080d43d840382200d801860707014460f10101c0b65209009001900b007034404440e10700500240c0c0c0d0920707119090b00c5046980180c05400a41c5468082c04250301c2181400d0b00c003c4190228100340e882040300941c0602041084114180e150018509510401e80c00c41c80c03181352281030408044170748882d420b05444c610120061951224940240244640c2121250380d508000c0000364441c1c0403101c4800007014030000748841032018100c02c0b0341c619941607e0880c0741c00384000c2801018100f5503807035002e0019226444103000c04990340c11301d40c10826402841400c2030300300811401c100074198000d0031f031141841c010f01440030020744101015201074080054042c0c01000c528802c0240c41308059a8a2619032107002c15900c181c090101204d00c640114100700c0c1030000d0481e4201c641e8548008905914181441070f070f800c401a5020000090f100055182940303a4191107101c00350410a0a071000504000c84038042111005c840d8401d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 922359658 1250 922358408 922358413
    0x180409020a051507060f0506090612070603052e05100206040b01060c0c090507120e07030507051e0901080607030b0909030307080415020a020f060f01030f060c12021206040e 76
    0x2400180c40e09010001a1502210914240040d00e1500100382c062001c002e00014107000c04100c810b005584141e000f030b1415240c030380740c0c0c3d82c1d0390741400500c1820240c9110554801a01042042e00c0fa91006030031100b0502051000715200380a1046143c1103040c2c2c12405650910812580c80c10f070944000140940c0042c2016142584403200c400301c05228a100b808403850040081240300c441e02000f40c1680380c0100318a0078180d0008290a005600082e44a80f030b10081032640040043c0d00b0301140c0d03000c001005e00b14204021300c460b01044c01160041c00f4081c91a04100783e0300c0041c01806000e81d039005104914000b0340013000e903891012094058412031080c09060100802105d038801128100440f8a40316403624281c00c1003804140010140302090414442da800b0079070305020092003048070220b488034400d84418140c05c0c072008141c5120b60264034001250fa4204580c0440c047c00d06a603202c0101d1001e030107982c800c140c042c0031280030303004200e12850b1038400d504640941100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 922360908 1250 922359658 922359671
    0xf09050604090515011b03050a030f05011e0501050301080c04110c150411190302060304020a1e092910050702090a0506040e0c031216120c030f030c0e060a0c0b09031804 74
    0x305030b034012446c003d0190400c000000c0e071210b02400707030f00100004840d03100d0401056a48075041561500c030074511200c80104007500050303543c4100143c80c16980d8000142c009600810300f04401001200c104c4555032600348140c3c100001c0521602d6400441c0c90440a0385180c24074000f03900d0f251940703505120f650003850342d9010311025100102540c2e4143c1d805592500c5500004036106600d07804144c0c1800490066066260314400c00c2007181d031800ca040c401d00c040c0d0031800c001500d407496890a590440f0018405501e018180103242c040a030500303d01d001401d801040c5c005000f10307100e48400d0b84840500c8200c0c10b080c8160402015081d01030080c06d801a00004d4030b444944041580715040490100c64058021b040d448402d9449401e005103041d45207005071200010003030070fa011a400d607022038240c5029015010018441c4e9031040418500e42d010880160000322440c0d0420008002442c0007580301076481c2e014420b07000040d501d40f2400c50500721302202010300b15016608010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 922362158 1250 922360908 922360937
    0xf02090f1b0a05070b071101050103050102090f0321090d0803092a010f030b040221040c0e010b03010302100e09100905010501140f07030c02090f04030e1c030f0905060409051501 78
    0x2004e5580c00d07030b48130284501c0d42c0c450382c2045815510344203204000c0d510304800041000701c158018443e800b030a4407415071038900d000c1090f40b00e030500b01e59039000d1202021902014527045004008070a0018101002004240c58040c02c0741c20440300d00c0701c541d00503840400c03410b188250007183c010ba14032294096507102c10009205002400310f4400f4035851300348180c9583d940c1e8040d50b40084d114041c500c500b1034035003440f410101d030580b0b007561500032a41000c100410381d501114140c87c4a0261185181d20755030a0003064440c0c01d0801c420081312500e0b00c0761541d9031201c150702500c81050318510081c01d1280b0103007260010f074481414014030260601c40c009160702940c02c45840082150b840329220b08042d0307841d01c04910000e5201e10070408000b407000354011b0751f0780514000d075a90745d12100c036042440f019079041562085450500304042c00040c2c403410010401c45041c0c0b800c1d000c04e580d1070000c0f941781e030441e802542c1c2c407a403650100940c0840124280030b40503000d00c2c00e426070a2148 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 922363408 1250 922362158 922362167
    0x90204081b040f020d0603021f09120c0312020a0204050a05131506260f030901140a03090203030408031c0c0c0813030f060e1c09120f02090f1b0a 64
    0x1c140381c0100441c02886103202c0d6203075030010100749803000040d5550610040c19400074040c0d808100c2c4110451030b20070019500284c020f40080c030180c5c44e4100e5180c1020014031004920708011074000c00460710100c0001e040030140405004150001d200200f050700c1040b05a503070081444500c2c03032510040102e010003825902d220150010100e540403240301c2e110b4000b801b602e822104818405450b1b1602e0244c82d01c4140210000c038105480d40d040002244a03182d1281c000a540021241d4107084c0c2080301c0700c0020800d0884d1070400003510b14490b804030b420b54000b0361050302e06420100781c01d0f00300c07a40c4c40c80010079041110410050120008809810340e04003100c050141d490220301d0348200c880c125030138800303540c1100d160280a9410f282c4030019225841007030a075801050082550506e1000c60000b02c0307066a203031101d20a0174915004407688440030203a8059200341c044a015072100d40d000d9000701e010403007610081c54894010010322400c5810080305200c02c03c64040c01d907501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 922364658 1250 922363408 922363423
    0x40b011d0607051b01020d03020c0c06181f0e09040b040b091005010b040f090b090402090714070c03032d2019060c0c0b0a0e0111040f08060109020408 66
    0x1000c8060440820500c00300e5107a004184005102e40310311032000d600300c43d1120000000d10000d90071151201180e04085040e1301a81c0d050480c503a1103408044214944078001c2c00c07440d110410707101c80020300c010005410316860704000d0800b00784030084540e8103074410412800c0100c00d071001c0c07482d42000e41d140740c10301000030f0000c1e142c501121b0120b0803c031010301944010480740344050003956100c408040346580144030701103c80d81c04000002d4614440d00541c042d03a0801455041c441d562902031103e10311008041c5410407000d400d114000b1100718015027011401010f10780c036074504514018115142c6088030460051080c105c02e07049031a00703078001c80000204d00c1e000e8141c0308803512009900c2290180b200040c082e8800d000048410740034003c0840f40600003d00540651083c02d854121102c40e000e814820801d0005543d440140c210142101088000190f40510002a5541504503800a0415004880042094890400005001d008000d000310700e40343c0340c101469a9807d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 922365908 1250 922364658 922364687
    0xb060a0f0b0f030a060e090c040c090b07060e01230f060d0b0a0f061511061f060c0203071a130602011b08060f2101200f0f04120f11040b01 61
    0x2c0000003d0803141c2641100f80105910346407600302c1d08007040150b8407214000b140ca40218500540801c14a20900300c143c00c880c2d1240c4528902446902c1d00005007004410301d00d030355900c0f0410700707185000d800691400222040e2020b000f908200b080326055030005000d0034030900403c441c4002007080001020380083c403000002461012800a000103400c0c2544003102c0c032104e01c601e41c86401d40005210101401010540c1c0540e035403404034444900b00105d9542140d005484103204250151458510a074002800c41c0c4040380c0d125900240c000048941054200c40454101206c40001103010040c01840c00280041c8502c4458203c80e56896140c0d4400c000c5907601143c0d09444001820840c0710000d010213181422030b124140705143c207501400003661070f0540d0740400c003000340174000306541c0c0a04810301e0110307078001e55803180d0080320240e181e0020130000010780000040c03c2c2c010035031180c28050008035850a00008410f0050900f40c0a1801e00c100603549a9020100512855 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 922367158 1250 922365908 922365937
    0x90606030e0d1709070906030f151104090f0204231003050f04021507060f05010f17030301030b0c0d0e070f090b1503180106030b040b0714120703090f0b060a0f0b 71
    0x41e6042d02e40c078945100c2e46d02880c4020318151000c814040d402d00f82c0d9107485d000e00359500202c00180031745400c03038005208200b51404240010300ca451103e030001c111000b007001c0050305003a165011038030040c8400d000d569817103079130403e01e20720f90400c4400d03004100070b80c1c10104a070745017652429020a0006100a114035002c244500310410361405440c0c03019001001040b81001702c00002004040c280503000c8804415400042d818102081462221400202560030341c0d107580d440211503070f005000c2004002c420f02000c2d800004520800c2e10b064040c0c0014841645820402d458424040c1c1006c041682000504205621084646090708213024034442e5240c0d120045180619240d441070005542403280002c00e10400d65041070060380540d40e40203194a40f01d80c2628414041440303009022820300c1ba51a4602100110702e62004480c140455102c005a4034011101c0c8040401c64103140020140015818400c0071113000c1c2c103200000400180c01d102d462a000c1c01017041480610 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 922368408 1250 922367158 922367161
    0x613080a03110d050103061b020a1b0e2503050106020c0910050d0b010f1401020601090b1c20060f1602060403020d051b04060e0115021501090606030e0d17 68
    0xa1003680481600c070314184a02d6102d084151040020700b10030722090700ea190a010071890030088207101608105550f40080000c2c807200d986280c241890b102401d10041e04450001070200c104580c990300c0b6002c0041015080307040c0001001d0703038038540b0000b40100362908005201c62500050004500c1c40e0454101c500c82d641c001d9808100c40c000c0d08030301c0d04611038139210020450445e8056040e2054060100136441d110180410000d41404c000d42c0140d0003c401002034800980c014011103101500b07040842034280044941c0c00a4808102c44a41d080c05035402c0b400b40c007104c0c440c898403040f00c04524041c030a1081001600550040707800d2050180c680070115583d40b0110340c02164040c2900301228500d0410b26112226800c00700030043d07202414045618040c071444090f245610700e401e0450f400c00240308014458447c0c03c00a51007814840480101c11b003100600030000c2c0003010030082e0601e4070003801c0d105200c2031113006a00404030650300582145600003081e440c1441e40119 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 922369658 1250 922368408 922368427
    0x3190e0d023109060b04050c0421050a0c140f1324080c0a0603180602090d062405010503011410050f0a2307050c040e030d1b0f02061308 60
    0x500e01101c0703034041005440400e482c0e1034142c60f0850310031540924003c111031802041800155038007182c02d05101103080106120f2024004407045456007070780458039807000540d441c240782c0f00d8004004c0da19041e401b00304202130841c14100c0e41d206041501e8007a04000c088010441c0700b014810341d017149a07212904030300c5250054410003c0400443c80103003076a07035102d503084c0d214140b20f60024011308103054003003900b501a0041c21640e290703400c0300b90940e08158860030020341000c00034a900c64410a9545d012030b10900525100c10880c90281c0c40e9582810080d143d0002c0c139a201505000c8103000401402c8585030001d01d00001c1514541003241c0b03600c0e022101c511400c41d002540c5000400c43c80380769030384074040d9160410458101d801c4500301c0030b582c5040380034a2000134496800f448080200342015084100446076440840f400c00c10b0400742c00303041e42c0e900310807500b6410f01c0c10122460150b01c440c800c0c031a0809070002d05941d00b481900301c0304011b0a20b0000e4061100000c49a08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 922370908 1250 922369658 922369699
    0x50406170c01260412080903030c12270106060801120305090f1c0c05030610050f1e0d03030504020f090f0721050a0b0a090606051605011d03190e0d02 66
    0x100e10780f044400401c5280c103251800700c2c3d0350f4242c8002d000417401c2e0001007503482c000040700c0c000c080d025140760130040102d0850100c800c1c001d240c445400d00a220752118108011008500d44100600109541d0700b4200700a000c64416031241660342122540280881e400400303d81c4965001d542445801d003010011510f802c0f03044000b00308a40c05a0b17015020322038007019080030b0740c80407420355540f0748655042017040451409600da011548204580311441c0049100706221200109014030340081000030380342a40780d10b07080d0b000c079448008000840c0741241d4070400045048842c0d84403070070070308145690003500904040901003c140075880400761070b40e10b041040f00549040c09a4500f0780d041a01070120615564002e441d03c20001c80d0450050083e001541c240d83d0340e250600104000b108064124100250307815542c40246003003491250540c901010b61100080da500e07a40d10545001403002e40711076900b085030341d802000da1592007004840700715030101c48a55a28052500307514 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 922372158 1250 922370908 922370957
    0x130b040b0306090f07050117010605030a09050f0703020906090412050c100207030f1101110f0717070506010e092805010b031b0102010e010612170d060b04050406170c01 74
    0x150300d885040300f008007400000414000040304803040e603520039135541c015222500c030011a00002d8140c4001440200d202d10f010795403201442c04081040d102944540741021101540e1080c1d60b0400230382030040d41000f8843e01d41020040e601d1542c0c0b882c02c1d0722034964103850740808800300a00090b601c10021001c010514501c010301c1c40440d643c101501d00640803910015a00020030041c948142d0001018032809203850107110081c3c1c5403200030550507081745e0001c88100d50381c400100182c06034140d017501070407200c2e103e803000f000c07035505221070030340d070810000c101c12225809407009c240c0700c039005100903006d4413200c0643d01a10392140380c940c6c003402e030910250740c05104035844405210702c1c0c0054581e0034074080e002040a200442519426644103004140700e03028140d03c440c00044d0ba004c100300964210329031650809030301a81d40001e4924030b5100c1202d1038400f081c244424a0709119810051a44104040c00241420066601c500809264a0604c40e00d0500203400030400c80382e05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 922373408 1250 922372158 922372181
    0xb010915210c0f0b0a080c070c140111030315032e09080d09201002061f0f090f0b040e100f0f0216060e0d09030b07030209040507050a080c09130b04 65
    0x4007443c946034012191640c205503103400002d5070078004528003210366811a0780c1660441d1052880c14203081d1805544001401c01a0400c680e51400c0d00b039202090004c4c6010328a140f0412041c00510000c0601d046103001074000360100c42c180e05921810144034113441c03900c3d8864045080b01d810308005210b4041c250210042c1402c0c8013180082010382a540400c0e0012007003002c4480444200340841d4203040c50717500b000741c0d000b9004914202d400c462104a44501c100802840c0b40c0c03110000c0420414941c0300070401c1c2c1e102d848074814848580249003c0f5001510204510a08000307c5070f07680020f40c9000703880a07500c80001c0e07000000c9801803020845840340942d0b56050315440b2221a1000301c0041d20b42c07525150024022100126403107000d10710a07541c0961044c00c40d1689100d008015060380d00340740d820480240b050b2039500400380308031151303200c940c0c48074003001020744400d0005000b0081100d04126500540c0c0d01c400420380712a40c0c1003400140303130010070701260081c098520380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 922374658 1250 922373408 922373429
    0xd0b0402040f030605040203160f0e0c091807230301090203040609120221040e01053c18060102070b0d022a330406090f0b010915210c 59
    0x40b084c403809400007030003a8802c4d400c030740d10441440342d0f81c516580a4011000c484226160401c5880001c44031681c118026440d420b1030070a1110008804c2c280d41e0550440704c0c408802000700d10740d080b05002d0540340705050090485040c214a81810340320500584d0011540840880d041c841d055200c02c034141d5208034900b10401c504540a5a0703003480e00e4810b49074440c0050b0303070740540f0201c90641e4201e0fa44ca00003074000d41d00b4001000440da00030326000d409401c0f1086002c0c88800054550f9001c880510401e80001712188148841580c07034406050000c1030038800d0100a03680000c5402c2200e10030101c82d51194561000100680720703201450380e00c114400368600070300c00c1040c80c42e00760301e094030111045070b040400301080c0c0088060b44140d2a121558008417006241500a43c1c424802c1c04001081119030352400c2d480d003401403080c0c6460407444010301c0703c45028400c205040f0602812800c1003482d0007914411482101030003451241082402000c015007081c0d83d10240015812 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 922375908 1250 922374658 922374689
    0x20409030210050a021309021c020915070f02100f140c2e1b020c0603180318030f07030c030f05030c030a0e040501050f13090312021b1b060d0b040204 66
    0x4d20502030341040203c2c03401c4140b04800007a0305445803003222822003070191520b80114808640d54000c1d0005411242c00c9012210a1451070420f6001000030501c04c150984070f841548c018841d203c0f03a141d031030300300303000c40031084c1c1c0c803c00d4001c00366552080d80300c0760565403000821245070800499444541001c090344400929210301e06100608001e200f94040242e403816401c000c1000d07081c80d4070140584c001d402c03080b0f2a03080540c02180d100200014000d02c007640c50401a1039503108403040c40341c13011200e106004501d001c0c04414100021039008100307090035515105000411480014005601c201061781040401d00980c0d5094440c0e100b62070f25281406409081c0001d1003102c24030951500c400401c103842e04200c500e520850244c1724503060b01c5149508402401890415802d001003d0f00060840c8124001840450030040c0c1c1890b040e40c1540403a454001d0100b080d02109030b5070549412140c5410003903401c5201c4812001c11160002d4022400a02c21904000050f0001d0303075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 922377158 1250 922375908 922375921
    0x5060a210510022b2901180902030f0109020c2a031f1b050910110115080c0307080a1b0b070602030132010e040605042c1902040903021005 61
    0xc5181c0c404c46400080340051440203240404540030000c02da00101950340400008201d602e015104007a4181401e0010740c40c82400402040e11550000391480d4000040100c10200d100e009801007204900540c2403d03515a402c98450402c00c0c84412440507600001d0412007181048042101d006410344072a11441601c88100c0b1a07000440702d4003a040c1114136004150f00c4c226100030011554440741080302410800c007081c03040300040420015803c44500d00c01000307100b100c415407044442c0c820868030344003803181804800040039100e508a50300c208199039021501140c800d07440501d900780c1d80d40d04091031441482e950800f0b180020041350711400c108181e40214181c414000d0b041c0012100c008405004244440c4030002c00780140c0c0c0c44c45040c0d40984d02c0001c141800400110b030494641010400b260069034800020f0b134074104c04240903407000b900704880303c0c0f1031402410301040c0e0f040c0402640038488070002e0060359260303000e1043c94401d0108540c50019040113010318240903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 922378408 1250 922377158 922377187
    0x16052412150910030c060c0524071215030318170c01121b050c071802090a06050a1e03021c15061704080a020a0c03050102040905060a21051002 63
    0x81c0d0075039026003120000b05103400d0f0724000480031254448400c4c002181005411616668404000c484034452010707660320550001c20180848403d8042c0080189020074000705040c1c3e040c201e071440c44d4604440144054450060395003640d4150618044400030901c00341907440c0c199001651840c2c2504d200000980d000c503440300d40780070036a0f400c5120405000c201049826010581c10442034607140584e407103009030003074214015201d0584181903520b110090104504c1034035000740c1640082d96034801e02e02944a04007405051405505048441d0300140c8002ca01e000320089207110781c0508000079122f901216000e402c0c0d03188441205041c6113030709010b032580512041010750410408218a0300c0b4900c1503040c001e0010340386006031a162034270101a071042001108500501c4d0220340801d242e0100700300114490000165218a004101c004454000c0d20035071080c1001c10301005048030241d02264000b403e0001c0107a03403506440c01510b0010b84107400308541d1b001288404025246 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 922379658 1250 922378408 922378441
    0x311060705150c040603050a0605060d052a040503010c030608190203010f0204060513050102011b03020c07030f03080906090a0201120c020c0a0b0406030e0303070504030b0417030103120216052412 86
    0x1c0d407020b000c0e90300c0741d01c01c8000b0741c1c405002b11504000280130340540c0381c2c5540c000d56080014480c43c520301c2825500722042c8a610701c0001118100c0c001800c0206040900c41c1f0140c0c2401454200072042c20145580c8d150200e41d250742500030301b0301400006540e420f40c854540320309807841c2150345542d200805029504452807100c024404d8100c0020036500600a0380001c070010305e8041c0300300c0324041d81079009400a2f83d113440f9034459014040300060308003240744200c5000e07071140d845034501807100a04d44240109070b401d10f5001a108400186d80207181c0b00c0c5440c940780c4020a1000130f641d0124a03010312440020b03800403030218002000404a4024400d55080c1e580070303c030103965500c186a4030310003615124001101003004001040601c0b642c1d64010f40324100409804441d66503088064000780c0060700c0b5543d0402740720364016010000071110340b01c00d80d24241c41514090002c1d001010358049011216200c25a6841c0d1006810481d84510300580b0714212504022220030b00e034004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 922380908 1250 922379658 922379669
    0x3050d051914100611070305010515120a0c2d171908030103170c010c1e0c03080106120b0312032a0f0d090f0f0b060a0311060705150c04 60
    0x601800c40e004016140b600074820a1000301462030ba500d018421190621781100b0070056029104002c00003880a014081c0640e4044203001880b91003181000f0800e005560406919880401c2440002d19814020b90403210041c801c0c4001e01c4250308101c0500700d181c0c1d40c03580488080e110108400318052451020b900724001210758418810751000201030700d0590180440c1c070140010000940e10009502c49080b07e140c640d4140080c1c02216400d41c2c6008000b20003080c00d52400403000c20700c0318010300c8007100c240b03801580c2c45503c2e20060075060042c0a11000c00c64015600c01300b0080b1504104c42ca0100941103030480516540e40411030b40007619034803031039110040d02489504001703010b01c003040071040b2960b10f4a695a80b1201d0181d001110000610b03445041510215144020302c410540c015844800c001c090b92a001c45042d10081c00d82e4840c0001150074800f00d0041d10100d00c05440c240e034566174500003402c3c039928081001503d0b9100c142010200074444111401400869170b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 922382158 1250 922380908 922380911
    0x40e0f0d0912060903021203010e01051504060512040606050a060c050d0203030103121d1507060e0f150915071106010f0308070b060a0911040e15180403050d0519 71
    0x140320104486069036071140825038030070b10503880c0c041060355105040c024801d00440d014142c50181003045504244c1c04041358152100041055040c00720340c0c0c822100c2d0180800e0320341401c004c0050258059079460340454000a00003a00300007050b0b1000010b05401412540707520303a80c8200410f1007486020450f07403409084950490140004180c1c2d0590398000d000c119800141c0508981241035440100340d1030700740d013140604507256400c0d44203144000380714055840316141000019a01250002d403408d60014102484082c5c0204824050300b2508190075002c3e220311001e103160580000c8204c200c092905c1c24071207580c0d008000c03610030071002c400381d1b5070682c0d941c04000d50089142c0b00203040c0903000c01c184000907080700d900030307400310008050401071a00d4080d0801100c0c41c200d802d041040b0001030a104090703120000c654003d01107a01c0000c800342c0c40000c0303920068407000721360400e00d64201240030940182c040d29800024102c04011a28110340d80d14003906002c00030315a20f5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 922383408 1250 922382158 922382173
    0x8090f060c2b02060c0c0102041a0a080f250509030609060117060f15030316031d090c0f09010c0506040302061b0a1e0509060d09020a05030a030f0c11040e0f 69
    0xd0306103001e08142600b440d005042e2940e2148004803160340084440c4085560811000c194540341100c0302c004040c00a82140d1149218103001d0b2070f80c1000780040e0450702d80c810401c6113034001d0081d807803007074404604d40f201105038405065809011f080c8109916010310300404c01030100000e0440e0484083c05480716560b03e4400c4119100c42c01621000b280000e03500001d0500e0104880302001c150015040340e203000900795500d118829889421800240b42c0201954800d2030b0b040160000c101c2264100c0c4642080403101805101d01c950742040c58002044507400d50f030017108410031003900a02502e0162074a440c00a481c0c40701264060303244104c2810200c02c01d58107009403510540291030380300b8502030b00c0224a920280c0c1120060800ca41042644201c0c0c44020150894040300c260204e020050b0744100503071000c0a0304120b019901030007958010030360007204d01c0e140307c03068180880140e4007410400f2a11956605a94005040c408030b914204000a401c0d034041080d101900c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 922384658 1250 922383408 922383463
    0x10608120c061b0906130506070317060406050102030405090402180c04061d030604030e0a0b072004020901050f16080a050306040b1020030403060507090614070b0408090f060c 77
    0x80c030215039184403100b43d0a100021403410f245008000c22120040064180d580c0c07940041e81560206070118000f0b0894000800c20048000c0001e4000000b00c4007403003035600b801c00007582d0340110712899204060041c0400c05540703515031001300300300b091240604503140c62803140030150300a124070400240310504200007862185000c042095009019200948070764500711211440182103036482810060001000502c480080000c1d0f4440c05403422401c0402400821014004141c54091401000240d2891ba4000201c0d0345c02401b080d0110f40b650180141c003c540c8150460003042c01000190103a07417a600000903600c98417086806001d2050403a0a0181c0c2c0e480402000021a810304c610310100b0568000350500d0740021001c4a0400d41d4a072100402c0d100160760321008100f40038410302c075596204241328546190070280900d041c94994aa103141080240042c0428901094002c007a036107884035240000c0b802802c490700d0f6660800e03100d89603089080041041941a44118030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 922385908 1250 922384658 922384681
    0x90b22060902190905010e0f0d06110c070305010b0901270b180a15030206030c071b060e0a0b07050c01140712120b030109200a032004111317010608120c06 68
    0xc131550282c2030508568004092105502901204950185c3c80b198800d103000e4074bc4002d4482400e0290041c4003d170324500303107142150b9007520030710700843c100001808100e4905ca140da0718400d44500300158094100c6044009000003e861580440300b181c50105101d4541c2580d402003007054003c10400240d0114103000b2821484000e42001c8148002540745484802a1020a010300401d40b11502c4240240e245544c09070424008107448140e1050682880b15515000d02000c8100c64a040c1094491903681c10280001074104442401150801112041665072035603001503c140c07541661140a0444d90b06c0c02069424a4517240715100c8034036050141c410a0b60f00502c588a04041700d100b005d09007444500c0b1141c0155816000100041d800f41070400b040700710007010100803170f4010400007035942452001144031018400f240e0081540c1d4054001c6a403844240c40d012500c0350240341c05082c0700d5120313540d00d004040107200d4141101d002042c07901c035404151411030f50360f0900d840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 922387158 1250 922385908 922385927
    0x1513140a0203120c1f0f050c0304030e0d0c050306070801090b03010209300307060509060c070b16110708030d06090204081002070602091018090b2206090219090501 72
    0x254036500070400b034619000302400600f04c501c036030405d0350b4100702e20703400d80d003844d00b00070345010003855480c00e0b0344c80c0084180c415079030010901c3d820f851641c14103032001401a809036044911614401c1d4a1008210b900240c1c0b800814014098031807a15102c074020700007180c24440d05031781500703081e04d000f014035041c4211030000070f004081d0a008241400c0312154180403405c4549045942005050216801c001a0a4141c4900808681e9241c189101c506200c006400e400b4485802d014100c0080c0b0a17445069000d07050b0058983c20006820049030014514003981e038990003960700c041650b41010000303001400003008140f00c41961a001d80c0c00300d02c160302c03032001e0a401c030f44076000c51328480790002c048590140c0005030a10003900002100c100048500c5804980c60303014008217523070ba4201c284002c10010400300156040328000c0345030210740d020310308140598610003024020f2994460405085040002c5494134405042c00b1007101d21074605a020900d042000140c5600c40c0c960107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 922388408 1250 922387158 922387163
    0x606070f111002120a12020c01020f0712081006030e0c120a05120301061403040302010e0d0e1806220e0607050903060907051c0f060903120f0608120a021513140a 71
    0xb00c0ca02120024100c2d1425201c881c2c00686e40d400b0001d0031004102400500041c0c08006a4a80da44045180c415101c00141207090300740310440c0104002c0d040d5250301ca1044131828100442c6896100030394900305040c205050b070788030303072020700700703400b6a00000b481c8005e00d00c00c4c02100c001c40e00c00c00c04006540800d100f16170004c3d5101440c002c00d082c80c0d0001d160003510030300000c00c00b920080042400d00c08569168000a42d00d04040d000d2440d040c000c0c04175074032000d07803a440d46003030220120b451054802850780e490010440d0380807030340217168848440349225900341c0c0d0082c01c148400400a03448520380358400d11035200443c00b6858003060700c004079480205040346030200d05002c5241c120720510183c030140d1526020a002c036440d0b00a184899110355120032002003951800310856031001c80000949107405414070554400040c052844952403000070348681040100f20f1800700c2000141d030060010909016404900c008040e44107840703806041c04000004540c00e90391034160501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 922389658 1250 922388408 922388443
    0xc0920030105150f040306021201150e01140903030c0a02030c0603010f05270708091c05030402060d02130b0a02010f09050c0d05070504060605070231050606070f111002 74
    0x100294a4140c60f001d503240060300b4510b051810b0940d0300340540d000f1368000c2d5102600000c3d508190385601e03002c280940881150300d0001e80f2038140003401034505440d0700e818064410b2071a81c0302103a038410341e10010b02c010304499031454100318640e10b410904400301d0080c0308a411440051a00c4026a81618001c960107901c0706d141004200741d100d00a881550b400221082218110319480411031003510301341c035400e035a42482200e00b0b15100c02041c6c1710030541060424890802d52180031a90041c0c0c0450341c85895500c0ac0501100078854040420000f402407200051300010340409000610300e00e0f0000c208210b9080443c0702a6950818000d0280d001440468510304e005500d41c0800303401602110040c2d521100450201c41e0745401c50004504c021442504519007072928a090060385195008416420b4201707aa0901d160038031030516584880014143d501c0c3c9105641400b40c00800702410090181400c010102c480c00d40b080c040c1c20341810034205a07000003440f80e030442d00c0154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 922390908 1250 922389658 922389661
    0x118020310060e0a0c0512010e040302150c0f09120106080a2607080a02010e122208071206090b0c030f07090312030f14070216090b010203040b0f160c092003 69
    0xc04c1030007802c0d0002154280b04080c8a032005a241902c44c00e030180020300000c4a4038207203402d01900d82000a843c80d152a03810f40700b042419900c950958507a0002c64a85a45030300302c140005e004000b40101c0000e0070341c0b0701480004c100c0c10000300b801d0030074020503550240d00e840c00f0029103001355240c50b01413200c00402c401400903492500500c8050780341d00c00010b0204c2d40e040b54906281340e007088910804030205610f04168014100300f2400c2903190010940b041c645441151621414840d46034480d000c8941c10703040c0070540c0c201c0c1104c4da03844011046079151155000d030702c1c0d4200740c1d02ca00c40003010381e0001c3c140502501c280c00903660005000c194074440000103c01500c2c3c6414141940c0e030322000c801170b580115810702806200c8540203802c00b05a1840c030340c035070012035038013032520181892688581a600801181c2c00ea0307031000310465075104204a194020300c14907610310320340604c04200e0014040e000460b8070036140c07400c80502c0480d4000c510350105442c40210704058800800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 922392158 1250 922390908 922390921
    0x4080601060c1e1112070e06010503070c150203011409042301021b06042904060c031b17010b04030308011e03020303190207050a030819110118020310060e 68
    0x8050504880c4100c107803040c2c1d0325607040f02000b024034566040b203540c03481403510340483c90701c4d4201c00003401c0e620005028132450185852031420b0060704140c1400800004102c10500c0b5459084400b9044604198404c1d8404101c00c001e41c000d1042d0f4041d00e01c0c112001400345800c0985902658010105202d914a205004444e6001c640200d02496500300880c0c0303580c180a410a00d011410035000d00303c94070301814a00a0282840300842034446000d02e020400c030032180e28aa00540c2200d1b00240350703031030320b2000c0d002490b400880802805040305c50014055214030381c102a101041e07041c1d051a41e903084120700700e01690000601046050380148802c190350f86110b08030000444500303021960b80d07008a03056900c4a0300e0542e1f8000c90411010300300d43c0400140c80101170a42e04410401c4c0f56849800c0d09020307048203a51901c50607209540114440c20380f0000c02c2e913080c03000300005080d004140341c0748196504128000d0080c1420a150a80039101d000100c4403155824403142d51140b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 922393408 1250 922392158 922392167
    0x7030207180e0d030f06080f070515090303040e09010f052508012102062101090c0207060e06090d050322050a03030906080c13030c090506030a11010f170a1d030408060106 75
    0x85c0404c0c445943d80303150018901c0c00070445a00e00401c0c88000c0d2000e41e06000503c070220701d01c1021508013940401c12008107803400401c0300c00311200d407503450300d050300e5003207416014141050042c2c00c254101000d02190400c0c014021450f150b20081b03421020b404030809407200d0340c00b4420021880c0c0303030a0343c0d030255100000314410b01c0c0740b000342400c0c0b43c92446001c0148002141807206111b6a200300180301d15501846032502408903800180a42407800d10f00404d01000150868003490000c01d82d052252200042c40d04015403080c15070742c48402c0c0d08a081c401003070a1074040901480c450000850f828402404000c0d02c2d05035a47c0301091f401c000058910703d030302030840542c903001080301c1c0d9040503000e4507480c090343c0f003030072103603466403408400100b5140040c00c5a442a04415040c80028100318501e52a8070000c6c28046403e07520340b04180d030782900070480c0c5685120180200030b0003e8440d40208008541103290012410340e0180056031b0f40100d0080c0f003400c1e0f01600050011502a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 922394658 1250 922393408 922393421
    0x5060102010c0926060702071503021903020c0f07030b161e1103040e13030f0503190b0a05120304060813151505030102180f010c15051302030307030207180e0d03 71
    0x10074800804240c44000c1381c0c03070910100c07050801a080040300303202c6900401c801400454241c902942041c26001580803d400380303195050a0641c0001d082502c00014442c50b018407074154281c8200558070304044a49140840307401d00c90102c0c0d44070a40d80d007030140150109040c003610200718600224101a00e4001c440540107549200500c00060801041c0d44128861184808100031546172032a0203015240448610400c0c04401c0c02000b03842d4103005450420b40c210014081040e083e0000450040f11140d04110b0b00041050000010100008010000c4489075582d054450b0b940906a0140c0000f0b43c0008000d01c071545c0d000c0f0507106803a0409400c1040c6941b102031030355500d000003401c80e408220040040e0440420b419161f241151000000600c20b0910041c1d0403100c0c1c1c1d980800c10700741d402c910110780d5180c000c5407100907481000007107241e001d000c40350f41721b0302820065950026845001c2800b1071110a0522000c014003411000c9900304008205c3d4480c480d0040d0082c005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 922395908 1250 922394658 922394699
    0x50904020d0b070203120a0509190816140c01030902091816082409070303050d060302060301030c150e01360b091c11011d06030f0a05060102010c09 65
    0x42800d041c030204004980083c019101ca0700210780c0c802054845841c1442c000b003c8000082ca8102045115000494034100158644100c507050448070725111450b80503c040412821840c804000e041180c1d00e64100d01d8252184110340c00042504011010358680100080d0080302d1100440c14004043e0154440704103c401903074265a201d414148802040d644013030380e9a03100a4091808103003070000ba191207280319168040920b0014802d80da40c0046104c0203040000010300402c00d01c0142d03010300c0c082c66008081c944c3d2941d5a0500c0010051107000e2a00915044a002c0c0000c5000b4241c800c0300100c1a1101d5804075120284071040d002410b005a4850f0381c02c001c010080950034030801d000d04620004a0744804400c0f045c021085540091000e0307151002000c80c020034442c5250b80e989420901c0d12203982e5900c0c45064108201c03090007681c2101c004418403190282c00c00102d8880c0d01440350800c500c1c1c0d1040c00480c2a14009014080840c50100080c012004440c0f0746021008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 922397158 1250 922395908 922395919
    0x1e140601080d050c0309040c0c060b0102060601051c1104080703141912021c0320160b0718090902011b12050d0902180708090307030f080414030c0705040f021305090402 74
    0x781b40101007401c1c1ca844400310000541e12007a01c1c001c1041a2182103440002840201440d00c0c1a00010703000e80700d401c1d5602c08210424051070750746803494200d0100c1c41c9100002c20703191640c40044968034a414001203031b10091414120200d1403000414848035414681d00f400040c0d0251100100d030200602c20100318018800e01d844490100c0580300300e54015980c001904074503140440004c102440c0d012990b03004200324901d61702108511303c100c8240c1149840c001e035210090140d85c0844122042c01c8603000020f400290000d0a9100c0c401260003a01d0714840d40d5515000b024280006010052081c0790b1a40030364600c038030910141440c01d01c42d9000048036002600024501100c04014184025100040200c03040c1c4c001e02403604041d00324010343c00c2c02001e9a0103070200010800c480201300004000405211130031043e80d9040014205503a41c0d40c4649514545600c11800b896000d9814440894110000303842112038840c0b89882450195013000c0030440e84150103482a68000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 922398408 1250 922397158 922397167
    0x1b0306060a0c1e0510021e0306010e12010f06050607081c1112010311030604150513021e01030b100c0204110906190e0301090201080f131e140601080d050c03 69
    0x50b4942c0c501d6079440c00301d01c01070940c0312400d280007854031040c488400c00040c0184400411681e01c00c0303801e07c070682900241a102d03540c1030012540c50a056412590140050118064125043d0302207400c98858500500c9125210300900689104211000b080a0010001c48400c400307091215660307903129079400f14440d5502c158100e4960407445074081c1c4001048010020032000c10303901121000140c014168506c2c01780c55286400142070030860016440b10006640b21090042c44000b15600821b0b00c85420120300040d01100310020303c0c240800d14082a9038400c0c0340c240d20700060350805596030b40150784140e0900003c0c00140080f0040d209060144001961307890000c2c00c01c3c0900c1e081780d0701e10401d2294004200100454455000340d01d011090000360740d101403000c0d80035090300340e100e813507031907410000f000495000c4e00074014850081da2004c003428000f058000c190f0240351600f141102d05055241c40c0d030000e1280c007280e640040301d1541282c0c060000f030a4040c0c1041c0607039080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 922399658 1250 922398408 922398413
    0xf03090801110405040e060c1e04051504090e160902091c06090219031505060607060f2408100b0a080628050603120306060c0106030b010e1b0306060a0c 67
    0xb900c051151154440c0c402190a2105050600c60800e510b02044020122400c09440d071203054030a020144081c0c030f2011401d40601d01355002154024000500084221801c48100d8905a04503014018640342411010703103074003400142e405d0140381ca41c1c1007405640e1a01084000030342c0010f0400ea0061402e43c1400040e03141842491080c600403540894841882e104120031451208040030701c80288210500c007050708034440714071042d1400030003d0039498590000381d540c005e640c0d004110a044ca80160404000c40c0c02c1014580301207004000e4240c1000205d142000f030744e01075100b41d03602c00c2c3d0781009241c0140c0c20042500e81c02904070020151245010340c1010300c1100d84408ca08000d4408454180c0403543c44e691000c81c1c01c0b8200b20900702100007a0325034040a80220440c1d5001c004612542e40e81e034212050500d004000300305d00d03903580c546203040c0003092007181014441c850010380300e00780041140400402c0307440c60600e0355461204006054001d20103200c1088500c0d040b5000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 922400908 1250 922399658 922399661
    0xf0f030c0e090915010f032f060d1b3e0708010b09150d0201030c0e0418060506010807020a030513092a020313060507110402030f0f011d01030f03090801 67
    0x5500c2d60001d04072135035070310411134054041a40b140649012181e410400b0030095622001c20340440850350178000d47c41c110000140403d00300580d4000e0001990100e402c40705c0e80080c0c0d0318120f0408400340d0424408050f941100800d409040ca01c400740740200c0d440721252640b010b03246038a0108800a11045240744c500311054102d04c000b69580d00164050b07250864101781e015200e10504000d00f101d41020403020b2454810080c18103450307948005c0f9041c003031901e0480641c8003400030088040e0384416020b140c00e6500050324268a030401040306544560115442158280c000b0b0648010b80d941c116900e034003415500740c60303007038001010800e00114040c04208407140d40300441010b240303004210030760505140742015036104004503010110729440c4042110000d0034034a8460005040100c00c03012031211039540280700008000341c51940011590245918800b00644c503a00c6040c003c0c1d0312004a00160081d40c1c03070400400000d8038155210040d28424681016100d984940050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 922402158 1250 922400908 922400911
    0x1f1b02060d1e050c03010b0a08070e030d02011e1817070203061006020f0114070c06020c03040b04032001021002030403030b0904081e0415110a0c0f0e06010f0f030c0e09 74
    0x228001c1c0c042c07689400302c0060b401103a401c400241d100e07914652510810b406984038030821b01c400d1002d540b0000700d41c980100150319485101900f51854180c41c280001d001300060214440300b40c425040d003460031a00c81c42043c000380100100c4d481c8110960b1030302102544600300c03024070480100007010060f04c0600889000d400018180c548860030208085d003001d012104821060385010a13000f841e07002c00e1701c1190003103524105622844201c0c140b031006441665000450703403000240001c1e0207045c0c40d0040085a00400300c00d4403224107420b60500b9820116400740c0142c0c81040f0310203c0d84003560055400078400c3c140003c88080000205203003080459090315410800700d080044160191480f05900c0000ca0001e40744c5070400a022445054107503c2c0802c00000441102e800c0c1000c2258001c5150019112850301c1c1e070311910607c902c00240281549182214042143c40d4060701200381080801c0d2541401c2101c1ea420440007071201e14030700420861007484403110754031070072340b40da = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 922403408 1250 922402158 922402181
    0x304170d0b090a0213050f0604030204060b040510090e011e170607081006020615150c100b01030902333702120711060f091f1b02060d 59
    0x42030401900080090b41c0ea0001c1480b03402c98010080d8801900030030495600b95076086032003410078002e41c1d001c50494007580d0002900249000000f160901ca02c0000d4822104100c401c03242da610701c1d072806c0301e840445102e20010a00313000f005019100303500310710340c9044a812102140c1d84d0f41d218100401603280548050f05a00081e0600016603884165254055160320782c2c401401e1521000940e2003000500c03c0d13034484605031090200765a034501c020400d64900c40010785400c8c2e0008031503102d000c14424658a5858030b0031985d000e500034002c000d05540c005140e041d520f0b0503258500740480d86008101c01940920103141032914400000e004040d01d14012140b44a5801c0030300440d41c514800c4460680340c09081c0085120780c0007440140104610b038401d521400540b0700ba50800804055255020f0b4000c60480400310040340135190080d402c40e405e403800c824804110200803c80030901002401030603c2503604002c02c00180741b1248003a010b035247c480d10103140412501540c500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 922404658 1250 922403408 922403411
    0x5030a27061205240f0609102006011a07060e0601090903080f0c31060f12110a0f11060c0405030d090b09120f0a080c070b1c020304170d 60
    0x341e0542110621495038048003e04c900340d50080040310701c04c40b00c00600b100364856041d004015000340c945d8015544101800b07042e41a00036100384005c1c01c00365468403246015496420039114070070000503028100d80420140c0030032948a50b81c0e581090303000c06c20584403e510360a101c1e0b004c6204002450080144480004e101242440d00030b00c450b2020f080980001214070600119103c1e030303401c94807a244a40314141245191411a8415012000307545a405e40031310070000f11240c02813040040807140e0b036a00700d450510020007000300c4848144d11a880c400c24006680000d005400f1102900100e060100d483d010040300305181600484050b031001303001060412450508018902d0351841c142407507080a424803541e00354074000c808902d03126074500a00d0035180c1d0414400000050021400c0d80c1140b042ea0600030a070341c0c80402086024030503c01c00103400310380030301540c000803a06000e201e942102145e094010303400140041d0303210700c81d04010b0100c0c0b01041e4020308200e09407000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 922405908 1250 922404658 922404677
    0x1c090c0909050c1003061a3115020102042d03020f04140c07020f06070b06060f123115020a1701120203070501090e040f03030b0d05010911060705030a2706 68
    0x8000e6400c03400120399140385014030003c0c81c41f00d075544c40352386144404642c0c484110800c403900070300307000b00e40e0080d0418505500c00000580d41034004100755010301086400d655800e00500600138172203d41c0c0d140b0152002407e10042c070300004042d0003000000d00101c7c18180c0c0010601e40e0304815a2007440c00703100019804118284402200007a43d42250340c0d0f4101004e035200c044140a0040006118020000740519024a00310544035100040f40f004001440c10220640300d00c402d145210361001400d40c10b0300800a03010303a00c0d4500650080310710008000e907a0201000e9003100a051051149a01303101d1502c2420b0442140203211108035070360360302c01074014107080806c160455410842440300620009507440b2a03a500944c0c00b10360860b600c8030600781107009103a096107082d48003800d060b00d03009011054201041050140caa001c0358168182d082203510721420000500640040c440b080c0c50500800640300b03141d00740c0c0d0001d0f5059000e1481410f903075406400801c0418113180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 922407158 1250 922405908 922405919
    0xb03130b0604020928080703050628050c0a2712060209040905060117010c081501090f14120a0f0b15060d0608010b0a050105041703130b1c090c0909050c100306 70
    0x41d00c000130612140941007148c1113442e441d031560802444030030010140c540c00703051341c01360348020b408101400500b0003050400c0c1c407031500075070b00c0008414006905007209600b05500388040d1480210b122000505151911200c1c001101c0340e0b0b403003640c5841d03007441101c129844502440c0280c44c8a4400b9000541c1424039400c0b60071005102c681c0c842e031500303403614605504600d030250800081c020300003400c075101d001200c034886503801445001010b1400090050080c11b048400c441084038074050032216107d03400e54401090300046d109607541e50201000c112002881508214442050084080c00d036010580b603502034555220f003180d83c0c080402000a080c0300f4203c0484003101c1c0d4009592078800000e10a010b40c0c01810483c02c0051a0a0074218081048400010500d517044c0c070f0f40d03030703541c48446141e400c182d00e0440c00c141d20f00d0142c1003984c0740f03109121445500c4015810000c0c2407900e12402000c40840840b00e80c400c1d008160001c1d603030070428180002482c0d4000c1121400c24 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 922408408 1250 922407158 922407229
    0x3060603140303060a0501051c241e090908040e040b06040606021f1a1e030c09070813021206100504180201020a20060418060b03130b06040209 63
    0x41c00c0c0702032260418414031145a1305c11903140100c0e1b01c02d1801646403450100244403892a1005404c0c0c02e6203081e4995520035140c00d0900e00040001024010940d036a500c0e0300240d0040351950304100316000f40c1408000c1c483d5211100240c0202081414030780c407074034660140c400644098400d1a40e4400300300c1603103003c2c080c0001500d003c0c4094408840d08081c1600140c1102d00d6141181da00d80c005908046c010765103004912500070700f910b0b0340203407011500400e0614184114041d000d400080c000c54141045000d0154040d9621041242d075016120747c4842410042240e01502c1094069180720040201ca40110b800030300510515141c14100f20465410800310080300c44601c104201607078010420325003054001c0c14113070042203108030141c88440104142540010081000f04a0085400b094040c04505a504220050f03c1da0206001400203c885100c0803114607a1940002c43d0170035819000780e4050005810060000002103020380658900020040e1070319003e4070315000d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 922409658 1250 922408408 922408433
    0x2031f0803072907030903031b0c06060f050102030307030e21030624070b04060e0607262806180c02250618030c030305120711100c14030103060603 65
    0x801682c0c0c00f0742020060807291202e8002e00300b009041e074600c194030916000303402c04101403a00107020111403028420181c450710b40700c00241c52131490301d8008207000110290200a542e0160015821a500c55a00310058581201010300501410b03a000006129141076081401000c0031801d483e4a80042402a589840d0003131059594510806215031482101181e40b2701307410081100d9141d440307041c04030241420034103003400e0340300b131104100c0300c03a40c8002d1010000300391303207040fa40000024404411103103040c0c0d05203600c451005184580e50046140f000c0320320b852040c010942c6039491442201415403803542d01d0900d52940b80030b8109941c184021040d0309260100c082c42d40601600c003107881e405c0b601640f0b007070150540c28141500084001c0100551f44030031264035198076483c000701280c0000036a5207a6070f680101007804240981e00c22900901182e0040c0170f00c1138412008405400c41d03d10660602808501d03002d191130b09036000318084c6000362404904c01d0320354500100c54485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 922410908 1250 922409658 922409693
    0x203010518060a12060b030f1612030e0603180109080c07120f0803091207150b0d031d011209060504030e010504140639060c0c0c0402031f080307 64
    0x7480c1c04100e03182d42c1c0c0b1030301002520300c042d800041c84016490110010104601042d41c1403140d1804900b0250001840d00c180d540050741152045507200064502d00086410040210fa42030382645050308050f405180d010343e09444020022200c540440e085440c81c0d20242c81c060000100506007a1041201302c1c000c0080d04811f13042031056443c1d045105081c0900144450000404501186c00c10892104405040c151007581d980f0301c3d10307200c0340442c0244001c040640c28000000035600e82240907890307140e0551102054003690704500040104044241d6042c0109101c504954116130b218000d40c0070303c69040083d9604090501405031740d083d82030281007183c204410311050b0b940001d00d40c5900c0003526580e44900528088081e070140c03d22a407010282ca500350f2040a00640c4001c4007100d28210a5030390940700c12000f5503242c82224920613143d44442103039899810903030700a5034015400011448021880c0c00420480c800343d03403284203194404038007402800b0910500e03000f43c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 922412158 1250 922410908 922410949
    0x51011120c0a021c021504096f12081903110f1b06130b040f05070305030c070f0f060c1b090c11030c1519020d02030105 53
    0x500740311031035500d0000c2480240190b00a00540c1e05000040f0054900150f0080000d00c000304002c640002c19040b510500003690704000d0140355409009160102c03904410300e540e818051a0440d08200f5242c101c0748100300c042c01c00101408190003001c0c00350f81000b2001858030560011140380207140c0e82e80114209800d843c103401d000883d00012604a140e210080070000e2048407000e41c000d103c50342540c954500005400400318a20000804103443e19031544140010b2049a465884c2c0c01107507901c00704425070000c00040b031418000d043c0e1140c0704103001441a04240e0302c850826090350f00489890740041f03003109643e20180000301c00b4000c044e01c01c941d071034a40900d0400c0c0382a144501424030015002c840c003408099a008401d07080150f5020080b699030b202c0d000010442511010300007460320038105000d54003c004c44e0502c013900d100400004084144143d001030b1701604d203804801d48041a0340704181079001400011a05140c0180c8030340c5003400b400000d65800000031481c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 922413408 1250 922412158 922412167
    0x30b09210d0506120a0b09070e071e031a06070501061a0909130b0a0f0b0d0503030910141815040f1703190f110d0b010e10020d120605101112 62
    0x30b08002101d01c0d0b05074106c84404416100e900480341800b00ca80c100c0e41003500f83c03078100540c40750044200341501060103540c0d80f00706c1010004404441e0f100f000200384c41d00011140f034082c075000c005080c205005200005880303036600d40c00380395880d4402c003d452160003c138500086141c44105903901c00b6030b0b1503a204807040b80795076800800800400c19650a559600d00b81b44c0c040c0d10303900c60301104501410304820042d4604007140d5030b4000711103142452042490005131582903009007a03040304070920714030700354852452801c24080b17203050b84815445240f456090114030982034601940c094900882e80818070300308810304054201c0b03024021403080050004407000300a5440514045c03500000b003440a142400c0040d00c04c2c62100c040702e01c000316800001843c0d0341d200c8402000c09803900c00046c1242410300400c01440800340026070004456001d4003800380d1800c000c40404458001130b0b294841000850300250b03c517051000442038070300c40c007038071200f0015461030075201301106050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 922414658 1250 922413408 922413439
    0x7020f0a021c051603060c02010605130203061c081201140108070e030309100503340507030e0d050303040515010f03081c0e030a020d0302070804030b09210d0506 71
    0x5802a1800c000e00410784241c9a004080c0b4604402e001e00d503024080d103541803803031030f0030480d00903850000383c03540d0740380806205520f40148148402c8a00140074440110305030204a402508000d02c45a003140f468085240c16041d0350741d6103007005100701c5500b511400101052030181105070848101084e00120210007a0f8005014542c45070031803030580c41d201c4000c0080790035070160454950f0840c4000a030307421815002006140301d0070242c5600e610500107510142031681c02c0244d1f4861001144408070070941c850030080c85428000e0809009004020020601d8031f14100003d907a10380010050004110052000c48208144040f00702c120354102031400d142444140710060040d44005140498084904124000f541d1094410020728101a04440e200d6200c140710000500030101080c014500034230a5412094005c0e807028102070455940304c29004002d0441c1e41c040c0303e00500c210440448032540002c6106181c5030a0722484d40026010036030f180541140e01c81c0e1a1107808450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 922415908 1250 922414658 922414663
    0x30611030f0a1a090c07050615010507140322060e0406080c220c09080607080114090711010504030509040f050f0a020304020604152d09090e0708030304061407020f 72
    0x2c0002c1c80b800001101c22403610140340168545040781e4000c0342e61403c0040f8015070754042c19220740900240d44007580c520040218800b0320324001c50214000307204640102e0012054481d017603035110201d03460304044005480e100d203540c9800c038091011a507010302101da803200e00508409002e880501c607031400e000325151203007842d13041a4042d82c42002000c4041244251701c007080364078000304011a091004000f0001100c5000d0000d80c4d10a441c08a1210f500c2024064102c4154a108000d860500c0b4204040304e50080c3c60f000c100f040a50460440240c01e02c03805001b18420786a8a1b40d0346a08010310058030601c203440341d040d40c41c00c010000c0c80c0c000e030519244d002000c00d0005076a0350b142d200003403031030180f6048035040081e0200c43d1083c242d00b001400b02e848000c40002c000100700400d5915100b00c1d1000711000140d0800402c00841c200c03500981d1003241a08181c800160300d03405143c1c80d54100b02c50507240c0c6500d0303078840c0c90f4041c024010740760413614a1000e480220320410859a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 922417158 1250 922415908 922415911
    0x213210305160f05072d06140405041a09091203043008061309050a0b070c080d02090f0405151003020d0f05061f020a110f09010801020c0c09010f120c050303040807030611030f 77
    0x805100a44408d04d115007126001c65018110080c0108000501169183c0d4032010034070a90b4020004000414501400003c000c020520241d801d10301c0e69032183e0f0303518240743c106110a00b10400c07442c1400294000f503980c103000600203988401c950303d004800c02c040300e00141d141c50055440c2050090100f900421140d412640000b004992038940f08003c503500c0d04592400b4242213004078416680400c240c0090840329402c840f07011802c039805080104642050301c54040e000302814280044e4100340d54410502d03111410700608191121044c00142d0700601c0320846416a02e81c100010f5182410006d595254804040012040c0300d400107552070344800d4010300609810f401034410380d900c0310602403201c40003030031504495035111040d45c00b0b900002007030007240c0500300c803c0d005420105030381ca04840251041c50b0100345000340d050108903a904058907400d11008000c109a10200010b08c01800381400800104e0700e50b041035800c540c008040c10a41c41d104106114580030501c0506 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 922418408 1250 922417158 922417169
    0x91212020114190506060c031b060a1427060106031d12040e090106090f0b120a050d030902180106050c0715080a0f02090307090213210305160f05072d 66
    0x4d400c1d1205070000354140520540581c6030302c00040c191091484010b074071000112030038201c8d08036440b0902c4a0098802d1440680d020411b14000180b8038004280001d907240900c502644018103864072441c20260b00b608001c01094075000144183e81c00340c2d8011824004540143c0080c00c000520700d2030340d00c990322170401000e80d08000309100d00401c3d80034000400c101141007003c20700303852490b00940180d0380e240384907504e081c1943c2c4031404089009850168030002403c03040e0401c81080e07004001d8010242d07003042012205c9001d140c0083c40e5a03000c1c254070780300d86031a80c8070031004618040564100c82d400c1c620b1300240080135074000c031100390805950b00000c00c0500168030102c000b4002c3c82007032641846040350000e0008010750081c0031110540d200d08400544422a40d42060705061012010700707081c1a144010034400d001034001d01e91007254514142541392507215a0b00c190200540740d0780c20000c0100302c00300548040b0ba020580c2899810146410346907a01311135107461141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 922419658 1250 922418408 922418411
    0x50702090402040c12090b0114010e01081605040305030403150510080d0c0609061b030b1518030a05070b030f010f180f110708131e0b090109121202011419 68
    0x1801070b1170140500c0c280c0020f0381c0b10304101180f01c504002c00140703000e106074120300d00c80071034a49403941f00b00c01c0307005c011a06031603960103526442c06241502d0001c0040c2020024144804400240144001c0c0300843c0543d9542e410410110250411908054007000003a807084400300300b009408030380c030200340240d0b00f00580d001c038987c20103402400035080010000e61034040b20b000c402c0d011044a80f864003444d507040280d43d0000061002d01145511a0000c2a10a020031400c49401084d110741020700070b41a04c0c034080d01030362540c1c0307803491741e42106100c05408030030889442d008420340390050041c1d94400f402103240131001d0307206007003665165803520380b10f8515076024042a04001001010380082c29030303079143c40c1811040c5070442981400703c102c2001e40044c84810b030440c001e200d201001450f8281610f4105421420f80c456002907040c00002c81c03001614a900303070300804200d030140003805040c08020800a00b12085410400e0f0343da45508140031100c00521400900004080c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 922420908 1250 922419658 922419671
    0x13050d0e06090406121b06020c0f0d0b04050631140a0b0126010506060405120109060f020d0c082401020c03070303090f08061e1e1f0605070209040204 66
    0x20608901c5012581c9800c1400c19600280404154107800c0f45c20740a60140d10381d00b86c0500e0241c50000b4a881200016801103017240650710b002ca5840c010040000c0059100b501d2903a6440c01003001202d087da4030b500001c0401c1000d42c1d801d00601050140811400c20004c000122690001c0e23031548054810005c41034070f8031030010100060b8810769000044081751b50b031b48407100e4011144815602400140c1e10701c80c1000c14805000d018090500104032038142402c00d0b05001c0f41514072443d910140d900c440240b17000c220741d8072511042100c0100096a642e1581e1141c1d000c0d12410002d1f20304200150040140c0d06d2007a10342c003000c246c170001c1c001900140c801d0040b0316180040d801d03039034903002d0143d0010402d80c001300181c1c00c4400c1100011031036a6a051003541302c3d241202c0c10100c250907000030500e000c40c8020002c1e40441d001810410058980070601c42c00036044a03400b810481d05881d120541001880c008020a598030300303c0c0c506540c50b404209020005040280600e84456 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 922422158 1250 922420908 922420937
    0x601091a0d050a021b010e0c0a290f0c0604170a0c030e030a17070201030608060118110f032a1303060207050f0a030504030b010b210601021c0305010302030613050d 72
    0x4c04403071841090309020001d0000c559085402419030042040c020b1142c605403420380d0071320180b61400c41d07001c807541c042100070051402205407070308802440c55510401c03d1042d41d030300d0000505060b40350100101887c0c6898901503c001080b044080303900c0350309018a68a00d60300811028180d513051400000f902c42c001d0100e0314140c0d140e1001001e21107000d07110340c0016400d20142076058000d81c0c0601583d0340d10f11400361140070030300030448242c0c2c8002c0782500703028890308200d2000345280b030020b01d440c4042000c00c0c100e400c10740b03102c40f42c04a1000c5059565060400c0078000402c4078843e02d243c10150003810301c0340c102c1031100820b41a008188907060000070300c00c0c0c51250812000f0f481c4103844601d03000305a50b010303002c12504208094004541c00c0c5240c3c040e01c44007e401080c0310105603180d050850340080007802f660440c803d40c410b0180700c4600480010482a003510301140c507504610400d0b003422001014030003400c52036100240450b10003d0300d241c02d03030b10900340900d002e1200e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 922423408 1250 922422158 922422161
    0xe0a230d031101060608060f0f09040f030e09070c05011d0706270605040e09070b0702010c061d01021b0c0a150c23060f072c13050601091a0d050a 64
    0x221030402c055407038000c0014038240c009070003500c80d40c0700710346c19180294160f08101d01180d9410209812101c4030f400503001560048401002d03502a0610072030890b01c0500040110741c1c22119100042c01da8100a02005424000c88041460034404007650300c11642c15107a40703445900c1140c080054040c610400c42004141b10b5071216100e00c0802c0344d45442d00d101802c243d00a11803080c1b100c0d410b10000b8180078010036071200f0f4030740a600c00c80c540001600111020300b00d070381095445030f03528000d0001c4111b400102c202400100070015817102900703140504000c089041021454001040b50300c01c2e03980c1d41e204c500079a82084040e40e0024940c01044610484041c0020007240c0c5c6885104218150f061100b0b181100340021100320741d980c80b101c1303c5211010354aa10100b405140c2d40c003070308403818400b00d110104803d82c0901818000000910a401c0d1a0f01403644903070b0344062005951307111641102804049003540c8082d04480341c001e00d144200318080c180300d40e0302c10104200d07100b00d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 922424658 1250 922423408 922423427
    0x60d0c02190b2a0a030501030515040503090f0f100e010f08160809150106020318010c030c080a0c1b050f0108014a010e0a06030f06050403050f04060e0a230d03 70
    0x207180e0011303220b880004000c2c00604d0280426030ba907108140004614540401040307126a61040145082c030401d9020b0080031108215519400898000d0440e590307112800c1c140b003240b00701e03541d516510964074005080d01040f114203104120400e0304200030072030b5004090750035040500c6e180c50302c2e80d00c28191508021035a020190140d50440002410035800005008241141c0820308000c41001005417504070b61141c004000c02d5000740c002c0301280014000e0803112003241010390fa100940c0d591104990701e03a40305000003011205050019050440786840d8090081c00d02a9040d41081c0708a6000b505a4402d4040140811315160304441242d0300004241c11001c000030700202011000140c2c00d00900a240300d44443c43d0001d000110140600300450741c00010316015919142c56401c05410002c006405008017005041214a07107000104014511595650820301e01c0300100080c07075050380d11800705103001406090100c81400400381d00d0050848041e05141c0c00c615060711180e10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 922425908 1250 922424658 922424731
    0x806120106030210050301080d0302250501060902070f06050702010204082a0607050d0f08070c0609060b06070f030306091b20010e0c03070807150507060b060d0c02190b 74
    0x1311212515058006021b5410b030b40c800c03010781d00c0294408604408900640006e04c03543d010b007e9610a0b021848050700345603c0c002e00010801c580c603088400e069901040003150b0b1580c1510f80daa080c440140f050582020962008bd458a071410b0b940d1a03070350747c1c0c805034a01d0a400084045a80c500c0e04142e001c07a104c2d0103800383da110103850401d0f41e120b0024070080000701d81c5403000d00a1840c0714443d402c0c403810468885106000c03d6845040c01044a40411903060b1355541d880002c03940c68201404415216500500b0300d0141403030003c0030744d4000d900c0712500d141000070038074510707418004601c003c0300715140541c9079201d40e1810700d00c010380c03841807820b0725441c02c100590001804211216034103c203804403000b0740d6484108a03a01d00303035032043c4e030042902800010308607441107005001481c040c2102041901465000482a41c071101b032581003a503640828506454051003541c14200050255456450a541310034040000050884101071981640818007440c40d0000c00c0030240c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 922427158 1250 922425908 922425919
    0x80708090109050109080d0e01050105060406050c1002191101060f330e0406140a091d0111030a0c0806030d050327010b09011203050904090305070203010c0309110d0308061201060302 80
    0x170f0309050a881d01d038469065498000c0c1058030b00e5492080c1405094122000a003a081c40d2038542402116260800c04108105000311010b84000302600d0002c0d2105221406480c802c503104241c014100c0c044034080c07503101d0390500d4800c024620b8156a82411285144100e04541d80c09801e55110380d2020102c0d0200155000c07000160f06170b000c14208107200081d00d04005490321480c0e80c8004004800029520801040c000e002800e181d4101002a1100f0314031800c2d006000c2d05414295044040000000d3f80040100070008545000351000c1b8055820015258203080010030f86961700c07440c24400784580000401c003600d0135801d0600c20030304a2002c810500c0c96824070035010f0b219900c407080c440c4802d20000f1503660036010b00620181d42c182c0f41d45103030a48980174080038041c1c0c10016024040d0900c0503002503102030040da800d61801c0ea600003503061040c5000c0d0b0200894010282c0645400700c44600001d8100c240c480d0000007c460202400c14414005805001a40c10094104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 922428408 1250 922427158 922427171
    0x11130903080a1107020d08161a090d0903050d0e131127010909090507050904030512011403030a080c0403080403030801150e0a0513060305011a0a150807080901090501 73
    0x103600610075030007070025280074003891581c04120805805071460107540200301351104400102c0c0000200340030305840003c1000600c0580310409004a400350002d58000c0c842d0070024807283c00c2c000d40540e2a0642000440035080d0b0300c50340d5441c01c661242c4818801c602182d08110707921302e211003d46860031301c0280660192081d000215402410104c0014a0f52030131400300240310190b2402c82004c10f030350350702e00c3c0b91420980401501d01080c00b0f5909004164011038640c03610124248654001c0d1642544d403286044046501c1005a0262070f8100c131444055061b076502204407484845107160050168540c08115215485036500081c002600005d0010400d600021920704907080307800e84182c40f402c0480305a8403d141e030000158004503506007400103103400c81404800381c0242c040050000c0d1290340301d60071100c0310310b101c007088008491203110740d14204d0142c0d4050203205011134100d01000c2405011683d014103a4014091b134140020140c00302548101e001c941c0040007030001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 922429658 1250 922428408 922428413
    0x170f0406020c0f03031f090606212007020f032b0302130611210f0c0f15150d212102030a06090507170601020304080601080f0607020613111309 63
    0x5802d8650046e822400c60b204001548548920032141200d00d652100030980d98000c445208000d1070408044d07071140d035040500201000e604200302c109a003051180d42c2c0c2c2c2c0b1503004005260101032400c034841d80c003641d0040380180040181c20740b1108103810107030b40305000e101c0030307800390103011200c4950051010300025029480050703590b216108806070348015095800758903209054248407440180104412061900c1c008010a25501d10130140c0c1e03540769149200030b050203141c42c0c0781d00c8030b004440c0501a1001042101c6140e030b0400306d4081a200c010341c3d8540b0301a40c2e00800c0c81d030369441c00c814000386640c0a524107200714524006845202c0d480200098000d410564042e0480c2d4503054002c54820041d11416000b100c05031a6480300290405c00c8468504000300598110300040c000040d941c8400c01c581e9000c1d1404030b000e4a207401e40b6411070791802e04002d00000840d031004003845a185001d440d07401051b500140720501224202021416202c05052222909850104407400303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 922430908 1250 922429658 922429681
    0x1206190b0d0f08030a050c03150d08040506030411010f2a03140408011e0b010804060504060b1e040c02070509010b03070504030b010b0705010b040614120a05011b170f0406020c0f0303 80
    0x1040c00ca8485c1003015480300748648110b8001118000c00d502c45070752075840541340004040d1076051150345000c2c0340a8550780403900380d030010b42d412101d50014441810482d0b03007082d1011512801b91030a003100c0840b080342c2e01444403250a5458264940030b14460515100e60f98460340704581c142016922a41d58485078024030b002170a499400550785003c03920b1131014001d6952507541603544080c642c445448504c010700c000744c8115400e40d82d500c01d54200e070310340040c0350486080ca103802c00c001c03030600c1c8c06100c140c80c0130b450003030110b41004a081c0915521360b9066410354118030029038490381c507250b003624940302e550405801a140240005800c406150080801ca4442c80092120403082c0c4180020b44646000f0a810070200c00ca6650717150070681c40c00001035010108948801e26280c40725400c48009042c44030450300010540d410060b0005150041106111081ca90b146058048108001d502070001844039800041c0b680d800401080803c101150050a40f6130700e0070704805525 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 922432158 1250 922430908 922430911
    0x160f1106131403060115030b031606020703020f061908071209060501060e04110a050a020703140a1b060203180301150803031009060e04060b060708181206190b0d0f0803 74
    0x5a0092040901080600b00031130007a0490b61401076640300d4070070b04c04050b0b02801901c0c4800b601031294540d00b42c00030300880860b600800d0b454010308441c84c03c40c014040301c882e51010041c000d00302001022000c2c82207030030001e541c0005140c4020580c407482c40c12644203000c4100a03c0303c909180040d8140203e5a100d94121101500d900000c1200e003424403098038040031000140c90000e028410345140200020480c0c6081481541e41045d1a541c440c6007002c41100c01a003d80c0c4003078060301c10010f5540800800520411000400c1490700030000d40d00d204200749055400904810401c85403000d40240c00036001120095103015110080b143d501e41086070030070b90540b241680020708034124800c21054070701403004900e49903510388410010300300450140c1e81024081296901064001010744820818001c9907480e031841a410030424420500b0035120303d070410000d0100c000720480610007100305008002c10030354010701c005002c0e29190b00d0b014183c24081c50800c1d003005101401107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 922433408 1250 922432158 922432169
    0x40803071205070b04051506040c0c061d0601090203010e07020708101104080d0e0906010903020904080c0a0b070c110a0b03041407080a0f120c051f0f060321020102160f110613 77
    0x1fa02d503a900000c100641d00c4a0390300701c0c0130903441411032020600d0f40d080303600000381e401003a2103401091701d181841d14409a00c0652190b07404001808840c1e0002da45035005103c52008005403400c0103c40c58950101e40340d01109a503545d071f0002809502d220907500101051b409451810025580152030030161000d641d1007005402d000820079070081c0c3c4490309880c0c018200e139000b99650b40d14070f0182c0d44110805d0721281305103080000060f0824032003912440d01075580c3e061540f424907002407600c0b0340100041c403403c04408180101010001900d90094110030400a80104000000e0606050b900318174550f00070700000344c00340030070300c08245480c5106051080c02910001000c5400010b1200003c01030380024400d0080c034a0740d501c00400f2140001d400040f0a086c46e000c1c4811203040f07900886e00020844c1c02890084944003145952012600007503142c1100c0c035042d00014840c43c00d0041c01c031130940c6003400c24480f0034000410f42d200094141695000120030102c40c6062038400e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 922434658 1250 922433408 922433443
    0x1f18090302070501140403030e060f0313171207050a090b1305090903070201020d050a0216030b061905090118150e043008090a30020102040803071205070b0405 70
    0x800c1d520803803205d05014100e0801c02d00303040c00c40d602103400700e04159225910003424000e081000241000650041003440c1d0981c071100c04900d004000c014600e20741100c8000c0c184034141c102e40b1800c400e07030b50040c0d152820955984030880103455140c19500500c0b400e4101242d010350702d0010700c5060042d190215611000b540d1508881580e92140c600000c4c010780003c0078401c0203d0051000e40002c0865006031130340b08030a0843e15501000660080c0c4101c0700304002d0082c0c9060070582006d030400182d200210080c03d100200307401500c10310502d42c52905c0c4030005017684400340c0c403d41f400182520030140c500e50391401d66504910964055900001141c00480450f50288080c0190b5490030705120031003c07242010344806038003c0110b40c09028254641d800035403c00c06002da07003041d404c13a003649044482c107104080007542d0104429a841000144100075002050701c001e958054516840103111010841d000e01900328000c00d805240307000e10040280100c0c0c08494003840803803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 922435908 1250 922434658 922434673
    0x3d05040b13051f09060503070302040903140a03020403021008070801050111010e0f060703110a0903320f0c1c1b08070f050f010302070f06151a0c011805061f18090302 73
    0x13110040700c0d141d104242d815803003140c4c10001420181c228581c818041d051101c014040c4603454181d661190f081880040d07070000302030003145050b0034541c001c0b0320140350001d001d18118501414956041c06114103000e82c40c038404020302400d40004605d10040400e648a04801540e03e65695005035140340120b030500c0c040d07844144403103080c1d8202980f83e03507860300301c10b01e075845440c0c08107601d0750038919501c10091180c000701480c601404032242b00c00c000300070001045030030301d05090964002c0d510541080048e0365117880c541f02130207002a000051040440d40e038010054420350107a02c038148038081c003d0002842c10011030500d04464054810100014104d0011422032165190040c100c560780040c490104600b64810030520300503c045440032a141c845402c41800e00d010404440380c0300040140c5000002e0282442c0c811f0140400d01100d86c481da0341a480c1c200082074401170700e502c45e031408072841c21591400300030101c004a481e50030040c06002005030802140035809480b4803076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 922437158 1250 922435908 922435919
    0x19110a0503030304120c02040917030f0a110f0c07090510030506070f1b02010c170409060905060d030f020a0b0103230d12090314033d05040b13051f 65
    0x82144e104a41c043e8514040c1c0790703014000d4411180392941a40c000d51f0f544a90800210b0341da40300b114200c401102d403a200e14041e0828070184100038808484141801041c03c00e201c04442510100e8081040454998004500051030080c20703501c002d884506000a00940c01c070b052620380c041c0c074000d2054416980d9190001d466001081605100040c000c00e2242e0080c2c00b0419022551841450081104c014945a441c0c0c2c1e040c2c215804802c207400010100010252403055100800f00f074103081c045850b002c00000c50364020544040c00b84009892640a03481c800e010038240d060303115151200301e513124241a0f0038071003840f242041c020618008480c00240008000c09040d000d42e4030b1413034682c072300000940540000c10040b400e01c0b80203241c50f280700c0c1ca481d028510070001224813544440100300351405104420324403d5990440c500340601a00f0110001c5d4140d400544001c54a50050000301c1c4080080c3e2101c142041d142c9400e000a141140e00f02c220030206041c00000c0d16516070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 922438408 1250 922437158 922437163
    0x7050a0206070e1314010f1d2214030304060606230d020405031c091a041e080102160203010e0f06040b07051603020604060f230919110a0503 62
    0x10680002680c80900000e041610401d0700e2018408003a00c3c0801c09012100940c050710700c3c203010b841c1800602d02c018401c140014185400409620305020540d006840581d00c0c5801d000d8030703030700001001d03200c1401039407440798205000551002105d140d103008241001c0e200d41041d00d003141d03064100440003400500c02c0c500c640c1480b4403000040611411030590f1079007640464480c111a540034400014559030522088425000c0c400035141224800ea00060048102d030f04070000f1a440c211110a49644810585065030481c030fa47c23240c5907205000000d000441c5921040d02c640c000204c881c142140e12140300c024a100340e000f070007028240c0e41111f456460501000d1a1039004a000402043d941c2d589550000360740e040840c03500d075560008a00104e41c1410a80140c0d0004080c03208100851040401245043c441003208101512000319500e03000380d40c04180410784004a07011150501c540b460002031805090f0b401035103861314503212600c00000743e00c40c0009510001341d0b070070702 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 922439658 1250 922438408 922438417
    0x11a0306031504050723040507090f090207030e040c030b040506060918130203030403031d090c0711030c2d100917030903010f1407020a03050405010323040803010303080705 76
    0x1809441a244080400040e0b454024016240c9200f480c80008412184480101c20640c80d090701404c1c54455000380410b45102070324140810049541c20004165900300c2c0c030090f103403e0329015036501c4450804898901607403400f903a1091030711000c2642c8a81642c07000e076500c001a2814801d80e0780f2101000094001c0c0281d480e040404003028070360300c8519440c00d03640030a054102458030300d00c680202e407640d00560070071004112041014140f600e400d001d2072903580c3c0111051402e505e403803800b040c820300820000820621244500118541c0c0511041001c1d030406461449091200c180d200d02c004a901c2c05501001c0b0202140c0005060185c11890b042c03142c1d440345c02e0b01ca271808100140181d007004088156020a2005a115a074280900b2030603100c1d1071004210507000552016000b80081d00c00c10566101405003000070342c101040c0d07021a402400c00040c0d45042d1a4440d0700f0300d44509040d03094481d00c900700400c2000300009036041e81c0c040d9407022890350320110107a425104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 922440908 1250 922439658 922439671
    0x3020d080405030d091703070e03070e04030507020d06020d090c090b060f0f0a0c06050f0106030e0c090f09030702330c030403060b130905011b03060620070e0708011a03 74
    0x10410855082040340c0d0094501107100380c550710710140f46481c0f4132086c0c0e0015260800040c0200483c4034007481c0810403c00945200c80c081c2d8050f00707203503401404600c28010001d009070306a00802e414841e083d070640d0540502c005090014110501e4105080c0d190780c01110200e81c40d14080e039030700341050000d031000b000c00c2c030007081d20348025180e80c401c041d00000c11000420001c0000c0c040051158041c46004090001c454407555042000140c15a4189401c041c102ea1100841c41d04560311540010b410640c0c451450f18035488000e0701d41d085100350800650052602e00e4008102a400501a0813030079554030f440110400740d00440c10729100e003070922415640148010b0001c103a0680c0000005100117041144e11100c50541e08161144080155140d07591501c0c041d01c115000b803021030700354513140390070010705081c00c40c0074100016903000c41002c6c0c61001003100d08075008202d80c40c0646401031000c031325458000700c000e0a00800b405000040300c00b0140c0c0482e800075500a880c010344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 922442158 1250 922440908 922440913
    0x40b18030a12020702042009032415040e1204030b01051215060418152a081f1e0b0a2a150e060c030f0606071a100303020d080405 57
    0x840702e10340e0320040e403c03042e4180c2c0d00590342e43c00300d07504107010114644680034880034280c80b5560301041604018000ca8080c0c81e44141401c0c2c203844810090f81c0942c00080341010210050520012500800c1000301c009c1c0a4810041040c0303100c80d044015004507441f03084a01c00b00e030303200c4092004013424940b4080c504d9104102c282400e18000043c1a40300c000680000342c0e0462804011890402c0040b040d103a82d06030f0001c03510204090300440803060404422200d41010480c2590b44034800c1e40c070303040c0030800d130038021036092058040b12103510480c03104045083d41d01c4558410090b500081200b0805103002800603100100c903095503003541d2540c5448000c0c3e22030350308141e042480314903285465188861080002401c2e034800314035415203144009640302510300d442e8031b00000608002c00301e400900401c00110b280c142c246070b0010043e01c403151648080d1501c1d0918254404a2401050083d41009040010150260100c034040c0c0d0840700d50001200e81500c3c589410b0300d02606c140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 922443408 1250 922442158 922442177
    0x20c19120b070e21060a0c08010506090f060d2304020105181906030501062613080f0d0902131a04021e0d060905011505030708100e040b18030a 63
    0x390101039030799110710340e41481002c503214a0002002105210000d1903500e40e03540004141c03001c2000b4050f030140129000f0071100a40850280c0b10080511800c0d1142c00c000a042071503803682007003c1180c107005003e41342c896100c15810006807000d03150584a10012600ca03c4141042c41100b40c002c50301a1101d900d0200b031100480a100440c0c00d0322901f0030a00102c0354854640040031000420305030b6400192941000c000518025100d444161103420090b407124140c03140007203880d045461415800840d0721240760080c824001e5940c80001d0450204020811550540008000b54800c96541d0160780901d0400012280d03040c0362400380c000d124441804905003903006080b06001040c900c40782c15452100c200043d400701540c1c4401d15212602080109541d0168501404c0790100794995540c01b04001403e501000707207410200880400810098081c0001c46030140c4500c041014542c81d00d0f082554003500251004000c00b800a10504010140407064410b940312a41e03464299 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 922444658 1250 922443408 922443413
    0x360c0d051b25051f1d0709180b1602010f0e0a0336090b0607020102030d020f0702101e02011a130608060f1918020105031f06020c1912 59
    0x4124141c1a01c0b40904040b020040120f4001c02100c0702040124080080d52040c1103801070a880755030481851124401680d80c05203440400c00f02c05a601c01400001d0072001031440080050940030050901117000e0300348003003070012209011310740903079030001e020f0848003423210011903450500072180da420446042002901c03a0036640403448484005030700f4914444114000c1440d00141035a113031164840030400d215042c0036000100e00c0898015013080441d40010b5164480c001c5c0700107065500081030f1640b0052101540c80b40ca4010f032800c551a0b4000c9030180c021000002d402800d03e40060407511128414011130820195001141c49401200020300c14404400d1a45218841d01e07070f2008940d8400c20041c6611901d404c213100e445a00b40702b54466440000c40500c00001810040b17489042a0803404580f86c8c1a4207180c280e1f9a42d440142c0381c0d0402481c250107400da030721401c1000035a40e500042402d01d80d0001c81e030118481d4030240640108001c14861510701c82d085181c0b4102 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 922445908 1250 922444658 922444687
    0x6030f0c0703090312090512030403081b0709020a050703081f0501030b031212010e070305041e0807020a0e01140d020a060309020105211014360c0d051b 67
    0x245031007424032503030003a200c0e507402e1076001c1c42c5d10034840002c220141c1001540303000c000d922218054500650f2030310303080d511140a1442081e005403400102816601c00619003000180000e0102107001c6403548100c240c018a607900514090f0006019080460b030700b001000a00c0302c0076600052a03d00f018500310041d0040c0c1034030348074154580600e1098205525100c40141403604810010207150b60405881c0404c2700d00280051041601c4e00003040005681e428020035644941d458041c980c190f84d02d8001510321842000941041c02524009588501e80c03501c1416290404400d102d009080e50601c000c2214010000c4d500c145070300d00170081c4034000c1d8080c0e40c3c00d60041c03404614160b20407560218034285080f40e02d044d0034101082007803c500740031070140130701502e01c501c80d00d10b4204800188040340890110750002501201e0500c400001e41110a4216009044104500d03000d410340c584c9400c071410040300b0300c1c00c0c4400a180d45d101112004040c108041c402414284400c0c607171403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 922447158 1250 922445908 922445917
    0x601020303150906031015030c210f0807140601081903090317040f03030806010206150d0201120f14041209030506010303030b0d020d050303240f06070507211106030f0c 74
    0x19050300a01b0101c2a0082c107a008480141082c071248429181c9180743c207030f41807500f070b40c0100d0720b0940700d400410400072007201c1000c805070440011004a14030342001860f620801c4401810340c0c1084103808481e04022070740c14101c40c0c2200a0781c051035014140513410304002d110048c00511188000d000180c0e140c800740c0c18a1220341012420140c80d0b080360594216181c0040e800300d4010070800c1019030b810401035900031441e0f001915000f1000e004030f8560070301d1280080c10301c00201c401c4d005000060380117204d8805605000d100040040d50707482c4800e94159020b64104100007052006940600046421285d110000304101da103592021001012f0030002c1c1680001840d840f000940c5d94100206800381c00382d406966281002201110b4516803800c2c101e1140c45491158002503844500300c0d0724052058480303a0b0f40724014908035090100b42c1c1c1003c001880748180300d4001d40401da00b8840c0c0c152090101a80580642081143c0b41c00103c0da1411400306000015442002404c00750 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 922448408 1250 922447158 922447171
    0x100f080d050c0c030f1c031e020703030f150f050603011a0c1911180c090f0406080604080a0f030203100b090111011d07090e15100b0d050f06010203031509 68
    0x2912010f9010300040e0801c664101858140da01403c4041341d41d940364084a01c3c00c10203030904200d03035809080e0481a46000000e41280e1a03800706041092502980040381640004041004075104021036040341d04d12600600d0458540b5900100f80350070540c0c100ea042c1e175609000104c2915024810f25410307800710b40c40c40028001c1c40700c5801ea08140302040600380303201c3c101c990b104194000a01050703010549602506050750002e00070b1019902c0300b01d42c03100f02c05072003000c5011501d20109003d840d040d44a1203c0d481a10300300814891500041c00005074030fa6940c020311300469104405038081510801501d002d12102000300c00016001800d5030503043c1000485401e19108040c2107684c18011609685180c0e010714181c0b520034032102000d0000840c0400c0350941000d0400c1d07403008034050820b40b109022010400d0301100550b910f00503c001d60106039540d0314440188050705007610310209081716000410255070011060720f22a40d502d11941845207000020000070300c8002c2d004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 922449658 1250 922448408 922448413
    0x70905060f0913170406030b040c082202090f071421100b030a0605041112040204020318060112030e0406030209070c1b080a120504030c1e0b12100f080d050c 69
    0x180310010340c3d070303204c01c68441c50781403407090710740c1d141001c09016658509140c92084d07103052040602580c0291405d904541114540c7c1503104142040c088002d00c00500603500022071300c1000b0f2555003003400c45c1e209004c542e803040c1c111508001c007007109008058bc802c40c1d11114410070f1001481c000c005a90041c8514502044a0b0303427214081940d620580f103501c9907071313100c075000d101034140381c028048110080e08a071458000c0e8402072a20312100640000e02c116000400b04016100c40a04074070307100e42584c242c6820f56900c41090300300008841c0c0072400b24400390954000742c9013512440044030740160020b100743c2d0f2421800c9889a51121007110705070882c140704c458044125910b2005405024020f100e0b40301c407400d200c04801c440394261010032000b000248002040c0c1c00000048030001000b10301900001008603a882109400248000c030010071001400852038161328000c00440132001426500c4804051806a15001d40d440b81c5e44008034039100035206100031320484500605 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 922450908 1250 922449658 922449691
    0x403290f0903090607290c0a050d06080102040f09050603030f03010605070204090b07020c0337050703050a0803040618031413170102130b0403230a060501030506010602070905060f09 80
    0x954982c012171000c0c1d032800342d4a01014441d5016810034111820402c000a44602e01003604001c540301c1e51004500b0090003203201c85c00300d006a00f10310040d00b4805c000355152619a40f040c420a0324034446c001c075103401c040c00b00d60781d0b00b0044100c4038a032001c0c070a41451030303003001e00030f41d00d0341d00056003280c0103a56a040d00780810b030401542401030358560702814030041840f041500d46030b480b00e000c1c03250300c00c4464807040c2c1c140f65040860040181c0c0521944100403401e00c181031a640d03034000350403405038031800410400402d00661180f4410341041058800184004421601382d0f200100495400b1140006140c030100103400d01c5401c0e200120001e64440010101085601016004d540c1d0041408110050940040c00190040031007450616103141c035074101c2003101d240c0d40c1180c442030110205281030140209140c05030410418030595170350340780043d9510424811200180603070384022413001842d014080c00b0b540010041c6486001e51000c00c80b0380e8034060100300e00180640d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 922452158 1250 922450908 922450927
    0xd020a06030608010c0806030a0b040302070b030c0a11061b0d1e0c031407080705030403030e03030702100f2f042d0f030f060c020c150403290f0903 65
    0x1000440a0010380e034010440e03901d4805044c0c01d442c0002e2800302030040c01e60410101e502c2c005412884545c0101c0344c0d03225915182800e03424080d0580101c042c9400010400515000c40d07c01403140c4ca51a54030f00b029a100140080d0302c2d08016140d40100e804e151050600082e1010003030011044500d0002485800e2680c004401161400d002c1d607015480e2102d20f45000c1c3c040c0f04c1c42c002e40c0d40d0580c1c5958145440c0c0c0d001002c40c42c0c024034071400c0c01804004036082c14031940c02040004403030700460755030317091610380603648910001c0071001987c1452440440380010340070700c80c5000707a510101c00300b5900131145c451312161000b01442d00090180000a050320b43c1e242c01e8500b82c0d240551403a480030b1400c203030a449189540040a0024640703608000103680901d03140c4240d40c001d50001707000000180100e09050803880c0103640100d5440c40b444e10b40560b10002d004592180a0800c1d14043c40d400e449410034a80c54410010188040000c55002c0307025460743c0d010507283e00781d030714058015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 922453408 1250 922452158 922452169
    0xf041e080c0109110f0307051822030806040e0f0703200339010518030c10030c02010e240703060902040e01051c051c0203160302060615180f0d02 64
    0x18103543c4d00130128100d03451814000c40b40c000c61041540500840e43c03c1c180850084160048141d40d44038120300003c0c01d4610070390b041d618004d406142d980528005060090201c2c800342c4286204600d4200790b445620000160088c501e0700f0800580185841c649456405102c1e4043c1d105020b8000c44004201c0e0340e09000100c2c402c43c034040b00010708042c00f02034004160b038583d0380a018441113419841181e0704041620908142d61204c51080d00980c80801d007010700d01800690041c0030500140d00c0c03140c05402505101c5800d5000300070140100042565405510580040341d1103220341c000420026540c00d030303520040c43e080101c0c00c903544008a00803030f88184d03c80301c12511075200511661400e02d2480d500d0820411898000d007030702d6140c0365200c4c10300003422a2003003c29a54500c1c002e00a0050301c061400c00c10161864602130f08010b91240c0048800707620440c8102d1403046181180300503500070645c0500c02d0b80c0303c5c074913020900007001211212103600228000500740141c1e0796 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 922454658 1250 922453408 922453421
    0x311011b181505030421020c220e06062d060a02031b071802090a14010c1514010515030c030709080a0c062a020603061203030117060f041e080c01 64
    0xe580c1c1c00ea40785050306200100032291071103680f45c00207400350701c2c4510784e00080d444035611003211600d003100c0916a00407100600800270341c29450600c401c2c1c0e84a04004903025101d0481a10f072941034211007600181048030103501d02032030b00303000708000c0c0351801c061010300501d280c540116441e01d44c4a4108102d809404100304541d0740c0170490500000c2c00d00c2d1003821072420798580a6003401d140000081400d1014041c07034441c0c40c480404207a440e84203404444545400940c2900c0d184481180c4d00040d0111210059800c0c506100002e62428840f00c0780c00c06080c2e11031b10504545450110402c90f80c005001201004030107040811341c0107040c0041d0a90301d20030030414178010b240200160850807124215041c40c9100c03440080100c1d0030800c02c54103503604642c100c0d80c82c0c1e1500001402c5156181044d45244004800031036540e0506485100b000785400440301160340c1c0311031100400008907001401c2c01c6408440c010134031104032652000038820f943c0c80d03091124207401a401c5811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 922455908 1250 922454658 922454699
    0x302070f0b04020a090c0807210c0801090c050c1f09081b0c060301050f0f0406091d2505100e091e10051f09050415030311011b18 57
    0x1d01002d0008610304810035030700030150040c06100b960b4581b480685180f81c014840400d01004042541c4454003002d40c003a94629002410403008a03c03900090504c0000d028006019182a0a00702418090400e40d0040e10741d04004242492020106841c01c0c3d1500070f1014034280c841a07801c000503580c00141210303040f201036a41112008048007450404160b205900920040005010320707101c8010841680109449010400a000b40420001d03c0640d214000c4689003401c500d00100310007120070000b40e0b09070110b446161841d803003460750030342c000300b0300000070751903c01000b943c2007400c004c40e100305103828049511400700d0042032420130b0496110110700c50300d103425402d4070241c4514039001044018003480041c100008192086003504520090310300480d4011142407140c0010b00207018098414020140f526854040c07040f080c0c00205c0104840000b513242c0700b001445060301c0440203540782007900301402e906a4001c2e051101e0011155040d05c030120703482e00c4000c0c100b070a100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 922457158 1250 922455908 922455923
    0xc08160317060f030c01030905030c250911031b1c020306040c05070b04082206090509061215060402070c080a0b06061905090d06050403092301050f09010302070f 71
    0xa40080351045801c01024244540546034040310203880008135848050380178200010240e0083c01c0c010700c1d500855140e010329109810360a80c0b0544484484a0074600c1c05400d00b00c001d40307a04002e001d440d2851680784080e0001d000040328845120f820016545010009d0f0b80b400c150b98a0808001e02400d02c056019600001446004e042c030b4822003075054018604a401c160f4265600843c0800280c400742580c50081401a0809003450408001318a041e0041050540c2e070030003e000400544240e40c030a103030b00000212a410900820442c4021000142c111900b4180c42c00a0701440941500d800903828042500003c0e26a50450043d240f0740c2d00501c01c50b2102c1c40d200d123202a005146600540041c0b08041130521107a0850740080c1c903c2c141503446d80c0e44070002c95441c0d140d84c000a41160b080105000038540c100f032418086c0c8800001d0490f286e00e8640c0d42030044aa006501d50000d1003c01941100c030b42000003405940d041450007514041c0b143d00c0c0d031003031041004419280341 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 922458408 1250 922457158 922457177
    0x703171602010f11012c0a05030702060d0b091f06050c0c0405091f02180f091501020a0602030c0909060103020f2208072301032703230406180b0a0c081603 68
    0x1400300d107506c2862107080c0001400c0c10405565019241c2c010480024002d00012458540f1034025030007402030380c0d0000e0400800340c500300000054084154204140d2503601c654042103043c4901c00310b45500d17002400030105010884148001070200800703070741c514011040c003045030b100c00600e4000008140200036071910388085610485104003484944262420300c3c0110403034890403c043d5005286020b84241d09140c880140e0400d603c00e103000f816248004104000604400f01802d44d01a06864403092a5500e20040d8100d106488901031482c80500c00340c0c0381d42d046800002240c1d64000e0f140b03001c007a40c45118926091080d00000030b0315035a00300c20a440f0262072410311103503c00740780c02c1c4880704be0f1b030080c8056920990309580c1c0381e5000e044208141401040d20b0144401c0e407200c4140e06c520904445440c0b82c1182c0906130005088025810b440d40ba0314200106030f40f20111040d1421184110030b0702c00c03110403a41292025400e012505c0035005024000724010f0203a210702205 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 922459658 1250 922458408 922458461
    0xa120c0504060f17180c271306050403271a0d02070611041a0301050a0b090d0b070f0f0203072a030c06020606010306080102030f01061101060f080703171602010f1101 73
    0x8050306d00d5030b414090034000d61150012250440340c1c106d9583c02c5400359442d0348610386152100b00717600001501850824040c0000c0540c0030344545c80781d203010300b070502c41c101010707620b035900304c0c900c2c8640c0c06200903040c00701d1801100c0300c00422010a0307010006183c03040f155110740588005590821080402140c1001502c005c41126501409078054092941d13040100060354144d540c01343c89072812000c03891300000c3c0c5403e1b240054060f00301480300c04600c0d16a00080c09d01d002800c0c8000000c3e06070720100a03c90001040d540d9941d03010f2803064801c2c510742101c080340550380d23900c480c0003040580d00101003244c2814140203019a0703406084d461070300c500054150f800701c1d40600c4503030307204104000f440900c0703018840c1076810341e20b030010900d9461810603001d055660000c2c400e0300200c1700700190040d00000d4100890780314090340c03104803d0364015145940601d0020081205a400b0310740300543c401c2140951345601d5040154002000700c3d00309003150107100c01e4922922071003100511 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 922460908 1250 922459658 922459663
    0x60314150f19030c1212050306131407020106080a03080402101404030c08061303050915211501020a050a290a0905010e0d0c030c02040b150a120c0504060f1718 70
    0x40c1216140500042d0403546d0740b1009520560400c00401001101040141c0c0d2804c8001c440184208024414111380d16a5141d018000b550400050761802100007880907004c104403070700d90b4154507484070700c1e03450347c007440071000071514800d0402c10a0b01901503a1080304c0058000b0318094140400c4450805a409250981c0902880d005502110409002a50110469501c9241914082e104448544007904507000b55181e680c994a040384402c2c80350f03019031b48d04078806e4003950811210404c0c00001a6120341c0a124050300c150012800140442d450340c80b100c008880b1055043c0b00c099481d100441006815036216041c107445001c020180301c0d090050312000003510001c1c01044008460240c441d440440c002428004a61201c605655980d40b150214502c01307080d0584044080c0800007940d80305014000c085001c0c020020201c480510515060001070703180c00c0e2500342404070944840e0103010350b1204000d46548048041002d0b403c0b500e00501e118040b400ba600c0b18011034a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 922462158 1250 922460908 922460933
    0x1b080c06040b190e040e0d0305010e060d02010f021f061805010b1c09060c0e01090803040308090d021c23160b0703050f0a0e0901060314150f1903 64
    0xe12940c0140014401c1c1d0300014100c07000210b8446a6480078222031109540096204034500e52103490840390540c1e81c04042241c04c200302056504003e26a00c40c04070203c2d0725415100703540c00613403242046e801940245e200415400950049401110b00508111603a00b4004042000180c845500b003190002d00740c2984a40044944180041d60601e80001da00c0c1c010982d0002e0b107000c0d10f0001c864400300b10750007401041d0704490184036080071244003900c44002c030a07040d40010081040060b01000c04000e0764240c952000c4c100e464601c0480c00c010413512421000da80c000e01d090710480d4000010020307070545d28401c00c44003044081100c40100e0071078910030805800c1e040b250301d81a00204400750101560544844503894540e241400c907414000c081c4500b540c6100060070380078184c0c0192002d00c0c40a0b0486020705540e0700d90404801761003203a11070030039428400020540f40e40c0e0403161103052840203401466001e50010001d006400c40144220441c0d1410300144140f100c02c240740c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 922463408 1250 922462158 922462183
    0xa0501020c13150b040305011d1b0603040614070305040b060406030b010e09031201091e0c0f230a030504050f0a1707061107080c0d030515090c04031b08 67
    0x109980901d003000314a8107070741c40055603815903491615401c105004a42500900859201d4903219920f80c90040c1c0204802c1800715486140f5402002290b1000551904006034600c103030301210981d0b20501c506600081d104031206a12281149418525003c00510605a0b95008030705c504040c20012108040500002d0069060200c03d102150408891a04440303c10a0f44002580c0b503c5000382540141c201c0000c00140740c1000141c1d11710f454005101044480210f45020b418184510341121080c40e21000822951440d41c049180684601d240560125516a5075454890340320302041d0701240c000e102203a0381d08244806c3c80010405000d0390040e240007001c8034140741d1107200803621455458024801d00080e00c0080200d00d4200d5610300c610400c0043d00d440d49441d040343e060700b01030000d004034840d810424182174420300480c0e00443c04460748520101405050200100b001010054150005c110010002e520900d031581d486c00c40806070760030a8100300b05581003040703c5012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 922464658 1250 922463408 922463413
    0x60c100b0411071e05030a08040b090106031a0601120501060c030e0604050d0b0403050c06100806100608010909030306031e051618020702180f01141c0303020f0403140304050a050102 80
    0x107844215205000c595081c4d8200c2c4e1002481400900c003001c0c0e00200301802040c90101285c990107190b00031058030b0041c0c2c030803035810380141c0d2044801030898213544405010180000b68416601c42d24020040c0c000d45d06142c481c1c0380c080000501011b960302a4000b100050010440900f459401080d40c08810f00450b421480c0c5460180000c4d003042c1c1d0010090300d001c40d0b1001080415000b1821680f0214030a02620800e16084122004a000d940b194140380c0c000c460000e001c06002c8094001622900c0c0c0b20401c069023030850b00c90050882d44402c505040d03a40b000400440c00032030351440b80c84480070201c0303100c600030302d8464106100c1904110702060040e00a00080c00701c002500710000c01041c00503254003587c000207103041c40025941206120342414810312141c200b2120781610000c002041640150600f0311848a070044083c1c40c1146030b0806400000713109400626070052914001410607849403160f450541014000c688640d10025040040d030400e04841c1c030042c5003d001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 922465908 1250 922464658 922464671
    0x4060801060e010e1305010c080121030c0803060a081c0906050301060801120206250c06090506030619083004050d1202101109030f120d0e030702060c100b04 69
    0x2c01108000107000319481004043d0000b40c05a0b905007010300e0702c6400034024000c080c20781c1c4020701510001c1c040c107000f042c1886261900c0795030441460381d0855040d96151f01d040700584a0650681014000c02da00c06a01440061032401c100b20304022860391a9441d80039100804000d0071445190340483e090000c02d0004002036030700000000e044480312099040e80340c0581c4000b8626206540c4000412080c801c072005221219590b004402446034407496129503e8100940b42c00546100d8960310401c10030001d2400c0c01e01c451401c810122110203440c119407110034860505242d8400e114080316560421070000245000910404000100f02c515050408002c1141618029800b4081000c10781c462500c076031081210490407083c140b0104003a18501007442ca4981c0030040852180c8900303e2050705600c400305840d205128040c4002e032030300015501820240069003243c004900013803003c80007684456000345046012140608106004058148110381a60f500c80740038514151 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 922467158 1250 922465908 922465919
    0x2a010908070909060b101d031614030a0c0e0702070f0f03080703090905010f0f090203090312070c170c19020303250f0602070c09020f04050f1f020c0406080106 70
    0x800105407001141d0110303070f025903801e010f07025103490514a90000d0250500720400c40e071144901030003030010350411029078940d4003015a40c0161070090014038004c504100103040700b408500343c4003a400340c10f81742010320710b80780c1070180b10040e884000c403c1d800c0c0e0100864a5814892200500001c5091061103800d00745e00600d8582c560100810500000a2080c20725000e03142000c001d00d2491418485580c41d408072401d0301d00507204490481c8142840804c3c84001030003503910a40444000b58240903224080c00241200039118100348159481c0b1400031230000800e066442001c1d045507a695001e0079091440d03c260fa01034101c13214580b0040400581c0c0100c201d50203034445000c0e1031251952045070a95003200364400038200d40011040400b040282c1e0082e000480c0211540c0e03420565660020041c0d1140064000b0700c640d0801041c0701d90b00e000e0044244008015201440202c1030311034218a000b082031740100540d00c44003c0b0649403a150181d1000360554500900200c0e1600c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 922468408 1250 922467158 922467163
    0xc050d03091d010609031203090b0108010c020d02030c0c0603060d08120f0106020f0d0f0302120a06060201061509121104020d1a151e1314040c05070b0402212a010908 73
    0x340401410743c20b01904c8042628800d409c6411102e401107412049c03542e4030341081d8028225074070198094007c602d00103141038000300c2a130300406900d0002d00b03a10301407941002450b510003001d8550008043d500500801e8140010b0013100041c02c450300396074240004a4000ca00d4160b005a04552050030b85460f03450000c6407400c5661610b042003401140e0401050307000e07001d001c0d034404072406840200f091101e100e030000800c0f90100e40081000544a2106194218030002c600c004200c802c1d40030000c080d0b048594612103400340590181c500391450015040e0780c4560b0741c02104640703da941c011000c03858400040c6c3d0030700444000300c00900d40b118012040c01200f1048200348404c90380324a0311186542110b90010100d4412244103480e0b02c2d44400340350030010a540036030b16100c055003900340980100c1d40c0c201d801039450b0009540d03943c204400e0180c2410040401d030785644518501c031350100031420000300303400c0500d81c10fa552503001086041207040c5680c10051981006c00a00702d02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 922469658 1250 922468408 922468427
    0x1903021e130c0203091306081e03071a1005010504050d06021602060f04031e0c1202030a08030115020c03011a01180b0a11160806010b070c050d03091d0106 68
    0x2404440305030121100024840c1c104050890180340c101180c100c04168048018482444101c540c9604007882c43d00e03400848210f401242029800442d030a01c480d203840720139003100640d1030110fa03e0800310303681340c50305040d0000c0400c42d100c2c1810244001c0e0116036003d240030f0903007131804038245442e00e4001400f043c0c66142c0a000140d00081036000d5403584c000d120115034001c0e122503920300c0002c031000a44d038410310059030364400700124600c680000c203100300d8686802200c03010003181070400d45443c50700e00c10383c100c0c1e0511030200d0740000983c945c0d000e1402485415031142c1f0030004208042c5c140403200c000c4c18400c6c1d140260342a8610000017403030030304081c00e192181043c90b00070344201c2e0400881e0030000000c1e1002c51780c8444994001c8000c0c0780110020103484070002440311480580c1d0b2140030f0491b59400a00047c400f01c9054400b80200d640a580c003044115034800100e600c0365035a0b0400c0d40010480c440a00c0142200000b01c807050001d500007168642c54454001c00d075401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 922470908 1250 922469658 922469689
    0x17040f1d19090f120804021903050c060f090901170d0512011e1a0406110604050d0e01021006090510050a030c050409060f050f090f1203011404091203020306190302 72
    0x41c2c034202e100c140101141071a0100341c1c4084443c0100410540150000c0c0045400301c2c814100c190b000c0d03040000640040e81102d62000040c55902009801c10807a9005a00180040340003400030714030340e51381c58111500a2038010304410900740502c81290514a03003030038403020302904100c4004054030394980300741110400700c0f4480c080000017040d51003034100c0c0c1d80010746580c0300c400001e90000111004101f01c0310251158185080e01d4500c564446000300c8010301710742c01c454004c0605a004007145c145900052050310105100c0341d2003c0204c1c1c2c91500100c01280d42c3d0700030060a40800701500002d40812a140305c00c01c0d14517642c5088020a501500e80902d480300c045008000d40350300040e101103e0a1414421841d0000f02414400c0c0304035040c20151296104500580c5800b240c0d200c034200c070700b5501e5440c6a0a00301032411362200e003030909800541c0c070701d941c03004100062142c40d0340c0d03000c694000d81e0380d04003d001c000021109500c0d00010701e41c1d0400030401a525100c0c48660001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 922472158 1250 922470908 922470911
    0x608090f1002130503100609050106080105092406040315110903030703110c0d1103120f0d1517060a1a0a180e0f1f060e07050717040f1d19 61
    0x190340150107003c4900540c4110303054441c10010348541c040f1034000d03105850b80c0384000c010b207a1782c6507001c0ba0501030a01c94142c00100b00e4000c47c0f1004070750901b503e05080041648030480c113002d000308607030368420782c0140c0f00b0407800814012284224001e40ca640d1243c5002982000c0580002946070f10039458005e05101108152090291007400400c41e1001c004002d05255402800c1c00c161707105a0001040c828040c01814030702c40e503035400076a0ae90b11244290315042840540908005202100b220050307100c00001c00a001010940c4140e6000c804c0e1001d402030742040701c00d06081d1510642c082020312102c0422150b2502e81901d44800c44100c520741c070f100300300c460071a100108000780d00f541c1e1030300070600c200541c0c2c500000c9080070f1050029040003600303504130b81c100c00c40d005ca01840c0d820340881c0700404c0c00184110040c0480c24010100c096204051803030f6146140e20a1303200030342c00c00110f002001140c110150014100c0120312040303001d4681407440d01c030600010b025019034203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 922473408 1250 922472158 922472167
    0x6090e0601150e03070b070317010608060d061e061a0301030803071b0203070e090c010c050303151804060b0a0b0a02070b0c0c09011805090a050d0f0e190608090f1002 73
    0x2c5100e808540040704015050b911075640701c0b41d50782d10320f50000400354042a4950105002e02e1801c20075a0b049039000d503070381140303515050204061040001c005a405070b4a60074890030400725002c1040007140000f03c000795052030807113561961141c420b45051041300500040010035201001c40340c4c071071020310b0041c512905001c0c1540c0c6c07141080601039010f119242d80400d961114040340b07401444900126034800482c640115450400b11800804d5a001800403a6038440049030303040c0507942c01048c0f141d154582810302011500b01303c9050350790720b445807840350717050074442c00c680040d10942c04480e18005d0708240c0a5610925172140e000c12440001d0f490f10a0b0106104081100d00300505000350b95a65000b20b10240b080744030f06207426441c100100740411400180864030701d600070003031f0211304051002a82d00100019941043c0170340400c0c15080b40d40c1e0b840700310200d441885004d40c030842c20540020305040009080d92000ea2000c4d080251700c030400500010340f0110000c0240e5035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 922474658 1250 922473408 922473449
    0x412030903110f0a11060f070818120a0b1b1803070506071103120c060a051e0a02070b0f13020f030106030503040602240c0d0504050a0b09030c0106090e0601 69
    0x100b4502c0c0000c075400781c10460034600304041082e000140c020b01028020390340c0e00003000146c2c402e00321b031403a2803130f010040c020015003403e002d80008006a060300c14025000700100e14a04e0a284240b00d090304071660703001c1000051070f0792603001210a1b0030718140a940c03144200f40f0703201c0c1808d1f10b200620f40c204502403690f404c0025501500c0b0191100352540c200303142c04020203400c40c400901c02d008081082c400c00c5a008140e660100a5100a084540f03520146500400c030203010100c20116404441c3d88281c504440c2174024003031241c00582d601c0a0f0700b009043c1d010040c01000508000d441440032030140410b00c1c600740c1d0b804480c0341d440300750f1a4000038014400ea600003001c501011030300050207600815540c0720400d4110007070034208040c483e9140400801c640d41440b2040500035a05100b80d9903114503402841502212a154807e80b40d0000f40c40e001c85401c402d55000090301402400d0a000c0d038030043c5255541484644501c403c00e58654405006024070f2446148841c0e25 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 922475908 1250 922474658 922474667
    0x1080327040e2a0f10180306020f040801140f07030c0c05190c080d050f0705030c011103010504060902090307050d08040906060c0605090f06010b0a170a020408060606030412030903 79
    0x10390103030302c0c080310100480100615522010f50b521140004030300403141c0745500306050000311001d401000c80d8640340c600c0c0c9041e030328400b26580400c20020a400c0c00300010700e02d41700a000600080341d81d40e4403607160614990a50300d01d0706c4110304445060081c0032450b15030400e043c0d000310071170502190000f000c1000315101c1030344882c068803034810042d922150389500401e403808907002d95141110a078030740d0b0606581d202508103040000704208148201c0030004400b40c482c2510403401d40303141c8484003d40d01d00b95212a100c86090110001c0100b000380b0342881403900420b5180d0f0150b040c0845800000e8503124140304a602030000f07440114200036807402100d0140c600c100b020000b568461a00408010540c2004c0780c040d0700d0800170500078031002075003121101505e001046aa801d02104000940244071980f051001d00c000304100c04c0000c0301d040d446200071010041e2110300d08000309180007805400140502c104009200104a4805030404070000f141000f00b46059103103021039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 922477158 1250 922475908 922475921
    0x108090c0901030632060919020309010e061e06040203060a0b042301111c050c010606021605040902030a200604030b0402010e0307180e01150b070b0108032704 70
    0x2030740700241800110030412070f0751181c2582e04102440c3c42810719a95a03880b001090400229030f00e11468001903014540182041d82c8040421031041445915a01d00c034283d800c1528280340701e075100d007000d10761000c04010240c0d00809910310701d1100003034551810000607001d40014000d036000400a14292540f000c150010700c00e440c03c55a4495a0f04451080912030349811940000c000f10410748540c458004250945d101e0005040a01141c0420b810310000c000569008e106050004510f4050280314100040215801500c078240e0381c0c000d0807400311099003045d88558a00740740c840240e00d0024074083c1460b4050b10b0306180036646600302c0180001090000d5200a002a0200401180d0841c0c54040c40c400c0c0c903203818131400041010303201e51960040030001e00c0c08080d5020b00100c02c0d000100b2a2404000021300520383c91603003148140b050300406000c8100060120400900400b2580101145c8014500f000c50080c01410350a030348040e010b416030520194506141c0d039690094 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 922478408 1250 922477158 922477183
    0x30303020f070813061d0901060305090a020418110d110d0f0b010b220b030a0f090605040c06080703060b030a0b062215110a030f020f0a050a110609010c02010809 71
    0x9500c44842141d41e54400c2d04c54043c142c00501c003062196184840700400c11001540105a56501d2782083c03004c50040100600c0f11003c0c0c401e006441340581c5903489142a03146105011070040b00c100e04001035082190500e5900810402442c400814a00041444050030494000c1c190845030f0614a1008290080140902c05420000200e900c180b00040c0718030103010f1801c0c010900c0c012803215000d44640300b440e1100c00c0c00c100081c0e241c41c050380b09510f08018081c4c005800343d1261140421500f08480c112800480c4180074054a81c100403030301c0d0712a840e840c003403181900f4010000f0060101801c0190360b1511161903078490365030b04081d940c100b0300101540c2c01040c910040c802e05210548034031080d030340e001c02080024030710400c40032840a25444c000c0001c10030554003140c0031150000b03030720114040e07200c03000a04141844034070340450250004050b1804107061100e00c03280c0d01c14045105482c20003801d5090390b00040208141038090800108650300c3d031090a091600300c2100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 922479658 1250 922478408 922478423
    0x4110102120c1c0309050c040c03140c0a110604051f0204031b0f050102010b0307210c0e1e04020102060403030c0e130e06010b0a1e0201110c030714060709030303020f07 74
    0x1411072800a0705040115007030258055072124083d05404403401d101d00980740740c201d1400d20340d0b1401d0541261112820501e8001040e003241061251100e0054541c981340c52400a00b8440c8954440070340c00c42485c0c4c3d00050291410130342d440e1640e49150521900b0f04640b00e5400e006030000540c1620015074004e4417162500f580c41181c04500c82c0140a8209142078056021409503c14882d500d9051000350041c03001900308403000507410a0030390001c8015800e0142000094907560250008000041c0c500a543c2040c89084100500305282e40103106400810000580c2e0700050700c4d0f40158150030700048040c0d20344011103a2640d404035080d0021003c0110032840e407a1607100c0d03c442c42d861400e550160b600c51560f480c440c0f1440d036401000070040008800c03442c00c40140805007510394000060700091404825602e6041180340000702e400102c0c843c0d05003e805410210a054003001030301e2545840c0001030012449030001a04041d4089164000c0551283c1282d01f101d8000c1c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 922480908 1250 922479658 922479667
    0x3110706030506101110051f0f230a051503011a030c0702090406090b0108150c0406140d090c090e0c030a0b07031a0d08070c1202100c050c090a0605270411010212 71
    0x904c013803c1c0c024502070b0520140e0301c08c0010340310070840c840d041561200c3d110000e0320468003203c0c010091001c45419440312a240300000c650b614550a0300d0002864031960b6102e6141240003440c200c0601d070000d007040380803c10810356502000c2103e0041d9812511245191540d0900d200106420030b0010029001180003241002e000100308014140041d800300c0f0790396032505928114001c2d40704980105141020401c04246040040c0a1040030040002114140c0d5200d100e2809003d0303114401e519983c11461038200701c144131680e100c88090b001170000b10313031321f58074004240f1000304900d040641d034006110445032000d48a80031190002c0c419181c0300321764241200030b9801504125202e154020f80094041000714000c60115001046140d8841d4000f00584a41801c0001202c040c000e180c400c0e0303403903981c203142c26020380e12007080058041e0901061004c401d811130102c04d01c2082c03070340c01200084401995564400c1d482030600300c0c0007001d200141d19002c0540d0b01408607000208 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 922482014 1106 922480908 922480921
    0x1a0109080d0c080705010f0f0e03090117060f060403061b1701030303110c100f05090a020604050f041b02010903180617220311070603050610111005 65
    0x6000fa8901203080d0303501c0342101c1c031061207004c100b5511141142ea071a1107205040c0358100f2440203520303203044540003070486e00c0e010b00041e0070418600000f0b00c0750748903424080c040071800340403503459946a2a1450180c0301000071400e028504420300c400e0b441c4a0051071042450b0700300011102d9007151800c4014101b002d141b41e000d03d00800c44040028020400801c0038406440c0000b400790040d500c54051f5403010709403185980c86503884002680d03a81040781d084950031200207a0b01c001e900080780c0034107680c55002d00b00086142900d454190103400c4001d0080c440d80d01c640c0031800500d514010412075008650009014242c924614500c845400750020b1801c0a05400e2882c000340015a8125191040f00014528210181e0310841041102d008c0c240c141428455460000c0201c0d128003c0034aa0101b080615509500b4016082c0181003200b5480303130f02800a860310a = true := by decide +kernel

theorem cover : BRFrame.Cov 922302158 922482014 := by
  have h0 := BRFrame.cov_init 922302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 922302158 ≤ n) (h2 : n < 922482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
