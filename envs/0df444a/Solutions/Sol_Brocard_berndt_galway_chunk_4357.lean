-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4357
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:21:37.774588+00:00
-- url     : https://prove2.me/submissions/229f27d0-d42a-4a54-9cea-ed146b03aab3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 783453237 ≤ n < 783633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 783454487 1250 783453237 783453247
    0x5090d08150907030513020a14040b180f04030905030d0f08090c0307030b04050a080f0c01060512030702090402190b03151909022206020a0215040b0d0f020c060c190e0105 75
    0xc1c003a070b01903900416a450000c6c801c907540e5000035094034584c0c122821030050502c0b5145541441e000d1514212000c5a0150303507030041d80c50722031006000a003084480c0304500045000d05018030150303400380030b000e0161417907080184000f6100100b18254940010b551200241d10540c0201da205080314004001d414640d1a541314800c0508014105503102e01640c0c4461000072038580003821541005520507132650002480c1d5800c58045030b00060240039141c00001c3d0800c000b108071401c00b0707812620240a07031214000301e059110b4654011401208082c00072600f120004040d40c410b0a80101f409c4c001c0c0440b03818030031002410a0a107002401c1141c3c01d00c2213283c103801800c60555003090300395070003880d001507400c0c1401c698403504c0542c0140c807400040d4100030329915000814440b00500e003a107003c4007400c0c2803080800001119550b804010194021501110f54114904044800908200c1442001580012191084102554204100c0c5401407503005080101616241c1c00c02d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 783455737 1250 783454487 783454501
    0xa0c06090f12093c1d0708010e060108150a0b0d050c0403030c080318070e0f180c010e03030d0f0204180506030619090c1716051e06070605090d081509 66
    0x511000180f1107054400300e01c1300d10300c20102d040c100c00146126080342c16812680007020900203c05080c2c68200301004006015600c0d020742000c1e040b070350030310b00090940d441e12484880b60780412401d80e40161803403000501d8025840c0540f00402c14000104440e450700b03440d00000f841980700017000315605142c0680402d03003403006103610900b0704506000680403190118204209600103000c0b90300b051041c0800060f045e501140c0c41680c0061805c03a140c3c5502c0080d50b11019086010304000f1b003d00380e01c496407414026074440c07a400e0b0f0018000e0b54405130070100650030600440f1003007000c040c04070001503101e02525004110142c05856151a0001c548602041d10320001207055100d0a92800007072201411400506020b01d418501660322032006050240c200407a500000482c442071109035203541c010141c001d15100038056003400c1501203403443c00791752009080b451901c0c041009202004c41d00300e0900155503283d5440d80e035608500c09500c02c3c581c3d44503800c498007800183e42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 783456987 1250 783455737 783455789
    0x250f02061e030405060a0b030d0c080a0c060608010912050406080103060504021f020d080106170f0403021f090c060f08130c05060c0c03071502030f0a0c06090f1209 72
    0x44411100c0040c81c0c44440d0228141d0603500a94084509500040c02c2100c0c044040c1b0403241990b900310040d01c03881070901401031160300e500c240581109000182c01c408180202a0005043d90210040c4441552200014000c02e0214415543c4204000103d031000c5d128101311010f8982a80364000c942e421511000c004100081040780c0103405102440e4070502c1c400b1441041d50350603402001129140f1b6001801c0b003506a211409000c03c02180d986c1c458251309046505c01025401000c2c030b80c1d07a60408910340b10300640d070307003142c3c104400c041061b802a68003c240220b0245001800c45039a4130400c40f400c10502059030001206440818280500010842c110354026404840d910703850300001402648030050180f03466204110041c3c90303003002d02161b0001d00e8055965031a20080ba00e019407284500302a008581c04005641000d450181c3c04161101d038001c00c081120080030f02d840210303020300d2a420349540e081c2e0b403160b00340248030345080c60543d102000340714590300368850500c44c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 783458237 1250 783456987 783456997
    0xa0c050612011e121b17030d0b030a12020f120306010c02010f030e010c03061a04080c0d0651180209061207110a0b0f040f0c030503250f0206 62
    0x1501d001d1a00c800100c00054126040b507413801000300840c50307521201c000c0b500c11400c1e80b0040c0c0c206c44019050501e02d07004401d94580e07115a00000c00c00440000009062903481c00000f42500b0b4850002e498490780050310b103002d40d01400031100c083d01010303542da96502044072054000f0307901d0803810300154454018480300080d00c1c2004106400030000041c255108004040002541c80301e08010304500040000f80e540c440c940101c5c6420b04021107252507105880c0141c0c02000028880d01c1041002e40c05861110903a13042d0103440f418045044d58210034084500050500c01d048510003d911b6100340c06c180040003507203001c068640303014030b00881c0400c2ba40b02c019540c01d01001d100e5407034100050100a000d01b181c0c0041d85000755000d001000d04180c0c0030100e03800124000300154940440981042008140b0741c6155a20300e0074501c103001e048170040810180b000e0000400c0000800b60440548001c0300c408001003840c258200026181c4003c1c044401c02c0c1002e0002d8100140140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 783459487 1250 783458237 783458279
    0x9051003020c0a2a2c0907121a150a0819120512101d0c0301030213020c0a05070302010306080f120a020703140307020913052a120a0c05061201 63
    0x100c42820441c1a40c4c1849440d800318403206071590b0a0810000000d0707420418108603c02c50405081400040b030b0f40d0030381409034410035520702ca641c10a01610a000c40340031207040b031b840c100c2c510300040201020f00b640f6a065004092111012a0030040420740da0809820544c8040b40360ba00da80b03034003180407003400f607200600031704000e020324095845459a00c02e50300091036640943c07522480070541e13581c80e400860100040c00070700074550803100c1101d0449404445042c0510003441403203009100305969010a4464110348800b04035001c07440d00201c0f4005d0701c0402c00d02d07558000190700c44203c0010030110707400407a9150030319028100070341605c014601c103c0d01841d480360f4500701c500e0030701c104900d216400403c201c000c40c03400714180b9512191402014511842e6643c40c2c41e41ca8100020881440818041c11100518684c001d40000000107004100c0390b4000301d034441d00c0b02d075000010f54510880d00000304103400c102c0112038000ca0001d40c915150780c81c0122612400c024016a6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 783460737 1250 783459487 783459533
    0xb06030c1909090603030c200d03030906021204060906050f190f060b040602060907050105040506040e0a110310061b0b04020d0c081b031b0603150105040b0a09051003020c0a 76
    0x4162805a40314404c00b85201e40c036000080885810500e0820511230358805030b410b52806122095226020910121a03050802040281503407a2810113401403525a10100c0b1407442004103121450300041c11403030248030104401d80798070404018030941255105520041c44010140282ca603911415103020420800200f00b911074603034006aa10652210005a02c00400d00ca011003042c46250014282401d0491805107080302265542c01680b08aa001c040340344001510255950401034040c0700c08003400c0e5072890300c0301303030140c45101e58041c440006080511081100042c3d140309050716030030045800e01c1e9600d40d8200682c280c110b400441d04204054000100b40c0010020060321030400028644603110140605203880420a40e050030305040440554842c0c98140c12079822000303072095420740200070401a03e07544600d901c0b004c01c4200c00194034542c6580300551200b036510855900c013141402d40320460580c00342c07524001042d0005041900014405011056260000c1000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 783461987 1250 783460737 783460739
    0x919050f15070b0109021207090302010c0605090f0105281503173f1009050720010b0108012c0402180702061006020a050312040f080304060603060b06030c1909 70
    0x2c050b40c150f02a480058126000b01d0701c0a0000d00303540603141d000d182c0f0b01d030071886030f4a15000200400c200c94009400d131540c40d80030400c400001d200b00c2d6043c1002c100248040d0501c5441010300d054048503400d40195091070450000711a8054a03044140d042007c260a40c110745402d100c4011044901541c4071041040f88003000c140e040f00e1b803025400b042c2a240e00c01d0b0f080c0c00100388500084405002c20344010030007503008404500c0c441030380c0c800e0b030000585030360342034094a0000c1d000350038464031460860000da00c10750540213415030780c40c00e0380e07125000c2c5d995514803000c924100b40d007940d600680c24020700390390003004e8940e03902c9400100900e00c8510f110200b602002c20036100040140c1000f020002c90000014082009010703034801003986210540701c55849014034030098458210002c081420700c06a515041d85641d0007025842d56820140740000c01061340b840308442003400c0440d02c400601c1c00e0f1040d0307842003801098581c640170f01000b800d1a00f0203084103013014000b0040e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 783463237 1250 783461987 783461993
    0x10507080f120a0f11030f16020c060f07060b1207060804082b05072a1a0f0a0e03040605090f0a0f0801020c010e07030c0b1c0c050919050f1507 63
    0x141e85000f0f40110074001820f108030034448050340c01d045000c60804104006020050b062803290a500202d00d144404690f503d040c000c81c2000030092540354007410114448802c46000c60042000038815001080541911424010044203503104c01e030f00d5400010b010844503000b2807031142c1c070901c1200e07058580154080307060302d500c4008980c400d46450079501d040300140360f0f00c01d04c0e400004605000382500001c0320034141c0251200010b07010000350040039010081a0400014161100030941d0090301e00003a020340d00004c100e03580c4011030705040c041e60030001d000c821901901c089640d820b00d044614002d010802e9408503400e07400c81c0300e0f6900090010018510340d4040d100b0b6400140c0d41e0082841d00a09403001d05a1015054200c02002c000040c6a02c140804036000c04003060b4562a036014101400c0300ca000700d0710922820314004d01c000580c030000901012404541704582651100c0300c0c3e0400203200e01895800c03018002c00c8864030b15000064001d5503091103c01850701d180e0307507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 783464487 1250 783463237 783463267
    0x1005150909040303020a180e06060a020102070f030216060f0c0809121c030c031505100c080c0a0b010603290a030204021c0506030a0b06041802041a031b010507080f 72
    0x1102500005d50104400208550104960740103c0441c054800c07c2414030001c0c1d4240f00d0702911180c4201c4001489540440c000e405982c00311781c001d42c00d0341d03420804d821b0103511045c40210507214102d40aa02059a83c0a141c132020501d05560b200210706495942c3c900745507005042e0f4503845140d0001d0403541d040204407100100c40303c4582c01c025052040c0c1d01806482c1201c1491091600b40040f4541d042d54114a0004035481180c440b400c0c01d5542c8020b03240c64109603800360041c40300164201b401140006c00302e030110304c190103c8110b6a80c91504800311010000d085040d5681c0260f42851403541f9096400c40440c010701c084505540c0b80e0008089a02600e01041440c0c07102c800000d94600e1803085d96808030080d0082c2c440c40089680d00f004030240105406c0c1b140355102032030302e09090700c0c0034001440e80d030181c03003044001040345240514400c8899060710a1040301081780c3c440d680c04e440103120b10350607100e060070402160381c2c02c80560009941c0d5040302000b40201e01028402c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 783465737 1250 783464487 783464491
    0xe0408070209252f250f090e0d0509060d05070504090204081b03010b011b08070c030308250207030809180c0316090f1809020604150e091005150909 65
    0x180c42e8a0595100e4143e0310748905030400c1c40701130540b4000000c0004e0403000c501a5201400c1100c04085991090005450b28419810407181034a4002011914440719440a404140b00da07041312415544044c0450b401d21407020040e8000200780940355610025404c00764200b030190901c541800c1e15810b600c402c80e089940000d203103501c0040400c0c56031341c002e1251002c243c0140c0c001d10514810400186c000d040041d82600b00c1c6540107021800d1005100a0b01e8000e030b400004101025500e0600420381c910540740350068103080801d0045003130340d807480103c0382c1d041c1d80c014203500e6195454de03403000d801102025811039140a403c1c1405040100d0b80c1d441440007000f05c07603c84c00d001240d004d084202e10030103024017006420074030010035000034240031118520801005180c240c104034014000515009400040100e800700d00d221002c070001d068500300e075480e0408000b036070003005a800020780c6c0040503009030480c14031581c1044000c0c0c803640000300351964600300213803010034844001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 783466987 1250 783465737 783465811
    0x11030d0216050907090b18061801080a09050606010c0f080d06030b0711030f0c100c020606011d1309081b160806100b220f09060e0408070209 62
    0x2141d0703040340c8003140003000409040103603400700103450702510282c14007070b450140c030391820000b050b4102100081540d030903107580042c22460b180c9155074403048210b03000c58605c90100b44500e0000d19201130390710551241c1e40d0449e008020076240c903001510351509809095903a59200700d800310104001c1e20040940450fa0000000c00364514101460b103158045d20040404c414500c400410724800070964410803001700c2c001e0380d1a034010b44942d14140301c0281425040d81841107160185401288491140d0400e0b21070442180400c50509010b2042c0003490744d00039080759aa98086485500406505108030841450181e1490b59402013501200f200e0030643c0c0200710681c005407102c0a04001003c12800901907400d1200d13400e4861803885c01980c0001c10041030b442c9402c0d514602c1d1014401040d0240210341e45c40c3c030207440500742c0c40c0c042d0b04109801c3c000009004892201c5440c8250742082410b400c08105500304020164050311101ca0307604110203000420901e1b8074403049241d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 783468237 1250 783466987 783466993
    0x16060204150f050a1e0c05011514041103191d060615036913080c0703080f22080d030e10050405070303020708032511030d02 55
    0x8078070240202410030320158941008810301c41c1c0b42e4500c0d0040c00009505c4030080b040342d42800406000c03105a248208090071560800d01011284030f40414550706a81407000014031030b000701e0003400251003a145c0441480c031001c00c009405070603215000b0040c840e0008021442007003154110f9480c1030714001201c21908643c061014a1600a030f5007140946510100390035854151a18a40345010300c0d1408000c0c080c1421a108004c25101150056458154120b0061600500c00074040d000798800761901030a5545e0a29401072240c08140300b1070030840304c50522032095807024120b41042c0d222640c60321030000c0c080000b495000260221003040c00d01680c031003414005000401d2122000b040040e2845081070048400200781d9981000590501140f03401c1444071142c508840401c150164510f040c080c4020802d002c0341c8041203034001d5080300c0703003951241031071078482c45640d46000b810720040903803218008030388110341c81690059000710880700d1040702085c24280e40186610040e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 783469487 1250 783468237 783468269
    0x30610030e0c12060108192d21080a06080c0d050304050d060c230f0a020313121b0b0703200a0308061503040203030304060504050a1b090e0a110616060204 68
    0x140d03042000b007a5000006001050031f807595200c2680842c1001c40604684100c0c814a00805041c200308a500f03a51258800d2914110b02406007006001102035174005025203011862055107801a007080e182c0f220083c110008001041000c5540009006ca501c0d00042c400015076645102200d9041401400041043c1254000041c55914207002c0044003454500d07030002c5100c006015101405500d80c0d103e030f03855a096405038a10300414114104d22807548030045003c14030a4130440300107219100000ca01d410003400112041628005d610307080c131040c00041c011901c80d2207410080c8140464844030300c1c010722541070804150340401e4000c1540501484141d08100040c212a076140409182c294281903000135242d100c00780015000644401c0440c0074080140304510049900c0110301902c5c0c50a607041410120461080140062800140e032005a8020079440301d040c1c0e1120f40c2c2021000100104202500440c8451000d50769451a420005040e44000c00240424958080082c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 783470737 1250 783469487 783469499
    0xa02040510020a1119090f0204060e10022104150c0528110301110a0305090d080601210b190e010b0909040b311106030610030e0c120601 60
    0xa005811003021580000306100c00306480b904402d132100e8046410340240b520754901c03c44221155048484001d140081803c0050b09903070085c42103c48545400d001c942d1008200002025050029000342c4c114128051940d040e03044282101c1c00841d45803070405444e6080f222090031000d009102243d20982d4040900c05e0400031144030521010590300540c16506444000c00c4950304001e15409040e096031002d03a4080d000346c901214000e042d03c0e111409120002c1c0909815101c03000ca50044041701c00e07034a482601c641e0700c10340060711000e841c035051001c942e44820608071079105181e03440012012640d10400e000b240c401d446040c919146040150034100100306920040c0301c2c0c2c0003040200c62503201d02c0c1d407444d03029400000d80440c9039071303540802900703046000e240c1c481800602d01501840c0c40420440032214000e02801000903016410700850344020b54007107a015035101e004070400d03880ba802156103a5451402d6800300c2c204000411a0a91000a25800d6070010001030020b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 783471987 1250 783470737 783470749
    0xc120207030314161b02030109050a050313090203070912063b030307140a03060801020a120e0705031c020c090109140a0204060c030e280f120b0a1e02030a020405 71
    0x402d0103003805444e030119518003c0c00c0000b000f15810420350b2040420010740d50294014514242c008064914206113884c0540c0c50f0b6005d2211036141d00301c04a0301150402c03461098034481d00c25a180c1700d090600300140c21048081005003180d0035500c9201c455405031401c1000010b8030202418101406080c0c60001c80000c0413038862803084d4010f000f04000140d0101401c101000d40c01c0303a20f540c0d141e050000b14040d102d25000b04442e980005031000c000c0d90b02a6006241d00342c0f1040402c9200040080a43c4404581c45115410381c00003001e0415038405000c0c098038002180120342c0710201d09804104a104d00340e001c203501075038400e2203108403020104d4051380030280100452030f081c10101e014142000307038038000e02000002084441c59071200301d84010300301100ea80555200000b00340800e01d007203640c0144c035540228001d00044e20b88581c3e550203900b0354011520082e40e030b22401603100911320350041c4000b4000e014110002030320380c4c3c8021400350041c2c20b0f016030717180d041905000c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 783473237 1250 783471987 783471991
    0x12060601110c0f061303080a0801210c031704030f08071a04080403080d0f0203040f0201030e151b07290709080a12020f0327090c030106030c120207030314 68
    0x206a810440d42c1c9034103507803000080300350003208030b600030340b596002d501a40381302c4001d03000104034680000d00d400c0c600303400986a038101d801d10b00b40000111103c80c03200d03001c191000c4000f40b2503900c906044c00000d00c009945400b040d800b420b503c0c1040d03a2a01c503480c5402207070304103444000c0b00103100003d00c41501415091540c21200000031030810340d89071011840f980c4800342224901084084170564142c021001004803c4020b6481e8106410003440900c1004001c034080392400b088039607050030100d4a6500a00c0035240d001c080d80d2184820002c1040984030f05010810401c80300740004e8041e0000d0002e400346050441141401c04403d40081070041c0284040c440750410412940c40c0004210795800e0388410b021850100d5080181e18206132108a04514080803521001c44a1015402d00900340c4000c07240030b9490300c00c014080c0d2a1826103005842070300c100018003130503001c0c2d004030380014003520b4a191000b035805402800c07a0031481c000c5000907214094400c501406c078490b15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 783474487 1250 783473237 783473267
    0x42315060a0912030201060e070f0906020c100507081e04080606011b11030c031911090601170c1e120f060120150a05090f0a0f0f1112060601 62
    0x70700d003070500d55000d000700040c0c2c03240f00180765000070700004051007900084020112600514024100180060608075000d0b040400040d001c041c000395181c40010401c094002c0074041101502900d1000ca9259010b04010b81e03940c4d0040000d4080490601c4100500b20001034200340c60382d040c090042c0c10243c0203010300b070400c080b401c42081082002c3c4003840095a0281406818000c100046410000b10200d615894020800d2201003864440842c40c2010311850803d440e0030303800020810380c4601690340a00244d02c0d542d20b070000408115411341c200081c034041d14101515000070308984002c5e445426250380000c1882048800015202a0014428070491103180b5200d00004c00400c4255001c4410000391003000004101c14004ca000c41c1203d068000000c1c58840d5980015140c00d4070a620240305403030030340405800104490a03065400700f0300c1c40404c1d009407a0000311140100041d5040c074103500c2d21151603a2182d2010100c102404040d00003840c10b03400140140c0d400d19030031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 783475737 1250 783474487 783474499
    0x605040501020304122303090a06020601241b06150e190209010908030f0304030e03030f0a030f0f0c020a020102010b0d051005070e0d060b0a0b0a08070c02042315 71
    0x5119681c2c0210944081e0780c40003800f80010308a9040c4050140d88508442c58014006902d480d0100d5010006103c0c1000654a0b000115a1a881240e0b251001d2141c05c48400080e40030815a0254100c0c51410a1b564030340744e001103000601640d0305590700f4030101c40203941c80035540c0030303039185100d01d200408400d80302c2c10251504049410384455a205441800c0750300090052083e801f610031080a0414a402c40307403a19055000c50340c0e10741c01650b041c0c0101380c603040c101c0200e190010458403a0241c5100483c00d00441e40b0040d405403c4000b0b692408548a00fa19003c426040c411000f441d80607900a020542e0b440c000a03085030f4244a03050b00441190010001090380000c400107440d03403015001405a6901030102c0b1a1514440003035406008030100e0302c14080c0c56002100c1c01d00301290300c82e4656030b0b03501c0307109050301c01c0030400004a20901c0005144a004090140702c6038005000410a40c503400040008298015921102c0c0266001031101c1c0307501c1b03540003444040d030688078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 783476987 1250 783475737 783475739
    0x3060507110d0f031b08641a01020f0a030503060f0406030818011d0910050405010b0a0909060b0403081303080a030207030206070e01080c07020117090313060504 71
    0x20050300c50002032084403e00c611640e40d4040c251080c2e10a41c0700c040500503582680c04a80d4000b0417038401501c0510f0032001582200c07402420240694054844520508106c00124048421820314004a511104119021700351804c1742c000d17642440d01040000000310342030841812200030400a41ca281103621091400140c1c03a40000e508400540605010740c40390b0f520000112604049a4030642050518134008100080c2d40d0140900c204492410348440c0314840c011030303440300f80105040c40200304002c00780142c00d1000707080c0c2c3c101d1484010605029216800304040e19001e0b03200d180c507802d000421406103a4001014005420990400c1c08042d107445007a00c0240100c2c000603150000001d0407906003c040c112500045030303c500c00c0ca4a4015040c4040c0080d00603000035405400b9900014036018855881d1a08800058440c0107560b29518100c006da6084070b00d04a05100314244048114419070f43c00c1441000750130010f50392801e050740e000c00c02c2221903125400b0300805000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 783478237 1250 783476987 783477017
    0x9150103150f09030f20011d070b09010504090504140d091a12070305220c091406132d0506030d1805040b010e060d06170a080d051e0f0103060507 64
    0x7814403104682d82c41c0049014002220500c110700f8202c1b6101c02d01c3d0b1a06034180144400112021054107021080e80c2c0340c0c580e5034050300c00b240304464030940018010001800701140c0c07a4000c80e0454000c460454500040d908514507068048a444011450050081101080846907110b07494042075a580c1070940ea4441c40c070110001030100403e25131180d0003d003020f030001c01554555044a0500e0b1500c14041c1444030b1004c0080c0190b031001c034200440100180c0008029600608000d4030411900c0c43e5403040d4001080d881c207140d507425885090045201610760752095a003411400001004e061000405241000901c5250244802c9001c0016911101c0c20582c4c00c03120280d401107103060900004031080d03c415082598032100c00304d9400104422a4008015a014010050004039000611079610340c83c0c51001000300000300010b0885840d180c01c0250001d40545100c1c075404151000004803410840d4447c0703c0f400c00d24010014013009000325078101500e41400010f98202c46 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 783479487 1250 783478237 783478247
    0x109110319152a0306080d080c0a08040503040b04030b01180e030301031b0b0403080c070618051c02030703080304050d18052709030901030614031509150103150f0903 73
    0x10110109940c405019001094901c107034107030240c420345400c51108264101030300071700250154001a11400d00d8041e600e030b0140062074080d1022100c0c40d810803642c104101c07041d0400070001c41e0701380000e200000301c1c452290042d2020b14030840d1020050340c10300140100c1d603188400c0c03070704c5803505103080c10040c2e14020041368190394105050030f545440100340355150b54805c0d80240300b82200000c1c0041400103010103800d9481184003900c80c0c01c3d940305401c4440c150701a40010b045486030f03504026500d40801c0c1c4407290745d02103503114071841c465000241000010342c000d035029900002040100306041c800e41e0449041c50510011200150503204600c1e05140035050103038681080401c404c0030f0803030b0741010301400b00200750b241d4500b050031140c594200300481c501017801c01c000031a00360343c1c0340034425030007101400134201141c1d20081e0744120308001c4c0030f07442d050058290302890140c507035015030301943c0600d401150303e90071082c1080441b81d900120320344a0b03240c0030480000030341c80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 783480737 1250 783479487 783479513
    0x30c06160b090309180a05090706090b0c01090203070602010203040302070f1401050306010507020a1518080d180e04030203071e05120f160c050a0807121b080109110319 74
    0x4885411002e684119a140c03640c0b06100c00350741d005101e010901e00b08040303544410302c0b800c82e040f010320180d20350146a0f691060315005110201b06d02d09000d104008150b0041d003084c0000b0000468444010740220f4180042c40d0403160050350000b04110501d48c040106400414850b11141c0c0000d160000440c2000d0074008224100100000418a40c0c0c1c49502a50f5070709800422520300c0a40e80c2c0c200c0502e21400000b6100030401140c4117804100440208104840c12080542501d07500070000301e9108034070300c42444180c2c0741e900c030120300c0c2e07001100340c40e1099219400443e5504035900b4208400300e80f540586400750341000e10400001c801103044100301a920040b40c2c1c07604815400096036001d00c001d100342e4403d1a2250f10300780f10b0005000070407540144c61118459444070180d43d00c4007420300803148041805400e8100282c244011648134540113800c1918140d00c0d110320a080d42e45441040d100280041c0060280d807805220220031a0070041c0c0703c480360320072030751401404002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 783481987 1250 783480737 783480743
    0xf05130f03082d090418021906030e01151712130f1a070201080c300c0403051c12020301090209030c1c0b091204080a0308010501181205101109030c0616 67
    0x2c40317401d42d071100b91410342c2a503031647c000c00c00301c00d01c4c0941e0050940c0440350b218000000e41460445490705a040c41800c041c121160007041100341005c02c2e441d24040c1003120f10165100d07001580b0b0007000c150000d400e40d500740611108a4500c2c0240402c221901500101b04180c01070300755502c2c0401440c2240c05655080c02c0c4001c0641d5066041281405211100c0011032200710140c60b2440110680c0900b50030b120312000c80a890703900d60701043e401240001404ca6005d542c20341901c402d201c0610080c0d07085e42ca400e100c0e110030750038038a050307030420b0348580100303900030920204515040c03003483c003e090309440d104c4802032410790110640e00010381c003801903070750fa0300820001e00f07051010220002550801503507642da5075800d0b59862018040c2134002440301e41c000b2481c2c1d0304c00c07080d551188403a411802034290030070135418483c0d0ba280342e084a49109890b00000292601e0140900c010150b08200c0e498800a100341030420410304402481410204401e241d0000105080070380190 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 783483237 1250 783481987 783481991
    0x15060f070f2102150708060d060e030406230f0d0b030714031e06010b0f0c03030f0711070e060609120a0506090d051312081204150c0e010f05130f03082d0904 69
    0x1200b0300423450070721041c0c80c0034000ca0700348100c200e0303083c800100800071158283d94020f1030881c41710504014581c80000408159420094150804540f1010b041c2c13001912a001804040c4a00024a4010954007000d40064011009070341071400b030001c410440030076041030b0610089240702755100c1c00c050088481c5c01c000071131840b020840440685505c2c110345d0048035520b0810740d807080c1c2c41200454080380000d440d103c03049040300c804100c800407510140e01241c8141c441408020094002d80030068001c0103514491190490400c01085000d005502600003418100001410641c20180c000140201040400d1900d5000741c102412140c10710a00c2c103002000c3c1c9803c103018801c01c0e08d0032070003054400c103000a0100d03018a020904020080c20015441600020303184001c40b0340c3c680380401e0a41c402c41041ca40920000c084d880e900091151a00762502401002d41459420603180d07440045455000c055090031900480d0012016004296407600380020341445075a00c81400ba917 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 783484487 1250 783483237 783483241
    0x11270f10020a120504080322060c0809090705091c02040c020d0e0d14031306020114010b030f10080d0804060c03090c09090c05100e0103050f15060f070f2102150708 72
    0x130312900c2910081c00a020541e0b0b915180540345404180003150141000e80007841c0006090b07004559000b00680c0c05155981030091410400c507030700c200103200b0020312000f0001660150356600803680c130b141100741a101000b46d24010700013196000341000b02554448500041d0484c1c00001d80c1c0d00881003160b80303210044d213030314203550046499510340d68188000300d5038640c2d80c4410380b9030720191805075000b0403962482d0070000301484028400d03003205860030801b060f0040065030000b0b42c07151800e052018807564030f101051410403030748040d1001071048828041042024000d020070464075107000d0151841c185c540200d00700700c903ca0314080350350700d1950710100b244000f0504000c000c0204510140131291901903c8074581046440c0004d1030800059007aa003020b002d42c3c082c02d5890104201c200b0303004d0600c046a446110142aa110240305040000743c404502171102480340c1a00c0c2c540380c00d24688007250071520b0864a055400880060310030392030301d0401c01e511100c41d00d001044c42d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 783485737 1250 783484487 783484523
    0xe100909150501240f1403040507081204031b0806070c060902031e06160f0f031107061b020a0f0201081806010305071e0b0403030311270f10020a 64
    0x4800041c00d01a1000d041400008420b200b440c40d480f0804d02c528100005020b0000382100c038290768543c00404075161980000c400d41055000c2c6900c144998200c0703040a844034a0149051420045032168100014090040218095604084000b0016070030642e80c18001c0d95612080c0041000c010810050100e40512410380c004900706500076003580c46044103501e140803040049520210300740b044c480030921404070312103059100045c603034442041c0e108440e400c45141d05161542c004160319000f0a00f10300f1514001000c44c6481070200088003840030442c0c51400d49501400415900800242070209041c480b07a8005281e0902e0f003081d603075403181042201138400e4a01c01d0355900ca43c40001c000c1285c00910101619880c49020045003249059441e514030140504051240280001c2000034029000030417180620603005050444c164030b402d401174401d180c092041b139200440c40d8004e0908858100000390281d4000c0022820301001961380c1c285180018034060441040303d9103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 783486987 1250 783485737 783485753
    0xb060315150706020403060c0f020a080a030e0f03090a0e0910020f070b090105090c0406061e1e2705060909090f010e06091b01140f0d020c10060e100909 67
    0x840e03400703048480e8030398006040140003500640002c032071062410212480482c080c0d15090f40050282c0e000382900d0400b82e81e2501c007a00b0206440050544a17032165280080a01c280d102501a000c0203603280e001c00810003800e000c06503c000d41c0a0043d906101001401185909a00c49040300140c0e80d140c18082220661080c01c01c0a0812000a0140b102000b41900b15034010000001160302c04030004d8108021a0064403918001c40c4100403591625441d0a080e41003403050307814040c40c511148841600640d0060710060006150b00038800700308016000c000c000c0c8409040169a1241000003088540c4034000415110b400d89500017204210200320300003414100100912400084004203640c54109550f0200075006103100c080184807000388000256005a546c50598411a02c03944000e03809908105881c20040140400800490004000b807010f200028800d901c41161a001140d00342c0d0070a4820b00c2282091010341030492455100f076a00b90071001400104e02e20300185 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 783488237 1250 783486987 783487009
    0x903030f0403030c0c05090717060a03120c0c090b0a090b1906110f2103070201111c0e0604030f050a020c0a15110a08070f031808010f0e010b060315 65
    0x30402400003030200406910940351002c2c184604245550076481e03404111405c80100c03181c100055440e1000307009405040b0000d600008080d104001081d01c030307240e4007960301c080b041d008042040c010305c180400240402010003404000f804110002d2024005604820035100d454004c0b0b0301c400d01c80d0703030750740d0380180d002c8608403d002800c01481c1c0e0b4007000b405040d2000e0520035a40241864801c96000200d0901d050b801083d0050022440303e55103449160009010701c0110366031139006225040d2071070000e00c00c1402e080006090320844490081c01d4031107091080301250002c40078800041d4104840000c403a046060082d212010302c0700c1285041204c03000725034003075060748001920340000b09204158880e2075031610316200b004141e9a03501e00c0c180c00001c0115400b000510003190f404035400d11500e1191800b0070f040000d01c00c8038003008085410004660f50b6908544003240000c0c414503100a40020003406214428000540079000040c12000400c0a1020803c01955032002104d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 783489487 1250 783488237 783488257
    0x50108010308070320010f0e01050408091c0b014703090115030821040f08070c030b1e10050d0b060d080c0604060c17070309030203311712090303 64
    0x5d00c1980800d41100d000e010705402e9002c12034641000c03101c0311f4206000389031046130442800751074541d440080c0462000d104c00e5580740340b20302c0107a5800051001032403c0c0242490140c2400301c00300c0561020354841100020071030641007614452500c4401c03118154034405144000b91282c0d6252001c81c0034140d02030019142501c900008401c102002024008510b05081c1400340008540c0c0920081c05081e640540181c0303a0850b040000344404009016047c4140169050655207035240f2941500c1035440000203080641500c1c0400d1080700074030350003921080700790820f504d0940410304032000e40d1005403442c20a140010955100da04486c0e1110351302000d070719502c041000030152502c00030b41701214601c0c04c4c03c810713000840c0f044070301d40320801041c10700c41c40721b1300c90840640c014002000c0413010b50109026140241c02c810400080c40410100d84106103001d03454011921451504102d800c43d680071107901242c0c50008545240b21004c0c58450b580b0746440000900c1e600412280c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 783490737 1250 783489487 783489527
    0x160e0105040f03081e090d06110702040906020306030105060301110d050907030f080322030905060a09090216150c020d081302032b030615120b030a210305010501080103080703 77
    0xc1001800401000c1c40401052220b0750510390251700c00440c0701c0e001059a0000c0d000300312002050312603020680c0d80107030000551902c00c040e4081016540490000d4441940c00701c00c02c6aa41020700580703501c80000c40003001080c9090241c242c1d280988429800d1583d6124001480c0000410005015540001c4454251800340c68000392603070040721031400c0c0613482c400b0050b010303000c52150b5a409905131a81d8480c50b0900701841030716004014840e041010050740050700b0030161009150301491114410021900c1c0d00700401000013020401c3e14070f0b4900300c0a01102c0b40d020034544030304111454800e0140d00c8440c5000b590221710000039505000306007a40d0594407101c8013018100c4114810907000546810040c3d086824600c2080c419041145648030018441d507501c0c00302c0d05950702d0000b5100c42400101b4500802d09200300d80c01c00d00d000c603a00c0b0b284441e4140c403210601d545002e110940c10800006d03c01441803100600345180841d1500426001d6064501c08900c18506 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 783491987 1250 783490737 783490739
    0xa0819060b13020702010207140901030f08130f0f05061204060c09082b0503060a0b090a081603020a12210507060c0201090b130809130615020706030b09160e0105040f 73
    0x408000754484c41040b405031084090000312844071407040034080ea00107100d140070360320715180c542c2004240b8508441404007041a003003110450840000a002189007141040c1d05050780c0030501c00e000d07044188144000e100068003450440d00311944180d0007403002c103c8078100344007a94501c140d5048010a07000f244d29100540c0f1128003c1c04c04108680b94078a01200c081c602590715120a541aa81082043e4400d011507038941c0300802e0081400f90420613485d550b16451401e002e0315207050b0a1511012500b0002c4d031510510a00117440607071000400501e4550b40c1c3c001c4140180c4603c000380307040082c60814980200260380206400000901c403261081780300034000c1080c4441150004501c0020078400300c2d855030000348866001000710702d090403880c2044419800940a034650b2901d8000105840203c5038030071500c5249a001850003038102000601950f814074400fa0050000c402080300c1c0304050115140c1c1c81042e81080c010a40342000121201c0c400c40e040051a40e440e04d40c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 783493237 1250 783491987 783492019
    0x8011e05150d060b210610050702042c101b02030a0c1502160b0a05070c062423031605010c060f0e240402010806010818010c030504020f0a0819060b 65
    0x40c281226800000c90444696540000c00103201c4001c07907c5000100140800001802c280d8440400440361f401c500304040c0e0103c42800c5100c06200c000c84803508140c00001824100c1c0c01503c200802c405035010841b18403103c000d6030703070040b01d81c40f80401c941e40c0076000c00d01611070314955420b09030707a9055513207a80005206e041e0340101c40c01104c4980c5868001210300c0058807490f07000e80059540c3c0c50745d8200ea80c0707030400035042005280e0100c031088141d0b00b8500c504801050004e00c40b118514080b01150721804c00f1940a080e5007500a03080011642030140c144030b0180250342003400c054416848609004000b040400d10b03d811075032405046090751031001406249a4003104007001071104505084109540240e6000b03001c01d1041010840942c080d031b0184d64042e4861058000c0801020f502a00f035641040d00280400d03034881c28002942400456500c1d0204166900300e850341c5401d0b00c0550b1201200d8052201d801891a01410030960350400324105800a04d81e00c52000050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 783494487 1250 783493237 783493267
    0x120905030109213b090906090d02031e030c1e090a0f0503070923070e0f0103050f0a05071403040624123008011e05150d060b 55
    0x7900100009402c5030310300d5030303113114404000052251203c1c020005584240030100300042c0c520300c0611509107054450a902e80345452840307100000c00074522814542400c40c00c0221520a81046400401c24100c0d40320340c10809151668480c5c44c0d83d60759940e031107006001070281c9040b10140c01c00703408100106856900c0504580a801ca0300c045035640d9038240c1c3e068148a6218540d01900001c4041201d25515070003912f006425a4030241070010f10303401d80d440060704480b06008144201000919803c06101e0b0702080c030030a080800c144c4c10500f129280b403000c000d1400c0e00071525a0000340307400b84200c0754080c00000c2075440030303100d007402d207440c1010b03000d003a086404000180f02d2201d081d0006201c0001103910301c9500c020380044640703449449414040c55803549202c0c1c0594030f8250400c07012844c030010025030352624554108021041329021002800d80c0c1c1c0408400c00307021996940c030200c8144d292034101c19580d400c030804c40c0c1000e080399a21040f42c59401180d492007100b025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 783495737 1250 783494487 783494513
    0x8160303030608071d0601030b2e050a0804061d0706030605091302060a0305220b070212270a0f080d03230a0504020d02060301120605010f03080304120905030109 71
    0x20707803410310100b5101d00c0700b1036407042c15205500c1c1e042441e45100310080051122950482010f142c003003544402c030b03030104201c40c0015545c140004100a0307481624001c40502c42003a040324540700c4d1901c040f14400510000014001030035803030742c528035000d40c9105240c0742d1017290480703801e80301d00076a602c6024004100a1184c103004001c00400209040d00c0021440c609070f0380106518106003045008500070000100f104101441d002d0340c10021340507041e005041d0341c1c46100d0301d4003145041003009007820701ca0701e84080c08071030030720070308281001c0705000f400514828181222001961000111102130b207601000076003941c000080f0b200d201c041005441103556071401d1042844a01d82010310141d6800300080803409803011411414041d08010f070000c1c0010310401684645400048182d030003a800341142c40e13410f2041104100060051900410640e00c00e068068515100d5881520000304010079143e052070f60307a03038024000c80c01d5001500c00640200720a0b001482e1040350382c125 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 783496987 1250 783495737 783495743
    0xb1302130e0c19020703080d0b1903020604150309021201050402210d0c0503130e01170c13150801141801020c0a1101111f0c050307050a0810081603 65
    0x20000c0041056104509818040c0001d640d03038078501410241440900c80034010b992085005501d000808a50368401a0260303c5024100041c0040300104200c00c0c540012081100c20410031020809031361150161000c0790843e041158584280f4002280201004c5a00a5014400c5070181c5070300307001544114496403091301c1c031040720010006115079012440343c0035081c0e81e01440da621102407260412a115500c620300b10f90030100410942c4069481130340028480e8401d800041183c1401c1e6000240c5813090072001d80342082d81840825201c00d0018030301c401e826155680c1440703a0210004000040c08040020011002d030a4550580c1002c1600d40e5400d840b002c0d215040442010310840354105c1d1404001d0490300c42c6580e5603071141441c0c01d5041d040c0316441d81d0001143d42c0a0120314240c010400d00100241c0e0790721a010f0842e00750303455240800c0340c00d200704211070f6040320850305850311600781041319a40e003032412054046142c00241240c00390307400c0b40310800c1040e0303030b89402d882c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 783498237 1250 783496987 783497017
    0x9180108060603240610090506180114120408090f0a060f0f0806031509031c0209100203070503030417040b160b0604051003021522031a060f060d0b1302 67
    0xf02d0280d9a00154210400040d841c070310384c408124146441c24003025401c50600309030140550310800030b12103800c400912118014460f071a18030960f4020110002030228403580c07030501c0c406c030281c3c2e03015440051000b089a58000745c000200d9440c2c109100703042c0c00c0201208103940e01c0d180c004000300700d000b000c01c0110f510a0080c2c06000d0103201d0440c450000980285800000003015280380390024000100a010810100c640311051004480c2c090341c1013840980d40f0b890a03010302c50202585404202103400c2480200c00003030002c003c60390040d41104611a0b0b400f5801a00f03070951040d41e0100c2c0f00041e00040300b40020121441e01c1d402d1500900c1c211100d907664100b401305892044814490308101c1110500061402d2800e2840c4a81c0c00ca41450502d5030101480d10308681145d4810f4071039004100801c100101c041032001e415856042442550030808081004001412401441004d000c502c0d6000c2c04003d5204032035094005240e1b02c010200c4a090703400942c008003188042507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 783499487 1250 783498237 783498253
    0x9030307050418020d022b1b0807030b061629010e193809072d020604150c0c02010f03020904060b0c011d030f07171c050105101409180108060603 64
    0x4501ca201c1c00114448c5003250501171010010121582000200f54006040d51289940559182c0300013802750a00400c1100407121028103241c0095420303050b24010301c0c4c07c0400c0d850742c030f041c0e4480d20782c3c1107c05201400440743c5461b00d030f801c00419003204040d0b401d407a2242e00901140210260045036100400801c0e034400743c003015580300c0c84541401c0382c2200101010904c86881008075071441017282c9a64681901021110303030070440c01e10742920043e840281800b05014200141220b0710740c42c42010400345400030302c0900780000e5424040e05000031b40c181c480a40307000750119900342c10005c004000013511403c2c002019004090790300015864450f002182221905081032031184c400025801c1150402d01540301d035104100841e9031810041c00031160300c01c9100500282d140300c00c840002c08038054440012950141c4c840351113142119012101d4503040042d07040340b10301b14001c4a0f5a65001004510f40d02c1c604c0258240c9050740400002d03116a020448602841e4100c06aa00030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 783500737 1250 783499487 783499567
    0xa020d0201170405062e1a070602040f090510030b0705031306051603060f12020d021206010602010902030115050f010305271c090501050f0d0906021204060509030307050418020d02 79
    0xc100790b11b5404a072a075081e806110340440724440c90380514040e10130300e1428241c0e985410998000754000c10105054010034840c40404c2c4c01a1640000103078510700c0150301d035032114202c01801900e40720074031030008081600100c0c1ca00d0880201900408148942d0420041d0500c54482c507606543c002803a002c00072407e9130390440c4a008507a03200f80d1284455034103400b00704c841940c8030022a03000e1401c104c1401c100c081444201e0003810140c00000c0c40c1000b5005040c21f4400c5129507644840c00c00406202c1680d4480c00b09038680400c0c60006544e0380d44406102190000d0600700848141c070600d07000031003400213244074041c12503641c044a20f040fa03d40648a8400a008240c0403442c14010400d40a004c1000b410b090716488201137541201c81d242d141c00c81e4054105619400311b4441008240041c030300510f500a001d52004501c1e502d480180103009c2c0c0220f00604044d025690754109417004680c0540e01d0f00039802e90219035454a5840410046500d4002c014ae50300801ea10700e200c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 783501987 1250 783500737 783500791
    0x9070807020f160612180f15060b0d0c200c04060b03010b0a050f04031704031406010b182404030506070c080f0d090b010b0406200a020d020117040506 66
    0x291991626a25080303505081c41683c04240882c2056000b03a41e0300292030100390800c51b80b41c03170303070f4041c1c40615002032450404d60705c0d411251a07c0c1c14103609000341005042003c03411541e90b084030390000103807560000130460340a80e400c000c1519420000c0c03480d01038900003060170030300e440c82103608009483e590342c2828940d0009105400d4482024055050a40c2c0501c008060308005402000e24094481d9250b00c0e048240324070315400c4802c041414000c020700d540091024050900090081e580342004910003842036040d91035000c685044e040f035480d00d90644600c2a502e0703038400071455250464425070550814030040e074092054901042150740100c400b40c03c95508202141d140089450040e42194007140d00e0780d200e5640c400038000442c510340d080601030a48000720545d900e16000f00141084c20b203e0450080b200d074800104280d8000040780000c450341901d4940c03007601d4600060f6012582400d440c0a804040c1042004001001c95514402c01940c5015644112007c0540c20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 783503237 1250 783501987 783502003
    0x10e01061205010e3403051503010905060a1d0102030a151e0b130503010c0e032413030219060b030106060e0603190609060e10210b1509070807020f 65
    0x1552002000c5005994490401481c5c401d000c49484020303071940d07411000c507901044005000035524814001d80f8280e11200c4071000200300c0c002d03c080b075525100c0c2a02c607180a00041042d81e51405c80213030860410568180400d880300085440313181800300d45014002441c0d5410300303581c071a14041420329020404440400c0c4d112000c1008504142c1c4c82c1066500c0030320151000350907002d002995503424043c07404101e0042c3e8400c4140380412041c10b29000c0d1701081244a442c140d00546102e17100000003d40c0290328640c0a0400421400e0903030a1542445010001c034144100f94003d201190b005034036640030680080001135642c01c4101c501c980c1042c0e403260300c4401000402c4c882018200314450b0500d00000005500d41d80e81032860489000750f12101100480c40208401c1c0641c1c008070000912001900a8041d480403001c010142c0d4514001801d003c40c21004c90300c54281c0c2a0358030312000c40900544030340d08110130081c0c69040100c400750700510559000460381400425040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 783504487 1250 783503237 783503249
    0x1e071809120503060f0a17070b09030d12090c0f1d0f13021519020c06160f0309030b040804051002010b0a150c0c031101020615030606150d05010e0106120501 69
    0x40d0803000210840b020f5001900496112213990000380c650750321600c1910081441c01c0903e04600c1c440b88145052042c9580103c01000c01400300003031946003c255002c4c05002c6103080c03010040c3c544ca40c00c000302000d507405001c0d10442d0401142031360b1196044010f440341c0303d120070b00c035065030a203c00c0e1019088498a20244010001c01c186590b00e00091102038030042812040d110840080c2006400c40c94502c92000692504402600e8040c0400f50808409403081490b00c0070084607412011400c0900600d200152600c00c1709040c0316006107070213107a020f01e1018460130036040c11410343e0000c0c0100d902c20640c491043c10700d80c1c0140f058101c41d084c0905a680803030b00e800404503400c03032105444810701c0403400c80c1100180a03204070320301440c03081c1a45011a40404002442c02ca8001c0c0010108203124201d44002e030341c0040c103154403283c211140c01111180c2041c010207405012104a156030605e4000309a940204400d517040e103e142d540c4440c8810000388400a69000b8442c072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 783505737 1250 783504487 783504503
    0xf030a060f093806031c021b0111120f0c0a080d050a0504020904081318020a0806010f02101e09060b0306060402040b1e0f0d140c0f1206031e071809 65
    0x5210044088561a03200c000241036611b048082d002040b00c4500700024280103800040b40c01804520030794028044c8042032070700360902210300000b26a1401d034440c03c0c004030a004601c820800c4030f0b040440714042c0010060782c40c00c0000d450000c071030b030b002117042c02d00240c203140029607204020303c00d5a1165070024445041610b4a40350f080456100c140d0341a100d1841c640d01084110449007035030429401c070207005956040d40d144c010161341c0b0180c480c070f0400500040400b01c2a81c0003c0b403000d980641d100c00124104900a40b0114200c000d62051100c1c2c1491502d0f014402d1076070102070b000e01d05805079405075071518104001c922644c000d040c000c240511001025444a014404800104469462030325030b2003030070600b86070001c03008850400d842e44603d83e4500702c245041904101c9030700302c0601340500d5045046450050b6014414000041000941d05a03420801e840180c109003001c585405504040781d0346542d00da0103000c0d0b240f0780c0c0c0a03040610345c50070711504d40d40b95044404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 783506987 1250 783505737 783505823
    0x310090c0f0c02030c030a0b01090b040902130209010c120c140606030a0b091513060605060f12040f1227380a0801050f0414060f030a060f09 62
    0x265102d655403102a40c00d44611070301403000d03850811150250034000c01c0c0201e101e6151001141c165840d0445060259051144020058403020104071804810600158a804400340120b8645210400141c8818941070819080310b07000340e0b004501070301408503513181120080c80f6580e9800300b9503140c0d41542c060748000010038074004134030303402082c40402c1d14100f43d07003c8801240b8101c15a40d0f01850f441c0f01b850b5000700f0205115120040c8000d80c0d04070308198200000c002d481c01401d051603400e200b0320000a04003d40e180c02d2584455202210800414043c4002006103001e008202d9541070046040e010b0702e50048004411108014215003500c403070101641c1c074030001c4c0015650302e080d2001c0c01d0034088000101070128008582d4070910513615250421503400714503a001d0340120320300310342c4c40604210700c1002c690216040c3c4940c6407108181022038a040340c000d60107001c2d60f140c0041701c5000305068101090a03401600c40044140c0d404c040c0c5941d400d0034034a02c52022281041d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 783508237 1250 783506987 783507017
    0x80f06010f020607120e0109050102040501020f0d09050603061309060510060c0503031f0f0b0a0807050c060621070e0702060c030f060d02040209060d0f0f09020604090207081902030310090c 83
    0x4031090154444000424516040740b1b80b00d0a4801b580011107083e500883c0c244890b5a0420408030079620200040c0900040180050030030003031402914020a0000009000d5443d00d2662104542207103000b0083c92a45007070007001042d050381d024080d0403070080c0001c5e201d0300c2407840d00740854000c0095841c0d40c480400c034030a1096054084500b1103410b0000250900b030302035051005000000d03d1a680300081c01d402450140021300110900009000000e41d040c40051340503400081618074185400b82d84014907044aa0841c101c00300f84103043c800b2807140c249001613800380e0911b8085030701c0d50b00c450400d900c0d9404100c0350800c1000b0701000040b058a030510000c03022070b00280006250020102c04a45a13910a174001400640c50360b0400180d810b240c4600e21001d01c440404001c1c0d440700c0e80c00210244558403502501c1e940104e1309200740803a4404032020301c900003941000c8900171003400b9403a60403ca41341021502e072444000380c00f02c2035000d0b1041e040a075a039041e13101d0614074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 783509487 1250 783508237 783508247
    0x3010911070f51150312030c030204180c0201020f16060c0e1311070209010b030928020d0804120c03060f020a090527070c063c09060903080f06010f020607 68
    0x152807942c0340c84540181000200341404c502039405170505110000f54244003800780c8015130000001c1500c10002041100240700403e860709140150101e00341c1a6900300302c2c0a0b00400d01011043c00b07001554210100010032500e0046104610a0208540e080019120785406048483e04600901c240c140c40315140c0e0f20100348000b0804000381070600795000700386810310903000030503040000014040042c02c10846243e09000e0300d150300181c1c06e443d814130310a044d038010000303002d0840044280f08108080701a40d01074140613803115405501ca003040600752060303100036505076181c02070740102c2070b505008841100e0a203885d845450340c580424072104000c4010b040003010f00d0380303076aa4a007040e5084000d0041c3e04a5541038005031550400c3c03003c50b0b121010311520300d00082c40003042d00702c2854107900340c034407500348004200d0300c056202c501402c10000c008100b20302d40070600c0201a08a644540203c64007a00200030f559510019202d2078100305540c40980d01040c00501518812 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 783510737 1250 783509487 783509633
    0x31506060319050c070203011b02120f0c010e0703170f180d06050a0e160f090b0105120405031b0a1119030219060f080c03010911070f 59
    0xd000808a040414010b03800b20340080e00d04800c0703980c002881d1025450300b401140c41d41c602d0b9001f48a0715084110f0081d5075031500c1e4400055084010031234861848a00e0207960310241d910b002404108036246920f9200c1c1034034041180c40b403240b543d101c4103072072603001903d5100190f06d50700352501403070b50b15159000003c0030256502c1207181094500044a0340540b070b001c0d1510140201e0400511404941403014554800d900c0710030060040240101c2d00c1c25840456010b0740c80028a070f1589001255148610004d00c02407140030001d100030401d000006000c0700c2104038000e5404848040c00c00d4071049450f81c050440302ea04842c03071450741703040301034002c6100e050316001800aa1f00c0d40800e07080400302002000d0402053760030020f064019064400c1c000031440c1121041c03500200c1c981700c0d40010700030340840640d2070b0030f000d2001e0b0b43d0000302d5102c140c000b41c8c0440310309074a141080f03000c1545154820394008042424503110700b03111800034500c4140360216014840c0d05c01501d115145 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 783511987 1250 783510737 783510751
    0x60d090602070501051b090612070908070b030105010210140415060f03050c1e010215060d0b1501020706080705180a050406060c0506060d080702100e03030c010b0f0315060603 77
    0x5204a220009030040c4010107490740308074004221440c100c42e0019840400b61a9600591800c00c5800c000e5650a800c0319942001d058000c030841c0c0390780c0ca04440f059aa80c0000c44203100e26140800d10209450140d4100c8009a00b11040c0300a07410084095511048810101e031123503002140024150440e8042a1036013880001222681c42605490304e0500303a005a4040d008480b4200b43c030300740141d1708290840b001007201d1003000c5440000796510383c2d8a140803640b611890100b01603036240342c0c150b007407550455081009424111650820040166040f0340988600400002c650340100c8107607200e40090f842e0503003886414000003a042440b1049258031050040010501d50380354801d40d03002c1c2a5990328580466090314086241c000041c082611030707603882001e500082d800c1e401700c400716035040c0d0308040c01d0f40c403011003900da00200c080025450702001c80d0403240d01d1015408107104c40411a11001d8081400040c140c80b400980c003403416080001b400280f00303041c00d070b0045d84c001e07003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 783513237 1250 783511987 783511991
    0xd03030b030f031602011b02030619110a08190606050a0c0204020f0304050120040f051507060606111203011a0c12070303021201050102030a020c0907020a0b0a0507020d0203030c09060d 81
    0x5142c195500315803000424849500e0764999007020365030f01030b41031100c420111b04000080403003500029038540009001d02480141c10114055024460300044000c124002d1266280c40d5200000340115a00f200d402d040f856a00110350401c2c10341e0f02600c01150880e0b21154505400c5000172a150000d149042c0d811079000c001c00024091f2440003144614005d0000084610150811340302c40303107004d6140d00603c00c00707100510060718600080012140e007210324050308a410300c40c8040ca40540000078000340d03d0704e14000f8000740c001001030701c100c5002095500035010700c4078207a203d00003805440d4421414603e84015003403034900030500c144500c01140c100aa803c0809901c503407141c04120006a0003103041e10802c41d055078481d014000c00d0014600f447c41290000b50385008903012507110b6042c1d02c1c081901030b4002c2c0510b1410f01d030403010181c01840d00e00e0070240541000c0c0d441c400140b1a50160070040f03440401a280180c201041c0d1a25218540c2c0410003650040380c10300f0441a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 783514487 1250 783513237 783513253
    0x20117060109080a12030606110601050d031205070e030c060a0c021201060807080106060e0d0308150a08030f070b061012470306010f091a10050c0c0f0d03030b03 71
    0x40f41009440f09880c032030382441075503408540b0010140c2d20150312550a115070000b03848420000071900c075040d108296905012140141000c81700c2000781842c0000d603600c0c08046c07140e13083d800305222050740300075021102d041e015441802214800d541080c0001584503c4030001460b000745840706074140340c070020410350f40701c600c1182814001d600c141600c1c1c4d59020b003040260741001b00d01840c640e00301d894900c0c50f1611b0310091b241c0600248110030101d224100015995104219403016122020071280c80710a0b04040624503801954142e46d41014440003c4642c5070451503907820002030340c0c95402443e039010002c009019482c1400604145d082c1f070402000c0c12a0303185990b182c05041a21030410710b4054001c90315591022031a0007070308031000600c40b080310607409404661076010b00143d4074414450170fa2000300e2241003e648155070103060241d66510001070803840000d0700c15210000500d03010090000000d500064004800305000e0300880c1c00381d03001d05604000039003512002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 783515737 1250 783514487 783514499
    0x12604050a1208190203010e0c030402030703080a0201061a0403050c010f1b0b070f0e030706050a050c03040603091502040e07111c120e12070f0f060501031211010504020117060109 79
    0x840c030b20302c40c600009000200300100001036842c064045807582608515550400d0f546148281d4000e2000150007400004201151810405040216003040c900c0e03489080040e00240640500e100e103d00352415100c0320246100d80800302e0741120f60040050a5815014005546407584840c12005015040708584400c6543c0307081503030080c1c81820041d48a242c600e501520328018148050700300b000c0312680c0c0d401500d0000c2c1d1441522044e081013502c3e011801d4003216135200c3e85030840c681e80004600050510303015004440403900c074204c9101c00301044480d0304101d009500c0342084640f191004501c1407806007240320400c41b1010191010014a91118504055030080010024542c80351400607800d0703d1003114021104a0094040c0800d91150300810f80510f100140c80b4032902560f40081280d100c45500601f40d0010040c0002d603981d08181003103445145a101c08134103210f1003819101c0e010f100c1d4a21595058403076949124840301c1d03080003020010714075414400d1420002c944 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 783516987 1250 783515737 783515753
    0x30718030c080c13020309070303080c2b110c07090b1314060102060a060803041a09130c140901080f07110a0803150a05060d0c0306150201050603010b012604050a 71
    0x50b11000004120300410700f418800340e0141c1c104403070a1644140140300c940c080110300e000860f42c1500c0d2a0030107440d45d480100e640c0c440d801c9100c0144804156550101410840b0f0714000c51020364104031070050081c20324000e02c118000800e00e50000c4409001003003040d03105840d021030103042d030f00000003459403440448180b017283c0014110702c1001c011096904200444d48682c0d0210180700e518a0500b50540d01e000b14000c1104030580c4942001c40c26882c0010f07619681d200038034001b507008031219102d0041140380508030009440030704514070f0b0038491080303480c54032060b5a2084940e4034804400340c01c181c0a07100c0c20403c0903040c905030f483c041c10442150014081c407002c0d03079070703003000010025007446004a96004400b080c00c03c02099441c0ba09403116003041d500c011a01c00c424a40403070082c800394006251820710820006100e5505501072449034034180c0003000624120001501e841e5003c00c10440d120f07034241d81501c1d011841c8a48290083e20520444207001d417641c2d13485d01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 783518237 1250 783516987 783516989
    0x90905040305121b0d050604091e05100c05040501051b0714030f070e040f140a0f06051b190e06030c1201061d120a060e03130515030718030c 62
    0x4002a000b18103601d8081c80040b02c1c3d81c11906403100300c2d549804010144807540a4688007902c0d040da108006007403600d880c0c11980c415540b20760300c00401c580c40d1400c41c00710035903a00c05403024070401400c0c0c000c02c01c107449103c03001ca80315244c0c981001d2078540111410b40c8500310200400401d61941c0000c41c400300309040160107000506c000c012441011f26107000d0040b401412143d111a1041080180307568001b50040c3c2c0004001c5820400d505002080362050034040d103152003414403d000b40580302001515480c4203410501581e20b40b0314000c401c001d0f600d0100e040483d01008200c0a1100ca9411807120403014100035911340403a00016003941c10448100c0e200403000101c0441388641a100a4003414040c2003900d00c110401a102e101d1030810b07800c3c0e070b001d060760301241d2031100c2d0200844416681d1183c0c05005d582d2055006544039000004489810f03984c00350080780300d241c860884184520780c5e201003811b42d51100b20031240214407003c0401c981c00c400d840840403448100c4500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 783519487 1250 783518237 783518243
    0x1920010c150c02100911040207020d051c1115010b1c090c0920090f0a0905040c08210d15030203030f0301051305010e06010c060f140105031002040b160309090504 71
    0x41903502039102a04240200c40c0e13100c07001c3d280249410010308544d030b520303500d100251401602c48801d03101081407070121000280c00f600c02ca0004e0341e24040161050100d0541d5940d40025132803101035030316034841c9034400301d80e4034695510044c082c8402103409007002c40c90644c10815004400707440701e000c44640e0300f01502c0c0340344031000920010000340600c0300c1e1000483d241604041c02a900c06a042c007411403550300c586940310502400f5580d100c107a10152001510070010f03828035150480c034410040c840d0180f0b60080001440861100f0515000c0301c0148400c2c081c0750040e20b59101c0c0c010214509449100e1842d8840400540ca040001d001e408200d01c42680d0390f0b5042ca01008040d0008941c80801681420018810b81300c04000c00c0d42c20810a003409050350302c042c5006030107010f4888007030428614040c43c5001c01200c0150840c101c85040c1c05903190b4440e1416403101b60b1003280200d003d0004104002c00c1001901c82c07121210a00920301603800a48131010402640d031306031000c1e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 783520737 1250 783519487 783519491
    0x4080405040c090905072f1515030d020102030601270b03090d02250302010507030c0204050c04050f040c1b0c050303120609130b01121e050a051920010c15 68
    0x1400051824070400360811000e00f8047c01070725101d08003d2180c0d640d603a01c05103804001d4091100c04d041002020740d000f100109882c841d00c0e0030025140003851a420840c864440c104c180202a401031007200d014a034181c1d1042081d001c1302c41b036800800020400d090000060030070005008542d4800b640c000c0d10400060581c807201e81600901d0420000001c8608158031a013407902002040e42100c1242c0e0f0a00b462500c410351410165201800b030741029403c0340c00c10082100042d04a8020026103c003201e11007400c2c1040420301c4115901000d03540013180d0b0f40382c0308184105000202c2007003144a1f40b204e040305500d6102182c1141c0000c12036102004100701130182d81d141900c0c04540c001040e000242c1d41881d15181c00d80d04074010320170392140d01a005501c80a1101001490010080c0c111107007030a1821807030002c1d902c000e200f00544013802145495002c203046030b0080c6090701d4000108500802d07452900e100039854034501681884003001d680d40020301e030344d016101c0565000c2c0f40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 783521987 1250 783520737 783520739
    0x1030803073b010f080f06130e010504110118030b01120f08130911120a050c0f040e09062202040507030209120109030906090305060a0f0617010204030c0909081204080405040c09 78
    0x13402401307010355030708184a000310402440f0040e02d0340f40341d40500100c801d480c0d80105001030f01c00070101d42e007502e002c9508110400081c002d01d40684003440ca001e13078400900c0c21181c0c84d18060545c5a000c0100030280500041104658240d09205007600800c20300300144083e66582c0e160f540f00c402e10a60080c1c001c0002c0081c00003c1c414104a2004e01481c24580f41c4003400c1141500d00003003182d114150b07500c1c0171400325000c0781c0c21742e4100c1e107880300095a076036212600c1788000082110f40300140d00c1000c0008286104c003047c0c03069900a880d0481220394115400c20000c1c003402062502010742c24410120035584000a42641d109002c00002c0e075a140c07801c0050001b20f0079040082800a03614003000064030000d0255030100c9031200000b00c00800c500407a0140c545940001390010b0540c0000c140303610190300400889120301100300c800d076070300c5400c40280c54030a1800380441c80107009000c030307030b00c07601010642c49441624642e10f00b03038a4400103000c403a10b071240da800041c078102e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 783523237 1250 783521987 783521989
    0x6080a0506060a050a0c14150907080a030203040902091309060b041d03040905040c09091203050907180c110f0a020306150307150c061109040b0901030803073b 70
    0xc515034206005070760715480d0415000028000f40f080c60f90b90700070489400000c01c10f100f03010002d580c6c80c028481c1540c0c070943c4520280e1a81440c01d41c2c01c68024041c203440010002c1c4000390001c1c03036035032680140d8100381c40c2001d900c0c001e40105e503c1a40207018920984982a41c0d0f2198400c3e692240d40000341840143c801e00c0211f6200c00102001c00041c0044520058000400d44080310300d5084041800d5807a46003c5c6031300078003a4822186142885115400c000c04c0c182000c4030082c4990b410003056a601100503a50012441202031040356145e13540040202d40c1c03c4200403406074100281d03040041c0410a25046880368150030302d07085401004114034042c0319003a0001000c0083e010f48450102c000b1f500c2d0050b03441000554020000d101c903106004414000505801840070481c01400c079140b104640d110085080c0b040340313480d450b01c2c20351070300854950503240c10124050440e03a0344102603c1144a08180105103802c0407000500c1e1180144203440b1075549941e05520000004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 783524487 1250 783523237 783523241
    0x1b080313090c030504030504050d02130216050d09050d0b06010302090a032609030d0c03140a02060411011d011808010614090606040320040b030a030801060207150c140c090106080a 79
    0x50b05890030941400140004603520400395402d9550889589100c44118800034400c01d00d20b04c50f201d02d16002041c030300d200c481c0038188880e02034011801d81b061424a4001194440311600680381d00ca80303c40d90843c0810503c032100b0341d0101040c140145051400320001d60f9500950b842200e04d600c51031351042c404139080720815859007c074402c035801c120102001a403640b005c5104d80081107541036150b41850310424001507000c480b4020381e40c1c2e8808441000707403948030844055912602240716404294800d09250003843c284001032881004034400442e143c2c01070a0841c1300d054060540440d2402c42031040b2001086904644510280303000c081c800115401444180b01e044d061008201195492510030b01d81040c42141d64034002503140040c3c008d100c5802195054410526a002015007082440741611070703e80855002554034491011200c0d0844040380001d5101d00144001569602e10884c05c01121000cad100350111150115580c98026070120000545c500b0901880507074034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 783525737 1250 783524487 783524501
    0x904110c10060f24050715020a1d0306060d230309030708032517030106050703120c020c060c0138040501030b040b091204080307230a1b08031309 64
    0x30201038000f191a0450344042e048000607040100d07925071a900840c00c3c4140121a5115484030302c90b0314124170200c0e500000e4000107121740c04941e80040501e201c030300c802000b0010f4034009000344102e5444600780f01200c119043c0440d0484008500c0350384440a0880d41070b003600e03e110045440e400c4003c1010719149140d440141d4030b8000304480c1c2d108030300d00002c0014003010340603203018190a500e00600e1030562000c3c3e81240000100010880950003002841e6242c0241d99203a003c1034034803042000c41f079200b40c45201682c4030079101105420240c020340090841a0000900a50f405a8010b26020600b110381c101d07840c18081a04107003603d0982c0d9108507000c1e20204101c0d0b040d980c482001580240c0302030024010100050b5580008100c003c0740504007003e0701d912103545104140e5a904100406c95a814401072240082c0c04001401c2c4510510030000b014522308503101c803840c01140d4117aaa42c1e0b040c0f03c15005c00c0c410020402044035280340501c070389401c0d01d0410408110761314 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 783526987 1250 783525737 783525749
    0xb0f1c0302070f0f0b0a11070909060b1503130f05030a11060901060602100b121002041a071a0c040e070804120e0f12010e10020910080106140904110c1006 68
    0xc4680f041c000c0382500c1101c04103503440c40346440d5440d41c02c2c01c0e05540c0f03d255415110a0744c40741034404a0006050f411a0049034442d04040c08034034003c0d010000c0ca0036115028184031141800000c040c0380d045208040b41c14040c0910740020308540c3c17100c40c00e40d030041c00240c002c602c804140c4082841c040001a038800c01d524000c114840c10301c0c3d002502c50020301e906400b82502d0360b030400074030744d10107040464429a25040700c0c2c8012807051064042d40040c441c3c19460f0404408030844e400fa00340441d011350f0b03030000ca808040301c02449111961540546203076031000d01484042244289094002e00801a60302c4104441c034141c60a031034040c40350000310302003026107111560281c40b8011079491104044070000444074407001018010b10a81560001611915040001c2007889600414001109940d45401c0d01a00801901d09103c207200b103100003007103112100784441c2040007600e1600c40c020000b00b41246403864440058010444080c40c50b00441c9400501c600c0d544140710003008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 783528237 1250 783526987 783527009
    0x10f0501051309090305281101021602090a0e100509160510210204060504081e060a09050304030f050d02010b01030e0d0507060204050402070f030908120d0b0f1c030207 74
    0x542c01e01c41d841c140c41584078810200f80c0320096601018042c40c2910145001c01100c0205004215a01c82021100c00300305070100e040764804180856040c000c0358105000c1c0100100340c6462682405518040140300d03000c0641e84014124850300203100b0258054440c500c0419142880200c0d10b040c007801000914070540e00030340411144d181c176034a9424111440c20080c019281c05140700f003140024450080d18a84000f601003912030f00080540199407503201102c00301d0050a001404c14010410f003c29a948024002943e170141038114022551288050380e04256803903030790070408880003904442c550804044640c06039424400c000c1e0700c80091905008144211801c40e8070340a4580c441e000b000b000048890501880c2e03012140100000390086645a81a082141d000324110000724000351032108000703448040090461203a0480c3d001c00f500e03200ca200a014018034903c2c441070340100340c84081602d1a0341e03095601e0303042d50b04003c10620504542c6002820600c854200e507203c11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 783529487 1250 783528237 783528247
    0x1306020c0a20130218211225080d14010501110c0f13180f0c1a091c0c09020903120712030525090e0f0405100f02040f030803010f050105 60
    0xd030b101c1540d00f114121084006a80700b0120380c0d695546030b107850f06244c00241a0b070042000c661204007034003c1d005502c040d111141402000a101845800306003d050008100803028404070400c00c010003030303c5900e031a8a040780c14122081a20031035045030041e9000903004100558120580381c940c9248079014298405814001806001c20b5018507030080e0525280c101d13841541d80c1c03107202594010b40460031081ca00380351000001c04039007400c9800f400482000208400c6002d810120014415041e90912603074805000002440140c2e9208520341d070340004003c5081059000f003d01043c50001d03a07030f040302000381840d0000481103800010801c0101d4008240150002c2e00065050b02d03010039581c48507600420080d00c400044280041010004070a441d003110180d802ca650600440350b2070381e116040c90f05900c604643c080c6c2980c03c810104007031020346074000540a80c0c140c0c07006080c20703240c507284c40c080410340d0030448401d0400401130140156603126a00208401d1034054600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 783530737 1250 783529487 783529489
    0x10c050a031d040906020d0c08090607080402040f0f0e0f07050105040b0d0617010e071a0d0c2307050c06030c12060406170d03050105010504060c03081306020c0a20 72
    0x1144045005400c1190160150410b04240c0a801c0d0303001c24018014000c0744e5403401e00c64001d50040300e2130380e00613140c51092050140170310700c2140b198141d0406042c01c4c0c0e4560005596100d001001260f00c20355a50090301220807500c9081a00c2e0b1090900196403120300c0c1c01c01d440c1200701d2180e0400f941c082801040903a90280855090b901c02c0d603030054a41c400014144090001e40d000f0304500705031941c10103240441503000301182c0c1d103413000f00c41981d40d0703a41d01d035400440402d070101300f800030400c0709255110003034000f05c003115114500310154002c40d40c000f000f98403410400400349140028018140325007040030a40c84e5008543c0c281c518103064040b01503030310849091418808039000010240c0da00d581c0320500521042d020380c590aa408010780380c43c2c003181208070000c00e2901002040c15445501030314107840313a0f900c41216038002c0e501d09442c040401001e9529044403148410300103807441c000760020215240042010307000c42d141c080b1048a044440c05c2e4108d17407082c881c041c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 783531987 1250 783530737 783530743
    0x2120a213305090916090203010b040b07030c12020312090c0a03140a08070305030604144012080c0a02070608040206160c06030b0603040803060f12011a0906010c05 72
    0x907150072219620000340c0c545401d01d165840c07030344003ea00c0030407003040144c0682d021848002d100881c0180740c00075070300c8050314022400f080c0594400a181800103000c00f404160061045d5402400c107216090015038401d001c800044569900581020641082d9500d8051100d5004080c80020b030081c03c805070045854444148405003441418294070340c03da01e4148040d000b0b040e0041d070384540c1d580040c10054030942c0140c4085016900e4110103048061180750101c0c012400790b14180404010901c0340c000307005031600c004a881c034400e0b4059100141308510199018880c05807009101402c0c4005003c3d941c000300802c0b104103080005551075503003c180708080d40c280f810184a0340d0bc4034008591640216080d200016103000030702001c1c00310f2906c0810440c0d60964090154041800501c4554002031b1801000101d0500c0400c0c15403401299803400c40001900c2603210174440100341c2d0a40708880b001e0513425000a4005c0f00c542000e0005590180c03080c2071000103200340380da0302030b9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 783533237 1250 783531987 783532031
    0x5011d090118230402010810080d030603120305130b0603030d0906090203012f03040804120312050702010c0c140f0d0f0e12101a031501140a0f06050a02120a21 70
    0x1b040100240c0011100321102c04014068441c000403605072112401d0040e0051003503010036100ca180c240915a800c52003801480e00c140244545041208c1c0d00303940e48508a10090981c030342c180000d11208180700000c1c031500411500650021400481e6030041c142102c6000a44c0503016001003c0105d50240028400303460910110072103a503030f40c807070500003110300880c0c201211903401c01040c5801d0640c07080010200e01c501003000c111710340365200107a0032200000c44010100c0c10341c0c0d042d41c0205015001441c0c003041240309480c000b002d20584039003004c1c0240c0d10b00c03000c0b400e03024440091591000c40d8030070310101500c182ca4920000946950741e00d40c03034040e440c0c515496203251010403410380030b407154410001c0c0495100d030303995100e0201909401d00a01c0b40c8421700d0780c140c48007031501021220403954003100400041c0d0900704200e5403580040c0da00c0b4107610612520500d1500184010301c8a501e85a40d5081e034440403504401c850940706540c800e400f401c101e02c003c008103000640700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 783534487 1250 783533237 783533239
    0x220914070804142a040e01150b0c010b04050f04061401050f0f1f0906020f1204050d0c050a03080415020a08190c0b07020c1f05030105011d090118230402 67
    0xf03045000d00120301494500c22060030861140d8000907030b500502c0c080210300310003a085400340444040703000142e003241d410580da0410043c49001c1001603148403001052001c16160020600040301e00100e400c7d150143c5103150303030081384010070051060070310625003603c103c60410181945004001450448603080c054030070900c01c7c208508035512054601940c0c444030055014801c1000005000b0040f1807182d00d01500810810855544002c0380710b0303243d840c0c1c3c1c124590611b800d210500c209040500e20884801c1090200462a5030310164408002c51040b14203a946034108482007103525a001e4000f02594041402d140004541200303507015848111350700c0704d030b0781403e0398110381e07204018502810b40c40603502441840383e400300d21581d03445000e441d003800c0001419a4907242190a2921000080080c00140850b41c0714040641c00b8942d40702d46100c2090710200040d400140a921407a80e83c014285a641200d40d40d018a10486105260410744e840229405c1e19032020000c00013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 783535737 1250 783534487 783534503
    0x3061005070c0b2a1b03070506030c0c190c0f06020a0f06020c0c1c120503160e280603060b040305060a0914100e06010b280302220914070804 62
    0x40d24030141d54204c0040c0f54107481c16041120301c684800503110000c60060424440c0024900c0c8450b090005d04070381100c00181045d031850b5190b0090f050582c114414030580c03800740c00d01c0a000c0f049504114040c0c3c1c0d003d045000419032801d5031000700500c1a030b00c180e0540d08000711610100b001061128001c0360840405641c030850121a40d0901c0000e501e03055208000e0281007403440c130b03011250b03180107106840c0300400545140081e226070000b00c1c2c00f0082001003c034008500c910404400159070b501400c14070465a803084064210107074403500b0342600c4c0311002c08025681c1d1501032071004160506001345802d013951117007500d400d8010103403502c0c1512342c40c1e40002c10808217241043c891409054174028802c510911004e498859964400c6100d1000081b862291a8080b60541421100c1c0c50801c8140c08854200e00042c0485d00d0060540c00d00c2400044101c5007070000c00c10200e00500f90000d41010261000c032825404900d441100203c02c2241d00341d0000303038a030380141d004440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 783536987 1250 783535737 783535747
    0x13150203040e46020d06080c03010207051c170c071b05030d0e06070c08060115050a080403030506030f0f0d02010e0703020105070818030a0b06010e030c010905061b030c0303061005070c0b 82
    0x1200036103000f9102804010340700242518000c005039110a0a45080c8003d90300e560320218101345c240e000d00c0701d026215801900900001c44da440d8205c2000003502c0c10070217a800210301c611040680102c07001c900094000601200300300b2985042c001c17664410174086110b0342040d0200c1d0b92042203420600603c1408194026196642425140c3c4607510420b480c0d0843e44613880f40307440c3c40b801e1007403180b015448404665058010415211080e150b980c40c0c4030141c3c0c6644084001c0d000150080d60940110f154512054906201480e01d00038030200601c8230845040c002400c59401c0d00c3d007014642c11807403081c00141e900408841045802c03c605075100c0104c61444101040174a01a035414400d15403c4000c000040401c688943e009880d60f501c00c808640501d0345905807009140c0c0050440541030255240c40b9002e450500c1101c50112481c1d1030741031201d840e56120b40e10114241c0e0010003007188034640110300d00b9048070346203071460404805035a10741481c112405141001100498 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 783538237 1250 783536987 783537091
    0x2070b0a120e0732010c0f0f02040903030c0f0908070902031906060201060f0b03041101141210032a0501390c0909110613150203040e 59
    0xc2800031094040d20040e950b00e1013408488002d0030210f401000606001c4466030030820500c4100b0709041e1602402000c0641c0c07841940c5107105000c03154962181c09034405621244039042c1c242c0d04c642c50000f040d0040e0a000b6000880c210440701c2082101c5805100c012804a500030840344040c002503200c1c2c43d5408140005926400c02c00c1d4400c2c9040800101c10fa41500310004680c0030550750203529407240540c0f00c092000f2a070250a21400a41d11b4108e0b500c1000000a04101c20a07000e05000b881440c1d5284210150b81041c8440f82d603c9061080c060104c000504022030240140b10b0700c072421380e102003c0c855501c5040d0601c40c5055030765150f01e0a442088105c8158080d0080e04a911002c0009500120a20603211500300103c04140c0d1012840396511598001c4092050170b0000030800038240c2c00500308984c40c003254080080c4807401c0d4800040800055005180c5450501102d2a070559008041090140c02145a070303150456200c1620350341ea40d040e0100d202c10315284 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 783539487 1250 783538237 783538241
    0xc060209040617061b070218220b0108060a090317060d0b010b0a110f0a060b060f0301120308061e100903050607050408150402030705091509010b07110102070b0a12 72
    0xf6000481c89070041c8051407190001250840c4514070440352032039114140b50380480203006000001350056032000410201c003a401403110f9018484503620340c1c210703603d444044060b90f61900211010312215006201c040d02c2440000e52100040c1c07410010320400d40c5004001d04042c1c0d801d914420000d03000b0860380d0304e840324030044a41d08520040055690b030800e40d041070f07209480705800541c100100060b040804116000c0c45411500240104041030301c50304010041c2c5040e0a1340880708100300661541644007860007003a0300503914407001028100030305481801400140b042c18840c0d02040303441d0300c107a643c0d10b01080644142090310091441924880250741003d88948510002c0100700d42c1c0c4400103205842000c0150b85503d600f030000d03e52100e0041d10020b5060300490800c0c13100741000d206055010303000e0144400c040340e0380c03400710344000404c1e040004e0030400001c294050000104c1d60000c11070082c40100802c81c50003c5055803805911a04010080f8141a40202c2c492603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 783540737 1250 783539487 783539489
    0x60612131401050c0d0b0d0c060e0d0f06061a0f0301260105041202070f030503040e07020a1a0a0b060901020a08160222061d0c0a1103120a0501090b010c0602090406 72
    0x2c020f5030600a08550141d007004203c88480ba013410030406503801d00e00c3c004ca80d0325a00001d003000e102e04110058030729180003602c03d60001e2903040d01501080240c590540c0d5507010354400110700d400c00401d001c06061800109520130000c204a40c0350f4600101101c3c111003601d494090b9000c16010502102c0c410302d466200c2560a04003400b06019588689a21140c001d8080364000d99071038020f00400c0d0035500c00900744d03400900c030030482500030000d41c0d540800c1c0ba10558904100756640c481e01c134880c0c2e401d100e080115110070071840c0f8105104d210300c2e540c4111130f40b50400d5960b00001390745504002c8004d100c0c01c4080303040340440c80900159800c241e4020100300365048075000250300800901c40742c54006082681c00189070341141c00320350340205004020303000b59071008002a0550300050801c3d00300440400c4c4241c50160038005000d42680d02c44524200c1d0170506299800d0399410781001401600e48032a103540d60303030040c40c5130704000c0d40100056220711203031001800410380e13 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 783541987 1250 783540737 783540773
    0x17040f03031e0e0d0f03180f020d0c06021b0f0904110103020c0d030b04050c04030f030f140c030306010306272004060f0315030f021216060306050906061213 69
    0x81c90704100c42c1250210300e2413800201a602d50f586803150010840a6525200c1200c214032090890707030300454100d41c50351700402d0028011482c031401c1079440841c007440981c440c42c016040800a45040034003450101c5071100c00311508094921084000b5041700390250000708000c070800306600c81d52740250140c940502e0b00d0b005546450040366405405400c01d03540d0305100b43d1920000034009100300c015541943d0f0400d00c06c3c100d186840d5419500301c2c20f44c442043c10f01006000c014982c400c3c4c20000d01d607201485020315201d0810200240070f86a003034008000c501c4824401041742407209a144103904800000031401c40c80054402500c8000b801c0d098000c03160000d8082a010f4004409605402580e41c00300480720810386241070f03e0031709010081c282d00003590303e0009441c020364201c903400310b0442983c4003500146440307440c02009600c140c01107078580740100100d2900898083d401032003912000d00d491441c10103842d4900b0300500000c03080f9a0501d000042c0240741c1074646000340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 783543237 1250 783541987 783541991
    0x80106050c12040603090510050405031e07020627030a032304050d03090302090c030603191a01150f0806060a0f0203070c1206111216032a17040f03031e 67
    0x10b144c02d801400b6064510080d1014410650901c410304503500c195441241c001026600b007944221f0070380250003900211490440b41400301902503980d110050001642106d103160071101c181142c1c448426400d000c0b24820340143c2e0b00c010106c2e0300301900d6001185c070120786860f082c002800c501c210340150b801003600580200403001c109508034036880107880c001c9500301d942d0341c2c0c3c04001400d5844115030103074250f008025401c0b0411102140e1070703c654820303151154001c480d0380305182c0c1e0003000d80c00840500b144060b0302c0300f5141c0103050010460080c2c0b801402da46840000701c1c800388114960101000804180f041ca4144240203a400d941e60050610780b880f0f070395507654412880402d0301564240d140c07041e04c4c4c003400490f1045844210903400502000c0d134400608281081c40040001d05140d180c82c5001900c1c503220115503002d0780d02124000342c903108403c0080000324608100381180c400d803028000410300c0a0300301200741e6031501c0d0128003810841101080401c0e981003c110840c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 783544487 1250 783543237 783543239
    0x70c110126010521030d09031e020a0303050601021501050910180501090624230d02070b0f10090905011107050307060506040519150b120106140a080106050c1204 71
    0x540701c155900d0480d80111070b803036000d0402c1c801c002043c0803030001280d03260b40100101c00600c0659081445554013a0900c1166000e20101c44500041c819a400700140c00000035001055090700c00c0c40d401550a2000700b086200840d0300c5241803006004051081c0c0110000521b06404100008040c0175143e000c00740b0b54800c040f00c480030348420b00420184034201000811100c100c240211a03000f02c1c00c00d005143e5034280c4d02030351100c40b030040e00d880540c840d02c07004c40707100010001010355502c010b50040c1d4039042400e010705038138405440c0c0160304802c0341c24090400c40d402c0941080c2c540401c8005030740c00c039910b00b00740101000c000d0071500c820041018030502102101601500d0300690061000342e0702d6400f04002ca54003111720440045201c040d68126200950005440181c0c1c01511181c403500d0b990b0300001a04900101081190590b0050100f1a8082d040940341c03029901a0750a141d00c0002c0903000d8041405051304008000c144005c51010420180e00700314140c200c004d64032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 783545737 1250 783544487 783544547
    0x6040c0b040f06110f0d020d0e010216060e030c09130c050a06050a050a030209030d0905011709120906250219050310022109030a180807060804020d0c08012003070c1101 74
    0x103131062012800449c000e002c858101e5400860002c045420603558242d84904101c4e0a4440c04501c4d81e500c6c0c0c041c411340e2b203070b0f14450f1101d074441d40c01340340d191400103070824461510b4042105036400c81801441d2003202007007105d4101c02030ba082450f440c04d00c0d903180c001d2041c084000b8002d4180c2076605100306981c290a4a401c14100030907150b00b80e940c4502e103a01104501c3c1d2480b0140d40440c0c03240e110304455801441c4842c0a0000f0140003011645005034295910182002d8483c00c8004d20791298103041c00c40c03030565042d20341c0090303540321b68101501d4a00000e884140c6107000094407a00012241042001414200da01c1034428850401504000807440d640c1d41040c404403021a8002c8800f200720410201d00b4411104c48034010108a82050303821110100c010b44100d8102c2548090750000807000351842001d048840000141000c6c2040d404031031458449001134181020014090313142c1c3d01c0040440440e4102e110882c00a80007001210171007104022622429071070b00440c444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 783546987 1250 783545737 783545743
    0x20f0d0b061903140f060a0302061c050a0f0b09040309030b0402040209131b021b040f0b1f020c0d0b0a0506130e010b0a050a050a3506040c0b040f06110f0d02 69
    0x1102000783d1845960f66607105c40b411040e00c003a1001c0d41c0c03220420200b00010b24120008240e0141c181026010440080c0380b604192802501c007a2034075130702c400001003200d41e2441805000c03181142e54070744606041d02d01800c150040e000140484084000007015515690100d40c0100c1000c1e0910001404000c030341802002c07001d1100c510801583c0c0c00740f0159100107082c001102d1030008a1105000320406c1000410110004904aa4450450001c55520011000302d501003544285a0082680d03100038104060601e015124003035074042480801c800b510309075402940351400050944440c00002d01d881d60034141c0ba030040742854a980f884400c19003000701e00300000d40e0403050759500d82003000002c007014040c0b2500300030981400c01c00040c0902c800701104d5850040389000d40210b0318912038120f4180d00c40b01c0141d026005200412202d200d0000c000e080b00c141c0c5504090030328600c10b400d0102c901c07585c020003200b003150444e44441803000408603908007040340d56580c850f01010351 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 783548237 1250 783546987 783547001
    0xb06120406140106050406030915060308030106170c0406110705040f02040302210c01081e042102010606023c0d0809010c0801030b070e03060403050d0b04020f0d0b061903 75
    0x150a604240c0400755240d4030b20708041c141c03009900d4607030415082810071001004a180155000040440c11407007030711051003070001443c02410b0542e81d96042c400c015020700e10714141c0300d40440320441000b001c200300733509880030b80e606e9160195030101604041c1d482d21041ea006103074058079004c034200b1944c4c5103500030000c44e0310030740c0c04075120840d44007520161150040e05100e130750441c44c50383d000c3d58400c40c00568401101d8801d00341c044450240008141c1c8201c400710754111191500243c240d0030850340b09139400c40b40c402070091505111000351915124443d44900c100e41c0600c030310b2000005000c40c61100e904c950382445401020702c0c01903407031883c1103c05010555000109800c0e55041c000c601041c1b5540d15844016441d50b5103003820740500030010020000010605985da0340c043c003500f4001c038000d036961920b91031005900b07001c4540c4115050300c110310401c4813140e80f0780250142e0f840d020404a001902482c1c801c041a0301e0b00c2100c0007a80801124075000444603016840b0382 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 783549487 1250 783548237 783548243
    0x13020c120a0e0a0b1b0703050d1809051315021b07030b07020724030902061306030c0c1a10081005011d0c0d050a020c07030507030b0c031006030b03010b061204 70
    0xc10045500705105501000340101c451020003001003c08207891035410001c0105c5050454154994070f4561034104500083c1c0040020420224411865203e9005101501003558204414200640e009098155003c40140342c404202c40c0c070040040395038166003112105010002407040d21010799501c8858a010444400c616130022814462000584006031040d444585a0310031440c0e00c8800302145c0c1c144007a04050f100c0e240070005844400141c080d804000d0038200001c1c0c18544003505840c881c1e050380081001c00000400400c6601c282c0080b2000c01c61081d011541300d0220484207101c2541020f6810301c164104000c070340c046513001504075400c068414440b906042000f1590500660309000c4400c030902c111440d944680e0310054004c5643c050042c90702c10011142ca04048103a030040e00e040d000540100140300d010100903900090314544103240d403400ea11080015031881c0695403c01d03685206518203038038250b21441e0800001041d0070f0b00c2d02c0c8604599010854112022 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 783550737 1250 783549487 783549497
    0x120e03040312051312020a0302060418060905070e0105130b0301080d030605060a120203270a201c1a010b03060f0411030c0f04090504050a0b10050f13020c120a 70
    0x2030003248220f040d903031881c681c1d00c0942112894140c0e24000c215403514240c0e170090000b01d002006070307613a800900082030f0721010554401400350b860022250303107521200d211414242000400e580c44010301c407029600b401c200e52030b0600400003812811154200120103140040045005840042c5e141401451a076003404a15164401d21051f401100d80800c049088017201a52101140c2c002c1d6901c07811001e040d4598111000081c3c1100d001c409502080e0b0300171010800078442d0060850005080b02d85d41840c103198641c0c0469003c6030348051b00d81ca8540c90321140d41c100410300302c09103020f00801210f1410307540c4440700380c1150350007036920301d2040c4201d041100366400c4c60f000348040c031802c820cc1ca0703046989507481038103140d01c0001040c0b600c00b410400426201c415118081c00390b80900c00400107911b152800c01401e010180400004120401041040741c0c0c071200c801c40c8013002a1668444034030f4010a100280c0207120280140b030084810301410040640060400e44100b82da40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 783551987 1250 783550737 783550763
    0x6150c0507060e0d03050a1b12140f07170c011407080105102c180f0f0112032303040311121e090d0503121e06010804060b01120e030403 60
    0x2594503c00c0081c04541040b1034110201c08280604003034107400359242419207440301e1440780b100700381d4440e81044500924100002c101503600200081064042e100c07518507007550407000d01610b0141620060005800c0b0400100d04202e1009480c0c800149a0081c400d410070044d03003662031079089a02c030000414800c00042e50340b0386405108051021038540c40790524814180000d200355440303101d032400c61070707644000d000d41b87c4100d412040e888200e0140c40301d042c20001000880e90141100c03505a01d140c0062243d03040315076103521180c2c0c1c1800c02c02600c102008803907140070101c0c10100080e0001108100505030005121030b00c0c1d88210050f20741401c1d24900a154030300070040c52004a48001c0c1044c100800c09000500d030741c1100510400340b0441950310240b840d4448050b142100540105001840307900141d07501e040e204070f044203801d51402c100020b080d00350060011307040c203480b80c040c031485902031100e0280341402d556007440500c01c201d0519a9982c401c1c07000700c40407034006130 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 783553237 1250 783551987 783551999
    0x15182e050403080304110f03070b04090b0409050316020a09020706020306030f19030c050c0402030702030d0f020f070b1b0a0c0302190308070f05130e010303030b0f1507050106150c0507 81
    0xc200c1e01034a90142000b419078a4503150410316041680320582c00024031001d001269908021907001000c4413420aa540c9003050054801e41d10340707103003080c0118107200c2c030640082e00110550b4410703215458500403040940c00000d2251000750302c149001c80c070001301380d014051150000c61003070f44250201d5070356812403d8052394654602507041c188100013620f07100024801c1803035091142c000c00032900b00d02c4131031000404a9100b039400c2405030748006040a900c01c0d1900403104030b161840c40450400b410031100d55814440c14100a000750518400600120f05180103101c140f041c2110f910703124100b4030300c0074041113004042031f000751007030542d8651041111019040300703650507590100b03691506641600e540401031406010310500b400100030444040480c00c00420f20084103060700d51650030050116621411107900415443c4200c1c03d1684542088200101221200b2a600d41c89400c0050043c90650029803031300420000040c001c0c2d40c440070b40c40c0d0035400f0314260b840595a0704 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 783554487 1250 783553237 783553247
    0x50a1b020a080d0e010204170705030d0c080d020d1e0b0411031302060901110d020c1c050c0906060d0906021b0708060123040c0c06110915182e 63
    0x220000e05035182041803010328401038204e505446110f1002500b050744071008240c44000c0000c1080c07842d4400a010040351030100000c02458109017003030703040d007040d68071280014402d83e0103c035181900040c004a00340001c0c0d1041c001a0051601c007101c080a11303150101030182280e0052186051941c1502020044000c4a010740701c090600e9080007980c0d820301c40035800a02409040c000050315584030301c130080c0182180d0441170381c003400c0007186800c01c200b45803441d40c18455a5142e420384003400610b0014180000782001c48140d07802e50380d138800145080c4a040000c0135003a0a28100108128030750700079104001c00c06541ca0301d6213002d00402541c0c0c2c5560b00c64051141e000f400100495581903080030701030700d80f0319014dc6113500c0c030341c0109080e03803a280c09000005024a207540103104961040c101918400b41e01c0c141361030340c064001980c68244041c58805a400015903e180c0044492000d42d03220024252015281c1c3d4107114115181c0c1440481c0500c9015484401c41a03100d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 783555737 1250 783554487 783554503
    0x2090709030606060e0a03020405041a0f0103030306060e131a030a1b08031e0a030b1f11010606360f140d0201123603110a0209010302090c0d050a1b02 66
    0x500121b54080c03543d000c10000d01b401901c1524a401010104500340e04452107103071040b9204c0401d68919495864000c0803603615034001070400c80d103203105c220243e0300d400c501803030600454004524604950035811258100040e00341d41442076600c00400c00c030b401201403442030004241d083d03500f0380d034940301600c0303103e103500c6c0c01107001c1084020307030341d034061180038180000740d03441c000600c1c2a142c0081244d042d50700049001001d003260385414820307409030a081c101003000000340519898500054041985614511034805140400152541800900201d81c807003500034502e1250359000d00d1b038448280d6010305051120110702d5904603040034014000b40c1581a554041601c0510048100411500e0243c410b40201c10310500d1220201440d5541c140200c49200000303540d0615018008011700203004d01540c20000c44a409a07032100c1000b81100d405564580d401d07030b030301c40c3c0e444d00030b2051036081c40788507190500748914080d440d03020340e640da41300030307104510051704400503643d0b6071031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 783556987 1250 783555737 783555739
    0x1e0d02210a0503091002130e2a161e0507120c050f0105070b0f071b020f0603180708070f0b13150c1e06060501141602010c02090709030606060e 63
    0x40261180642c8103800455000f00d504007034821840c6400008810703a4030080e111000ca4180000c14003042d0480300703c094000b07805e000e400c64803401e400b010344444114000740040722007000c642e03580c0c0c040307034105250b01c5641c3c0801404840c07480103104a0f10440896400c2e2250302c10504046414424019880340e210340140404021a01e80f1081040d041c0001c81180d0410006101250000d03882d00ca42601410700ca07080c00303207545048003000740340c54240c900e6207055804d4400a0809a1251901e01310100300030799000f0303600e60b89c108428428400071950700910348900040000c4407130020400100703403140541c200d181265240310003c241d0103a410b0b0300d0380b01035140314100071940e6510181c81d40464203062000e099803880e1a00007a1680e0664030260f41c800100e80681041803e21031240a00300c242042e001b06100c1c001048518001c46500342c4120f4200e1041505685c09020b0340303200158010100012460000c80090030764030184022101581840804280e10f0b00440b41401d0340c0c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 783558237 1250 783556987 783557053
    0x1908010e030f1e041814130b041203140a0615030506030c30010f110c0303041e08030915090105090a0605040c0509040305130905010315020c1e0d02 65
    0x212000000600100100f40040c1a0008001c00502120321a104404461590200180354503aa17005403c1601000b8000a01e0041a9040d50002081500006d400c1a0410342c40b40280060110690040200344105c0100c0c1c030741072040000054440d0000c4040e1140c003082000c400b09010700c25401d503030007a00d103581c0c582c010081000c82401c140e00765500034400c0c0c0102d05400700d0494174003ea144410010800300380d450700852070845a441c001d2030f00b29406070268a2900000700000350b120300018100a05000c41843d40030031111201286001c49500500001da89081c00d4140c4d41d594000403401c90224100d1100040310313508180b00d4a48242602d10140824562990700c6a0003060010011145045135401c0402c060704c07003c44140c4901d100ea201d4a50f5544081d17103000c0e000801e54000d003421803c010050000405840c00c0d05d200811101c40584c0710000456054140900c6507034114044410800600c8a0180020001c041c030322260281c4104800b8401c0d00d00d4842c3c140c01c41250104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 783559487 1250 783558237 783558247
    0x60702040f0b130b1518060c03190903110d02012a060504030801230112091514060f030604050a020105091c0303050a0e0c030a031209021908010e030f 66
    0x8102600018114107084000040c40000003000401000098100b6010141c3e43c290310b2000d810000e440d800c4c1c95000e0070000b8185004a10a104811110400c19014100100d00c00740c885c032040058a4403a1b110340c0420311031204590009107105014401601c0410280482d072041c0e042500c0c00e251003580680d254a0a0b03107000c070316040092500401170304048280701e030501c0401d0342d91007010300480c4296201080d6514040e0040c07400381300010980001c0b07045204911240e03802c9a10300b048041d22400101b4140d00c2c6081c5109406440b0005c3c08805042a1a9107010348034192028482c0008440b2020394151100602d075561404481c002d0542d405040384001541c0120058032859400034296003001415514000c5501d641c140110003194483c014401c0f41c074810b00403586903100410040c600030404c240029510481a40050144188031010380024001034004c0c1441640242c00a24019100705424404200342c0c0300310700182d481c00486102015000c001c0f81c243c6c594801c2c2e80c2d4141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 783560737 1250 783559487 783559489
    0x5040212010e0c07050601121b081b06040e0a0606030f110403021207030203030417060f251b0c080c090606030f07030b130f05010f080a0308060607050f0a0303060501050702060702 79
    0x60500a0024a0508001d04c82c110008104000c4540030f020084003800c00c0b04414500580c91010b1484041c0d41e4803050003007131060440000b030054a46e221401c0540c2000800d034086a158030441d00541b0341800340f0003c2214404058010310220303071441d42d041003e2038140342c05c00120344985200b0082084208004c001500d85988180150350714841592101c556a030b001902c1c5912a0b84400b420030400d02e00211041e1090280039403024002c07110113624035000300007446403074041c4450030f0000c150000e800022481002ea01000e128502d040482035800c1c0e0500007104400b9102e040354030301ca110030a1445003801c80c00c1c24011200500381c103045454a58102d00c1c90304004040300101507681c4100081c41c0d640c0b0003136549002140d840068078641c114007100607600705800c202e0300b8951002040054140000381c0b0b000a54041c60b00702d0590f22407100080d0706100d41c1d000035100388a8201c3d25041a507001c18060b0429102e038400700281d50343c4400549240c0510031011b584031000b400341c0409 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 783561987 1250 783560737 783560759
    0x91a1f050904021306090e130c03141c0c0c09060e1602030904020307170604090308070f02070b0c030316030917031504050a1a030a020306061012060305160504021201 73
    0x71000040026007030140e240c442412043c0d4650020000598550003000840c1703a000d00240c00c5250103a00c500314040c3da40710b50031104003501c4000c0030482c001170074075103039403045c89449a004c0302001b0005c092100d609005003254a1100e0645040011000001c0c500c591442500c04461078044881c80560b614a070700410b80303101e09050760a5000c10004000541d5451004602c0341c156034aa07c00c5403c008140d04070055030003442140510301d4101ea45000c81d82014074641c1c04049403405146c1001105403c07810190940e110950300c882c0840c111740c18110220103584100c0310981e200c070400100748401c600303903104544040e0074042c1c00b0203020082a0004001c0d40c2c84010500c0b0804081c00c808042000c640c002c4070700c6806d06075591021881100031640c0542e6006086004000d01040b0383c00192310f5100241c54244503400e010420701605000b040488a50080104100101c40c1d50741455600c0d009607008500e100041500d000c61079260501c01d40c2c1287c1c000410030821a0300b00440310740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 783563237 1250 783561987 783561997
    0x62601060f1a042103030b030d090911070807060e0c030a0c06140c03070302070e15090115030e030f03060411070f11031011090a0f0b0f090f0406091a1f05 68
    0x2210b10403c00031410b21180d0228181100b02c003e0f00008604840c1001000c841030105403500c00c1d04803941c0c0f50503640e840344542c0c0540e1b80340706002890b01103e0506030a2407050701c1000300340070400303c5c00c2c0041c0f043e1540910b150840202c02d43d5401f141d80b40405443d80003180c80100110b513404420f102c40340c80750b000c511000024184041c42c00004042251840d04054401c4006038000742d82440069a80c1d01e40315003181c81e01000d05600c0801c600082c0c0010f405000f55030701e100301101c03040c4440c0d2113900400403408803c81a659511244055420551300443e111380c012403c00d0402510901028110740391140c10618200800d4440d6441440404410380f003603a16100b9080e103001108082d105005d614409000c605941d069101e041c001940b040da48085005a0200c2040003203640704012100c2d41030780100315aa51f4210b0000054840c00340d41401500a4130340b101c0405c14041d5a0701003031400718100f4a0448a40b50380341082414003d41811030040100c3d08500b16000d4041c03c0508 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 783564487 1250 783563237 783563279
    0x80c0105180f04090f02031006060219051c08040b01080703170703031d010606110303070917120d0c020c19060e030304080102030f060910030503190e04062601060f 72
    0xb0145910b4070300024156003580c5815500030b00b604d0101821450704218440766010303003140522440c1d25008000e504d404c1910217140400b0418410030040060a01c8822251000344240c80d51207900c9180041107031750222012a448030440001140384140091500100c9521400c100d6808040c140310400607000301500314107150f102c00240d01451110980c404224140400002d609440c00c40c0042500d0001c540a64198100700288100c02d540409500c0c203a41084e061310b541070401c01021840c000c40c07002040040c40300400c0780d04036107841c0d4001c04221070303199086a00c1910308500300500200f10301d94800110205402c100940c1c1d016a10000794400000d080c0d0b400c1c150b840b8005070176603000b00d8200c0c0003207118100b0810585820000181c00152050700714029a04558031107549128400d03002e101a00400c0078050054410291010f4040f0701030f00c10300040d80c1e280c10551881c05c403100080c0710801d905034088450b0b101441004121000c440c00d90440a103030200005003101511446 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 783565737 1250 783564487 783564499
    0x1009080c06070f02011515080c0d0204060509010807051809100e0907150c0f03080a2306040f0915020307020102090a1e06171501110111030a06080c010518 68
    0x901410a0244040341c4500c580e502c4204002500c900c000f0701b180d04e0124213a00100c140c00c2d061043d005140425101c069a608042215403525019505107005144c1c1e00301072503000140c041242c6d40c0c460047d080c2d150003030b20b920016407284d40303094909020b640c0414561503c0d0044a0790076140103d002074109800c0c49400d12010380707911b0307030840f92007003202c02ca00d1643c07008800308411128040030040840062070408001a9a550741520343c4090b02c0c00682040b204134080f82e550401540201c0d55141c08030303800c45c4ac0c03801d03007840c01522030310840340c1c40d105a103031900d00d074001c4409004407002e69901064100380b2402d5101c00800940010301400b045650a00c4048415100e206070140603100b110346044241c0349100c0881804030320764020750200402a0a5028400742e003100003500034840a001d249640c4100004a8a458207081c00428940c02e1148401307842c400900103600401e4100420310400e91910764082d903488401281c1070000700d0821400d08218850b4240308a480c50045c14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 783566987 1250 783565737 783565747
    0x1050d170c03070311060c040e040311190b070f180605031f03080c12210402011215051207082a040908030601020606030a0c0b07020105071205031017100908 69
    0x21151554000c614104c0110f02c1640351910995010414180d10000300c00d402840c003418149680e40022024000038140015440c03c6030f2412030034080d0309040c0380030381846040100d55090500c10303d08261140004101c0c101030112107a0b02c10094122481889000504090300c1e18108644680c03004040007510003426140500600840e543c0400450190720419111018208a40d0410700d940400c0c48004204004044110034400032007101c124900a001744151349500069034289002560b003021585000702248404545032001c10030780f1010703a000e031805507010340900c0c0c3d80c08540c06420520b0303105002d0070610b1020b869000804060340b121003251206094089070544040c414115200140401003004550741005100e40c001c000700c00a0032901201d03158400403203d10300825190b0b110020700320301907902400441c3d40c0ca82c0d0210701d8401c0d42c1800c40b4001c1280d0015607200356121102c0e480002c04240380d01940c451440d0500140482c0a030050758031006120440040711180003c1c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 783568237 1250 783566987 783567007
    0x10203042607081c020a0b060f0409020910090b0603010518180f030301140f1f03150e0f0f092503051c030f020c100e0a051b0102060f01050d17 63
    0x71903030004000c1c003c010702e1940302c1c40c40c0038602c18029021100865008800031004541d90200300c40c2c0021058a0140c402c00184000c03d01400d40c4601c0030703401103004400d0165070040f4009020407901c00281c100041d004010810141d484284105540541061518010500c202003c0c42c1c1220030781442e84175842c0c4041285040c51a1f1504c4480c0a0f00084010032003d414a01c00f40008807003252a00e441c0041d020005021141180e101081044140c00603c40c1d940650710101c001006410100342403a980c3e0404117816070200c411502d5641c8002c003190b103c0c5043d41c0385900401107207005e070410b00e00d8490448000124040011300002e00c7c01320000204ea0b0511440d02c48540c5a01004c018805142e000740c255410303807194101d203610401134551200004a2601c5800781e80034404100c241418029038a00040301002401ea4003d2208000c000c00c00311000100c400750a07001c0c0c03401a5201242d0100c2c1d10703024800c940d004029048143c1c0040c0e0728060014200710a03e00345410001d50030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 783569487 1250 783568237 783568243
    0x10509120c0d060f0501090908070b0405031e040311090603060a1808040608070206070e03030d1e05130311070303090b0a020a08031513050412120608030a0806041a0102030426 77
    0x2080c1c0f41c29560b5007140300d00e4001c600405001d01107843c01403028140030347d02c0d680c51303101d400c07009009259110003007820000d041c0212042600402d40d44245e40c140001000841e0b400b910040f90f13040d051084032200d07810912000d034807901740100a40240e945003c4940c001e8480c500e000390003802c0800551001541e0b107809080601040c1d0f0300c46100e03141554020f454003101a1070707117080c0201d02d4000c00c040d50300001103c1001079000400314149405001d501030846103041c442c0305c002d040401700300000307402d01150011240259510b010030350b6199143c0ea00c424081c08041d0000f13888010500041c3e2508004000c420450f10445020b400c041e2900d12407034005440c00e1050b4806603245406619060480ca8808504100d080040382010764400f01f080507103003162028041c40125451350300400d0b5108400621080e01502c4d03983c1c802c41e1005103840d0003118018400c80c640700c041e000480c4900d100c9a90314506800640c500350400d070f6a07114a10701c4200e00c503c038240e0706111032200c070414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 783570737 1250 783569487 783569509
    0x12030b041b0e0d02060a030f18061e1401062610080c150901030e07030519020109120309140f0307080c01090611060c0904110a120b040b010509120c 65
    0x4601d8004401011003001010000b030b000c0c455200e0600d407142d100142c0c2d40c01045941400d000d04001400f8800070203460003401c10021840d2204044003113000610940d504100141068884003182d04001b103800b5030300301d811004200d82c0703e00f10342c03005000c028001c4071840504203100310700014400d9001c207603058440b021900d48082c200700000401114030204002c2d044901d040f260002094104000f0b14032500540c8011130426172540e42034900e03020103000d403074055908a01910f8410340c20b0b0301c46d00382128065504038009082850005038006143c00702240165042d510400d50610307086150f850050b0404900c2d51003d9805116841540c081001400070801c54001d0042d941c926000944a084164440c2081c000c24600b24114180040b805079888400c159680751105e103880c012500400c1e4101d21084110f10002d0707001c0d4110b070043e1320402400c0b0001c40030301c420742a003418001526110030f01c10b0b020600034008440d95203000000c0221209080033210150502000094092505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 783571987 1250 783570737 783570761
    0x5071704060b1002030a0e100c05061509010501030b03031204080c010603200102060601080f0a06031a060a080127171903050f010e0718051203130806060d12030b04 72
    0x520b5510100c9801c000300149409a40c038000345007000b10248028140030401610365108882c0c441d00b02c04442d004601c0a40c285030803104840031071400c4901c000241e031071201018401d086280000400c0e40c0b00740681501500f01030f01550926050451a08000d00041c20840368210180141c0104140902c21800214007584100c405a403980300440e011070000504070b8110f402503400c000c86660003511090308007503081e020506c2e41d51345a02640c0106619000100074621400e5511a4413015041ca680107076000c0b0740940c0e01076a0362401600700c88440112500c08007170150030500d11000e00301d441c2c0703005000b400b6020000901c0208800a54440081c1d004620b40c15001c0d030003c0341d49441060b9110a0303c600810700c550400e0a440c1843c440107140404219200240344103000302d036001c001c01008040c141a84201814880036126040b69803007103208483c102002501c5000020007034080c1c003002c0e0800307082d8203494981401000f0380d40c03503441c01d040d11000d1882d503175100c0d48204403050030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 783573237 1250 783571987 783571991
    0x3052805040f0f03020a1809020418151b1b0f121808063c01080d05160201030b06073305071709010e06180d08010f090507170406 57
    0x1090a0030b030050500140c0002c4001040480c0500c0182c586a180d1800e8031207801203c5401940c59000c440a00b160325002900720b82000c140e0020344200f18210749000780700380540d0071440040031002d4100d804003000100880480140d062403240649000d818070f901454845203c0b00150302e604103144101001100c4080003418a104416408030440e280325001e00b41300c81506180c400741c80c3d40e4000c0600351901c01400000c1c1c540080e03282c0c2c816005c0600da06070700d03160706068200300c00e500c00360240300780b1246010312054814918070a40c100c841f41940c1448440000202e9001140140848071420740c01c510108a014041548071195001000b400e01080200c0c40c0e1442c503002074200d40c036441d003a029043c80c092191704e64108842c006490104890651903a0300e50448074007601d864030924280340240024061945844613203000c40f1895101150100d0040900c00c60f05108240718040c0c5911070254140000c0c0c10980006401c03410f03070301d0010101d80400c40340303001e204009c0d01c040b18965 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 783574487 1250 783573237 783573239
    0x60909030c03201e06160905040b04020408010e010506152b1d0102090f010806100c050102040f1d0f0f010306020f250c2304110c0a030801030c0b0405010c0305280504 73
    0xc4802c1000070b40c01b2480403072091001015901c05015883c180c0070315071003240c035071040038825183d03541074030028854407000b40891007a240920f4000c0c081520f440c0c4c06089041801c284030b180700c01c12201044021301c04034100250380000c0a02560b0203c054140003921a40300e040c5801c40d078403e15062000c07000c001aa504801000c01052580c1000e07540e06104a000030460f02e561804000c200c4200b4904041e0801a01481d140740240b00ba030b000540003080e0118086260382c104c554a0b0b1000c414070114815903281d81e00300e08034506d001c07a21904034021540040c0000794054000e042e0f2040b0f5425003a00f011b00e150b0b40d040c040c4020813003042034240111880014041c600256100800780c00c140c1c003980e80c0e0034032501c040c81d0f040000c420f8000c07038a407009202003007129412a0851200401900c00c042e6035841c0041424000384402d07180d440404101054051083d13044404442c016144c01c00c240c0101c1c4d90550781074001408009000360711801030713051840260499102144aa5100c0317a41d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 783575737 1250 783574487 783574543
    0x405070e01060801060f0e12070f18060f050d03230901080a060f0b0a110a0b0105031203090d0f020a021206100801060b090d0c17060406060909030c0320 67
    0x5410142e01c16000c22007540010400a5007181c0001120107140c0713484c0c04000e1103c808114800805200300c11139101c0c1c90300009905490045c6031043d659400c1028103480c01045181007543d945004050381140540350030001490079943e40404c00e4030a0500d070b17254a00f0012682d00c001d200308007140c0070034000200070000b0f6a121081d141d1168031800200300c02401c0104c00b002e45a00e5004580b1201d0300001d4800110380030b1820307020b00e00903007000c94001861034038103000700c0c3e0ba0030301c1001d000c0d214188142d4014100502600c6c4100706020007000840c01c50f40d0200c400881034410302c03065024003100300002d41c0301d000304141c0d0940c8030401000c0b82d05045038000003c0400c0c0e80b00308401d0345400c000b4001c0a2802e42211000d10080350300500c000760505001c440c0d034159074004030b2600d04205502c084108042078681c8030328021802080200e5a6401c14006d46480081c001c00189905180c43c0009000c0d100c49600f05010048040360940d2044403103241c01900c1c0c480802c120040010701080c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 783576987 1250 783575737 783575759
    0x3150c14031603050610080414030d020c0d090b04030803060f0607060906140a181b0e1003170414090406110a020307061d0a14031c0e070f0f0905040f050105040507 72
    0x50021b40c1c0004a804082d00c00034502a0068001080c0c043e10000075011b2010402c207689c00302c0c904000c2155640082131000e40d44030000400e040c04101251030025861691505032411243c001074264070391344e07402081090340c4448036411a40904127122080224a551286231030380c910402002541c01c480c40c080f05102c401c01049103000c582440c0b180b4000e0f10644116030351159001d6507245074030b034210320441c0900a03943c22102007003e0301020451141140c0c4105001c4030301942e00a42e01241644054506104d40d003d80b07484080c0c030148004442c01c05281096005004820001d0925007008050055611110075007005070700101d400701c02d110051081610004e0340c0c0d0300c401c7e1502ca1428496031100c8440c07030041c000070b0607103074500c221403c203204440d2404080c007211880344c5d4840385035400508c10020040c015108010380810b4401c10010f003c01561354200480c004249001c0d041c0014100051040388c00d00e8949403910000782c024001d89005500c40e0014040450500300f00c611 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 783578237 1250 783576987 783576991
    0x301030602131a18030f0111070c2102010c0c0305161403150f0a0b1f0305090601060516030509090a0605180c030402210a06020c100603150c1403160305 67
    0x590f22014070a01840d980b05080f9400c414010b00f5107000041c4a100080c10030103150f01824165080c03648030301000b0720b40130040a1551040125a0216858101c0c0c41d1010003a00c2c0201103103841441118007640c09075a12031000f51080640070b03c1d9546039501c4504001c00420700012120b000c10080c044065a02d04010385a103040c0d000f410701101000342030740c0040004e07008000042156000c82c000f1001b94010410440c03010b400e0300c0a091800001c0300600c0040303c14000000e103000701040e2200310201e111412521540c2e1000d0800c42c012880b0700903602c42020440912008118035400f40d107400c20720070300c1502c1390b8000144540c40c010921810707e007040c18031640381d0004820003c0888202c010389802640584845094501c451503402e91404601162000da00c01c0c0b201910130804260010a21101c004090380c00c2540b80c40d04280a5540500000304580003100d203d50f803d01003a8028250a00180b0f00382c04401444801045154010350f083d401e840c01c00c94052000c203030140a515 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 783579487 1250 783578237 783578249
    0xd201b0a08090411040308071109070e090f09010f0921020604030504150c051b0a0b040e010308090f061306020d2a0303020903012415080a0b15030103060213 69
    0x2402558501d92544107a24500f4032590341c4228500c82c5030446070554002e140d01c082078560361115030410089800c03100403180d1048a91a00040d8000d11031040113203080703006000c50800341c407001d145510100c401888800c141d981c85062035560481801031415480c055012072212460520784401e8011643c074462007590f01400600000a43c03001c1287e007110390800c9018510524002d04841d81c81e00f14002910782e1241402a8400008000910940da40b00326111050150741e8046005180214030038004120304800042002c20f104ca4000c1810000040c20704c0303441c1c443c250020b500d44e04a1030441c1072000e04104c0c00d220244c3c04111094812190342014080700790403440030070440708400c02c0b4641d01011100c2c000101806501a602d06c504020000e008144428840b011200000664000029245403000904440c804811003400d202a5980e103030a03a82c0d0900344000c0c00c903040119401c2140175060005044410010314007079842501d01584d95048608072000c00031140d0050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 783580737 1250 783579487 783579493
    0x10825080103152f0f030c0c0d0206090c04050a090203030403050a050609160b0a02010b12030a0801050907090611030d05010608011e05010509040b0a0306050f040b07030204030b07050d201b 83
    0x1d5503604111010700c0840c02101020407404c803070740155195440c0940c500b03a254148002c01404242c61042000d030202c904400201d482c603030600b00d41207940f0141507490802d2900185011441c504050704001d078080301545000c1180034460340400e00d5581309901c180c0b00398100307061810070010180046500a80740c3c0008190903d124484802490341c01e220f114542c1030300142c5a100d41d0b00030740214840d100d005219144894402c003d0301c5d01c039840300c0b40c43c5000410400000c0703158508442d150707004003925601c400c002800d102c01907030110200c2e01e90154600c418402803031510a24003509010744526502e5200340e500d0680150400c2c0041903602050341c80d992014820f990380b0205480107404200d50100d4980311041c0400d00440c0c554001401190502040000c900c0c4032020441c0100d1041c80540c540d580c8190b81203080b402180401841e049041d4042000b461040c0064400100c21110020304a03010401411290113003401804c1010004a61001800200b851018140802b2405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 783581987 1250 783580737 783580751
    0x302060a0b18090115271e09050a060c0903060b030a03080a1107080c011407050309070b0307050906070606050f0111030f0d02040b0309010504021309050c01082508010315 75
    0x8110140b0304018142401e4610000340085500b500310220010711901025445500c988803d00d2004410300044240d04468020b2881106644105032409641d05410114804924080800f4080040c41515035119180304030700031903424480c05000b2001394984d481c92a243d4078208054030340a507500d81c42500800100c1d00405e8001503000d9000c04ac942000413148455801e107510b9002c0c041018000e0140862071010344e902c150300940002c1291a441c11741036031002c9084440e4801120b01c92015004408100018003020f0701450300420641030240c102b001640c00b003445504113038429102c0c1c81e102e0600704050b082240c11180c8500080ca484c60748100310042c42c0d07540340b00e403144d400039011000a20b0511140f8079410350b40544a042d2031280d40f414800e0030503000c1d10042d502a4403492419108010032a801c0c400c1c105029071000245c06a0614200151410040104486400d010720004200f100d0080d22442440d040c0c162540750265043d800c1c0b130460401c91002850394980342c070007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 783583237 1250 783581987 783581989
    0x8060f1804230706031410030812040203070e0a02031509060303090d0c05210d0228030c060c0f080a0204030506064b0312030a18020315040302060a0b 66
    0x1000c81e61254201441c40790710011040c0755100b0a601d004000614000c0700c0001c5107030307503242d0405013903060602c1c1d014015444401c00d205120b401e611000308600403c1001984200304185d0310782c0d01c04d0008064500a40c1d485509120200003250740f992002c1c2e0000400650a071500483c021070541501c0d0342420703182c0140820f0381c034420040c59501c00c1426030611003c01600c41c1c9460b0140c071001d0080e240c04030b03000200242c81c03106c80c00c995007107028502e103a8490601c0003944d2030400034004044d0035901500f20320708140c882c0e9000d0a408100082c041702010806500480c079a400d00c59950034151040140c0003059081e014198a200c180100010004940c000881c207030050300c100c90b2503c02d1800385445100c107081c0c05144c10303164590f071109a111a5690740b81034514034141c910000d14802007070105034844d042003408038201d000c1803002c6032034001c0950003000d9001c1c100d840010708a01135000030389041100c4840c0c44908455404010805070b0501c60543c002403001f4081c41b01ca41807070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 783584487 1250 783583237 783583279
    0x50f0316120309111207050301020d0509060c090307031103010e0d0513050616020f012c010e042c011d070306060e040506010302040b0109030b15041a0901181b08060f 73
    0x311072a00c42c110300b600c0d2188055046c00040002c04004000b1507950b1038601d81e4001500044409600314094600095040c804078030480d40300d600700030041c219581c1140e4034100c1e40324580c00016010765842c0145c40d440c50303081082888030000743d00c404e0b4880e19003404210103081c40d03810040c041c41d4240b0010201d01081c4082e6583d05d6411989240e00440130b0340122542d40034000034081c14440c0400041000540b12064010004280c2c0c80000f1012490140300c03e4031001070508410810030718180b844140860302d0605040c0c030b05000862003070034500b00600001140d02c00d005440d04040c130100100138051054000602c8031040e141114546512035544401051002031300454843c82008156846001c50714051540461002210706040032002640001150301d140180e150480c0d80d40381d080c00d880d41601d09203004008248aa0800d4030b5042d0303d910700650986043e45404902c000320015070898440103d495484034128608103080107030324075614605d540a410a500c079418060030b21 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 783585737 1250 783584487 783584513
    0x501140a0305213001051e01030e0f01060e060405100302030709090314030106030207050f03130303110f03030c2203080f031e0108010c02010f050c0403030804050f0316120309 77
    0x24100d100c0014100020683c0c451003a48806070300b0340c01c96614050040c1c0c124200b10184901044251030366030700e40082c0066055401c100200c0c0000c4c05040711402e40c442e4102c04002d0b90104c0594500d5100c405007682550201d81004072a50b400500300245402d1511660703074400035020b40d2010640c0745401280d2240440c5c0035a42c6200d031030b00404010315000354448041d42000c418090b58031740e582c00005009400022080f030b0305000c0c420b81c2e80c07840d92000094a095480384581c0c8a41c0c5451940e054a006040782039103ca180907110b03107440604004c4c800f9510944607005d01c190b81d8040007182d9500c110044400340071141c01c4d0071050000c1002c64013641d000b03c0340342c040340b640c81e02c8800240b00041400c01080d000001c01400220b581d00c41900402c0164080da0028010600d441d02504255a13040350252440842400708202080c0701d14271300380d00940a2019a40466202c8060b54207541c840c03c1404504015400301c4010400301103000c2003501903038a010405c41e8080c3c0d0720301c0b07005aa0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 783586987 1250 783585737 783585763
    0x90e060f0106110a171c0b031b1203042601091e0f02040501061809091502070305070c0e06010809160605090301060509041b060813060207031e030501140a0305 70
    0x200c0242020f400390070480c0c0c50b00d49401804060000700d410f0302241e015070042038102c2e00c04c1a000b2585103d210940103a0320a55402405003480c119900001c01c545405551100d0b4001c503030b8508000c0c21002440180b02504c0c807070b0980100d0113880c1c191051000d614010700c03995071380340c0804600410540b20b0081400c000c040200b00a0f900d841c1807080c3d051008c83e602030760061034000001400340d0440328460240015110040519548030341c103200b2201003100c090511102d0b804000c4c2c00e401c1907401000d6052081c10140e007040c2d5545c44028411600b504101e80c0e403269441840460b6801c01009507000700b140d00201104d2170984c141c3c004074a11441210148040420b130044035540a4003c039000e03005c042c102032450700e45820b050507100d1507542052820b040006010070182d10824a081c82810982100260400e00341c0d6060005d50004000760708100104204071192034000240c007503484580d9401144550410202e90007035261079450a1046005d441300300001a80480c01000f0024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 783588237 1250 783586987 783586997
    0x15020c01020f190f05061801052802030709030b040807020102011b1d1f0801090c0806150306130c020607030608190b041b0b0408010b01080123030f060709090e060f0106 74
    0x2583d498901c0c01c405112800034510f0160704208100b049a0380d8454071441c1e1404024040c90b146c061314803031781c0742c144142c02405e040d800d1000e9000c418580c0080d42c00150074540100500c1e6070b41c40d031003555503059408484400001840c01c05541e4240910808040148800340d50140c041901800303491171400b2502d030b4000041100d0040d5942d0003411520643d001d4035900c8031344030140b80140a18024040c413807903140b5025221050910943c80e00344203000141c2800c00c0c0d81c8440a040034160001040303680d001c0313a5066004280c500314001c602c4084419002000141050358000e010342e0f5036600540c80b82d5011030b084001803010700c4c581045003038107c840066140c035a0b09040c481000b9049500103a0b00142100045015541c070050084518980003000101c808200441c0d0f40701c7c0078401c2c5042144022030301c450b0808030310344100d02d42a004044032042c01c0c0c2080128204001110704c4d1001ca03112490070040c944240c060344070b5400316940500500e203050007101c800c1400600035a0104a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 783589487 1250 783588237 783588283
    0x51b06090604032a0609030201170103051203090f0334080d15050306090c0109060f05071e1a011403060c031501140f0d0b1c0215040f15020c01020f 65
    0xa070121584600a0b0130300c1d0310218558035010040c02c0514039100803800107450112000280c3c007405500e0b41a05d038030801803d2400b40418a400c60343c6c2020305281e00e50700642c514030750f074040c1c00c200030009000b0410044400134445d42d04c0b1070a01d40c1c1c003002c5010301004c4a07008400554044100d80540a0750300001901d14402e40200245500b01d406c01d6402d0b02c85d802c140507065100268000481000366240c1c0801a1518000c44000c0110700141020034000e10034200040c44010165890303c0c101c503d012243d00d110f4540303c40c0403010400c000d00c1034100c84014003114400c0c029041c00b015080d001040709050078180c00c2041e200061106000400c402019841681305201b4440071003142c07030303210f80c64202003003403100254400c91640304401e2130242e444a41e414994010014220482c1c100c110101c3c1e580c090107082801161030707201b0707100100400302d003440c0e07000c58a0002d002064041001541c02c0d0794080c0c6400c64030705040b815503000b140400c01f034800008404030f100c6071081402d101c00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 783590737 1250 783589487 783589523
    0x303020f0c010e0109020906120a1e060f0903091707030b100b0f09100c12200d020c1504271b0302190504060c0308130609051b0609060403 61
    0x190056888070501035082000b07208009405400c11a83e07107000f2200f102d0700d43c48200c10400d41c01c6580b84604280c2d00100c1d000d8000c142c40c2e0564508681240c14400c1a0390705598828040325440c00320904a46d550741200010705920000d070302e0240450b0f894036090780d0b140c1d496983d41c03101c00d0320001b01480b05c924002407481c903040389400001d01d9001400390301d40e40010703407075043d60308082d0a8500403400d488094482d144034a41a04010780c03c003a00b21180c1403c0d000403102e1000e900d0000d0307483c02d130084c03000d100d541082001c1d24480a6a40c00340a60704c8240040041c0d9078028522034603104014071040c0105505070001d070b11145003800300d440f04c24010341d80d0358010b0a151b541d803c000342c48226109100c190190028400c00da1002803003144115415001d0312a400340e405400300084000c9085000207005051280e00f000b0204001d0006660b00d54805e010343d9042d050481d0203802c880301e5030101c05000611601d000e00c0803903a05042144107004200f440c065484090300c01182d030b810104031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 783591987 1250 783590737 783590767
    0x50105041a07020321220b030f0601020106050910060201050a0b0102030a21050117010b10120c020f1015151d041404060606140304021305041e060b01140c0a030302 72
    0x40b83c0343e081080d0184d120178040c143c1160308880c140e505804001039040d900e00010142020566820808241c19070711080491b100c10f520040c0750505540d40d80d000841e256860000582c89407280c041d40400341070420f03000900b99500a011005818248003100381242e07008001da448010343e03071400c0303c82c000b403140362600680c0c00704035140d102c40e280100106190007005a08078503542510000d000450320f80313080c821000034005125000442c8070480040d8480304c1d41001c940b40500e071044440c0324a03036a0006082c5080b1581441e005a961000008180ba410000c01d0041000c0d000e0381c805150b0004010b41710f1040c00c00004260008009210f446546941c4880c80030090308261800358902458210001c0c003290142501154403000b10034450000481128459540900310a442c110010310440103080b014204075464107200f00c020541e1492032011200310f034083d41c008184007007d44005080c144811010700081181013084c69004440000c1031001c1e10340c0351900581e030381018040a06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 783593237 1250 783591987 783592003
    0xf0b070c1515050910140a0302090c0a092304020706060902070c05040e010204030819030b03150406140402061c02192304030203061503010b2701050105041a070203 72
    0x141e0a5162501d245005a940240301040700c0b9440b941e07415465030b04010310340200310781142c1c8000d2400030600203180680011810803c002e041004003584070341c005031200c0d4048409401c1c0c0500400c0d40d00c50680e000311440001c00424074140041e10301e10f10000311242d0070100c040d02071500080d5600400a0380e501000090211000c215181c2c1d110785410413900110b840741f18800c43c148648802601e0061007220106da070b0010b50359242840030081140600081c0e4104400d141c2c0d1542c076041e0725141408001101e0203c03401d2045686002d08d032034401c9030307041c0c00d19001c010090410000180c5480049541c0c0e10148032002010040c0e40d851100640700700b21652a13840090301d5002e611a402c8841d0480e016240c040d1840d224405000c03c00c424081c501c00070358140e001e040854944000410804000301c4040c0021800e03040c0d44022a000041e40f83c3c079034081044210580203010b10005c4121b01500c0c0c2440c1003071a0611b0701e1000d440000720351412500e909000903801003155010003081c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 783594487 1250 783593237 783593243
    0x15070605073c0305090a060905070e190c020309060d05060f270c0f040510050f130e061509191511060703060b0319021b061f030f0b070c 60
    0x1542d807441c82030262000d00b80440031055412031031000510414064050740744105480310090000b030106403180320141c1200700781511703d802000700100702039007101c04c80d03442a0300449004955803040600d80c400c440981e41000215041800700034200e90b00c0320300702d40c400a003101020440b521001c00180c00c5070601d000c010b42c80042c0c1c2c011505a442146d11001c6020a5440b924581d5500c407588581d09206008050f80c1082080005110524010f44016001110361402034108072251030407966551140400101010400030104100019640c4007948a02c0940300b40161605417122150107014400a0a00c508803282e254010303000000d003094014031600f851854840d02c482030142ca140c1c0900805152400b440c00003a001e14040e0294404642e4070300c0c601e03441c0d681c03036000c5401e10700e041a41002c110341c0c0070444050031030583d0208500d10342c02a00500707202e0402d84d90f0240b02d16400103200701e041c58800c1c8c0400c0481d24107003075a031040d034101d8420728069851200442c0c03d892081001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 783595737 1250 783594487 783594527
    0x3051e09010e0c0409171c05012615010b0c0f1e0105010e13060f0e0a0312060501091d07140301120c0b190e04110705011a1507060507 59
    0x1211803201504841c640c9020300e0141c07001d1140b4030041c00240c030140c61003c0c14200c0c1c04151500032290100c000c0059003921601a410983c034042c922007660400c5c0e00210080052034461007500c2002910306019100e40d5000740310b8201e414a14000304181441080c0b10380e4800318514420703c5d004d1059841c216256000d80340b100200e00d25402010488210a5643e9803070400046041d9284404003130207641001d41c901103c0703400b50f0342e10014114803600c440321aa122502e10a2550341081084003562082e103c08000c0d02500d0b88030b200700c503841c2e40120304220b413000040189c11403c0c0304007100c0c81d10921036040c5503581c60a0545821400700c0204c10700b0348002000282c2007a030300666104041c0718070400444180d45d041590214029845003400440090b0400c07440349014403082504110050004144c2c40e00c4005c0149a2b03070803540c016221a5140d90514000072112541080000c0e41203c003074980e964030301c840007854020031000420080e42c850110f4a124010f529201c200c015420300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 783596987 1250 783595737 783595741
    0xd060902040807080a05030f2a1c05030709141528021b0108090f030a0e04050a090b04020d080706051618030b1302040e0316050709050105030a020103051e 68
    0x2000a5100740b040c0d5006000b03400c004202c510021842c0303c0e0307094000d8015800c0c554040400d43d0a5403010582c161607080304d010170284085000c0f02441890509070107004e07800d0807040b01c000469a121900c208110003081000403079074200c80030005440d541e0000f50b107041c4220700814050000e13016207030084a000700e00700e1003d0f04022010b02617290050343c07040030303040001d00a90340d40800601ca0100a40301040d040e0b129445400b0701070348000f004040301e4060070384410310307411070f0f101d42c0300711000955045080c2101d00345805119046040828104038002003603d800402d00c80141c80240305421303d1928000388003601054800c82c58100c88204414184070f24a035030303182050214400480c4212540c052004010784a41c81240d801c510f480c00c4940d03505003421f9409108113012070340030366112042620101c00300041e01c1c0c032100c114505800f040c1642009486d0544541c494403003541014010700098030041841008240d0a0070301180341d403980c614085403880500c0f51892010302c5001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 783598237 1250 783596987 783596999
    0xa02160f030201090b120f09011803020d0e0105070b010308092403070e01080405060705091809160803040311010e04020d02070609140c0105072d05060108012313080d06 74
    0x40c0c2041100e100341c903280c3c4010ba403404001d045010f030508034404074803003100203559504003849056201c2e501200002d544020307121546640001300350b0940045c1e00c0340034244905600001401084142400c0c100e0400d100769480c0044000c1c1404003c1c018031020403c4c2c8441d0b100c00410200b0600500d50940c001002c0c103c0a40f03003030300101c0e10900090b0342e1030a812002d5000c0d404080c0103070740003000792200e5903441d00d066030250f00031141c1380d4001c0710705100c84040380700e4100a2130080b64441d010b046100310f40d01e035404584285401c04010394100700000c00000f012030004501158080c00d00c104150340a0000a00902070001210220307800054801e04000856000300d5136a0710411580c1181d81526131116694026000c0c02c40c0800c104000d02c1000c60004a8428001903440382c50b000d1812071a6012821250200c0040310b4661041c00180007003034082c029107020f640b0b0544000c03070701c00500108294001c1c02034002c0391805c00301c4240c6414401114116641c54141d00804e000308d5070f981e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 783599487 1250 783598237 783598259
    0x170a02120a05031c050a020f0711130e030904051807121a0a0c0306060e0a0303082d010806060d02011407021f09060e06030402030d052b0e01140108070b0a0216 70
    0x684d00c6407414980000620b40e4003c80c82600e024005003980d0a00b01282a6075101009003403818031a4030920a00c04c9855441c2e00780220962a25040080e64694425609010941b032010300391144140e4000e10586401c1c00001c3c03400d0440d40c0500e501c0c0700b15600d03810301640e208962181c0d00e40481c4250204460001c442c0c10140c110403d60b68100003042c0d031070500b2034143c030444040c90340c00152200b04102091240f01d20641100c0c425014083d0135600c840020b1400390881c88203041d00064000410091400f444a0ba600c9001540c1d602455010b50b400240502111200750041d86408035150056454070055104c3c6c1a546001064a0040516002e410310031103105520001e9420042203025092050a80b8003e0f54090010901c0b0740c0104070a07119a0820b09030b00300d090840d0035519000980c08228400b06440c01400040c003c00c1d001d407a18207550300b240e8001c00900340748004004070f0303900040f04001c44441c521243d8079540007503401c03410800c2968a5a880719401e15002c51032060744 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 783600737 1250 783599487 783599527
    0x705070206130e0f04081b030d0e01060503061014130906090b370b061e04090e0c150a020312150102010e0d0e060d06230901170a02120a0503 62
    0x20f80d2092035542d5080a9010705141158000c00c481018003800a20904410405032440c075107006480c201b4032151100000c59104c0301018400f60344511040026040600400d90000b19040d00035561a08002550081341c5003800c00c40d000e140d4500c11140311032b14680c05074000c0b07548004107008286a40c00c0051200c801519154050b000c601c46003151840a4081084c0a000c0100120f1030081404080002000c2e101d0f1403d40001c0c080009145010465070040345115200304482d448a08094501c001c0b5000040712502c4e60340980d40f550042d0341c1e40042c003026541c800d5500c035561603a112049085000c0c400f04a20751005120500002e5000321a408400c8102079000f0002030391032004242d034400701d414552000c5000140020700d1818403500510f0400012030011030707515560b03220f0b030342811102004000d4013840014007141c02e2500241031801015000c0350044200e49030701c501030b200c1c10f415800034801c580b8145240d1078080188640341c90203070014241c039140c185140006912000c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 783601987 1250 783600737 783600749
    0x9040b120c01030b3312070815060406121e230a1b0e0d12051b01051005010302070f02090903180409081b16090603020a0e040b040803070507020613 65
    0x130000b142d9028200f01c2d0403441450000c601444800c0800c0821180300784641c810003540d10410041702d10840142c41e86140100190f80ea0482a4680321092051a0803c3e444840c40741e10200070400c090ba41c428140c6001c10203120000400d000c04403d04884503216014480c281d508042d21250f00c1c0700b8200f4440c0d440c14101030708041d0356940307100780b80071120000b2000d024802170003400e030660b070f22420f0350740f00c144400740140301000015121604000e001d2183c1038001071002846030329449080c0095002d0a8940c4000c1c801d82c02e003413240c2840c0c41400d0203000d04042d40444c2d03a0060000c5190011395641e00034101c07034418203201203815203c0d0301654440c01414a03420f4800010300702442880c0304550410030752810700500f01703da01c00300c0b589907803104403900c15103034108001d58607184050000d06000000041e20b519502c103001c42e941c000d41c07000001d5400d043c20480800ca006281d9a88580d100000595950300c900052f10140103964020390000300c08903802e00c15030780c002d150070705a0b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 783603237 1250 783601987 783601991
    0x320070810200322080d150303020d1701140f04020a0206041a090c0402070203010e060712061a030c0a0915031508010c0e040506030f03030a020403030e190b09040b120c0103 76
    0x282e4885a078064402a5905800950904160401500341c800d1500c4054881e40c04585040d00c209403440507684640e000c61440605040704104154041003021110718440c208440005404120a4400041485410802c3d45550030800059954003105c070100230000304110b440d0304035400001d41e2050101e50884807074100380360321000882c1200c1c000384030303052084c0203203200b403480c00074000650000e1004a8141d0b407101642c1101040602a10341304060729030b1525020360540e0b203c1d009803542d03a0f0014844801418001c40d110460b00c003140c0c1d0080f9950352007035554480701d20807104186141d200554074080c4081069405d503058001c1020021406082070340503803100e920034200c0f8220614440482c854003441d03040c80c101500021744c4103400405544840d04002001815a03008603000e48040c0c0c1c1c0000e040c400c0540041c5030030541041501c02c2c050740740c10f0b00541004001180209000d141c40442c0c812840d0392146c1003840d182070041d00d0006007110b248034040d59648c00b4589907020038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 783604487 1250 783603237 783603281
    0xf050601050901081603060b06070203010212040605061c0b06150a02210f1210211a400602090411091c0f122007030320070810 56
    0x3c4000a50581c5d60b26444c440d41d54281c0b0796038500e002088074014203a04101c062040c0300c00740c1d03420302c007800c5484504a401d03030452515280003000c4402c020311241c03181c0440550741e80c00c8508030b151000c00942c0625108100e441d01400200c2408817540e1034101c0503c0010700c400740550110f0411070710031202502048010154581c0c842602a0031828032800c5414005c02e9000000360951640100068841c891030680794010480100c00401180303600c10565002041004a4103d41c1078002d010880a003d460500105a621000f10402c0c0c081780c0c43c00703d0944e01d4001143d10394200c03440c4108c07545556500080d28001000c0c3d048036517a24411032401417590b0500c0c000c0d004072180c5901c001c044000d10480d6200c0c80610024511007618049204010000010440c8e100d0060000e040d480e001140004407014129456000c02a00c1036904030f0141040043c1e004464880c1d92030100300e50340c00b440caa03506001c4c41c20309c01d503003c009148101a1942c031480680c0d4030480d80424403090301d545103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 783605737 1250 783604487 783604499
    0x130312020307140d0e24060307030f1709030d0c0209100e0105040e0715030912110307060513170a031401030224070b09031305010201090b070f0c0f050601050901 71
    0x9010442d001c0c00440d0f810101ea4032000c141800421841ca154280000c00c0b941c00745900d4070304941c80912000d42c16144844600010b000700103a64010001ca0040403204d06503564203580c00300240f0002c0c400e081e0704e40702e410006844c0040d29000c030030150890303650884540d00144942250541130b402459080045031451038100440b1041e0f0341360150102e516440c10040c48020400c41e00c01180901480d0000b140c1c5548000c1c000d50000001e030f4003c103a100c25810300c45801143c541340c01c1c00340007450b2265850080040144d5403c2d603040440021940e0707030703140c8605402905041c020b0180000c1a4000d5003890f1700c3e03000d041e0503061550100180010107103400d0a0351000e00000e9481282c2c40b611624104100070780c40e00ca09003000840e41404800d0380c94600f1090305455608003908041003440e1a02d0f900110680200002d100a01042505440f001c40303071603000d440c4604200d1035140b00c1072805d020f5140c0001041d80080b2508031007081d801c2c8103899550a018036449696106e000040d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 783606987 1250 783605737 783605741
    0x2120412020105250210060b03010306180506071d060a08071b080403020d1e12120b1f020f030c01091b0509010b09010207031e030801092f070803130312 67
    0x11070200b51144144c140a01c18084003040c03071404000045126515100310b800c4400c1c01110018a40200041e4072135045290030011340b0107010340300caa806041c5240310081140002c40c41e402c0302c4a41084110f203c0c0b40c428a0888031810071185410200000c5c038140c106074425615032080742255598100701803c000070000f0a85550b0000e000c41b8011f110900140c58984180454103210789070240d4010015200d0307104e02a5130f1882030700c019203c00b1500f02519084890800340101ea1a01003003628821000600c0d514003030752a00b2140d0424064240c8160300070041d00000300700f45402c40c2c1d210101140c2190103012a15400c0b1984002c0505004108003034000c04000e40380000e00714402e603070809a101906420001660781148981c110010100d515140d041400d5080788100d4002200c0c5410098081c18045e488000220700e010790340c0c1d0b050210005031407c80701d814804440050070150014826004001000e40507040000900001c120b14030500b0703061500c26100c035a4449407618030082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 783608237 1250 783606987 783606991
    0x90e030403240e070f1a1201060915020607080403030c030f061206140601142b020d1d07140a03060203011e1a03130807060e010218061c0203180102120412020105 71
    0xca00501c920b020f012501c1c415804180d51504c6d1a0303290300700840700c2e80d40420702c102a0706c5440072440b600c00901c00c5a27a5442d4552640809000421071810003190040c0b1410300140081c0030587d541c2c0880c1c410501c80e41198000c4101001c00b03000b0346455150703805040d200c401c002c58a240c0740c582094681c0d8141c00c01c1034800d400503100c3c080303803450104203845031b135204d044050781410015604400e62425002860201c1010080c01a29040151600800c4480a60343c50380b0a130031010b000d03412a140044c0c03440076a4241380e04284880318002c0458859901c64000404c02c500120011908007890300354030442003c5043c10000165844244030a114103112012841c010304000090074504c1521005003140d110f01076461a103069901c40000310b402c2e040500116940006d2080e80c00300c42c3d56000301000c103044800515241c80415400c0c2d8031091111220710140d0040002061004044a1221803003084402959206401628a0b84a44084504403550840c54040514141c41442864 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 783609487 1250 783608237 783608249
    0x60c06151e0d02010e031009060207020a06020609070504020c19050c0f010921030c0516140a180b0a0f09060905010e0c03060d051c030912020604050304090e030403240e07 75
    0x5514402d03800448903201d2076203065815200b0b1101244030b905040c840c00c0289401200c0050701d4070500d01c108440384240b42e1119045500c05000c0c02008040490f051049660440d40140e440304410304c0c03281003216591801c46c60600ca03114138000d201e80820103843e0300c801202c80c07a00c01032007900190342c041050701592210400b0700060144442c0a866058003a6009040c06803c0130b6503551000e03e4051040c9543c640d6a40e104020402c980300d9000b40f041206c401c41d40301010b139003820541e0010b44c40310304019408a0f103c05102c50562150640f40b405880e003004000100d03a02c1e80350399800751846220701102e0f2880c141c00005c9a510a9420314026281682e40034503540382d180c108451042d0240f0191543d01610b503c1081901c03800040e021200040d03207011030b03402801c0c24280a030013462a881810f6405c17601c1000009240441228180c860b655400507401c98604202440d602031600002d000d110304010b001401e05c8681403a0103140380a840c01e0000824150069494107254810f01d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 783610737 1250 783609487 783609499
    0xa0e0105072c040c0c020f061c0b0a030b0c1e0306010906050a12020415020c03031201051519030b030d0e060d021c020301060f1412070c02060c06151e 66
    0x440c0a61910b802100841401c440c4074090008141002408444501c5075100105010459450071400c0050740601410700c02c4410504012080c954250f000d480c2c02e00082200d0303901d9024010720341d20b0004500203150024031040c50340c83d100d646019507621030b28952598010035440c00c030524034805c0440307200c3c03001a540c9101e8940340280c1960319800c016411010b101c0c2c68031003222a4000e91003c0c0c03004000d1400748107124040f0701c1c400b070700341a07041c1d6980e80260800c004540720781d9900c844c003504603032064603049451000000126005c1c041c0e01c0341c10100d5120001c13815241581038001540310401103058501c40a103800c2d098030892441111240c20170000d1110b511490840c2c0d0142c40b104103c80c0540da2131010181d9210100e0f4800d07004140402c144030030502030164403800224511424200705890284030744522110325000820071010811942c0c030140440d1602c0b41564810a13101003200c1007414080540003048184461903800344255402031003503402000e05211070b6182c003a03d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 783611987 1250 783610737 783610757
    0x5010f09110c06010b121003330c0302040603110906180a03150603021e01120b030109050f0f010c090b030103080304030309051c0816080f0a11030c030f100b22050a0602060a0e010507 80
    0x640f49003800c00c801c074a800c9c242c0c440d140d0650306210f000751440700030f07079980040e942ca00f0008040e00b2a021320b5000b01c40d02c1c2c01404000708d41c0d10b82c141100c0b5098004001004c28007030724030001d50303100342c103410040c1201d4441003c2c4550403440d0300030a040c2c80c400c403244c0c00e1000300603000c0035903000100e6403140000c0c01140d160503201c8099114030a041c402800124910003140c841510f8000d400103100e5055100807403c0784080420710429010212500d0702541e25454840140f0a44c081800054400e0400001003800c0601961241c2089030f4482c098400c00c0800300d041e0b840100c4840c0911021030034030300000d058280b64149992420409440d031070645d0302c4a051440080c0c100504000b401c50b03403011071180c0400c0100156205120401d905076491921010350700d0245c0000c0d201d0094203402d0320701480004800300030758100045d426100c5a030b40f484880701c4800c12070960300c0f2036080a0240404140d0650120300c003403140020901c284091801080d00d40c0c220f07901140e500002442002d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 783613237 1250 783611987 783612023
    0x91d0a0b0417070c180b03030f0d0204030b010b09040506010e0d06091106040b0408010e0706080f041b1403011811060c01091208060f0405010f09110c06010b121003 72
    0xc180d03005805503000b003000000d121441c00d200d40c0042810384255900a1041017221081c0b0050f0b214200c002c0742c1070108604000100340d40e40100c403120020b284000c103090340c821400d41c2c162402550031000e02c400302c1d40c1d12a04032045900085480e40a1401e10002505550042585220084014150071700d004040e4450740020704040c40f00f00d801d16640d15003044180d841001400c00b801c04010400d50701e902e4400010b0031242c10710b80781c3c0c4980d001101b040100a400004155010038210b02201103a501e40c03810003644c0d50000300074000c5240314000800c3c00e45641c1000c40040d01c040d0000c102408103a0700c1a0202c005006000b400000c0034100398642342040781c0501041c070b84440c008155a5001d44c0c030240031080b0340c01d0200001e040401000654604840703900c10001065508021950504540c2100000c0b9401460007054a441040101e0514036045402e45600c0d10199182540c403001070301c5150740149068490080c2c0d44003c10300400d0403400d0041105d900c402040c040c4c0704640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 783614487 1250 783613237 783613253
    0x15011206020c10050709120203030418090f050d030c03021206060918090c10050304030e060f04050901080102070c05090c07030315030501051602100b030303060f03010e030a0504091d0a 81
    0x14204860580d002e0000c1c1c540e8150810030107043c001d5070031000c5001e1500720802407090309198014000215140040340c0503850200454094404506001444d141142505c4018001c000710040411600342260300612101155607640c0310965603041c000d01c0941c03103044041c2d02400420340c1c4031511540100d00f00745030140091221001c05028212031140903500400c5010045480030901d4010036001030305c601d403103000d20410740f0540c02c2042c150300f045d40f0003d040d14a0542d00900030040005c0310141d000180307064600a25009109040350340c0c407860f4142c042d401c0700c0e2044500b452400340215040c54882e503481e00c42e41c0f0b5107600c80d00700850340d241207000d40b00560302c0c140d051062510200c041117080c0641d502c074410425001d000080550402403030815091030f040c000703a01d0070307940d034a1940d4044110703030f0400340850300f440d40050312400003070051101d191496010321001440d1401d040d00302c0d0240080710844541040804102c2100c04140780d2201d404500e250000c54150b00060044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 783615737 1250 783614487 783614519
    0x5100219050c09040503030105030c04090308060f0613180f0603020121021b0123090c0120070e09010c030606050d02070f061a030f0f0606060706150b07020906031501 73
    0xc0e074200c2e02d05124410200c0c920ba41e042d5015180303030300000014007590408001814042c01c0660342007081351050b0710000c0075040041d1891b8031401d0480f070303508402d0b03684000341c1d0b44000390340b6084540ca507030760810582e4144021000120580c100028036107641070314840c040c2101c0c0c041c3c503180182003103005007004201c8815003640c4c1c40340c0d0074001c50341002d400c0d882c1c2048580c00080000383d1022100c68040c50000e8008030540307200a50400c012802c88041512030000c0000c0c01c2a4003828140c4c0c5100a0600f81500d014a00380f06101d00010031138004242e6a01030010075000308004001004101c054480c44e01030f410101d00100003a25254440b5401403003260b008541585100c4143d80e01c0c0802e59008003410300003440a6450a0ba551406014480200102e10010800c0d181000401c9841c2d0000910a911440000c910760341800825004034000003807200d65800040d454007203c24040e000890280d00803008500062031900380002c0000c04181340342d000d004660300c3c0c40e1141544084c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 783616987 1250 783615737 783615743
    0x110a1a03072c21100207050109120810080f0601150e10050405150712080709080d17090f061602030f0f0d0b091308090a05060a08070905100219 63
    0x1c116140030101e40c00003246100d0420821201100c0396060200f00d100c40b00c6581964600d07107449528910302030f00049500150300200c201586900807810034a0040030498400342011204140c0000015401092a07204822014506400c40c0c0c442d0902c40e520710b0815102400717503001c8801031000015246043e680c0e82690719180440004500106805402080000c00441d0000c82d0601c00c500d4003142444460014001650408071140c490414040d00c200d990700074000d042010500b418403c0d45014007402841c2c040312102822900000e0480710302011a18807a4880c101141c0c508001143c0782c4030306080c600c002d1006403aa8000d129036019140b00e00070640c4410491701d1803210010015103c40320300002000c0d11094651201030640d00c0c0014003030711501c501410804407200105400040d02c3d00402403e441c0c2d80c500f4007046900c03560f03405c5190b00001c040350f11600180d00141241c030540c51070340c1e01042d4545d10b40500c0b00705001c4007c0c0fa40581c208500e034000c040b24030b4903038058641c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 783618237 1250 783616987 783616997
    0x403030e0a080a06050901051602031905120f160e0f0907091d04020f040b0d03050702040609020c0d03141306200a17011401051b010621110a1a0307 65
    0x20756045907500e080c3c2c02050445210303440d07004014400c8000c3c07065560140c004282008080c0e5640d600945038481d0241c9102c030350a5a50007840028030520580c1c10300c40c08082e20010300d04000450101c0b22204490152040b5920480341c12541d108d00503100508101800040e04140c0c0002040402d0305c0003440482000752a443c005030220802d185410081700d8205030b03540d030b418140117220100c4110200c40c2d02076420300605217215100c1c00b4590241a40516000f0303102e030014030006020780015440520020700101d090f08d04441c010603000b0b0078400ca510108015032031144c03122650f040c101c0b0710100070070504500c00e001c5801c40e040140903104080043e0510468038840c2c100c940c02841c0d1000008002804100251101a80b8940540070080d0301d40307100b40c02540020302920500d4140241101851868036060b4802d40009014119021a20070600a81c00d1210140080c011090301c41401c8140c0000e00790801c0303a00c1c4c405450090082d02c1c01e0524031004424950b201420910404c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 783619487 1250 783618237 783618239
    0x3100f09060c1d06071104092a1403061e280c080f0103050c010c0f0f08030402120c0901270501090510050d1106090a0b03040807060b06190806010e04110d05090d050403030e0a 77
    0xf03206210403076900c0e95610740341e08901d06050b507001180002b20400d9001c0d9100005019024411358040d00d800055800143c5040c0c0d41d11070500c00450854800103080f9220b551207186182e1960821388024809942e06d103441d5552580c50003d074407080c44060015040720702c20305c14a510072050f445c01d650161b80141d0080310243e80d12910b030400c0010a440f10300c804014801145013134404501c0603540b42c0000c1c0307000c0ea040000200c201c04d0611529519000c1c0100084000303051940031503110183d11401c02c01903940d904c085001e00000c0301c00d14180800404013203054509000415200e5400c000342d01c90109240040c0032195004c0719899503c52282040060345031040001580325610620004d038480c0443c3c6011019600600980ca110f072005002041c556007444021070169012031802c44410f0707c5540040e9040f5081108142e0860f0610f611884c1210344640107110300c410300e00c420012036172043c0240d91600481411100050420442000424820001c01840440062071082c40d0703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 783620737 1250 783619487 783619523
    0x60f0f0c0222091b031a04050d05131503060305160f0b16020d11010806040b0306070c0305041e0312050406050403120306090c0c05010b0603010503100f09060c1d0607110409 76
    0x806803107488030000c041038132418403c01c2a000e5410400b03036103280e03011074541002d03a946d0340c83d02c10840400741000000304266035100c0041c1c0440d0000c01c0c4001a0740d03030190300700d40000e001d0605808103460501c10701001843c03c03001c1000c0340044444105010b1100c0341008081e0030a0781c0100e82c94080642c0010024ac0540e4428a0480c4020701c04d13162184401142d070b002400c030840040850784507507e4940301c00c000340c17408902c2552015192401855031b000c1490152440d008a030450a4111066800803001d0141d01002e801070724021900c50140395803545044034103216034002c4c0d0001072401c1c8005c00004a40d08000c41c4003078814100800c51545802920f012280c41d2241c400014104002d8502401070a2150115211060310001e16540c103080209907940191891f030b00a4544c4d844a80854622076481004595030003070052007400c4400707500904400403980442000250130400100c1440d01034106c0b001594071800840b20074038000c007000004d0601220542d660085400d988105c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 783621987 1250 783620737 783620753
    0x30a02090907020607030f0c1d0102010f0c020a02031011041802040e0c0d0c0e061c140c04030b01061115041e0507150305040203060103021c0c060f0f0c022209 70
    0x41292507074024141490500001410f5070700c1038130340e000080e14001e1103101e03150388440500303949c90f00103c00d14514041000100d004104038440c811410345442d1b08106815404078556081c07500032800c60741a070350b0064078581100d00d1002c48001c1ea2208120170008850882d1903c00401e44000005003003d42d00c00d103085480d901110710220320140000e02c554141883d10070b040c080c85282c41c16003500300d090400b00d00a48240c143d41c442440510a08500185882c1c00912a07400f01004100150034070a08440c000d0b08240002c4411094010020500b80d11941901c5508003c01009083c00d0005e00b1542401880c09002a2200740200c41412221080c01c00a20002c0740300303400400c922071070b006800c0d50751410782c24208100360400003840003584d0002501030550341c0440303074003011500400400c078440c60100340041448148100c0040c1e40c036040040b0f000441c0d81b0380c60b80600c07207068210880300d4500c1c800e002548a082e01c0d481818101c4030210b806080110807400081c050301640b03a02507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 783623237 1250 783621987 783621991
    0x30706020408010203010501091d0f0c070602180108061009031b05030a0f0203011a360705030106020706050f0307080601030e0a0f1e05060f0c162a1a030a020909 71
    0x3580f030390004010031007541c3c03041b500c0d401000c1030240a80070700d01c0f8101c504890a03001d040122010b1b203020100d0591000d810890b030f40c00703030f05c4042155203c007074900705680c3c18038404d5680c1c00314018600040ea141005a45d16102c0300315680c0d50a0014115034401010f6000000c900144003d0500b0100301c0c2e840c01c01c20802510302607040c0300ba108000c1e104150a55819a154505003000140904071503150348880c0e00c1c610100d011740301d0040452401c1c4ca0304180511f144d442145403404103110549400ca40114140c0f0001d50030383e0300700750303c9510070f8401d4071542c0e241d11803100e002c2000440c042d10800a064000b1014500818510000c04d09a49001606030f010340d050901d14074604c0c100076030001402440540380400c80700ca8005900c0701038986000400c1d10a05500500c0020b040e0b440078000c40c1c10000500307040306004111402c0654a43e61744c00c0b603074a50329060b0090340c1001d80d9440c844604603883d12070359a405146607600d440103504050400040c8640038401e02500e9911114158 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 783624487 1250 783623237 783623249
    0x1e0304030204060803070c0b0901051b0a0203060f0a050609060603040807020a0312090602211603170a0b10020c100c031202030a0c020d090605070f021801030b01060e01020304081902030307060204 86
    0x580b902e80c1c0c0c3c10b0550782e40c7c4103035101c030240d0b010802501d0481c0c0d8020040c1d03001c00c9041c08440c504246803000c0c032402c002c0d525000944c50301409042140304804c4080d80740c05600442d400b001030384e9980742400340d00e9170140c4030300d644540e0900000e40010440e40007088203501c080c0c0644141542c0c1e9558952104540c00c1810101d1000ea80c103001c41d92f81003000c41d589004a414985c807542962070410b8852007044001c046180c00410f4400a140c0260003150021800c99592102460081611742c0204a40c54040e0b1240d9441414914a1840040c9030b05170200c00401106141c4481030b4203950f84400800210305100c0c2d1500620140300792b61000e1446142c5040010039920044c040007428041400148030a00607440c00500510f94408191b804690340007141044540440c0001401507101800e40304030000c5c20700c004070801035041c4013241207904c15201d040f84541c1e401c00598990145009507042a8400b50740d1403400d50a0308102000d6600240590385010419141e0909a0703000d90811 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 783625737 1250 783624487 783624493
    0x2190203091008040f0b0414030d0209010906030207031d031009150b030708060c0d021902100f0207050c1e0306071805180a0905030d09060b0a050301020403051e03040302040608 78
    0x4600641000b41088840840d01e00c0d29401620706035442c3d8011040b03148000c1c160050b01e100003004c00043c68041c850400d03030082200d80700d4240340103040196010302400390020b14440c40000e0654000d00039603280c0340d0f1507150448000b83c1c441c480790360704070b02041603070b418442c0341d008011004942c499000310501400100340d400300c107040b00c00e058a00c00343c483c43c001e44c070040c001c100740348010076041d030440240d041c0d295a8038110042500a4040c1e44000500c0201c4038000d2080103400044c40a4410001001070003142c1c40144054228000c2d02d41c0a131281c2c1211130045054034140d040d2104182440d1500c810804011010a04d4a17030119040400b20b038500388024000c0b86030a20a800410080301c0301c400d51850300305051016080901080c4000d6142c1040c20b040200500c19035401005000f8100700d46002410844d02800890444500801d03141102281c682411700880e804c1d05d800000410308008420b010f8400560083c4842c004c0340414800400180d82d01d00034003006042c01360007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 783626987 1250 783625737 783625747
    0xb2701180e0a0509071d040201140a21060f031b0b0c0d0305090d0c0209130212010c0305220b150a0e090f07080c1005070c080a0507090b060403080d02190203 69
    0x2d500480f040038000c1c4290354414a000c0000d116800001803803801510529410f580f1030b0701c0182c84803502c800420140c1000822643d1001d03901c1466003003842c0c280c0000308181041d48024034100d0310070f07004074a8140030113442800842c404103401c8954412103c04018202e5a60030000900e8021011200301c03504200340355480c03240d0500400780c00c0084180136222203841000701501015148400074041c03011000001c01780d40c040440c041d24290080d240d600c0013400600c003680281907040c400e5010900d81f001140a80001892288212441d40c04c49410580c881e10380c1009490010101512500d1100c01c007513094070340082c004001e110b4038030351110500b05200028100669060b0160880e40108000c000000c00003451003595403064455403034807c00c01f08115000d02c1100009170041091410001e00e044000070000c02040c029019100165111610a403c2d50807040c040340c1d00080501013417000c503a076503000381081101c807e001450004440c1c05561440c0101c01e0945c0503800c0814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 783628237 1250 783626987 783627001
    0x30f0705010b011d01080a0c020309040c08070f051303060506060c01090308040c0501172202120c01091e06030f0e060708060109090c0203072a0b090a0b2701180e 71
    0x1c44121204d40c2c44e200f80c58040b8000000c02c143c0303000b000044076503211071401065500a00440704500700240052104040c0d520b8040c05c185426a40071b800100c1c00460302180610803030950f120014500807200300549943c5504001d06805400d60707074040800c204044940c6d909110b003c2096101e0b441e8420546464100717008860030396400703681405200c585001c55a90580c909076480906000162141c1080344510680000316040094005c50f202a0045070464002100780c0112000da803003090103a2034080021480c01c040345c08040c1c1130100c18050003014004e41001036413002003540040c80b6449501d00c140f50650603641100800c00d41c40a00240356405203c00c1c0141c490942d080c04007001c1134000a580c1c0c0303c0c84201524401440131002c1c1c4c20040c40c140d1003298040c59004102c559103d840c4400380f0b41c41900c582d8032540803d0400120740c0704d03420540fa1018001c0c0c4c5080c1c803648080c00c503529450b10703c0e04402d04020742d0014140c0003410b420325241c00f514480f02c15691300d182c450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 783629487 1250 783628237 783628247
    0xa020a0c0e0403020c040e1204030c0509070509060a111516020d0201112a0607200604030e22060807030203120f030c0d09020a030b04060c030e1c02030f0705010b01 72
    0x107005020540006010403010a400040e014903c1e1401e417000914120616185414260005200d041c00480014000280140c0c6050081901c40888440c401c584070b03071000340da00c0e206414142d50000c40a004120f6007501442511780340c2c5e00c0c00300c240c0b0502c54907524007050303945040b20110000a548600d2550055040007540307520f0f4030a0008000740390030b02c0c519010341c4c0038a008800c5c480130044501140c034024100040d110b4070100c42120024288000e024100010301000302c001c265100d400c17245203607800502280204c4d055110848650f1403030081c03001e044030094000114100105843c15084071034030600d00103114070300203848500d040d40304043c100040320002c03106506045c001d404010461204503500320070140300c46503881e440c001150000e0714240c580607600c008071800000030f200354136030628410361003000d0801c032030b8103852000d800b102d402128460341303039100c00019024080381c40c0b41040c0c01d10f22401184d0a000075901d140e20740760b0020301d0803942651903480d4010780d0b58000e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 783630737 1250 783629487 783629489
    0x80c030f031f0f14040204090c110d05180f0d05060403030b0111060417030709080a0f06061710052a0702040c081501050f0702060a0c02030606030d02030711150a020a0c 74
    0x80b9810040d1490305080c980c020910b07015000105804035000d00140da15513040f903004064082e0207010220508001401200303407062055020f0083c10000b50210b48036604403004034241c0545c018030f603451001801181042010b0703640d00131800300d8100780800d808002e0584203d110741d402080704d105082c001490b000386003c100300554000002d000c001303400e11101d170848029801c112500c2c0d0303951100464100301564440206030080301e03422028444030140715802c02d401020244200741ea5903900c40c0404100d820848140d403c89400040e0102c010780001e030704042500b51201855202e8a00741c104802c8108c0c17408a4000001000b1045081ca4001c800703002000d070520760780c3ca00e002d110040b50102c00e011400d041103c0015461a81401c07101500c00054021344160b032a105041d034007400c24844c40300164440d109000005080303143c0080c599105001c2640614203004040e40d5a141101001e41c0681d0f2118912844044d901c0085000d0700400180758020444440f036030909010304003030307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 783631987 1250 783630737 783630781
    0x2190609080f0a140307020d060b1e03100903031b0504090b0f0d0b04082514030301260102070609080d0b1801231f02060c090a12080c030f03 62
    0x3260b105040b00003141000403079400241c940d240b0328080d4001c0f41544540400250b01071280d030001d10a0002940c040c6106250684d40703450400003800d80ea4400d118040b01e4558140c0c010903514100c08166000b2601c540d100c0e09000c1207281c4207280383c0c4030200c107000441000075408242007160101a000381c442406041d80c000140d807607810301080c4c2d0584483c001502503c1e0f1580411700b0001250103c1742c6464422202c9004404401355000c05001c0c0b00c442a114080310003040c032920040031044034104c0710315852000c03840149410440c10b9210349107101c00c1d155405c2c001e82d80400c01c10f014990000c0e1060f11443e6481c0408030151044402450085000b01184802400d410035103001140c192148210268094410700d9440c0b0680075a80c429a40c102001d101d103028542801c0441015131209602a00d10310b03503c1c1c10060049000b055601c80d0b02800045080180c581c0802e4403580180c0510040c80c07800a86001d0145150f201c0c000070350010030300104101110f81015a1002c03c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 783633093 1106 783631987 783631993
    0x630010303170601081612060810141e040f051e0609010e0102030c040b0c2a0a0501030207020f2701080109030e0102030a020d03090f0219060908 64
    0x2c0c1116090040b403100420b0a540c0200c450300d100d000001038a4002d810681c40403203401e103d05500c40281c1c0d40c4d9540110b0086402e01110f9200b80b690758000c1003249030070140241e4120000c0c80b40c800d103107611400b02c041031603451302c083d000f94201c1c4000484030500d003019420541e0b00c03000039007041d000481c4d60b06003140200b4014820203000008100304086100241d00341e100c211522003440c40100000d20001c1d070304d035020b0072269081000b110281240341091980f00c40703401d483c1c5e0803084420781c0c0c0c0e0026031030184800400f5110a20742541401001e9010031011210f5844c010311400b046020071001480c02c40340030311080070b6108118805d5a41324100b034001c25403024241c002614400a00b00554000022608005900c1d802401040007141d4114000d000c4820111560000c100a030300c0569180042d505140c0010314110015a00c0e1502c081c1940042c4e80c0680b8032a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 783453237 783633093 := by
  have h0 := BRFrame.cov_init 783453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 783453237 ≤ n) (h2 : n < 783633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
