-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:30.85268+00:00
-- url     : https://prove2.me/submissions/ba14d20f-6e00-4472-a01a-8707b044d61a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 901438848 ≤ n < 901618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 901440098 1250 901438848 901438859
    0x8040b070305040302060411030a0c0b030a1817030a180c0918081207020f16140409020916030213090609050a02120c0310030803010b09180c071407121a01 68
    0x3200c01c183c5000e00140c0107400020003042030f02d005128124006021103c00d00784030380311101c10203a150000c0f0542d860010521803480c11034020a229160320b000d68125094540e40d841c060011000e141564586c0048005071a4421941c080c0e00001003242c02c007003540c1800d25081c0c0c1c51074124019a041586040b2845402507155802c214030b899001c80400d140c940746050f68258960001d160004600c035810040308110014000d4070901910307100789002503070034590300d41d19030808829143c0c0924601080d407800b46c2d540100c1182c1110220b089901e140340c2001084000e803050490913194a850000002842c1d0010b910944c100d0302d0030340c070403c0140c46400e40c00d82644510050040c441080c900820401c441042c003c5030401c13100c03828a098203642e95146262504242e01000900c10041008940da060044440d01294036940f05201c10380390036801240e0354010003001070f010221404544583d080308101000c050901d2010006284c0d5251501a081122009120318120800b0000081c0e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901441348 1250 901440098 901440101
    0x1e070e031216080310030503070c1a0307140901091509030b0a0209031f09020406030b0411090c04091a18060111031801030207062408160b160c0b0a08040b0703 70
    0x81d80b80261500042d070390b0280c1c407081da1a0b00040c0481066015007a00000016800c00c01041c03001c0c864030391000c3c1c1c6803504150060300c414840b002d03448280708004100f05154003c02140b030344c554401c0c44903216003000300103c8500b11190018828103a4036041540341640040ac0d079000c9070709c2110107000d980d40f0026554203a024452070540c01d980003940444000e02d41c20580c00d054071030400c002400d48030030780000d41903484680c0709aa4a4100c4002d20051005207011020107090a4803840702c10b003089658032143c1d11407485a40340e22913070340c04803500030340c08180502c1c7c00501c0205101c008003a10000c05010000660340540402d41c1440c4d5643d9004011061342c81c840d9005900446681c04a401500a54041b1004540303040d40c408803668040480034201081c00c2044905080c002c2c10171034080d2414901602c08044002c0d4000700b002090302d088101c44195044a4154085051900d02002c8184541d0040c0301d8488020480300c18069020084a10560280000c0115601c6030740042c2c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 901442598 1250 901441348 901441357
    0x51e09031c060b0906070f06050f060907050703080103110d151d070807090c030f02180103050907050f06161a040c091b0e06040b1b0d21051e070e0312 66
    0x2c03c0301d282484410440c3c0760510142c8140c900401d112011250940d880e0000c0381c004407080500013860801b48211400c009001a921504608141d0f2801700b07141c4021785002c805120081c031300c08032a180c60b83c032a1100040031220f01c1d484021000000f62008116001c0c5c0740d89041c8031201d00e06103211042d2010300096081c1150040e070064030803241481000f01c00703003034a4441d04003416118941d04600d0075540c8001c0c00d0480000500f140050544800182a103002811440c05a031042c7d04c18420b583d00c88444800c1c1007401c4032a940c4e10103202e01c05111000d0714100150045003004007041c095030089139800d103d280704000841065032038100040c101c414076000e01d050000904207008605000f4a2041450307000100740e2410199030304001d07003140d4800040044078550035510303143d400c1010005400e03a0380032800c0031022203c146599440b03403403480144a05107922107000c1030403900e4820905c010900042d00310ba0040c070340a200070380140c0700003140d640244500b1001d804280002001e86 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 901443848 1250 901442598 901442609
    0xb040b03210307140d0e0706050c07091d010608150a0204260c040c02030a0908010b01080606031f030308010617190b060f070b010503070b0702090703051e09031c06 72
    0x541d50300c00009224160001028203080c81030003c0e03003582d001002400392180860030360011078030541c0403083d41e0800c80c050b481035041c40018071007168011000f040240030348843e40800902004011000f0000251402c005105540b07000700100d6034034030120b401642e000031010652141d0300d4501d4004201e2080b0b01c6103c16168510b40c0c40417003007508400901c0d0041440b82182c030b00101d0200010215404c56100c640560301c0045e064402d43e03005030442004102d004000c0000c164994006020181d0040c4070522648000002480690700c5480300c1d03101c8805140548845922468003910104007070161001044e4641c042e15421840b500c944c40c440e0b0322403801031040c80c0704c051152016140056040e98440d00c1030000317010342c0c0b00e0407025050150140c4001440da500d082c0a150500c43d00b40c005140c03035030040100324050384941c01003541048162800080c00ea847c91050903603a010280da501c080b940000038054000400800b0b0714006682c8240c8030b91002c1001c021508651b92403268 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 901445098 1250 901443848 901443883
    0xc09060e010b030601050a0305060f1e0114040e04110127091d1b010203040e1306110c070308031302060a270f0504020d1b0f030c0926010b060c010b040b03 68
    0x1f4203400b4402e0b001640c01050180c000d00c420b100303200002d102600c40082e40001c200380e07844400415a40b11601d45c82c8510304684151405040401d180070f154401030010f0645a4034038050459648a1042d03248003003400010052400380d282a524181901072256001e40350604c0c074810a5010294600070700140d09074020001040050100740580a4102c0603d0543c0028040000e80490b0031146034401c10b03598401c0d80e04001e09190400841d00480c98030301d1081d505004901407164000340703003015281c00c801c10a071644d0352000840f40f10844000000c0d0401b20102c1c0080046400c45005c56640700f50001303090280c042c249004544140502c5102100502207000700610706066000b0899038981c1080410688652a003060941d22030b802c0c82c000003042c41030b40a007800d50522450700c41240074500203183c1c5150591907024001110042c860050b24402004916802540b1440d00814050040c03030700c402c0c54141440c0240780f54000da9010300c0c00e0421a10851502040c5003a4080d1002c08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 901446348 1250 901445098 901445107
    0x1002030108060714161a01151b150c050315090601020a0f08040f080319031506050a090e070c060501050a05030303180c060403230a030e0d030201090c09060e010b03060105 75
    0xc88400c1a41d129075129840100003071000d4983c02164940c1c00c9003c0d00d106c9425103c030b000c040038516030503071020300404e03030303000d12001c0265020311300e0703d4840114241e00d01d100886040c411507562080601c116410300d000c681220f910740082c0a10701c101c81038112060000c244005000207003204560090040c0c000f10712040024900382c4e458104280030301192820261166080103003440141c02000e850340c004640d50200c1c2d0050550f040202c0b81900e81400341d05d4094031210700402441c01a982400404205c2e20380441c0700c1c5200c0e070001c100c0e003280e0f00c4046c1003803d4054420850380d401542d4481c105800800c40e400c00102c081c0c00c90f40090001c5245a0b100007416013074221010700c106d861302610398002c003181d590101420141d030060001520000c520500c0d580c82100840d044e0784260000607002d004280c1240c0048113441c010303516004041e0081c070f0201c1c010200c0440082241e200c120380407030f0404c0254482e00680d01c1140c01609282d80f561080318540c00200d840d180010381c00c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 901447598 1250 901446348 901446361
    0x303080a02071a0106090828230d030c0e010318020418050a030e011b03020706080a02040b0304060e060601021b060d06080f0615011b080f0408070b040305100203010806 74
    0x41c0140302c85070007458030310803020030031445800302d070340c203074400400105808402c2c4990300040c808200350300c1800280180c5404e0801c00340c428000409000781c04165040303081a000d0124942ea05401c8007080143c034a04406014080d0060803880c1c461070001e010300000d81c046500920800c60482d0034854214a144034a5080102809414400402840c2801c000c000052020051743c078901c1c0c07098840800302c0e402c8000040c00ba1100c0803e04c0d88150b1540340c0f110120f600802c0d80c0c3c3c140e95107840c01c8803841c8d85180040b00640304e03590081d074400e10000104002e0122070b9108444052601007903410540b00c03d00120707683c0d80e2145c000ca40c00740c0781d8000d0030304500c0c00100400111208000105052f541d4212140c28a41410100581c41d0814400c1140d0001c3c6150314665604090802c5035200650b8004011140f82c0381000408013080001c0e1040144200c10070f41c0d0080c1041c204485846481d0186050180c2152000b128203104140b00c14011004900903281a01c070a400281202d990700d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 901448848 1250 901447598 901447601
    0x160203121b0405031c0e1507030309060204080d1e080606040b090a1211030c22021623011a0f0d030c02131514010e0121050f01050102160303080a 64
    0x1c8400320200c4208070004032030320140030300d440072204501c91080c450aa09006004441640c5810b031050090041a40740d03903041e4029190703145d81603d00000d403440340386000c500070310403a0000300031031040c1e2412504641c3e00c40c10780782c1114001c030907a4001000b100310a9803510005d490041d404070044c07009000c07485001c0c1c0a01003454008041e5591595545000b55051258503c284d810301400c15401007103003001c002000b11007200342e902001003004100003554003884200d00210a9070001410f400345807241000e01c520a4020224047c907204030300c030f4010744002d0000320071143c1d404d100c9144001c016010140200710006811020340701e0109080000c412a80c1c0c008030b050007281e201034030142c3c41c1c900d5550810071f0010f40005000001c0b19411240f60340380e500102d5812404050b1599599003c0201317003504e50300f800d20300112015410b0941c1d502c0300d03251301008414500000c00801c0010010031604a403001c0e02510001c0d000034580c04442e03542e900018020504c1e00011840000d4203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 901450098 1250 901448848 901448881
    0x60306010e0a020d140a1d06190603050706020c090106080103050c060a02150115030b0d02060d05040c090c03050610020d080f070e04060810050112170a0516050616020312 75
    0x140da00061a0103071803064001191a6a000a0f80e101640c0c5c1c10080d002102c1e110f8580f2028035205121107821840340500d996100c010708044102d2a207070002d0280481581003000a558441c0a0728541b83e188d800003550741e40400405d6105515500c00022018010740e0180d050b2074205019002c4035210f0014411164820401c034401c6100f180c0b1003086140e000d6600c6d5000e000101c81503400c08404480003416912840701640c41040010050001030341d41d2000c031698559140004034859455041c000300600181d4400503c003401c0504079040c0d40c0d899030003103220700c40072108501080c40c2e42034103d9a8040d0300070f542c0081400354000c1b411018550011301e41c00600392a202802904980118058903d168854200381c0e11000b54810b01000d0b5001d618050041c03c01c6c0851400c03081c0d15105120260340d805420300e00c4000030000100c038440c0044603914800004204081c0d4594505195580d400b144e004007405008075182211030702c04001c981d1030b0044041404860b840301d0300340900700d030780 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 901451348 1250 901450098 901450111
    0x20c040b0609030105090607030501410a0303080103051b010f030e011d0304030605090d0f0c080d061d0603061e130f051507020d0c0602130f080a030e09060306010e 72
    0x40510040c03050f50b40074002e2910410150700601098101002e003e000c0e0f41e41a0170103024102503680c80c141e040040c0802442048525102d0181c240e010b07070403d20400c070104540c035000202d440004c01410b4010003080e040300c2c460000c840d842140e800e00b030741556008030700c1d00e070000b5640c5004080507880303038101011802c141c10000941c2050243c00d00c44803040b200c642d400c160000304017001404010b11895138460365040c043c0007041410b150081103847d03401c0c03110007441901c10f160001d01414400707944609110181c00c02c9801d072500c00e40340941d84451116403084d481c0030300003131407402d003c41d0150050722822400051251411080e010801c07004001c0c0d50000760800f00c400200716408c10b505011806507000d400310400e419901d002071000200040b01359405120703001e10043c0e2000340c100059030490f2005869680091003180502125440540703803210901c40490226008128429000c0c407948900b41d034248034505008440208845141c0d1541000c0d0040188040e084d480b90b51200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 901452598 1250 901451348 901451359
    0x3204170d080628090b0f030105070f050a0201110a030207120c0201092702180a06020601050a1401030213060e1305091209030f19030806010c0b2806120c1203020c040b 73
    0xa09201601144510f65403000c09125100d4907070880d41c0c10800d0b0403410282055000340040d142905000c0d1050354064000801c01800064a0018502c01e60201d5035400903078500d59900d01050030010082c2d040840240d035007405034041d86e0041802400036540301d580c1a1074408000b45861051644002c1c203540084d000040c120320000a00260300c020201d03020a0311040003038103a10010f201c2c42c0c6000750460310a55200c0c40041c4070740e80d1901d03d118229540141d50500b20551000101c029024646a04401c030035080d5000c61081d40195403078540f041c2c140d4203100d4a1a12041c1c03c42955016030f452140c0d90441e850100517410030034001c080b08a4041c08440d10005001d18040c03400e100062a03410301654403095000700340e13020f4045504400240780030b4504e00b000707484800c01d2060240c007946080d4600311080e2164a18145a0711300c1011060040200c6035403008841e105503d1107800300d0300303008427000c0841c00d40c3c8904404040e03150076600400010040700140401448010071095102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 901453848 1250 901452598 901452649
    0x1e0a02150a051509011a131e080c0a0302011b05070e0903040603050c0f12040203210904180c03080a050912011a040b010e013204170d0806 61
    0xc042044840c021007502100103200d251101c001c94100c112503801d40d124004500041102240d0f07a9045801c030070281d04e00ca0b54a6040032003c4071407550707a074888680b0301040c0e80c1c0a00c00c010702d03902e01c20844c1d00000c02d50b840810b401c400c005180c8140d0000038007203000450800c40e0f0888140900d40900d2040c02114505501d650780b0407411001103903070405c0c42c0d000241c28428943e15002d986d4020052022250400c400c0110b108040d000b0740c06100b8580700030344005415075404114100c2950b158100c02440300040c407036100d12a0b485110503a01503403e0016000b0600c1455000c00c140c150495414002c460039a6914a019409210303250f00f04281130115a10581e615100303402c81c4940e6500004052407000640d03001141080400d911840c43e0240b0240680d03007001c40315505a40900c1c0c814075040c0c280120001212008044030800c2c411100d0b03544403443c003c0300800c103669a0000107020140b40602580e501c8d0081820000010301100c0800d2090404c0d5540d40315540d10011580003d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 901455098 1250 901453848 901453873
    0x50a051e0f041a07020d0f23070f0f08060c0309030705190201030f060317070503070c0909170c0d052104110f090c03071116060503060909031e0a02 65
    0x100d820104111205600018080008400c0304408124803c5030002050400c5020380028509020341140a040c510003443c401003003100d003603004054509084408055500f0780401c0320307520700c4140180112410180e00100e4112000783c1c200341240c003a40e000340080e0340c64064240303441d0000741c02055548003d125000000d07034107000e200220185940c2d101d0103035105000050a49091200b06200c0700e00c2c060b000c5c0045100c00009803aa030400c0800c03581d0f280c410386021840c620400d0f40c0640041a0814041180003446d0008001107006442d0000380041280c3e0b200803511039010540240c0d80309101c1c0b41b2040b8040d00144c0390f160311080461b00c09400741e030b82c01d4441d414100c1d011030300d92440c0700da2400c643c0f03880c40c01d0200302141034035010b2841c80d007208a0003145c400940f2800500c0701143e65410122810415548080036a01a100945598070000741c115001503500b1031140300700c40f0001d5050080001620386001d1f07466030300c0080218001594900d64010303444102140201140700d0710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 901456348 1250 901455098 901455157
    0x18150b030c0c1e03030f06120c1002030d061d07051201120809061b2503020f0f030a1202191a06031c0e03010e03030907181401080d0915050a05 63
    0x220b2422003010f13554030300c0c1c130380c40c1114034200003410948956040e9416280641d800920340040c180300351070840780c103444174405038550b00852990303c0c005810030300003180c01c240c51083e4903440e10810300c00d03080540b6100c00a8909000d0380040c00c0c0e41c2c610650040003030320039618400820b00c1c001c078070051601c4616408108a68450300c1c0f0f0b08a20455070b484810340c0e83c02000f2456401458a00ca0020b014804480840d51440c2d8400a8840c0400a80604280d5107070420444420f00040c1203803054800c2e490001c0da0b44c0d00006244001d40230b00c59005a402c0307080810800d03180c0c0d12105440c0079481420002164501c081c0c5002d40510590040c030f00300a1020110321803440145d25600f005011840406003035601486244106400502c00c3c481c1040e07002400f2000d480621010654004622106100410100740407885254110000203500c840203d1460b20740c40366a47c440148503101c8081030011000300310b500c00090000c01c907180c44203101c0e8014002d045801c01c404000111520300184 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 901457598 1250 901456348 901456393
    0x10207240b130c0e220f0204090212010602150f0105240a110709060b04060809100f051914070c030207080601170d170402040c0c050718150b030c0c 65
    0x40c410b0b50343c0e9841c0d0750240c01a103a00c0154008403006003008059020041e40f00e2950b01000c1c900d26103521011548407041d4060b40e000e00740e103c030210340784d050388988848003c10070712030710026018440388155404500700606101d1444020400156441c000602c105c1c4014034001d08019145651448000341140c0010550115155901003a0703100052005050103a15400317410f143d07251600800000e0081ca0940341201c1c041d00b41007400769a82c0200b281004074440c11340c6040c070300c2c15812400420540c6c2c00140601641c00e110f41c6100c02000c907180440d0748451451150080103000100002c3c17203241e9880186210f81b06075500c82e81c0d500d010a01e0140281c10017844c0c0c1703e040c0007a401106040003080200a800d143c03829442d2450142c0750500d400203030000c1d000341d48900c001b1102c3e034001d003404000c003a070020846440664901e0b080788090040b8450784901400c108600c0f0200000701500c03404d0319660103070f5a246803540c000d02c40d5240e1044c8c01c0780805010703521498152040d18200e55 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 901458848 1250 901457598 901457629
    0x70b01082805070515130e1602030918100e090c030606010c120c0807080d060906050d020a091808070305071e0305030f27030417010207240b 62
    0x10312003518081900e4841c4080000c440e14404646259400400c0002070b88404890055070071180841c202c890092251040c2032a50400c031111242c0001c26409141c5402c2c49010400c0e05500b000d9a0044102d80b07c0c400c41c414198403016200c031800e00101c80d00b00060b0032403c540e420161499403241c00d01c01c0b903003044490801c00e03040b1f000028407504081c0215640402d091078010b1203880240c2d03540b18a01c11a044500c104260306821000300702c8100c1c215142242c01892490300c400d121080900901990701500c1602c03410100d0000d2070b400d009052404d5990300a02c803104080c1408800d40c000c110f084840c442d0303c4040900b20011990960007040201d0080d510305980d21070394140300009101100004000703400702308a44002c1713a80070040d00c0d08012031841100ca42c1d100c01c05528030800c00402200e0b201040d44d00803540100f4004001e00442d0700066141c00058007801d205401c0740185ca80103003000680007401114951a0040b0601005454070009030507014200400c002818441e00b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 901460098 1250 901458848 901458853
    0x1211160503031603090b0f0442020a021b0a0f0b0a08060d0209161106010b04090e030c210d02031003020f0301110f07020a120c0e0901181403070b0108 66
    0x10301a15524203190907848070b03c01e060a01a000781582c48910403100200a9040325031b282012604015850b0454004081c241c0318614011070b50f00a0303505541c0130743e802d144200b40f0013034000b00480a140207070380c41d2070000c0d0040d00a24110310309910750040880d03125a8001812080070440350160303103068025003540544c451b05c401080102401d2050302030b00322441041c141000c040103907180009103510901d41294800c00c218205819120b2501c5c0190074601e40c0204000840c04515080186c4110389000d0f0080c007600303441826054484c0b086480320130707180e0480744242119100100b0702c45590002800754926000790b650006089070001e5919489040b4511030400c29450044503024021108400811400c102c50000b1142c6200e01c91420f640100082032400c00e40d07482100c6d001c0200802e0090b000e00d08054500712410354800d000c1c040c402c82c0e650703012a03042c2005100300082003c8250710701900380721719225200c8209050907224010b11003088110300041c810a840340c020241d4800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 901461348 1250 901460098 901460101
    0x91005120a050118060e04081602130f0b01031a0603070c080c07060e0f0a05010305090f0f0a05060112030f0507060b120106080d02030906090d0f020d1401180201121116050303 77
    0x8001031400c280c0301300c607008241000001c0c4041031608180700c0d007080c0d01c41c0201381d580407405c4164031503043e5818060341c803000c108000003021520743c100c0d2407070211641d0100805242d03000150111000c2e0309010442c2010245030603a00d0410600660f00060103040c240d56940b15642c66100a42c45000c4c01d40550b00010010000140c00040840610b40115400d2003255403a13400306140540c980700381d07410541c070785000c50b090300e01c05d0180c0b003040031101e41660005803e1a070955583d07868034004a80b2482140c000280c0c400481d50749051040e0305a40300c1d078810051800c11161034100300e005031403503960341c00c2005540c1d85400c44d154208400c60004188a0b00e13104145090085003816901550010003603400b02e0b549000849001d9803080340d107980e1211890070559400d078081400290000d94400c840d000740405440e802000c410080c00901c0002000070440343c41c001204402800706420340140ca01803c07540d0448403082c403c0d4128a07045c04803d04098034402130141e429140d5030030010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 901462598 1250 901461348 901461359
    0x1b03060c0e060f0a0305150a0e150d03020a030806040b0405010617010f080a0f05120a12050702190303020705010b060d02040807120c1a1c06080c0114091005120a0501 73
    0x14010702482049a040b414140700c0720300c50419215080c43d0104140d500d400148000f10491000700e5201409003581c07a00d40d0701c0c0d9001c10740c61001500c402c1d814880285800c2542d14264104a0f50b0503810b0b400303843c2100d40d40d90161500d000150002e1f0740030381c444c2008141501e552003910b000301416502c041ea0701740c0c05840780a8044041e0003c11050007248001e111a010005100759407a5204001d40b0383d0442c02c0c10000e040120901914801e40400a0110000c0754002d0a0806246403d8400c000f41d48035002d00b643d840400f041d03070860003030520720350b200482d0091340980f100c9400b5000102d11501440d0000d00740794021103000c580a6400705003840301c2401000540042d0100c2c01304c0489502c072584580280c008507104110540c0e60b50613840420f80c0a41094600c82d10503100b44d540300303c0b00c0300380c554050f02550080c10703614031404900d1100b640c070605d04841c00c42c050f000c806182480040a12210043c001c0e5408c017403040801c0011030f03403219064030700e10403140f1640000c0c00c0e50410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 901463848 1250 901462598 901462607
    0x1f0912080322110f130c090611010905120f16050d1101110318030c030f12060f012c220612210912060e07090603080904091b03060c 58
    0xc1815850030944014003000501c011025014a2008486134040407802100240e045004030b41d400e440c50b42400c1d5034000300ca810000000c240d510680b140c4400d940b030385542901302c03a02c81201403e20740c041d0503141010142c0c20024286480b4024643d8540400300020301d02005203000100c0e8294044200c44e141d140d40002c0c900c16010042c0d00a01030700e030704a0b1000d11540005440491116401410307104644010000c41d203075a10074405072038a8500700c0c0ca150315180c220202c0061401d1f1428009680740c03518401720a601c0c10161281801c90a540840d10301041107180810009145180c050b111640c2e58811500301001e50001000f0f0303040c2c801302d840d0a64003158842c1400030310300c2c514900000c01c501501c00442d4030081c00811401301070402141c6002046e805190541d00f488903070018804c06070400320644502a0880b40320a0740c411060003110b181d0f01c005041d0300c005002c41c410314a010341000101c0344c021207030052031010150000091641c568800c4503147c2c1e0b603c24501009800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 901465098 1250 901463848 901463881
    0xb0108190b070c3003020903030d0905010b131505010f02060a0507021204030b16020f0c040b0d021203030103060b180403200d022a1f09120803 63
    0x1050060018503591005100540c91503000c001c01440c00030000031600d43c031400e060b01c1d41da41c10809400d100504d00a0020b59032120703070210a035101e42d8448030b00d4800d02038001c48442c15000740041d4a0b281d901c0c24a10024100403e08039429501c07002220718070b6071010602e050740145a080010381040403000c0d1414080c15a100d81e0502000d100c0f22100b147d008580c0c01d0f03009010713003400b14450340c518030128205a4075990303008443d0b0000c00d0220a10480b508854442c10f00c0740601d208083c01808140e03901c0c1c4031120500300550109a0b030a0581c100b5400251821001034800d40030a48a580040d0103407014841d908079035031000c001002480a039001d40d12100c5010b0f504402007800030450b904004000500c0581440190034440d40e8014021a09003062420042900c48200200000075114181895410440c001c41e034607215107608034940b000d5425400034a4804564040540c01907034012000602d0b0500062038400141e11000c2c1c080201c019200d1100c841d40c0b898400f6115584c5001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 901466348 1250 901465098 901465109
    0x70e01120509031b030f0a0c032601061214010303020a12030203070c0609050a05060c0405010f0e3706030902010305151806130e010b09090d0e1c0f030207030b01 71
    0x103000c148002c031070010045422418409040307840c2543d42480c0145540314840702a40c01d00000240010301d1a070040700b00300403d201c0d58440c00100102240150402c0214071460361030402d030300041080b20300130307002c40308407198601c40032403c48000074072040f4000702640203801503042050002d08000e15003029014400e12420210b003141000c090041c502000e901004005694402501c03080c8070041100e03400060748142203c50604d0000440c0f2410b8109104960104d00c08464085040f40510b403048070030000a00042074960b0b060011510400040d8034550340056103040c00c40401d000003200c6000b400041d100410341c0b101a2000400300c84000300010b4010180c0c0039a440f19948010100308282c0340040300301516102c200c0010600d4100084100b41e051030000c04044201d410340100960520454641009a0b40e010900341c88144800140e40010840441c260b818a032803821103035200c11036500510403880390364030b4940b1000d07519000e402613405803804004003c520601280500b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 901467598 1250 901466348 901466351
    0x8030301060c08090109090513020a0911030c0703090803030403030204260c0d03121508151e070e06030910050c04060527090f0f07020a0b0412030e0303070e0112 71
    0x601d00350300107140c000b038550b004000c0140001e084000c2c2c0c0c0308520032800303000110702c2000b036400c20002000d200910004224010200b4510002d11590796100e0140c00808105001d461a43c2c0c2d640006000d074000d850450a0021047d0b01282040b8200f001c0e41c80b5171321a0300c00598850600c421910690b40b0341001001d9041c0c155485001d0310741c0841c02e00916042a51201c411482c0c0d49006e9a103480d2540c80c2c05280d83c43d148000c2c4062040740928001c4545100070389a03603400440d28500100f100b103401503420f00421019440c00a03c0d0f10707250b5401107a501c0c00c1d00d0005048400204282d10030342d0200c8850703000100b18402d5012070703c00d09403c0040c901610b445c1503c2c1000203041d03030158008610440d50031200080c1030a280d9402c007201c264004159081d54641300d10f150300b51043c15500c0c202081704240000703181900014100e4000c640200000c0f000d55240d6660040075820403103550105900c1e0307009240340b000c0401c080c7d40210140d8032400c1201c0c401f01c000600e003d2030340d9040c8582a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 901468848 1250 901467598 901467601
    0x21b0c09010b040501030e01061a0a030e191b24200d03021303060c0305040b0a0e0a1101020a14070512070b04290403030207050a050d11040c020703050105040c0f080303 74
    0x41503102d0480b41158004c0c02d011403042d0f14013000350300600280d406203400a040e8007140003440c10401c001d1140c0e12850700d0410002e00c1403201c03d50350302061200c0ba0403d24030401003401041880420781281074056442551268407540701143c6203051550080c810465895001d501c00c0e000046090f42c030b031f1041d02d00d03410003075440c80141e511f07000c0902e1741c0309041c1e0015548117076941d01001c11000c0c0d0f80103101442204101a802001400100e07000d855444a603408a540c01c0014002c01046d0101003000b0304140340345846030720003160058034050561040c1c803a000c1c0041c83c0e101110308111125805020b0107482c010030311030380e20308500111080e504525401d100c1401c00c88291810703540c0f180689200700c44464981c10990524401245031a0700100d000410594006070002c02d42e075043c1c030b890701001e5a0384203206109880071070003841d9004151054240c2d0500d680072005502c1e45204a861403a41c82c4c5400f42190010f440648020f050150280410420848100020680c60004600c0e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 901470098 1250 901468848 901468859
    0xd0c0c03080402011209050f1506010c0c031205090d150506011106042a15021b01320a0c050d020706140703120f0f0c110705012001021b0c0901 63
    0x380c5000a0001341030204880103450070601951100480a6002c8112441800040d12032956899a02d0761201c002e400c807400203c10394419010b600e0308685c010303114000720f420741d66000ba80a11020040f03003041001d000f00d000650f1003035002640e0302d020310000422101e0083c002401d484000702854144109400c4005061400090f125030241c1c20041c81d0002040303611030403c0840750003401c80c03608450f00340042a410305002000010360420b030201e8000d030b140510941010341c040c1607510b001c5522400070b6100d19040710740c98440d40305022454420020b11032039021a5400c191050710000c2c0b0f00710255010060108a0381130600514002044611318151005105c441c01041030b111207003001c14a5400c1502560004000e070481460a1080c07507000070511008140005a00d03040d941405400460710780030f0048815400c020740c0207011501c1c1000019900550404d120489600c02602c074034602e0035082c40600354040301002c00e825107080303150080d440d007028096498441c84410004000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 901471348 1250 901470098 901470107
    0x4050312072c0a090f020f0c07080706020a081c0603050d030903031103010b1617030a05041e2102030c0105040b040b011406160311120307121505060c0a05070b0d0c0c03 74
    0x46136001c42c3c0c04034404c11052800c202038003411885000d4604042110101e4400201c0c104064400600c112004156500d608030f0b41c80e030100b000070f004c2c0c030000c106880300d1569000f04650b0809030143c0118086951356101c902e0300c280c80c4200d400195030345109208041e45400350320203069484212500f15410010195010320900c812915406000d0003031070104581401035210312401c1c0038450342c6070315000e01c1c401c0c0a4403080390200e540540421100c8140d0700308908501c2e030142c00810007101c03590b40b50a400c1703044404007503400c1540b000b80141c0741c43c4202409558072030b0384a550a606141800c1c58015400c982c180c21050300c440f08400707090380c1c6448500a4a81e40031101c03c2035821150355040907a02d000424482c1361060161041616180b6010f000460240a095444405005a18441500b107030040b00601d4110b41c50000100b00070300e8010060070312000396406584012a0320f58540e0318149495111100901000c03911040c503081610a40c0e0b90882d00c2d0401e940139031a5598000d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 901472598 1250 901471348 901471369
    0x9132a090b04050a0e1b03010909020f03060709031113020c01151d1302011b0f0302060c090a0e06031f0b03010b0a081005100909081201090b06040e04050312072c 71
    0x403400e40341c010024082441a1b000e4480540306071842e0340e52075071034010310340244c292503505901403015200c1e80f410b5070038000b4000b0b101e4106a600d80b51600d0075036460032080141c84e941c03140d000080c01044012086a0310003028200041c400024044100d00d0250298811603806103800f0f0f031240c40c80101c401181c0004a500c00640711400c0910300061006940058005000a4640010790795000400120810040175180a5000c50701d140d5100e00c142c000320f00c52003011507003000b00d10404104000342e2102d5a900300c1802400d8030244180030f00f400d040d0401e40f03600750a00907140c080901c00c40c10300780309041c0d40b050b042e681003c109040101c450781d00c05481d5039900d0160340e210000381540c4200b0201c0c2e030242c00e40010030b00c008101d6090a40242d0001d520780d2401c50401000094a0182c03031148450300a00944980d04040c034100e04456003e80041095a01f07000800070703e5440024040030602c16406a00c40390710544480b20684444000a02d41120540901150104941c0c0e62003816 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 901473848 1250 901472598 901472609
    0x405060613090f1e09060501140d030c0f0210091403060f0f0417030109060501120501080703030c03020f1f0c0e010519090801021605060a05040809132a090b04050a 72
    0x8203c050303c1d40380800050031004c0d113101e15088229100108143d00c2d0304a010028025041440940d80b2155480c02555081c0e01c22540440203085040009019152034554140100c8102c00c08150307a401040b1003420340034001c000a520b00d03200740101c10000d145500107000580080045240000812042e820042d24011095600000040801a00e0180711400001d181c1d41c00e5280d50b510b21080b0040e245500605000c1800603031031065171104c0341b00e070314102d400d220000c050700e61a54500f5a0f0740700a607403003603086010341c8a20324403461042003640944900c0c80c65525414030040e07400021590750718410300400410080c049200d03a0b002056440c0703407950805d6007200341301d40710003030301c05810541c030403610355001041d890840000a42c001c2d0089020710103441c89966000c035900100c0d01c0c00c40c1c0003084900107011141031806e01940c0c0e074114003420000002c2200506401d0340070407400702408408202c00c0105102c0050b40100303c0300040c910303801e4590815040c800005d04689480c0100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 901475098 1250 901473848 901473851
    0x40f020d02130e0105061c02060a0e0d170a0f11123405010c23030402151602130603110603100e100302040b010e091b0c011109040506061309 62
    0x2205564030342c0303148056100301c0303201081240d4140110034081c04048861790320030600c0e030003400c852040114800e6a610703030041045242100500c000c1d03c0780190a036800c9d030003290b030b0302540e4001110903200300c2d260b0003590516900c40041560040c404080703220380c1810880703013a040c0c0602490024500c1f0744100d11580303103a1107a01c800c00a68a1036800c10074500238240c8000c500c82481d880c000b0403804070380100000e0040c0c44080c41c0694403100306a40c030070f142c2c0001a090303030103018640c000303150003d00c02064040b860708640300000c96a00103165101d00e61910180341c0007186880125111403511000c411b0291501d183c68402003c5002108680a0000000000d600030180440c03040074007810400d605803420275403c0000310500d240001c034001c07460300b03801072a0366014411800507101c000b480c60b420355888a01e044041088512820030042c1c0c14801000d900304203008013506a030102040340d407298000001c2000b502d10150140f400340a0801040ca1001218064081038424000c0d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 901476348 1250 901475098 901475119
    0x1b030e04230906060603040b010608060414160e030c060f160203010c020304060311042121050d0b090f04030c0f0b0a0504052a0111030412060212010806040f02 70
    0x100e405088006414550146081240741c0108209450207010b001c680c8110740040d695042840364900c010785010300501c682d1001001341c3c0b4828400f8071303400203002d4000700c0c2415000c00301348521442030312400c0e1807000607008c0e0020390364005e0800568607400c400600b555803003800441c0d168418a106c28480d6100000d0340c122070195840d08003851035010340200600d0807a850003d48a4006002e20b9000a0500e11500140c80c58030b070642d801c2d9401d6500240c0105000c016130b030003004141a0880b241c10802d00356088030303029943c50700f004c0002c90320345560303409107019142c0c1110303501c18489203e1038264090001e44070210a40c41c0d40554103090070407405d801800d0071040c5082c1514010700c1d400108081061448594004601452280c0101c8842c03002d02202c040a00c4800340410a154918007900c224541c440c42c42606a90340010580b4079080e1902407100000003400001e8400369000614000308485225480c3e0040070b10300003030101c0d800c0c1903540300200609401d0182c4511350425 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 901477598 1250 901476348 901476377
    0x1050a050f0c010c0f020106061b1b15030f0501030b015d021302130b0c011a01090f0b1b061006020616020601031209030f11030705011b03 61
    0x200d07058035200c140c0c0540c80e40c0e0403240310382c043d00d86180100001040160a045100e0050044100b80c0d0201d44682307400d80c501d1075a2800703060600d1010358205a01c01e0500c01007504a40304000507050f2201e503505281d640400260684507241c1d07030030103100d14140042002c0358904a08505549520b02d444c101d6000072078517045003110700d05c81d101c800708510000c81c1c0c00b0303100a1000f030114a2030f0b48000d03c019050080409525541e810040d405c180e003098191000100307503000b02580030310550900d0200d42c80c6c1510310f185030080d410030005d503035517043c0398600c00c0d008959210320403409107800d004542c20040d6010103052030b44900c10700002c0c08665411020340e099482c254491040c803c9030070b6860702c0c920045c0900090301c686000741c010000410f038030b01d20012585206d183e0903001401640d1865031420b80d01e50744512a201040020000800081e120503800840c0ea4014030001c82802c10743c2d41058248040c1d079110f607044c00544110a109004c0c480d16000030681c041c04c113003101407007a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 901478848 1250 901477598 901477607
    0x308161d0f010c0b01120201080a0b0f04090503131206110a14070302100906051f081506040b060c0307030e011d22060b130806040804051c080f030105041a0f01050a 72
    0x11001013542c40900008150036101c0009913201034001d9a80490030f85420102c501120764080702c070b60300303d40246181c090754146900070f800003d2158044a161070700d1058041581180f40d0482d2018680c05214082407201034040e040c1d8508500c040140303029005d40700a00303002d03052240010812004603010003070600902016948006806d014040301d0f0740d0740b80480040004a80b44444060100c051074144402170850b00207032125200188801118100c01500340000280881e03441519920006896141c0038081c0100045600040d81c681030980342c003a150f008a01d0307180d03041100e01c10700143c0c1058400c10710340800c3d4003a501c900c81e50a030340e03038244101e16019010410660400800040701c20440e801400b0403150780311b0300300c140307619205d80d6034071801d06403000342543d1030a00c420710041c9000792140e10040d1424040d0707060b0802e01e0b9610718254008030394101d0800c1d4048010401414980600841c4511640d9980700300c00d88100001d441500410340181040008281001080d004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 901480098 1250 901478848 901478867
    0x901050919020a09051002010c020709020702040e070305010c08130f080f0c0a0804050102010b03070b1206010908010906050106090b030f0c0f160f0201170f061c0605040308161d0f01 80
    0x1e11420355481d89000f20181c160300711885860b01900c810341d4001d601500c10710440b11050001d9015002c800d01d071849520180d0008541660b20990b1203500150b0500200841401103100b180049008200004084c0180700014100c4150300301ca1458800064040703d00d00180960051580d910780000c620509180d0040360200e500c0c500c03980b5100014458020040c0c4100c0c3c10136402482003e6a010505840c1c854600c071f89010024240183c100c403c1d0110300030359006c1010f15002070352640d140b02150943e0340c000d40c143c445941e203070700500c01103030711010003070287c0240c5490710324500340f503941d00c00301c40c50007065007020540226a0800710400107044803428071610010b481ca074034143c02d20b000351411001080740810340880344103004120310070002c0e2040400e04092003041e5100d0080c8200359038214140b02c0010800e08800c0c0c002140391080307901460180d034072a0a10301d00300800040c1302d42907418640600c45908401042e040e240c01c640da1540d4400e841e00c5981981aa005803503a151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 901481348 1250 901480098 901480141
    0x190c0e1510030209090f2d180c09011d0105010306030809040c020f030a031418071401090b0c0f010b0108060607020d0f14100c17040602130302030d02011406040b09010509 75
    0x500e641400321b001c02d40c2c01c3e914000d44860809043ca00d05e20f40719100603441e840490900c1e1802203000a81c0c6070044491308101200c00016200414911790006000d41c80c00d0308071400145030190b00c0045a0a0810301c1ca014210a003000c008250454580c134007280905c0054501c981d440c1d584681d1290320a000c040320120902c0100da40f10028003101070f000d0516061420f01c00024200000c1c0d138100c204003410030303040c1200094000d82d401c1140400d070405989401074180324843c900001d4480c140c000503d00602d0b03c0f00902007009400382240d080d50400c08d00c1c681080f40c04014071015669030011142090b40c11034a402c0807424503c0d10606028081c84040e000542c2701c41c4805249001003072203044680703560004c1000d400c141d2826a111658030842c0401080f46800103800540244e009100c145081c0308500c204581e139134002071520a0031065000140d455a0b81100f1900015031030315007040c0125020f02510001102098400005100c1c0500c11000d14011558440e07035401c0200140c203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 901482598 1250 901481348 901481359
    0x130b04050106050903190b0115140307050c0d080601090504090c03060c0215070c0f0b0601030b1302040f06090311010f181d09150126190c0e1510030209 67
    0x182e50740c0d00034025800900c0303880e001c1d018045142072540c040c00303101034000354045d54000c41642011140d17604100b44a514030144403070f540e00440c40c4e9096101035071041c90380d40d4449654000c203409850412003103205074424000c2c110203001440e0b81240001c401e869080d10005401203080c1404048c500700c6074406805941f80c01e19a01506901003440004851b82207180032141d15070f81c03000c8600c140040005003006200c4034100f4009420800c01076041300c0149404940709800500060000d1110310840e00c2c003a030300007000c218420713a81e0304000003030100341010700c14946503445042d04034619045007410400f410740e550900e240901d60007150301e0001e1070342542040c0c941b000f101680c6409441c0c00141c0250f00c0005032103070070000b0107400d4003201078010180c9905c0c2c1540e00e0300b4031614034a150001c2d200b004d5403011000c410003118100740d9440d0044d48603180142080360744008980c104590340208003007001130312024844c002c0c64038101640c80d2420100e9400081780240541007043e60b05c41c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 901483848 1250 901482598 901482601
    0x3120c070b040938040203060f1305070305060d020a1502031e1213020d022e0e1e06030705031003020607080909070503100b092106010312050702010e130b0405 70
    0x2440079510121640c202103244440d4104010aa1442c0700d002054440205103281401305007801d181e0059070301304c0e501411007125652000000b490402c00c0d0750742020074595403010030407065414001d464014bc07040d5420a0460484d40104c1c4104881e400b0b2281880300d04543c0010091003001110308010f102030944c8102001840c0d41d00345607020315240700c0b01d95002c0000c105180c07400320134025820741c010407540600380180c1c24405c2c90909510005038003107110900c480022500d6541410040c032035034400c1ca220903550104002e2017280042210700351485116240d09490b103804994008003e03003841503d07580e940041da02000e4403504002e400001c08030702c1004106d201d00107040c01d5501103d4511081d5504001264540022241c0905064138080104203065182000b4201a40c01900c000240e00101d40144034207007110f482254658410300c010428003641e0b6840040c0310b903442c0b604a1070100f00b500000e11038541c958010384500c2c06405045060300700c2d580b04c68401075015000740042d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 901485098 1250 901483848 901483859
    0xf07170406110f0111220e19050f04170d0e011e0513050c1c05010c08070f1107171c0503071404030b010b0c03072a080c03120c070b04 59
    0x298203030031912100b50f01c58801d0f01c0603014010700070860200b011151142c2444001003869420500600204555208400700031070840340166003544204000c0c0322050a80c122005034030100d40c801032a11420b0036140d0240310000c1d00003800344030082c0c140007804e600c0f202c00c241cbe0080103002d404071051441d80f802c02c01c110840c540d0710b59100c1d4980d03192400c00850751842c159071140e00821000400b03e0300001d120b080f4a24111900c10307070171132000090610000309640c48a003190802c0c402d8001058101d01081180c13580311020f04498105403070440ea1a01c00c0c1000155502c01c280600451108030350281036803104100300c50042800f0b916808181e14000140241580e0b1060702d01400190402104403154603815003282c048907401b80d1030420a81c60058914400e40010421170102e0204002c503c02061420007480f017100d4089103000551415600e684500940c00d5000034000c0d003011a80e4040e0f1f0751302150720421048041c40c03140d0313500d0a0701d40c50750804441d600405141040824007152 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 901486348 1250 901485098 901485107
    0x1503010348030b0f040f0825060905061b0403020411190e0a06090b0d020f0c03040902040e13050607080606041a130f05030a03050706141602070e0702030f07170406 72
    0x40b0307030203030f0039141d80c54a40d40042103120000f100c003d88140e44906000c00040c103400e0040c50030350100c0c4d882441211900d04261410845108103456043d00e0300080c01c00d002050000642003030b40403002d04030f010a04449209035000e2403002a2007a99181241010070511100320780201850201c02102c02c45180c1000e0020041c4d6105503008004880d00418018000c0c4030030030990741442c51141c240110200284081e5106d2103c42d4803400e414010503100d60400c002810207400d52040c050703180e608142d00c0b002e69900090401d802c82c20b11000d80c0d80411404903826400182d41c0c9080b42c000d60391880420054070a9030f00200000f10351004c1204013070448000703010030480181710800150382d210504c11a0940c18050150306401c03800103100003a001d01c0040000c2c901c00c071004211030052504070307400204203e030107200c04102c0d0b0309280d40413581800010701401286a0f00c505d1800c080100a603a8060060001c03132a80c0006801014410885101e003070450500340282d0f078481d00d4440050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 901487598 1250 901486348 901486493
    0x306030209180c01080105060d24122a060e01030b130603051e0d120b03070906030614090601150201090b010b1216050d110d060605030615030103 64
    0x80300360040c1c01c103940f15036224903095412201c0040c04103061140c0142ca642c0100444d03034000012055100c0c40c0d0240159450150000f88200116072a510040f810170814040b6500100c500d558101100500c940c00150004019110306141103050424036200680041c080c410400b6030000109044004051968000030103a920410540d0075103950100d1940001200c2c101541440c0c2214881100d581e1240000300f02c003500e1003c000c81d031b07488a2004a404c00111b6008100d21640340c0d002801445218003500d101c856810a154600389041c0c03e001e9186d00c4180540c03040034000941031940c080c03007500485586602300d015a0380e0b55941d0310303101120b40e00039442c0b1044410301c24006130107403a8100e0316103a01484c1d6201e0310700d001d00e6202060300505a16400701c4c4010014459520510158442c0202500301ca84400d07a490400100b0440f05c3e51038110380c0c520742d8004000510000c0d40f950b01015600d00f21168444070007100380041c960708030310052140c606101c0c0c550544071600741002c201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 901488848 1250 901487598 901487641
    0xc020102120c0c2e14041509090507080114011e080a0905070b04060201141e0402041e05071404030321091218060e0919020f0a030b030105060402091c030306030209 72
    0x740f0741c00115910959180000040d01e40030f545d402d21080001c08202540640f1040d1a40340c010710980d115074441007150000c2c1c40040000394107030014444108240740c0ca050990742428140295100884184071240e45ca400000801107810041110700d142900886541d0350300030146c52200b600d59100c00802d401c184160f500640c246a422003e420600743e000b4080c40300b034a05502e142083d2501c428440e1009003040b40c000b03076075444004000c0d800000c1c8180340c1882c903c012985040c200342c000c05042c1d00c401110000d100402003000003940104002c61707188103209401c030380c240c04441c00c94014210001c01801c10080c014804c1d00d03003940040414251151460540d8600303403554012600344101d00403143c3c000808001161410191980c000d00705808105c01610700b0303200141e150400e030092106a00402c3d10364420200910303081c01450750110094070118204205100002c1a92412140f0248039a07140c44001c001c3c9840fa03040300000c4c50b000b40c105140c6040040e11104da111040114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 901490098 1250 901488848 901488919
    0x1091103011808120601051b0a1209060e011b020a260c3001060b070308152101020f030f04120309110f040b030d1e0c020102120c0c 58
    0xa00501100b100d2202c81000d8105411508110583c000c007585140042c1c0706505210f0107000c1e4041602e00040c1316181c00c038504010701000703d02d510b03040d1f821800444108080c4642d0902c01c3c4140f0b5449020521000b00901e04030070140060400c2510f40101d00201a42240381c980000c41c00403c40b41801c0c00b03100c0142407e2240c00441400e044d03d95040020995000040c140108a55011510220607249285e04003021a4030142405402c41d00d07158084d000745900440c4120606800a803100e42c00b40c0c01c05480f5030484005000a40031180c040c0d4040281d90070140c4000714504c0c25419169a01040c003512662828984409400391500300c030101c90840d00c56909100c014446e000312030405038080c4003413008094010412070a01c038402d2314590001e545070310a00c245d0350100b003410481141a203034101131900bc0b03070b20f080c8010480000e14060120004c2d800c5e0060b40c0c00a4510381c50301011005907255855001403504000c4e40d030701295400300300500f120914100042e071801c8400452002d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 901491348 1250 901490098 901490111
    0x2d1d0d180801020906030105131401030323032a070c06031b02010b030c06030c070f0602070605101406030c09030f16060c1106070201050f0c160b07081b07080109110301 74
    0x21050700b0f03440346100c0c858008500b800104064180002c0c00060354a034800b01290741e403490441029840303001d038025800603c1200901701c00d16011100c8515040035503102d5407840c0303880022764801e900300c100081c441c0840000044407800388042a1040950300c0b418204181c1d9540350020090075003d4181048000c80409e1240070a005100e06010000054040c1070600300d002c003005aa5000103040d50360308402004140d001490000019985501c1014016215940380c148841118401003010355001c0e1103180c10b001c0c8420503005049050404c954555413642c440c00d07856454040d88006c1c5805204288400300000c402240c6a0040c9007110071241e911031303a9078421100301c00c03012000b41ca509210707040000380e41040001030161030f0060500c0e5103881c004c800019000e51161030070103456000564002d5502110810100050506004450800006403070700c03883d52040400c7c0802e46040300c1c0b0310500300e40c000d002e003100034040d51001300850320380c90038400d07003070184080c10920a518008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 901492598 1250 901491348 901491359
    0x140a23030a12032c1e0f0f10110f040e0406090f26032806080d050c010f050613180213060e0f042d08040b0408012d1d0d18 54
    0x4064902014040141600501d9098480817a4422402d40b6014091010f21054580c8100300302800c01080e10020902d03d050481c0200846c0e906802c09185c02c441044a1410001d500f4142c81c2603038101016540c0e503807100d250040007444281c90040581c80f8400c211414400841100404100384103503044000c40c0801581c420307031000f100c00c40c0300e801e03280403e02d020b0541c1440e9140300c42899900060141c4e140d1034224070f00001d01c049140001d4001802e4041e8250a02500c2c0900d088074005100a04180000a200b8240307100b103909040d5880f1600c0c03c5802031011075074101c603005000541500400101c0601038040e9004801c003000e500c6001c5451043d140c0d6010748510b0300309443c000710061020b003446400741d40c0a00400c540003124661800f02c0c81107001000108507401c0701d207540d2882c001c646402c1d1444201003500ca00400074006001d0720207010752200c0e07489070540c00560b05801c081c0c2d2040d404410b1800d42401d2090484030580c0a8021007500741c2c42c0b840340020201d203991027 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 901493848 1250 901492598 901492661
    0x60603050a270c0b04080a0312020f03060103020708090901080c01170c030406150e09030a090801020a080c0904180f1a041205030a0b030f07140a23030a1203 69
    0x4014592840c03002038040602e4094141c00700035880c41584440380b4560344d11090b01007500302d13412501840d00611041c0d401c040e0071030030351800080824003c2d400d006e007800b0036800c6408001d02d51418035030001044420040008125000c42000400d8284956151810265502e03039100c107441c0862241224215203c00d8103200c00c0c0301e884040801403a60b9516550007014140ca0032141c1200c103d0141c020848410400c207188c4101811070080d07483e210410300007080c40c0700aa01a01940e4410031407401c0351a80710800ea6800f41e0f500f0000d47e82d4000c1000820010f0072541415921300c290401d1803010003554101030b1002c01d0140d81d18610640e11200400c4d80d514064034014003800e454400400e02c0303801800035507406400d242002501c40c03419004079003415000503031440e007030300702c8002840450140b581c40464140b00759041c07154241400c5210298080464000040c101c104919000e83d07601081850360842d440200c003500001c00b000d0241c0606001d54a0030304000300700007609801d1111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 901495098 1250 901493848 901493861
    0x303130f080f060619150f0206010e060f010e1c0606090515031b211f150306050c04031e030f02010507050a031d01050c090109080705010f080721060603050a 69
    0x3010182c03d00340c0b1900108000380070410000d42c0144001000000c1c0100340c080c00650800705a21104998010343c03100034103200c816040840040b10318002d0050a0701c0740c01c0481d003c1442820007040191202c1c001480217070a044403e440030000b200020704008581d040582180d80c072034018820303500c0d20189080248240d80c83c00e60194003011000f085466111a07003a00181c001e041501c034070f4000b80349100300380203401148001d58083c44d9400d00082d40e9045807000b007100e6040c200f101204031800d1030f40030022484013a0203c0d845038081454441078000b20380055900410002103812007031460780b0f1582071070f4001c1e00070a4225089240003030040c05018030441382581d8892a18065140580003816400d0241031000540d9002c0344651f40309100c1d140c003c1c40e00304106070711407402900050001050fa0005030141c0c1004034104a01c2c0d0704118404840303601c030b040c0040c82c0e986074801140c3e041c006508031217848264200d44600c8070742ca60700c00b40c01e480d01658240859aa00303444141034401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 901496348 1250 901495098 901495123
    0x615031a06010f0c0c0905040b06100c03090b0706112208070f030204020a03240512030405150a02102904090f08030601050705060115180f060c060b0303130f08 70
    0x104083c4408014810b001c625078042c41189640d0f41540c4516404c030840c1c10071101140ca0040d154207106c52898002018107505410740780c6000008201e56004081140501c20160180d002098050070002c4070303000000207145d8940e919171501410607042c10003600c00c103c41d041000d0b009038081407400300800c80384141c5500302c07156203075989140d091100030343c015034040040542d20140f840388000803540c0c20700c8001c841302a060a10b0f0620080001407030407200c3c02e8005030301c208000c00c5240c40d1010b1504035140314140b00350700c4803980c02c1c0503805c0c0030f2560440210342c1c0c500217003211104c2d0324000c8000001591100020111014024002101c0d440c05c4003812124405101d10300040f8944006d42d403000041c50098148045d9071740c4c0620380035080e0009003164075201050168960301c5220241c4d400c0c080d48041c400f452803e0154082000140956020007010700d91410500284e50049034001070064116070b90741c0ea0713101c4280041b2070720780604c41406083c00c100195050300082c56420159 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 901497598 1250 901496348 901496357
    0x6041409070315020c0d03090c08010c0c060e0c0d05070906060f0c1101180f09050f0c04170a02130b0405060a08070b1b0607082d01140a030615031a0601 67
    0x18215102d4682d15500d00c5041d03100d4079001c01c401c4000940a06c62008100801d07140401d1002084ca0040c2e03911803d60482ca0040c7c0c90b241303604503501c0c0e2055110b11041d4100b800020300317907800c200e003504121503c001c4940080307002e1f80d20307400c10600080940448040041c20490380b92500c2c01100c0600c401c80e8a000000e29035040200031400c1c40101504020050600411131000b103603129500081a80c001e0300d9000501e082040000000d000c2e0340d034016900500110745180452044026000f180501d4195603485a200e82406800300721741d64410342c000303000c0080c14000000030f0001e809600040e500890038100440c1080c00c00061071402e0342e51440260803201d081c075074044c0483c1c109603506040300c50031024825984000788034450041c3e016641d00d04071031900c1207003514605034200d801c1054100b030541410f10101c0303600705103043d100c01d0034688941d80c424500142c100c030f41640019040ca45080460703020200418110f104491165690302441e298030301e070803100540119241130106 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 901498848 1250 901497598 901497613
    0x130b1303090b0d0b0a08070f1a12040507051f0314190e030d0f0204030b07051e160506150315040506060907210b0a150207030b15030a080306041409 65
    0x480160b0040c0000d5a0380c0c0700e000440b42205000a8007050499100c82203a4011500030301070399141d0b80300340d07003c0c00d580345915810507101d880c0a0124450304c0d1030000b200340800041410804140719100041030010050913a0070020020010340d20440495100400e1074a09130744031100c0040d10300d074403d8008290404841c80400c0c2a03d02a004186100a8900040040c00c4582611344036007950101d0f100c00068076142036180000f51998060100010700a003403104000e00d580c419100f1000c1660000703029103483d102c02d10710310885000480207066004920401011074210b07510b89402d0034044003201d000050142619000b00400c0d5805441030b001140040e03d20b00b00100c201d0342006161400588042910781e103040031030020845002c415447d4038104405107805284800901400c2622079008503240101958a00841c4001800d080e10349001481618244400c0740041c0c2005d419152201ca4078903000034540e108446080c072807450000045010000c0314103c5208110a20041c11076 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 901500098 1250 901498848 901498859
    0xb072d0b1602010914030c0606060f04050420340b0402090915010b12160519230306040e01060e1b0d1404020111010b01020a0209190203130b130309 65
    0x195400390000c400350343d00d5111820010780885c00100755001c28a01940d01c45032040b45003400c00030090032481c4900002d10038000c0c0c0c5000b50003101c08a500885000480c081030750240704401401c0c0049803540c41c0d0108901e00c81c40786c18501030390090340c00300818440c0c482c106460342d4984140b880181003039040b80000760040c1000c01441d900700d900d000c11a0b404412071450142170300e000360008400036101040504c0440342030489503410040c140b04289405401341c0c0001c0a81c041c01954151a18590213210b10982c02810888944102c0990764080560341c0107018001d5401620940d0040c3c6ca802d840f142555411700c100c10a440c400c149104003600ca11400c01c6401c0d019000f10f00101404101401803035031039100d0000e019a40d40000038181c6054000034040001e03692000d4902c0c3d04101243c501b507030340800c2070780c0c0040d4100e400325065102c4620583c1444072003c42141080c0c030010034481144010b03011030150b00c1c03240c0c03081246649c5130040131403010400e020040104000342000d015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 901501348 1250 901500098 901500121
    0xb1c211704061b050d0e03191b120c0506150d030f030b041a01020c092a0c0f06041707020109050d0203031e1918031b0b072d0b 56
    0x1c00078000c4001080b600c01d1032225440442480c8000c1d030210701c002900000e0038000d4002c818115129801039410552440809981c407050980c40604000d10f4142e01c41c410303501710740f00b0410305400c884400c1564255482c040c0021101d58003c1e035141c4038000000b13148004040c40010101405401e03180540041d036000d44006000307151143c180360310784e05807110361b072240d109141c00b10b0240e440300a24405000c001a00341110001264015642841001402c10010908441000d11520b01141141105942e04510300503003007031207040c0c000c0c584245c1480000103030307840c003650282d0810400c0d44458800c01b8824403074111700901003180810100a649800014103190074005020f503480c1c0385040c05280854840b0f00184e0b05000004a00107540d100d4084000300b50b4041c609065500020152107440301000c580700040c4500079000d8440d8080340c041501030010500c06403015181c51840c07406148840815444801202050150036822000b00c5202891140c001401c100c55884000c0c0140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 901502598 1250 901501348 901501351
    0x20f1605100f020901090503191b0f0e0907050303070b040b0604140702070602010c02010b0f0f01050c0f01020405100e1018051809150906070507060b1c2117 69
    0x22503600500051080d803540318014040e00351201035006030ba4403002c90000d454014150005802a03201c00c00b516903e0080308024810b071504048400d1321403442c3d5400450b034040c1c40e08000704c0341c0110307440000e039010131000c21070241c40c41d18181e5120b1074407a014140d40e8003900038040e0202d50510003080204110f007680c180c0010303024202040c40b02543e25070b81c002c0f0b4000c0e141e1200585c0109010010070f94203103d40d8900c0b07007041c4000c0c48103400144c00a0304203000d82d0961485200d0020700103006a01500460b0081e60400b426107104210941c0000d000f0341040c4180d078007400c00e58032002003243c031901e4269001039008101000440412034111b62181e451580d148020010007004101c0b03a998164a04a0045140080081d03140000716542860464200c2090744000002442240c40010071020307400869407030b0198070740f412414440b0180170000c000d140c000e4802500d0140b4400b5002038140d450b0700506091403610f0001e110345503214007421840c00042c03041c1d0700790842640106a031a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 901503848 1250 901502598 901502603
    0x4150207030c050d05031e07080a0e0306070e100e182833030507080c011106090601170c0406060f0f02161e030206280203071127042301020f16 63
    0x5504007803065480c1c81d501e9111070341c090081510582f0007a224501000381d44d0380201c15107018448000c0038008182070000705440f81e4103124001c000a40c098440e82c0030f15520b00120007600b02d080c100081c0020890032000c40035280011441d039042c0d55185d140c005c01302c6100001e0b4090007508060030309085034050002114462018120002000c200100110809800781d00c0c043c1c44801c1c0880009844601107980359076142d0031200400c040f2031004030b03c1d941103d480309100040c031901d2141d038604225070042c89645c000c1c600000400e0302e07a032051007000721b513825403a600c140c03a882c00001d03a80d032400c601d080000c4030143c403402d014120981c061181c1e0480c2480f04000b000c6c1c0c0b80e50008107141c04c02c04a2010802c4003846060002e84039010040308112940061490304c2480c1d214a00d2002540806134010340701c0c2e00d00c0c01921401c1002101100c17411400860180c01c00b0f103809488880321009540c03940c02c0162a840320030506208580d0000f50360241076107440b0100c09080071070780900109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 901505098 1250 901503848 901503907
    0x17010512160b0c01180c060f1101050a06140306240d08192604231b030106090c050d090c150903051c0512060604150207030c050d0503 59
    0x2222146006401000d4400400351036143c5001c4081da5084070a0b0b628802289a810148040410300700c080392070a8901c0c0b450002d5000701251810356403424920084600b0758600700402c01010115404102515800d5a080c0d11031694803042680c3d81400703694011014041001184102d620840200c2d40020090203020301581e0030b487d0407640383c000b032940e0f001000364042c40c0101590701c2601d0803090040a00032030a0010080c0005c4000440200010050542c4e1010b50040c9480c4003d02200444c0c00c00459400c0c1200c03000c880c0f100200e4a4400340a5824420007040c02442401941c05040150303440e6410200048074001c064504003000391290340800d00c020804180e0000c0e4071034401415110001d10301c0ca5031600c1451304291001030a20800380990040354140d000003160010300015140782c000b0307241d44000601c3c0c0c0c171895206070441100034403042c1c5040e0300070a000d404c803801484159009540c0360107000c05002c5808004085400c208140305004d5031005500340b00f007520460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 901506348 1250 901505098 901505113
    0x1321009050306061005220f14090c0313021e1807180506030109090302010b22140103050307082107050409050a0e0d12020f220617010512 61
    0x4664206068400400016006001400107050801a042d040801034504d03200351300c810b48006190b0f000f14031030a402c103400c4902c0001c3c40c11601019801a101c0c81c408084800d40c0c641c1e040920100210807140070b00d565500084100d80c4c0c404c2581d100714480b003450908420030b60700304229002005c1c0c0950a05d00c5000b081072240c0c56040c0464060881c00071811101d0038801c201130802040c1c4485c000c0c20385170710b5100b8400c1c2d44680e002c2c3c0c5c2c11a040104049014001c5160036409000c50a00709030f04108a075001032141e01686046400038403a48208011000204034180d0104000b400f000d0401d610412400300054a50002404607042000b054403801030301d101011042c050546240c03002880c046020b11012030b007441529080036000e00100000031000081d0f5840c4c440c01b08620040c0070b40b0500055158005404940c20002903004081c2c1e1822544e00800c80e000c040341311310a0040e07015501240060051400e50390011044101c00b4841c1e02c2c1c90300f000080b609c51003c0300344a004508 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 901507598 1250 901506348 901506449
    0x3090201020d27060503190b010903030509120d050306011808060c070c090905030d0c08100b0a11070801020a110a17070f0b190b1503150d020a0305060403020706030501 74
    0xe9050b010b8a4a559171942c2c0381409030124090341112400310711ba840c90300b143e40c1656a041507201c0b08903645403c0c010f8407850003c002991000311010200b00f203000b120510100c2e00d030300c10025489110240c0343d242c0e02d042821844911001e8501446100d90700081c0800d2080c6040300c0503098940c4500f110100068940b854001691846441151941e00201d2408101c440394019500b190200346000703551131070302c01d0303000e41c1204040c403645100010004190a80b18803420150450011440c225140b0b560340d0142c0c41d000794070283c0ba0f007002442450640e10096008210040d02e0750b040741c4101091940001c2203c2c0340c1e4410031007201d04680e0030140034009910b041113544120340e100c1c044074444141491403070070f45075a0403110340f2503101100f00b80c6041400d042541d411440c101c00171840d00580d180464814240b110000e5441a40d0316400070403c00300164191180f440795094850481c1c2c2d6000a030309840c2c081c045d01c480441e4949400c185194030300a8401a0510700100303001c040e942c03a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 901508848 1250 901507598 901507667
    0x30a0219032702031005041b06110615011d03031204200604061b0f0f08070507050901050d0809010c061d28140a060f06050f0103090201020d 62
    0x2980304021984548034003280d040100108008248081070341c4400c04019400261181501504110f4031a500e40c0458103024031022511245c00e40e800d901c800c0303103032140c101521951240390303440c04911500c0002924400300b000c044c600000b06171180c01840102039221041080e103103403e141c240c402404100b80341e0031402c5115010300d01580f68551130080030034041002c0010381e0304842c041d010410007046015071012240003004200140b94454070014500328100d1441640082c01c0200c6c0d40740c080c41807010481c010500144140110382d0035950301c6007441a800c00034841c5590250907400c4201c0824070100060400d143d0500d4000c4e8415aa981c61008455503450710030b665100100071a0f2100d2010015090201c4240545201c0544500110200403201000042c0a949120521680c28004010b16540541c0c0280103101006542000000902151045601c600080c0c102d50361154041c0c0b040034100754041c3d015102c04400003400303554198209100364000d1024030a5404803007600c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 901510098 1250 901508848 901508887
    0x501020307050408100e101a0a080c09010801050408030604020a30060501031413020a24030c170f090703020411030106200303010303080a0207140109150c050f030a02 73
    0x4540ba101c0e01d96090400082c0303880520f038220321515140c54106503a04400107500340300d1070b0301c0402c0450209840035688041700810002960010201900402c0e6114080f610444103a01070f900444141e07602c2c03000030f09840301924007078030721481000481c0460400e60020b00d1006114140b43c800c0d100140d0341c500e110704002e0b04150300019250301d540102421401240011300007480e00b88a401c01c00e2202e000c19040140400b9805000c101c150800c40d26000b030100000c10700c0000c4110340c85040c11801d164038004a19403000240f074007103041e515502403014201046000c03040d00155555494078908003070000b40c00711819100d42030000005076a24010b544c0c0c3c004000181c1070326545480000b401400d04202c0c03441182e000e00e860a014194004207881c1100c0d01403812104580322401140000c1c41400030107408000a610344d04d07030000c8150003080001d841481e20028514580030010b003221403415000c00041c90401c80400c240860901560300a45600c00047c1780c207080b80390280c0d4113041c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 901511348 1250 901510098 901510111
    0x40605071e0e150c100f11030a0605041d0d0e01031e1508070803070b0606130e0402090105060913050c131d010803251a090f06061903021c05010203 65
    0xc1d08020a20f0300304440044554000303010f01c43e00300010b04162640710312940d00a409600c0d6540b40141298009400c446000e90120092960320708200f03022201078085800340c24061410046c2004080580100000082007030002400d042d64188c0300c01c4030030141107086103040640b14000034080380c0811000344030404101c43c4c00980d081944070184440400ea82c41440705d504403030740802921a001c0112508603600038000003c0f666040300140760303800b4049205503032842c00c24002c1054440c0101540c0614000c030f521260742d0b070343c0d0002c2101c01e105130006690400001c0b010f501442204d908100d4010a030700345074038144801d401c805c02c00000180e100c01d10400b604401200710020026089000d007502a0180d0b01e07180b01783c2213001ca0180206045002508822154028481480001001c1e040c0c9100d8120680c03c0c2400400e5170b03a80c0d945120101401404045a00c61030700445039010240c82541c00403402e40303990200208181c0c00400d5480032105200c1034400a0f9003031000390311950 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 901512598 1250 901511348 901511357
    0x615040b12180a1203060b0412031d01050d0e01091719090b1803030c07060206010609120b010504050612032d070b011a13030b041a010e040605071e 65
    0x141c80c407190310707480080036100020354101200007107800702c0080380860545410080e200030720902c59200710024142c6038007440e0941e10110b00030440411003c0301000c110700903661055402e00da0182d070f03184e031114212800c2c04610100110b034002d01c0d00703800524205c20742c4000062031504580301c40e45444401c0040300c40b08540000c049000010880d00007800003c01e16003102524185412144144200c500721040d11268002c1c2d03440590b820800c070f94000c0c1022003a03c0c84d1507a20702010355200400c0c00344001148103110041009c0c640c2c90094072540360803003102c0000741d1030001400014203016207299002212a00e03041e15041c803c02c001c01142225107002c0f95008140500750b00d01c00d154945100206000b045100c0100307000c42082030649084609002445209944142c031a22624024140b001c858080000c24001c000d560140319901441b007100347d0350807880c68901000e40901940c040f0801400101d004566564840355120380070b802c00c01d811004141e48090601c440540c40320000f03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 901513848 1250 901512598 901512607
    0x2030a02070b0708010605161e0308240a050411040302091305071208181903050c1003090b04031202040512011b020d0c02012102030702060103050120030601080615040b 74
    0x40386110b4202e42c8440c0c68a08610294103200008140d4840c111140c81c001107a5600402449080e49140000180ea081c0540e6110781501d80a00b404000310742d80d00704030101e065031000e400d16004858522000060170b101000d400d2401300303c001c043c200499106550148400300043c0c0b915103400b80100c0041c09a5070401c2c40300c0c80c0c040c1c90100b254010b80c0d12070905588034000202e00c603064130b64000080e0421140046902c4c04034008079110000400845a602e07000801d02c40086031115070302e0015900748444000841b01a07007542c0340d0b114000c000d00458400640401d210f40b0078038441c0c440300100507103000c0d61800010551321007024611016503484001089681d01209c42c280200154009419080301101019140c82c2c0440000380c140f06034000385046c018105210314a00740c8941381c3c02c548034148404025500d079030074081198230b98030f848400c0134038012050404406d10680416245159652001151a19006002c50b50014000e03060003150380c00710320103130000c0c202000e051034030b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 901515098 1250 901513848 901513853
    0xc060e010e031206010215010b1602130e0f210d0603150c1803020918030d05070810080a0c090e010906050718230103050603100903020d1d030a14010f02030a0207 71
    0x94a50152881703040d54003130175100c0c100c6080c51000300d044404540f117080d1643c6800c440041010340b4880300951003000340c0d520181001741390384000c07403039a0203004842c0009800d070f440580d110b1a2407007180180020741140241807202400420068484c1a0042a1543e50303590700126000c868080314015500c459009a205600410702d0f42c1440b8140802821240f454011841c0d0140140108044418088850342c442d282041111704a5034040d01c10491490710b170b00002c2809800344e4080f13400c1d40c94140300141a0b0740005010b0300040c3c209042404162a2144032001010100003803801c5540304e00020000c0b039140e10859110340320729200d6401455180d8084e0030030004503041031000a15840310701840020b000380100c28a80d0a0030700141c9034603a0b00000f03140488641c4004010760038640300d0802c041e40030030b0300f0f08103110580b600c1103014a00f500300803400d451100e4043d0180d1045009902041c0300c00001c132615003c040c0000303254030850224800360b0f0300454040501603000940c0d1004c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 901516348 1250 901515098 901515127
    0x305060609090717011a1f08070c080c070e010b031e040c031406060312070807120c0807061e180321021611030604051e1e010e01050a050112030c060e010e03 69
    0x20646c40860700c00c0c0c07017081a8600402d1800c14204500100318000e40000c00c980d00480303801071000d801000e40b50f160314020340c1c0190b45402d18001d01d0741d0301da000c0d000081c1c02c84400341524010540c2d400f8400011201419000a00e007000f0801d0743c0380054403200001080c030504604102d03100e100003511a910300002072514210b4113006501c4c524034104001004507e8810039601c406600003402c42000c1502c00003111942d44150026000290005104080080c294007980054041040044e000703581e0000003c119110041c030748881c000020707001780009224100020011200401031072071480250051001c98204400c4642c594200b0009501402899010201038800840052103203140965981d40c40d666030b202d0040841440c5840c0801d0003009006100000140140819202d10b810718414060003811085032869443c04012940403c4140a524181c41040081c0310444429640480e2544814601aa4440e5030b44044884d502001c2c001e104100b80140000c54481c0c030035140900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 901517598 1250 901516348 901516391
    0x8032203050c010e030c030a0e0d1205070501060e04110f040f0e0c03070b070809090a0e0610030b16051c0b0405090a0201080a050906011a221d01030506060909071701 73
    0x130180c1c01407080c026200400002c442c41c400941c0303401e00c01d280159000c0348002084800040c403400f0000c045400980e40f08024040c018018402072068903a522040000514195030240c2004d2030081d4407101801e005030a642019409000051020000641281141c0c0c640c480503480b03800104216080c0e14041051001030200002564030707080300341c2e031407880e10b114908000d0b000d040f10000240740300300c41e071f80810494141801903810500d000000d029000050740004c45509025201081d03e4590002c0d4a2008120907210541313007068400c46880230840c0340070707001c0e039840c1c83d004d2449403615203000b020f000d41d100200074204c0340300c079100140c0b4403075008000703555492402d4104481d211000445c54111110140c1e14007407040c010780080306030310440d84000102201c0060f500300c0044076520000403609401c42508078514542c43e5890701101c01c0c070000e0801da0001d00412241d1524540d90703501310011f00201e601c003684e07030010215054620049241141d5649000489810120b00c051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 901518848 1250 901517598 901517621
    0x3060102010f05100311010516080d05010902070c050613050307030501020d0b011d0105160b150109060c0203070e09011803020f0c04090803190e03040f03060f14010308032203050c01 80
    0x284242c4c900010300c41803810302e42c4009031004101030241102070f4042c800710303446111801d0002d0540d042c42d0a0000c815804040501c030f26034504400040e40001501c29545060b0b842500342011516003410000960041082081c0c2129400300004032a9410441e8600440c0701b04005a12119550742d01411502c0d50010a81442680720030030500c6c03070700440101e04106090800310b17140c1480c58903903400b00154840c0104a980c640d014031184840d44404800003050903a1000791440d00c0c0c9030704458400510704005d4056102940074049505620402c1c2c1d8046e92440000981c101c00310814942040594001d501580001d541d40c584140c042c01807114040c8261002e0141d120746a4030091107100017042d05090304241030107640304024941124402c003000c001103a03100d98441142c0d4007064a548070403514646006500c0c8254104e50141e000150014800000141c0c42d50b00e618409074030042003103540380e6888001a007201180400e20910ba8081da848a8694158141203030031110b00c0d0590 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 901520098 1250 901518848 901518851
    0x301020c01091101052508070807030804020307050301060b1b0c0a0b0d060801140a0b040b0306070909060e06091308040807030f020429042304032303130b041a0c03060102010f 77
    0x103e250340c0d540c030b9900c8400d10b503001c010040c01200034140b05a5601074048c0080c1404000205ca00500da0f1003854a4000d81c0200c007983e6003d80c0d11410542201c080d4826075514a0040c804d6142c50102003480100b0f44070341d00141c0303c42000020004006044541064840c0310300820022a4440780b4070804000e889610000c02000d8440310403d0784822000f001d4048040e20344810104545550b04040a0400c0280c2140c01c1410101e5015104810500030b60b40d40c585002c00000b80e80744d543c1e440034064030002d048071245880b0505002e0418002c103005465040781048000b0314280100690b100542c01580c4406008c8500d10402041d610051030a02d04c0340012500e40d08d2846401c10404a070700c0c41214000344028034030230410b414840f098000c0e08400490400c00091680042035000540c5821018900030241d420180300580410b440c16140f818000c030311040010040c500150f000f074010702c1500032114801c000c1c00102481200d650504810100034881c055809000c3d403225524410070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 901521348 1250 901520098 901520107
    0x210060b042111100309021003050106030e1c3f1d0c090604140a0e0c030703030f0f0e04050712050c0f03040206090105120a060f0510050a0e030c0301020c0109110105 73
    0x1550350103200e06007803d0344148042180044507902136801485a0b55000d0702c1054921031543c8044c009120034403a00000c68180424091807550228040c080c4d00c6080d17000b0668188200000c0f42d88100040098088460140e20b0b6140c0350010315100b07600d002601d041240c0444455107510a48440c141e281ca4207054800324115002d0b40402d0701c2501020a4034080266611000050003624800682002150000b000c1c4440459070380c00182c04101182c007180c0414003114141a9101201d21000d8001384040c085c102659208144c0038942900ca4505803000c10060000242204c40030303985407020900800454000f04d955005869000c1c038071072a841e04111512050b0b604501c40148024403030707040090b180b00281e014400761030342089401d85190f0b41d4506a1207117002402140a8289206600e0300c00044a18200312100024031040d0358003800c01000c450242c1314050407807920740e814003684141100544091001c2c01c1360740030320303000400d000c41e40e401c20003140e54940c565203040280c00c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 901522598 1250 901521348 901521353
    0x122506020607080405161d090601030803010b0304062a12050112080f040915230f04050405151003030306090b0d03050d02070804090522120f0210060b0421 68
    0x14402e40c4000b40381080f01a90751035141c29030800c0c0b0591a10800c1507050340b03000c100d0782d00503689241864201c804424503520781d0440c1c5603503010b00344402060740380b00304014000e038001d950240d40c100b4410a80801d0360411402c140d00c0c0d242d440351442c51080300b0790443e051101e600503103900040c00760a10170070140d41058810319206240740405404c182c800209215204441c0e02100d0050400b8641082094504103581c490b0f00d0013881203000a0b100c08446002c40f41e03450350050240782000301b03184400840c4000340005800020410f071094014007220034100392500340c0301441224010359900b41d690030341c42d014048030155040a0400b900d40342e01c50300300362900b0700488606501800e01644551001f4031a02c003a1140c0e140041041001040005074004031350043d5000700c0f981d41300c0308030311002030f442003803d41806035001d040300f1a410400388001703002e80c3c2d20b0824005e042c41952a0410f2200c1c201060b5031303a03a400035440540c0040c00f00720380030060070341006072241007a84190020654 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 901523848 1250 901522598 901522603
    0x7081b0703050c010e0610150207120f020301090803090708070b041205100c02161401080103080901020c030f06010f0e040b1f03062f070807060f020912250602 70
    0x84004164029000461005050241c070641d00d50001d060000d00035045083d00302034990100703440c5a084e82c000c0c0781001c644140c0c10410700042d4404d55000780340c0c1c40e150170649005440001e000740c0d01c01035080070303610150310203025200301e00703019135038440d52400d203d506240703421207660004029402442c1d040c0f1280c65002c045404031503914807400c000300801e04205042c02030040c9007508982c80c21511452190f008030304801c46000342c0d030380415012b5441c2c0300501101c001f50b00e0540001c00c030f1401400020321200203000b4508041c0f0403a140701c00f29401280ca0103200340190040c651007170380101b16011070306041c1c40151803448410002e43c285950351401d400009011040140b05c91812080c6180380440010000c540066091142000c0307600c6030803404c52801d021005071862031101088225a80b0107ca000d43e902250262500d0b80c1d039151036006064078071070b078414a41c08104584003a51098400d800c9040c41c13001610010b0003544076625020154403c0d802c2240301c92200300a800d401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 901525098 1250 901523848 901523881
    0xa08011403011413020109080a030801050307090509101e0207151a010c032a030c030e1203160804030204020705030d0b0102011a090411040203090c01080109020424050c0601031a0708 80
    0x10204e100416050510040e1003220898200250384d1041400d032006040c0c2c040c0c0958100c41c8260700f0340e010385442740903c509640c5d0032203070ba204641c403040380100211841c2d440f600c44420182d0f5840c1e58890280811016a404001c069510030070300450f91290110341d11605401c00d903800341070250141c1600018150342c0c1c00d030b54050309003e1000310801c81508a1203510346e600d01d070300610b0018405680b901604076006941c0c00d400281407103440d4515402d01001c550700200d4520011b601380101010a540d00071051002255021001d00c8000010707191350010b130000602c074101030f5403a8841904120200c48021501e41d045a0600403007026604201c070704550045000e90741c09078079641d0303800c200700e41e00407001d50150460320000411550100101e1840c00503c001d070ba81c0c440590341c81c0040c00990046000c1c08211407242e490b0344034080f0040c4090f00c203003e014140281400c0031844294140b060980c0107070b490b84030b14801c4441c000050034855a010f406405d25145904041400b010300900c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 901526348 1250 901525098 901525111
    0xd090302010804110904030503180601030201021e0102161425050d05010b030a1101090506040308030718150201020304120512010603050604090204050108070f060f1e12020a080114030114 82
    0x40e40c800b09040c0107413191200402500034001c061a03050501d0028500e904c101c60307650700c80d0388040700541c807040c001c0341c1c240c12030307405034000d21400040e5025594884188004502559405c220300c0078480701640c0b280e040207003e94042d00c200109002c0700c50030003810f07029110b50740c41c054002d410070840c071201180031ba440945d17540e42c010380b4624000d0300600380380b12490b600d0701c07410100d0410402c03814906145150700b0307079400403030315580d10a01441c2d0040b070000404c5201c00b400061001c80c429424090a0896900c0c4518455074503c58140301000c1c460324800181d400004200501400149400c0c0c0340d0f1852502070b10380b40d0102c40e5661229818081e2004041d00d402c0428121765468004c1585190028002c000950355281d03001c1da50704141c4150b100441d0300c544002038050146040c428000c1840e103070b0106040b4400052900101214151000d00c40d14062030144844184042e20451009844010a0b541000c01d8003644c1506100307018480c0c2e0500030340c040c100c1e0541d04507540042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 901527598 1250 901526348 901526357
    0x4080d0f0504051e1512040609050a0c0b030702010b0a0303210f0e0102030604050a020f0406030c09031203020d0515010207120c1d220b0c1c0c030c110d09030201 71
    0x40030300c10854851041c0d500c52580403040a0b070f01140e1040c90104600c5000c8200c56030411014081080000d901903003100418111910b03001a01207982c6402288985200c2e44c2075451400c00e580d80c80300300980640289000120100c00c01501a4091080b6002c0720822103035402e0071807455130010181e03403201d408804000402e9000307030f900c000e4030b030001040300554490920110082603d124001e4208640780c0303100c0d41c200000719500e20741c284200c4000b03014400c105407400b0700741441503001e440a103042404110701ca0400201040507a0a42c3c0307c24911a9800b507901c0c41c0c0240780c041682e00c00350171460b002c0b6509030741c80201d0782c00146034000c441c00c1d070440170803241407414a40700c03400b215400b0b10012641c603420034040503030b403a403001e1107031644004006050080c800105078001002d200201039000080110f1009410507024010b001800c0300d81000803008544c1d1041620b01d400d00d2030003c2034403000649002c6070009075078146540a04c0c0108014031601000400ca42c410740f20190501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 901528848 1250 901527598 901527617
    0x604202d040501051c06080c03060615120903040302130501030b1f14060712230405090c0702120d030c020c01030915051e0c04031a07140310080a0c0806010b04080d 72
    0x45c22546100030074404810383c00c1004a42c3c4450300c1c2e8a41c0c2031100103034400c1c064140081c0d414605610059005403560711981e080081001c411210403030090080b2072070384410f00c00000140d4038200140c02040e800b000102c2c055146144c4507913409405040c040700c07030a100c811040d42440302140d0300110780748001d8210810849501054651250742009401c44c050b50300d021160342e400c040c1c0d5452440071681d419102180e440c15071010303401180200760703000a081000c03802915030316002d009c080f400202505180c03070b000d14102d403512000014000100c2d480da20b03151041030701802940c1030f05c030084c20203224511240c0e07108116030728100e043d10030441d690f034007080703031041c40c40501c0d1240244880744649a040c00c0f00b101c0401c0d0828481111040080e4905141f08124030148a0049007a61105034010703441120740303002500020f05100b2414800000044c121600b000010f030102d000711401a40305040000850038240140c00c202c001c443e003004200011100000c0014501c18180b8112030a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 901530098 1250 901528848 901528867
    0x11030a0b070806280f0b041401030507050906180108010602030a0206041e080c0106090f060e0610180b03040b1023010c0b0901052514030604202d04050105 68
    0xf08841c110311031104040c0600c04c640c00440c82c596105036101000e120304050b81d607405100551090313004c0c4c21030515041802507402d50280d000141c0000c22410102c2c2009080d0010440580001080d03592001d119900c141595800825407405401d0320710240d40790a041140c0a075803880007078001010b00300301207000c001c4958025080001343c1d0348900380310f0761460208072140c040d05850080d9031301140381c00b2014200a4480c42400101ca11440d040c40c02541c0e03a00070004408124000310041c80211210400d03441070501100c0c1c00307000c502c08130030307140c3c00c040c11310300c100400c020300c000181040c030309007448490003a54803109c04c00304003018500034040d4007004030b600c0e60016500400d015600030902031400e1040d000310f03200f03840c48180380b800001c036803641a4943c0110303000780000c122546148040c160760740300150344c40032002d0030104800001c402d14401104e085040314002580225a44404402202c100e443c1080c09000e40c840242000302e04034014404c03072140314180f280c00a5440c50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 901531348 1250 901530098 901530109
    0xc0412080405030307050d0201060b070b04080c100213060e0402030411130f060f0e070c0c060e0406030b0a0204051e0f130f0515122b05070c060c11030a0b070806 71
    0x1904025044e00c0d1106501e26056680c1c000170300c0d0380001b550a00b18042101c00303400068a100c0c680248044c1c800751201c1d10f54034166071101694070050f0040405403101414240020280f5500c00e16604d0300c0540760940080101d0b03175001c07009100314010018400418910b60310080922011603544900303080d26641d800003004241640ca507030b9401d1000004008100c81010403c070b60b5810f68080c820340c0d0f8000115140000c403030000704034081886c001c0c060380f8401c11090f51a42409040060ba6985a0319030f030080c2c50045070301039055500094284050300704011003807084001141c0707a11a540301840003070040240f0304009401518005818045070295030881d003c441c0c403814040200341403483c003407455000707038154990142d289514035469410002681049590304150700e480a591030464400c0d1240002d509101080801d00c40000031660f6108244001c00c0780d0703140c20301180b1044c87c3c00070000001e40c080302d200e1381140d80d403580071032080e40c44190b10006600d4035000a6031400005031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 901532598 1250 901531348 901531357
    0xc0309041e090804140105122a030f010501110d0c120309060207110316030201020601050607021908030a030c0503092d0d022505180411040f0f0b030102030c041208 72
    0x1070450030501d00605208401c0003c0050714202a0101580d1303132241d00544e01e52040550560b495180c5800160303c280115214209003420200481030094070056a02000d400a44182c0004a120b0004104540c0c01100e01072400d00352130040c100718a02c21602800f140704450016021803494100000f000744294407440d82954270080c1151208128103106100c00c1c048140079000c0d1090400e2402001d2100741c0c00c008803a416402081d10340c0c203020034041076070007585003282c01c04401e450000e0944400c1e8100307030181910900468982c1d6440c60b0007401e69a540140d417040c0b10041041c4611060003161000380050510803002c1c0c0901c0c44040d580c81d421a0f007110110383d015204400c1d064650214403189407800101400d0307041404044a11a1400c03140705407075000700da07401c40003000504d6543c06071380203015119040040c1c5c901c1d400302d000e491024080c0c0d65829583d07107030013080303000921030707181002c100341c00031030445c50510324090441c4205d001c1d00103070908080c00f800401150380c0855 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 901533848 1250 901532598 901532651
    0xe061e031903030c0305061203040b07050a0b13120503010315020c0f011e05090c01170403051201030311010f0606090b070804030507090516110d050306030a0b0403110d050c030904 79
    0xc0e0031a00070b040c018010008024201c000038146404100903141c10607280e180300c0180d201451400386494402ea072181e014000c1103505024405c540303c0460300c0d11280c2881000b8850902000d02c0307075851304101440518070040140310051005002165600558007540e420001005036100c0301440750929103980003a01541075801c007040000360200d00b04d902030864182c00030602807070316401c90b8940c403620341c000c40e540098080104501e46204070074800703820a001e410402d00c1c0a40303088500c1e01c8114260015408950b0000c0b80b0704c1c00c10800d2180b030000001c030078800c00c00b4500f4041c1c01800f020480c0f00311391248001050110038442020f007102e0096600034126140e550f90740c1104806490300701c032a8010301060805002140b4080c125000c00074100e8006010520490b55098600d50400f8150707507014450810a4000184104c020324001c2d07010b500c0d000b03001c143d8580401c0c0b40a0030a0084c0003002818810203200c02800026201e03d040120b401084146006c1e042c800f03c0003114051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 901535098 1250 901533848 901533883
    0xb03090c10180b04180b090f040f080a0c020913020d02060c010618090c12030504050607060906241512050a1e270816050f01020f130e061e03 62
    0x41c240080d4004204680840712208000d508481d1440b00f240e12001b076042d0051507020000e650340000214280d0322902c170b00319078012426562102169034000c011000d000c03441c1220341106500d8050740b82580041c2c0a401421080b20035070100f61440040341c40240140f43c040740c004404242134001002070035a40c81110100300d103007807003840604030400307040c0d514004964000c200075903200050700c07901d0f80584501d4601440d0500740301166114035002e0364032503a140c110400050b018010040e118000c14a100c0c2c01506502200085070315540c824050740008540c03141c5056000900a4480241c40000040c2607403550b82d40005803025200311100032000b0034491014003102e52100c600125100101811040728190b1545100c0b034050000e4000d2009000703441c180c0d070342c6411104042e8440c105842203908a0a0b0a50076a0070140b41030f440303140003192440f040300001003a20014609060720740c0080c20203038089600440d482e07080480e503540c5d0070b20760700442c1c80c100f2801c10307508601d844 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 901536348 1250 901535098 901535147
    0x5242b0c1502030a0503070e0307030204090503091504060c14030d05010f0f21060e160f05040b040203040b04080c0f030d060e070806010522050a1d010b03090c10 71
    0x6004098038041d00500107000c6038404030000d240d02c0001650494046901c2e140d2964580307500c1622110b644040d401d0b030612660350003000584590103500c40040c8034100440d00e980c620020000b10311941d001d04400c2200500007000031a60000c1c043e270031980c220810640210080f80600d05500c6441003542c2c00d14107100002a10244442e040300c02c4816441c0710103041c03503c4400d85451564210840542921240c10b04800300d48264010300b011130f502000c48089901422500503140d03904d521180096440700c500300a9424031340148640341d403003100c08500e0352400da40c0716246040040e00142052401250300400e010341000480c1095078405d04581d1542d884080d000042c040601440c4e03040b0303139032070041130002d4010307460280100016150f032801e2111880034000341528a0324525040340b9034000c0021503407079890b0400094078070b2224140602400a15402c800302e0306a100e106400000c01c100061030b200410b601c4249101192061401e001d100e404403083c1d40000d0940400414601c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 901537598 1250 901536348 901536353
    0x1b0f0306080303101701050906010b0a05121f1d13050a1a04110d050d140f042d061202030601050c06090d1d010c0b0603010204031a040605242b 63
    0x10013002c07a0200d100e0640840244c1c02001c3c242d0b42d007650818259481f1100500c052910700d03000e080404000e14180742040340904000c03242000580307884072440d41c1c41c1900140c88680c0c1c0184000b0700442c0140d0100b05061069004216900800007180021011012410030105012005c5500d4114202001e1072401c4036600c5880c84040d5022290807841042c05c0600741044030303800141d2030700305d00501020342040c01d0030b07108000b5009510004083c02c2164074070310f40c80035020b03001501c145d0755080700c5171040440550001a206041818010140004100c0b03aa8005000e4143d95446800075869446080c0140e5242c0541c40d4001641d004410400440303130303800201364003003c0e400c2d44d56010900a40300040640a0411001070024011020640201d90f4032404190044800f5000529280c0e59484a9450003800c01c0000b0081541a0610040c44168011190840c0100580d142c240ca030440440c0118640f42c00d80d01d01440740380d603d29104010007020155882c0400808805100340761 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 901538848 1250 901537598 901537621
    0x30e030d051816332d0e0f04180b06030f120412030c02041a03060c0405062709090703030f030b0112200d02040e0a0507050304020d052e0f1b0f0306080303 68
    0x301c40c0014100c0c0c40e074011940c0380e03801305624005c14400e80c9402045e0f4100b60240170200a54482e8143c000ba03e4102000d848005143d2801c3c0c0389004a01403401c2d8202001014100380cde540c0c01c10310742d60740614441805064400f04035811160103403080c01c0c000b852480d055070b080c5414103010754405d00c1c114001682c2840307400104a0290110280c0c0c400742e0301c2009440c0c00703025a0103200c1e040002881040c1e001d80c2001c0358051a034041d40d0700000f003030384400002882d03c0421a6103a2280e00700030820420150060070320100d8a90f5800c0c10702c1198442d84c0020881ca14a071074202d6055110414400316481e01024142c405200314200c903690b245601035803029500920070707500d41502c3e640c0050f103810000c0c400d15000d001c160b0344070362039622550200004070b100c0002c00c0d6400c2c003d00340d81d50850f040640e41e00c0c49984007181264001b402d40c000c1c00c021241070090009403e800d1540100a44000b8405291140c40c1824580070220202c0d0049005020540002d11144000418400c045459 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 901540098 1250 901538848 901538867
    0x1b030507030b12031602030f0601060c0219030f2406080102180301140a150b0d0510050f030d0305190f090219120f0201030e030d05181633 61
    0x5944051040d6a0614240082ca0490f00d548030355a810134000c502074110343d844545a0240000c088420720511016021704010b000e0f48001301248a112490086007401007040c0c403c80d1100b0940300c8020f01e59200d0f130a1380302a07880700a01c003924141110080c0c0a039144061107410010350104903a9460340c4484e8000e60040a0b08a403045004800d01541d16050240d4141c00310b10490320500c9403664583c0350f0180c0100520608280c00d200310124030740160502a040960040c200415141410f031000804021203400c1540903416070340c42119107880008615140081e24036000400d5558405020f81d50a02c032569006458100f903913040190032990072010100c2d00031501d880c110f408803586c0f00703a001c0440c85103089000e0200144000b10305a00400300301170f4018180812171209aa0f065400c61b40042000741e034043e5150148242c51010841450021500b04010400100d0903480b882c0c0741c0103944103592000201c601c44801001402c9480d03c01590a4419460f146800d00c03c0580000c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 901541348 1250 901540098 901540111
    0x105012006130506280c03020405090a0f0f1b0c030e030a05011506030509150705091309120305060d0b040c050303030f010e0606090d0f0609150b041515121b0305 71
    0x4102c0171075845204101084014541107804060002c0d03c9601c4070042c0c1030b140d2030601456400e000000301c0c0c4d1100342450b8440d40040340002100b00c480c1d4480400c42c1d8204032403110300703403130813070f010001804003502c103001000c403401c0000d004501d9190454142c200041c0540e0140202c0d840102007240542007044104094000c1c1c08216807282d00072412280c0c100c401030415400900340100301c4a55010a940241084c40c05918000f074400102d42643c071400b5440354655601c020701ca0501010107503403c40340c101d078035042c001c0d17050600c0000c0c81404018006001038141c1d00c0807030300300070444c180300c1d00030700d40078041c0d9480e0b2030700b001d541c1030b4040240725010078401e0700c000107412071078820200d881d50300b00101040d004540a07151044441d00d0b1170800c0312120b5582c0c001d100400d4a407209604141c1c24080c002c40c000411905000507070343e82c004a0000f408064130188801c1104e0590741104c401c0c81d15004400701c02c00c039000c1025003003009411808201003920088004d5050700305ca4130402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 901542598 1250 901541348 901541353
    0x909040b0a0617010e071a16060f0c0e13060e0c0d0618060611030408030a0302030919140d0e130903022b14120723030a050708090604050601050120061305 68
    0x2540c03050f03090145022940c140407c42403c0151078900b4040781c00c1100c44a0050500140b10300070302e40c6075011240c074103112001081d240e0009500b1481c1003021207a607840d0404091100914181c600703500e01074040c03d074900d0040041421000c9154641c043c00040c104034642c1408121349500d030100800c818090900010401e0b100005010400000c0318200c500741c400441ca0710710303c91801c0300203420141200390107009481c07445d43c00d0001d0180003684140209041c0440c0305d40303482090318081c0c8030b460030030a001c0300020200b6196613003028070310468030b828004100e613410f40c41c2c102d042011a09801c420000b602016a0481004641d071003001c10540d1031f0106004540703520f41c4854040c1300000c0104950f0400041c0785c8030b110b483c06c580e500740c94139842d51a000420500b0102034108440c1054195a100c0c10003581035030010701140c10000c02e001804141c11700b03840e060780b01d1a050103414144641c50b89a102c40c034240c0981c24200c8003150f0f06a0f038076418902c03859004000c0b002d10a480c0744c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 901543848 1250 901542598 901542613
    0x2040f1a0f0d0f09081201090c030c0e0d02030718022a060703090c2607120203030a2304060201050f070e0d0213020c010501060203031b0909040b0a0617010e 69
    0x91003400308803907860188a481a0818118882840142184020300f0600c55213940c40c140008200c1c0002c2e001c01100030112410725030400c14841e040b296017003d4441050b003842400c02c061034002c441907100690035681044200f19500100c0e02d040c565034850050600c00c142c02c94418009035001d04120032450600052100c049107070350b800344540c4056070fa0550007080c00f0801d02c0c0e02990242c08103c1c440c11101484c13a1340c48442c0c000b9650b111003e10001454440f001c0c0c400041070280130054250207180500c0700000e6004203540e03000b400000b80c03d0010042c1c1000d0741c1003c4040704808828501800d56590b034650000901a280070385885010311f0502d00800c06a0380540a040c03c0920b02a000112551b0642c08002460040b0700040420765030801c01c460400c20280145400b0340101d0b001140d0300e040c0b24014802003100398022014a0206100410040d904c0441d5590010341040010b0140d0b02d5101240d00280056813000d8103e07180102c0c51000d850040d041164868046810f80c0c110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 901545098 1250 901543848 901543889
    0xc07050a06020d0909140105100c060f1401050a121b08030a09080c3c0901080706110a030f0c060b0301060e011d060d080c0f0d05040906060e030a0809030f0102040f 72
    0xd90762000b9046c66110b1402d001448070303082c2800041214421440d18001070381d159120001210b0006044002e10380d181d22520550003c80c8414500504084d6103850105240518440404110b038900a09601c00d58011030340c000f0b003505100020f40744400640795075040c0304001800781c0c20b591040282034050441170300c0c400e203000066403040c4012a04800c1d60a14010b0b1000c41c1d14003603910564943e082490484100e0b2582c203011806404100010a50503003400030161071980544101110740d44000320050021360710070004500c5021505120b1144a02440c1ca02d0107003d03449005c680541c038105000405090014925048500c200c4c0c2c8005000507400c0d180e411443e0480b60603400c08091014040081c19080003043e0051504099a030510700c841c94071401c0108100c0da103800100081802c2c0840d2400e48185030003441242032007418040b49001007a04d034a003498010b025420007160051841d10184210070540a611008641e01d07902c41421803e604880c0c012100d0107a40c411640c0ca0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 901546348 1250 901545098 901545101
    0xc0306122e0504030c030e18150111060408070b100306021c0c0c08161b0605071109010e070f020f030f0403051209060d111309050f060f150c07050a06020d0909 70
    0x550701580d0703041c0c00084903201a5401ea4401900a4108903101c0a081e48d100840146600a804038070181d07041d590380000040a108201000301d40d0313900194180800500820226120f6541c0700c50000784540d65035001051000c0d440e44040c110038000501031254644d04140340002c4880e01c00b04000c08201c9002c1220044030203c2d00500600041040400c11500c0306003a0501da849580c1c0d180090340452160722030307101958000e0010500100d004001c11103002c404040110096580b5681980741c201850310003034001d400501403040240856440501c00d00524903060810811a0341c1e41c54801c3c40c0010a80c00b80c40141e4850095241e10b00084001e401229050040208854280240c0d078450304c0080c40342250384828250100580c003111000e144c1e0650041682150000301c5103041192061114002040c0c503100303089400c1d800d10241d4440480c1080c02d080c9852054031411045841450003030244c00495100c20b0036100061090b9000848c039044051079520300c0e4070a40d442c880c050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 901547598 1250 901546348 901546351
    0x602030a02070b0309010b1009030c27020a02120c1f1109100e220e0d0f181a03040c06022b03150b1812060c0306122e05 53
    0x3801038110150400c40b0f104103402941e00320f03003100000540c2414003000101e0007810344d03031080041a8140003c00500506490790320003000c603800b0042028101d18402154010030300210602968086140380c006403003040001c4c04041c0f4010701c140c0d600794600d10300f651441c200e982a982501511240c50b2000752170b0044518150510a03c0c17410700310100304000220a410a807071041201e0701c1c000f62070f680d80b94458190890f002a09050500d0300c403000200590b5070000040101e41c0c0031084e1039106a034014070002c4000c180c2c0c50a080391300b001000c005501340d160b501401d01039111018003008021508000c41c0180c0c810301039124103e40d946c40c242c1e01e650400502d006001c410b9501c0e840f62041c1c4400c182c044d56075510300022404401c202606818107281c0061001d5400401d0840446c0507050502c01c030f0b44412502c40d41c20610403040b65648907401803541da080c4cac8010011a0250f242e8440c4a140162080d050781e0b10302c0980c101d40c01da2100760750310950362045825456500c5504c54030805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 901548848 1250 901547598 901547617
    0x181506050d02130b15120117030c07150e150c150f06100507051e01060605090d080d0e0307050a060b0411070f2a03021002010501120f03030b0402071b060203 69
    0x80d81204495075210014080120510740001100c0300340030f150244500280b44840560b9a918440d5051104003d2412308611100300e6507401000004c400d0b8000144241c11941c4000078051164003007201100c0c41c581c600030491300109180b0a0307a21100101c030180102d003c3d49000c49820024580301c04490040c15200a44c090440780c2c003003600d0341400e0f1280400f0a8260820030300c5c0065503611507282801c2a89002c4540320385601404204c0020b0180300001c0c0910301d800303800d003846880058440003040c00010212800043e444549124940004549030140410b41b0f031030708a2400c2594443d2a043c200b241d0152078211084caa13440c0c280b180031b00316a40140c20500344595a07888d0307691080c0c510020780d4200364040d03607203c3e04034103962200c0701520f6450b02151800c0c41c5205108400c0c11030001a419641800c0c010321025030400408451260000201c1d0000c440c2030030107a00604178034081d0743d000381c0006004420300444010b000d82c10501107000341415070b40c0700400c0340c89000c0e04039807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 901550098 1250 901548848 901548859
    0x2090f01030f06020d0908032404060f18090204050c030712090c031203090b130303050c0408120a1112040510030b09060112060509040302071d0903091003181506050d02 74
    0x100100d141a800391160b0004245c2c009000c1c4c1882d02d480c0b0b0301e038104851210500400c0c0c0c4070034885416520140c15588015501400441d007480031a4800b4485c5002c1c2d054040070004584032414403a400000c0040d40140c81009a81420842c6c41c840b684210790041c080b5101c3c403140680c60f203841c4180001039400030010440b45003035942e00c85049003101c02c180100760300d848802e8013041041180e580a50301208000c0d40b42c414a1130098103440c80200401c040d00001e000c00c010100c07001c40d2800b050f8900600040d41c50440d0001582c0042003040c04504038801c420320343c1a2020b552000b08251101103600381c050009110040b41a0f4400c02030182d0881c01c60b40c0810f005501800e42010800d141d15804147c0ea078070b510100d00c030b0240c102c60980c01640302c01020041d010942400d4a03a20400a0b1760040c1807504000c0541e4030311400c41d03100e02a080103403075041010720079440300380846c4e02c0101403641c5000c075081050128000c4554140440d1038090b00184515003460704410b1260b0151070b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 901551348 1250 901550098 901550123
    0x8070219080a0c020f130e0c0906100f051905030a0f2306061b03030601090e010807050d1401050405100c0230120403020d0f170f090319020a02090f0103 67
    0x14112600c0352000f00490304804502003c0c0000d55440c02c0c03101502e450501c00044183d88290b15601e0980745056090140441c3c5084c4440313074a422040c40b20078945414080d07200c61196504483ca0f03c2444034040540c03001c00e100301071155001c4003d50050010300f006001c6051b442c0c0c501c0c000c40b0010001d2100700d0300b140d40c082000403d00020158013070300080c01241400a1019003c0301960080803c0c40f10750070000030080340350b0b04100414050145940c83e85090b6060400c45942c0b2911409491301c2407000103803090820460499104c6451481d40c001d110b1400c0900e0296564204420150400c0d81030a90801c0c01910010340064060310412826030200707400701207090f401011094082c43e400c0204462841e5443c610f1a444c065446a401001c5510351060020420380d0081004001c1141048886100c07a00c402c0308070707070003541c41d101c8011a40c8600407590701e10703c0b41641d00b1158078003010380304a0590f004190580b0040c001d50301c3e601c4070303980c1d03c074610100c40c405d02000b01090003030038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 901552598 1250 901551348 901551367
    0xe040201081e150a05040e072105030f0f1e031b0a1209050703020d0c0e0f060612250c1505010b040e2d060315070e01030b01021006060807021908 64
    0x20f0420990a0240c404103071280ca03000824261103000e101055541d02c1035a04101c0c505105a6070340c000c1c0062040104008030994030541c0b40e11035100744407c29200450a04421000b143c2140c0c800b00364000e280c1e038200c1502c80d0403181c40d001100c80010059000d004006c0f50fa03080c1e0121102c115a9075201c2302d0408440c8440d40040950300b03070507101481142c070040010b86807261117158082c00b68045207205458007a440d00401c5000b003c41080d2401c000510030580c88082c00e8410040c060034001d0044e07513136850700d0b072482106401680d600c1d918030111030340480e40000c4d014154a00891108107080d90b00c91505003070320f40030b100d131042140b001c003c00c00404028401564118043d40380018803810741c801010a980020304a01c81d180d0802002d110310391808010b1004002900384c1c03084020302e8103610152041c074000f400c140c103050310b5001a01c0c281c0e01c01c0c044488e80382290b2108100503070315060020312005040320a5400342c820382031001c00000300066641041c0f58000802d600d000d1521 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 901553848 1250 901552598 901552621
    0x41212020705031e0a0c0602010504261b010207050d032309030301050103090302250612051b0a140c0a06150e190605030f0109051221130b010e040201081e 68
    0x4ea2401c40d107401906200d60004400000c0000100a103a00105182c01c1030300300144075005115500c0580e1401440607a02070403440d040d15035080e040e00c10120140490030440340a031054480040c454065424425646905079111454070380c081400d501c00308400306504000c0c200190b410504903403003400100204e43c400d8101e410960302c0303403060320705500801c40d0b00b0b41c0d40090710305080e0714030300c0c0e801c014030400750300101d02161a01c50070000c4c4050308226113582603d510360303a80a805000c00185105105006944148100b0550a062030b511003040003615150828504125401801c0c1000d1811140d4614100d00c180c07507001110072004d458080c8449462500449a000032940352600010640d4040c0448004000c0e401d002240e800130a01e4490300707000d0360017211010700b42d06001020203601000140d0110905803034040d1915102c0c400d00c551039003080c0d034000301052441000481c01615202c1c0d41401a4801e0b2100d005a0700c551440d0f642281c100004424a082e5050001d112180807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 901555098 1250 901553848 901553893
    0x11040308090a080a0b090607030b0d0210110a03080109060605070201120e0c0603010b07110613061d120f06011215094b020303030606030c040b04121202070503 70
    0x104032000d0a591a01d001e4103204c200031055803d072101d4000c01403c000c050040c03039445101846e0401c0451001c000190300300301c0500c000780c000c1181d4400481c0c061b00640095540e1603101045501e21040351800601c1c00c40d0900400c00e80600b411400511180200280c4d0b200c5a4161200725100c107102440c103004000c1906001070034400c0c803141c071110341ca510000354060f000318a0940d950b4401801d0045045504000080c083c400800c2500b0985a1000100f419200e00386001030900c500f00c10f41d80400000a40000d0340441104c000900d00000000c4810760070750031400f52000c6a80e00c1c0c6c42080c40c0b40f0301c0322002e006207800e11400300d12900c1ca5480103402a110300204c002242c110b0824486080113004812540c0103550380d18009000c100e0740150748003003c881d041c8045407a030750229499000c06481240603c074088081a03040000809990252039180a0341d9101c44d620b4808400a610454064940165400c10605060700c0070403020240c400240042035121001c0e10141810b411 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 901556348 1250 901555098 901555117
    0x50313080a0e010e100206061225030308101a0703110609060108073c08030a0e151303170f0403120801061e0f090b1903050a11040308 59
    0x1100044100260a540c090404000c05a40361001d41d070a0303600260a00300640002c83c8544104241c88420503030004004d0f0303000030251f800c561500d0340c1d000090302e0704c045060904040082000c0858070b4140d80d607a40d000702c2c1d0199941549039201c10302d41d0700b00d009443c002c82045082c50341c418540034100308002d1100500ca45810b620785140d240c25281000c0d426a074058003030b080704004004e035050420552010700f217520010910645221130220109038000851740c034a00d42940d440f9107283d4900070003030081203010140c03a035810840a000b00702d18011a0700c1c0c0d1140c0c0001140801c00340303601054170303410b01b0310f0921010401e007180c843d480b01001420b00e00203c00f0003001003143c00b2054074042d000561060500f080d18120020001c0c0042405811082c200200180f04c100c001c071840003c42d9283d0000d08011000e500700d00300807601d000560700902002d841c00900c069440c4da54240544000342c0d136550802041d161094144141d40c1603041450b440d00f010b000600116a448000300780056 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 901557598 1250 901556348 901556371
    0x140405040221040b09063612040e01060207060c03022e02070b0405010605060a09030b06010210050916090b0a050105210f070f020a02011b02150d1a030d050a0503 71
    0x102c01c0d00c0303050200c1c0c01150110381d490840030603c03c081c01e04105040c1c011540c40900081a8038680765420210b01040343e090b80c0d0782d00d00480500080052010001d071440a60540e81e550351a4100300319a02e100b032007002c0042c1314040340010107a11842800d0719140c2e0640c09051014070340f5040c480320743d21354000240311060003515142009090b2004190840c4603005034034039440c3c01d0400d41d003190884e52040d0700900301041001001980000c025054a0f40200000d450382c44c0c2c100100d190551455400980c0c2e0f190500340144c9810026094903400e020710326440141d43c4071811442a60f110542c0c680d00304e0703c000e00030700541d801440a01029415411200c503800c481c01c0000c0c0c070280341540c0340316111a8180612801d80c0d4019202c01458505000a1841c0c050360742c0000d204140600c2c0d89000c07076604541000440d0b80e203042c50000c18a0114685894400307451200005000400038605100750204045015003030201c0d80c1425403095448807030601c040346c201035400d580018821100007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 901558848 1250 901557598 901557637
    0x4060605030607031d0d232106040507020d1e051e091503011a0307032306030c09010b0901080619030609021c11150706180209071404050402 62
    0x7501d0400580d8840c044940c0c020900c41001903442100150b0803030740403599006400d101c0641500409842c00394181c0c400d00310b112038841d0800c11803d004800e5011046890320081c0300414100e03c21060041d24115000c120701d4540c01001d980d01e0801444810104a02129601300c03046a40306140c000301d0241481440c04800c4000c003066944000c14088003090b010031a10080d08006207046451200300750314920310350414040003080920845064a401000000a500248240c02c00d80c85001c181100d224041080500c17214000e10482c0c61600a1160740307803c03681458081203c0d812240e40d10860303460300340c500300110f96205000380300c584c1000410007501318210304062140700035406100005a07215441c81000030204a54140e1220010307080c1ca48800710340340c100d510f02100000c69510305280a078140b6041940180900548454900310140ba00e1641c5009a200c0a900c21910611550b940100690305508152640c0a42c02c400313000600c050f0500b03500074090390080030b0301c2202c2c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 901560098 1250 901558848 901558859
    0xb0f03100219050711090a0f18050105090c130507140408011b0306061b0212030d0e06060103021611030a0602031f0504060b0d02220305030a02100c0512040606 70
    0x10503040d6950340c8a1035900089038000d99112a52180054240f80340c4245071404945030090000e5401861034030170104800429040c4021b1340c00480b41c0b030b8512000340138010422016249140310038100f91019401e10000a0803000d0209680d8601d0400400060148240758440c00c0100002400300c0305200764145421585000200507100405c504000421104505c945540c1d4020b9901c0840c0241410300c1e4003844080d03086680300b480c111070144c88a0981e540c40c00012121201e00d540201c0a000c00550b61180c4080c90700102c80f5581408111030345070711031000440881c070503000d41c904a95664040880014106084007c1e40384c00102101c0e401000c0303880311012039009031040800d8004160720020ba8643d40711444006000841d0300b04411480c003e44a10b4510900c03d00b4034025500040290007035070784081c4554540d074400c0490f0f02c00780d12458034a540e0b07444040032001500c0780d840c070b1303a540700c81c0b0b8058840c0ca2802035070382604202c141000c442c0c0c6003001901c21140c494031100d01184 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 901561348 1250 901560098 901560103
    0x21605010e07140d080d20040b04030209010506181005071a0402090a0c0905040f090807052503080a050d020c0a0b070323060607020a08010c030515010e130b0f03 71
    0x5001484041c0c1111031400b49203007108407100400f94010507a0b11003440120741c4202c207881101070340810109809400c1381201141c50311031141c8101600000c9000b1440318440310141054a00c29a00140303a641c94404108a80c020504080d50701c0206104403002e5007041c18007a0300000c0282082401c141765980c4050303491003101c0590007450040c008000940c6000d400040c0c00174900e1204002840d1080801480c3c01d030303a8010103028030b49504002c0e100b021550f00040c51950000d00306503c2d90150301e419522821441810007030f441c04804200c42200340b5000010491303611882043c98020390490942d61500200c002003e020707030034005c88140c4a014001303c0a00c07842713881c0842c006c1c50884c0d800340880c3c062440c49080c603445642c80301c1000603480501c0b90803241c1160503540303400003440000c06420301500081c09650030320312041400340e0981c000340d01a4810f4840c40c02c3d9a58900011034040e06400c034a2688116500b000f010040d01a500c400601d40000c4c1c20388204201c3d4070046071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 901562598 1250 901561348 901561361
    0xc03112b0504081207030b031b360702030a08011a16032106080c09090120090f0117070e0301020c15040b01050a0f03080f04150c05101e02160501 64
    0x1c0343e415002950380075811080700030941c406a43d0500b0000216442e01103239403030305403010902d00ca80d040840c0030410740d140c0309100170405880d000401c07800d8400122010380000000480d190030310b10701c08a540f460001c000e03560010416a29006140c0c6091381003010000783c404081c0700828100800385002d800c0e641c48003907041c040c1c0c842d01c00b0b00c05090b080502d4001001e440440840c603201c1c0034003072540e02142e00d8414120444589440f40c5880345a5401402a0400030f01c91410803540301030030006041c054002007408541300c01e40c0302e40c030b00015500342070000010ba0958140000045245000f40078211f450180500014182754101a14074501603446d01a01b0076500b0f000c0411040100c0000c013203000d0101a5500721000d460003000500d44281c60000818081000c110860640250300a84e4010030020200300e80c8207a0244020f40f51a041c48002d841d1800784620031090007189000d200340300c00420102c100d0070f04000c0c0e00c04009400ca070004950662094001c07030007044090040700b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 901563848 1250 901562598 901562603
    0x8030a061203050a1728111911070f0501051c05010609090b0301020c0d0c03021626060118020714070e010e0f190902010e0916030c03112b0504 63
    0x12595420300b542e01801c1700b03824600412190b11400d0410000300b16a44241c17134808507900d4524140c0c0c040800301800340a0b02070201020f40030200f00340c121113044190101d9007041a881d4000c0e6624050501a100c0031140580004800762400405c000c0d44583e00030882d40b40c1200741d401030100c00c0c081c0315040e54001c5c6d203d80005a0111002d2200d03c0a903c558440700b8812002145040e0000c0d41580d01c400c40e00c0711000c14031004400d140f05050092100328900a0a1040760030344603103071607090f031401e00c038002900c10307480c11380180480e101e100280c8141a1a0408100310310b466020224001a40c070a80c800c450451141090702090041040f001001d000503122452540d8189481100114070081046012200c1b403c00d0001c0e00c805840c0000c6004159100400c5600c0c15000507100005440740054001728503108204080381d010401c10141c041c2c658080c404d5404210f012015a040310f1b445018611080080200d50a41000300740f08101500c5507009a01031008183c0c0c08031003003160107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 901565098 1250 901563848 901563857
    0x806040317060d021915090e04030c031704030504030b060303030403020a11030304030804150f02070f14040e06091e210a020f030a112a09251205010b1608030a061203 73
    0x5003c041d00318001d040b05031a8525007c100da52a020a800c0b0003c1e004d00f010707041c00081401e80c01890320504d00c107000c0314016060740415007414900108140e005120035104101c800307001c1401440c01004a0740910340541c01408200642c2d1100c0135040b03422220075034944002c11000000400d84400350000707060190b4260002e403035007040503010311480c0b0030307010440d00300c01e03c1401500340d885820070503200da4071501307802d0669210100b03000b8020005001c1c054460602004088400081c0011b4403200c40032503ccd05440030360300419030b41c0503042510560224030300c895018001b4050040c11841500e031040712545903d000941d41035500c481a03402c001018004268980403080100211502d0f00c080200c10034032501901c00c00480341c009842d4890f8010402003210101c0c0c0d101c4104d85000424034600701010b410001a003c4405916400a00c5043c8400040e00e4141d617804d9401029902e540403a8030b1903256210750580e03000400006400d6910303c004224400c000031489402c40c0b294a6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 901566348 1250 901565098 901565149
    0x10302270a060309080f090102031e180a0807030305130e16030507181202030a1b140301090f35033301030207020d17040f0806040317060d02 62
    0x24810102074581049042c541803540020001d9616030440300c15600d101d1206859140000c0100d08501c1481d90082180e0f4441072611801c54031000240803400044841255141e07011007802055506c03407045401ca41c04c10501000441d02840007020004410340c008954540c9500c54125000c0d030580b0500d20352034101c0b80640c00140c02d4442d29800c9901030801c0c0d1a5040e00e0708100608405034065005280a0b142042c0304548040191045203139000362041a8005101c20311450300031140b244070f280300449104071040d403c061013900070903604a2000090074585403269103031070b014400724a80c40704a218440b40542c861950061022520f400502d943c2d040403540541007184030210500b030342c8400603041110218486807100500030a00f400350715a030050002585220448038040c001c60040031025400082c0c1100030015107498814000c0d401c0d80b6005516943d0a044030001c0100e8540400c10301e180790803041c0b4552209004001010300846c560200350302204184609c2c20303a4440c1c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 901567598 1250 901566348 901566427
    0x2130e01050102190f0201120e070603020a09090608060f060607080c010b0a270c03021b0a060c02030f09130204050415231f09050a0f0819020906010806010302 70
    0x40b40380f54440d024408158090100d1715088041c84203d50020306208500042074a0b8009a80191072510344034020303165003591700d210140203035001883d11000944400008074900d6064800c15050320070710300090045a40c1d50054003a030003030180400d44c1c8050103104d8440003c0e035040040458030b00400020403e44c03114410f00c481281f882e004001108544100200140c0312804517115008000402080107110400168009d100712051400c0150500d0b00c510503080c03000600300302c80d600c181001c018244019400320b071680902d00c2003000408040180403220300e8a10502030116256060040c60260380c1e400150854104801844401c100804201b00034010722080c601d00784d080b090b1628500d041c96000507801c504190b1460205c1490304039002501d84500d80c0d0384081c040280510032040d40383c1d1a28645c0640038800c05e2414441c03528a0b4040c41c40a80c4080e4525902a15111071921034000540d1580c0004010354105a82884030410103884d20951030011002c2c411260240341904 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 901568848 1250 901567598 901567603
    0xe0d050a051f1103151e031518070e1b090a03030c14030a0c02041a0604060207090b2409150d09051e0616020f031c1a090a020d02130e01050102 63
    0x2601c40b010880d050040024800c00c03a005070f0544070045410201c004017400e6503c0c001458101b80340c0d054850071100185c07081031242a0b038006d0011626081e660300d81080b10558511807401865600c40581c0f0100305a507400800d5005403011350b461076400c0a001401180710304210394826400544510030120601c032002c00c4440301c015602014500c3e20b0300c0035001405158a1440003405a5034a049a60b006002184081ea04c0c01c03005100e0342d40d607903440000a5032202c00380a04405580b600c1104419454007014120641100301c03141192000692692025508040c41a0750420314158400c1d40c42e058200c01410002c0d262880010b184505041c910324180e00144950460200501556101440000c5140c1d12407007071a100421a984000c080741000226041c400640c400402c0810701c1c0301045802603c014060841002003510186244581e801080c0700d50350800000c0e000b00340006250b400410b40c0f140c410354050304d003804a1041c01240204c0c0c5c0d000b441000705030801400b0541e8107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 901570098 1250 901568848 901568861
    0x1214101706060306060114040e07020307020307060e0d021e090a0219050913020f0c03070b06150726041e03030201050f04051b1c05060907150e0d050a051f 68
    0x4100c010040c40c41d0507404039596103000f0380f040c4d0512141c0c100700e41240500c80110703401340198500e800304904048801a50360742140100728070a02401c0d2010a0243c8122038003c4648c40081c00318075240310a80034030040c0170781c01c0b0348500031400e00c04240c03585448105a04e40640c03840c110060381c1741d564028101545007003642075010810f0411014980703a5600d4600030304664103010051b9140200c2c0816502c07407042c0019901c1c1d5000200c0c484007130040c06c0003114420102500d100341d10000202900d42c50b403294110043c40070204209008009400d52002e80c2460210b94100d0302c0d082e00c88458000c104d050403403064a0841e0324000780200b660a00820760010b144403044d0100741440d583d01c6403070742082030007182c08620580700050b485d0303140b88040645400700680a440e98590382041d603100c0c20200c1d1040c446200e10640051040070321200900f800c030322950b03050300350007021003000b160104a40d02900d0703501c100850711000c15002d10621100c0320365800f035201031500811654081d1100c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 901571348 1250 901570098 901570139
    0x5070204051e0c0405030601032a060503010e131e03090807030609140102071511040b07080c0d0e21030f0c0f0705040603030819062106240501121410 66
    0x1404e000800080d100080e04c00d0641e80e20800407c0300d050906140c6900f9491429003960300285258000f886640181c0218140c030803400c030b148102d40e01c07200c0e0340380307170034200500181036212981d413020398482d0390010150064400d18080c9c00c41650303000100c1c50002150400c0e58859902c511480801900003101a00e5403907030802541441c180c0d0329410f420034260302c09070b4107040e02c07806240ea603070030b01c40100c1340a4402805c2e407540f2a078a80c01c100e080740e0008950040c0c82e01c00d1071407862145024460100c09208020800c000e1401540391660f080c3c030200048800f603102c1808082404840d40001c2d04d089180d6034000d1205ca284403d9142c98a20301c2c3d80854007441c9413031024000301c2d50101900c2c0d88092050320550043c0b101950440040045910019240700750a001100014581e40d800c281c1380c3c021542808001c04000009612000039011042035000d8503904101c254010005544030803d82480001c2c0c91440e40c61900000d07404071410605514090024401406610780790844840c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 901572598 1250 901571348 901571371
    0x5090607080408030411150406031808030a02070c051003231b09121209010e0909070e220b1006030c081810060f05090105101205060105070204051e 65
    0x9091602915030080904054043e400020000301440000c903209201108007a0040f071402c5a81039148140c4c0e0014060440028140b400d6580d426119640101040360014410342c0b464450140000c001d43c800c5034120340074149000c000031541d0381c00e5010083d00304551000700d00340c20074502c10f080c560759480f001e403191f451140c107005e0301c0c080c0f04118202c08c40000c0d001c140d55080700800207694400d4020003600903c80ca0542a02d061001000b4003181c2c10203881e0031801420000411000d100c08580c008207603884514200096020820820b8002d47d81502c1c0380031807424801042440070142c001610500a610144074448007100c00d6400286100e20303040016001c03000006000e0340c4007806817020f580d02c603446c481c0400414061005a40141c0c5410000c066444034040b010aa0a21503c0c0c800c60f41c0100002d1a0304003005070350000711555440d54510340c44003034204000c0c0b002404040c10004240f00c1c039001138555100300c60060603070108600c948404880c0038a20700700d00800b2581c021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 901573848 1250 901572598 901572601
    0x40e060307150c021f0f080705070510092a080d081501030c021002041701061a0a030203041b1d0718050d150510080c06030403120222090b04050906 65
    0xc1c42e266601a03600161078044000411400011103a04ca030844031543c0d4190100300a8090307411400030b01518816443c1c008007640c1d03210064481d0300880c0005030654000070407100f501d00041c0c1c002d61450303101e44201e6801c102902c03e9280a03d40c1e04039481c254201440041c444c80c1c4040007004120251854801d55600d0224903030a03c4020f4001d0541c14541c50300864606140207022035512240301920840d1101c1d81c4403000d9290301000550000294a4844042520311084141040020f00b0768a13a03440d1010b440800c400035407004005490003d80c06081b925030181a540c40b03c0140201152007036000c0d440300c3c45406281c4050a80c0341030102d000b0350307000010b032070700d02c00401c9031404c4450050b0201682820202e11500c1d20014200900d00b0041040340e90010104070142d9030004100c0712903000200521015220a540182c082074000c0015400f0400c581c0050580721042043d06000c0d03019104811443e84680d00a01e450070b4840203003140d43d080522855611119120051105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 901575098 1250 901573848 901573859
    0x3063501051e0a1808180303030c0702090f0601050a0f110d11011406100509041d010c11010915020f09040603150b06070b060136030b07030c0e040b0d17040e060307 72
    0x70001d130210010502c880128142114510241e00003442e041c020307040d21f51760b01c1d141202814503030001c1c0d0100c0c403c81e0782d01e001c19241d0010121651103007806850700c41c900b1425410039208aa400c000c4401000160400d44c1c581a034240948541a4030302c0e01d072904c1000f9507507000c41c00d40300c0c000000c031150b84e8142d0801105540d00305a070401c001031030900c03540d07a641100c00b10b0041d04418a1500e0280e4526141410b500415801059020750035600e500141420000003800d0300c0454902802c000d038580d5082101ea9030310b174018030400e00c00024181c41d0910030070200701503074543d07407041d141c2000140d0003141072221402100b0b546801103841c1480c01c12544d9070002e0580c0040c0c0304a04001003041c2c08e041c0002c0701c03595a40307000796003003207900b0601600b8200358010990717000440c0e01c40c02000220300024002d0041c800120910b8540400782e0383c4682c140801000c0320700d41180d020780500001c030089078258144001d45081d43d00100c1d9100e08024483c403c00c80e010304414004d0740a41c208100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 901576348 1250 901575098 901575131
    0x206070207060f03110c070501090519090c1106091b040915020702040603080f09190e1f090e01060510020a0507060809100c110c0103063501051e0a 65
    0x2601d00310f05000f01214140342c8200d005051410081c060316000098010032404005446411285e00344d860084c4079840b40140450b0b10080e0100071400c40280303034140314154450300304504001452400c04d50610078080002d24100d4240e40c10b440e42c2d0014881c00298854400013043c0001050b00e01780303d50360459032a164100f401c6007802e1031003640420b652086540f19041400116008ac51258070f80403800d500d2030455000f90b607100d1180c052250704800c4522400360801c1111410043d800035503480a40c40d0246000481100c0c420a03103044010610b070107a0b10800c0705285402c000040d801e42001e060100d44c0740b1080e03402007503603c44480c2d0381c00901d0008901050303400c140381010306522a01c4805191844d00100000f0060810a62031500c55000c120a2108030850b4202c4402e206090015000c80e002809200c20a60305003003141b0300d403252041840440b80080f2515805003d0b255001800c41d074040d00c01c48414003da41d05058070683c010506034005150346010041c000d0350285480 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 901577598 1250 901576348 901576363
    0x51918060e15031f031b050a0e0a0c0c0b07091706090319030b0904060c0e0a0e1803070204090305040e0f090307110d0b0a0509010e03030c0906220914010602060702 72
    0x4504000000164070002c2c6858541c1d004001c07441e180c0304c0f090b200c1c41c1109110145109046000301c01100009481c82c00f61a50b0046a99490200c140740d02e0342c04075034002d440800d11100c24082c1d030f00102c4000800d1841e41500c101115900c0d81e425a0602115128036015034814404aa00500c1845501603000c0200c0e6218100304e02c0c00462081c0c203200c15805000e030404c0650788040304500700030501c0740e290080701c521102171344c40f4411819a01c0c00c224026100e4003810300286040000030303202400e1000e041241045440407a03082036004d138005001c0c5c2da06440110002031010404104031780b031242140d908000c0001c1100007505d418003046980707002e4003802900601d28082c5441b400d4440a00d65105180c0200c2c40c5040c1e4034004000001819080d649414690b180090f6455458008419280501603030002c2605e0810240700f0882190046c4141c000030401c1c007a0031300102c0c0f8071409110014100c2d4840410382102048001002ca18168851400d5401090401001d607a0109107503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 901578848 1250 901577598 901577629
    0x5120115141c050102092b020114120a060302040506010c1a06040905100b011206030b0f0a0605120a0b010f0506030a090804120f02120307030801090c051918060e 71
    0x54800e0350107000140304000102d408040d00c0c0c0e030844035a82800070640080403401070650304c03000b01c4081d210b041422154582c5001100080c0e071407105005620403096150306c1d001004d0344a0a00d03014414450190100f0740f000c1c8032080e0784150420440c03c0c1030042c117038410030034284a644402a0380b11104041d0b512004640b001e03100034001102591560302080440b60060212034070311400081f1a0001d24040d24007134007080003174510110748400350180c0c1c0e040c0c0742e000311600159110300c50318240302c1c5030140800b5415074460070017103840c0d1201c84a04006c0ea02c118024000d00d543c40c00c1c800d141440c180c0201182c0c0005680500250b00d48808807a00f11401000000d5120011f080501060040380c0150301c1c44e401000005043c444050b01d01c18146000b04c51040c680490f4204060b03591058a00042c0400e012800411850080358003064181e03885041c0705141444240d0490394441641c07050038040bd00b000e4410501c0c07151249007170054112407c100340d00c08555000540300f081c80841a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 901580098 1250 901578848 901578869
    0xb0a1703071101021005162712060e0105040506010303090b07020f090402120d090905150d140f0115030b060907120209010e1309140a0c090905240105120115 69
    0xc0318903c1e4800c0008240101c0d41803c104254109010501d040384140031582c0001408400303040346002904022031524100344c10903030b4003585484140d0700036101351340041d9581039a5100c1251249404c0c0074051040e803103070003d000a98154980a80004020b812400c0001011f00c0348070b00507140d2882c810903008044494217181da0313031840000e501e0703101003800303c0250156802c010941074028200e0401c0d40d01d0100140301990342c180040031810412040203902c0160b4200c0b82c400306e41c900b642d84140c442c1c0c0710184d81e0212205203034182503901c081c0c0b00660403010f0000130428000300380940c58220340101c403071409509125100610703038010090100b00c42c40d40041c0103040b680c020b00d28076100402c0030300010740060b02c80e40d0000041000c1c4500345d84044400c40b0301044150085030441000d503001c98034080c4103043c501c0000003400384079001c0311148034801103109940d45c00361282901107840f0a284060350b0420052207101c05042040f49060707810b103000390a0200c030001105055880d1044c0c1c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 901581348 1250 901580098 901580123
    0x26270a05091815090d02010e0d050c0a0804080606010e06070f02120109051e010606021f270507090b010c0f0204090501060b0f1201050f030d0e12030c010b0a170307 72
    0x701e1004001c80742d00c071140c20f441003010718006031038000780c03062244000c1019992003110044007a400e980c01d400065038a0b400100345c0c41340315400707140078046109140c0708a8440600b955643d040c2c540c400c0d0001d0007945e00680030083d443d80d0041185c0303a003140c01d50f062406c000c2240e0b1118101d8122040c000e02c1508050b82e0410740c0315095006059030f981200840e06020314030120403000c4034507502d40049a50030041d02003583e03400052501d0200c12800c28100000408104041c0104075106c40c0301d1024040c048401c0c10b252065989401450041010703140ca07510b40b03086030045603d000d00e600c0c103000c0340f070040c0c1d000310380304102c04620250140c501080101042c9040b5005183c00e80004260345c0004c1414646005403601400c8442d0752040d45d580c0d9a40c0700c80411002c01c11207203070194103a10000c0010502403140342c440c400f40c840900307103099004072800190300359002806400b1513a03541e00300d2b901041c42e00b415107000405001c0700c0914800c45070781041e901c27407103608405004003c2828 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 901582598 1250 901581348 901581361
    0x30606051e0f04090f060b0c0312130c030809030d3b04241202130b0d150e01061509060f0e09010b210f1326270a0509 52
    0x1070407549811070582c1d820f55119111440b040c000d08018a959410900d01000450030380607203002c4030802c99860f8011820401c2c01c030105100c944000300410610701290b0128800116810740b503002941c4100c840545605890b003c0c07520340007008450000b08074024003004c500903e446105003c2141035080e48200701c1030360280366100990100e485130080e00d00380c051402804040801000c164881144e86191555035044001001440b04040d601880212500102d0580b0b07500048210307402034000d407021803141e1207980c410f04200c041c0c1070000b074880e0f03486440c404d82032081c0405402e185205803032107001c820006000c1700b40d9005000a0000008040d90b020740244004502c03000001c06105080d03844d03070742958280d0401d0512628204041ca540c2241e00c1d05084210300c2030400ca02d010601d683c981050907a028884200ae80342c51349400000440b181c9034002880100e1480c141c0b41e9a552116000042001400441d140b141c0c0180550340725180d442540c2d4500b140c000300c484012580300c80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 901583848 1250 901582598 901582657
    0x3010507080f010b1b032803271b090b010912050a020d0c080a0c090c0804020114090d020603160206010503121909090903110111070506010b07210306051003060605 72
    0x19a225045c07448086040e4074100520414007401c400d50314030746848030f407a80009500359040c1c4850001450750141d03691208682100c2010035460180d43da10a09803503140a00c40000b8907a0401c400c1e642c0c456240920315600020402d0003004200c04103a40c10a16846071030729803120200007449010b43d00c1424040c07001000c0101d004e0110f000035681d120f5003629100c0f4002400b84190803625007014091440d5500950700c00f27104039010b0b1200907406510001c60382d00d036800006000d50101c0c4004910300980c80741c0703000e507108204191840d030100c01d00c01c44c06494043d0581c00740e44294010300c404440e484004050b00d40001e1070111102c0c50180381402030780c04d1a40768215054a42ca0315180c00241a4131505012280c2c000070020403101122801c1e020035403050035006041e035404100108004c4a02000400c0c0c035130f00034481480e0003000c20a1401d182e0348d4001c10640040c2d00c40909100519144d1050b138100102414204451850700a026260340544143e4541c0344005c1c240408055594 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 901585098 1250 901583848 901583887
    0x90201091a04180614010f093b010308071104060b12070305090606031b04090c0803030f0112030e1207170d0905310f0f060503010507080f010b 63
    0x1c01c0d04031800304205000c000c201d41c01a200e490048110581e40e50150401c5105000c25211301050590013880b200006455440c1046070500c10401070a070000343d103421180c01c60f0080c0d001c04083c0020b200403e8280100344c080d0300068420303881c6100040002904910482da840c03a8040107402070501c1e20400035000b40965480841d260303a00040300e050304003018800718401c08203606d0821243d2140e05866580780811141590140e20510850840710300c40f4084100032078000f40080780101045d51050700000f16644901816800030050100340714400380744501500341d40ea0b000000b003505032801851641140d011034000c4c041e148602480aa081c0861740180608443c91020fa01450098640d120060400003000910b0040042124036000100700d24084030846079100c6c2003440c2e0703428940c1e8540075014461059a413440c08226030260b0040c3c030540c441e1035a0001347c95240400f070609444004000d0407c0051140411180b402c03440d1041e030544071131700034180c2c480d4030f5810500e090144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 901586348 1250 901585098 901585109
    0x207170c010c0c08060a0203091b2d060f0408060c07150e031207050405010e120304140d060608061006110a031b0b010801060501020d020a0b0c09040f0c020d0306140d020409020109 79
    0xa0401b0409860350940085010303066000c00c907007031240624840b029080c0003540d0f00c4d51080f5001014007210424001d441854100c1500d003d152084803400920583d001d5032a01d46460380105007001001c009010180d031000b800c428a42c60300e2459640d00701c0350040344408121841d42d6015914280102708259024482c05001300d12581c18034641c040c095411078402c040c00940303011103411071801c0c00c02440e108480414015404c00d410442c1814212400c40000c03070f00b168540c03160401244103402180c0003061f802001c0c1070b8034140516001c0d11290182c00250900210441d9030b001804000340d48562a505032400c100556420602c0040040d04240301900c4941c1580001c1000c031419440382080752426001c03641140b099a0007640c0303031140c0da2030280a645800c000920001503000c01071184200c004d000103080c400791a6108211003001c00d041005a0150036680a42c41d0184070380000b40007004420b4080c6215103000641d1070300e4204009010719280c1c1030180459000300040b90203090b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 901587598 1250 901586348 901586353
    0x9030403120e0d110405060303120f090f10060e07080603030a0804030203090a0e0901050f090a030e01021e0606010905120d0302091f0f0311120601050912011b0207170c010c0c08 78
    0x12800e0600c1280c250881c06135611440c0303007a01183d407904c0c000003100d00c0300300801000611580ca0991050108100421101141c000d00c0c680b640484428010411560071313001700090024206006800940c0380149540107104101041c00b5013035400005032030b05001c0520301041682c4c1c03903140803411b40c0a04051030342c0041110202040c4581e10400051040328031400800181e0340c1c615001c00340210541d481c000c250003d10b065001b05c4d00c680c84491290a060040705d40c0c0d02d41c09517000d40c214402c0032040100d0303009071040c8201076920011600080c1421103040f062496000800740e1100e0620000c00141035001031500400c0d15204801202c40385d0082e240000c00741600e01c09008d845444d41c8803c00a4034109048070301c12082000e888071300c1c01d84458000c03142d5800006449030b5021410155000c1e5040f12601c005030030034010112010000c024404000d00c101c00d02a150201d541c0203000c040e2509260014031450009110290080034a00a0314100042c107000d4203c03c0706400c40c68090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 901588848 1250 901587598 901587619
    0x20106140607060e030a0c02180705120a0e0d030e19020a06050a030908070804030302150f060108070201090b041110021f023403081f090507020102040e10061709030403120e 76
    0x2d50000044104e4500a9036549d4170700c00105c111001c806401c54111001c01c0041c40940c107104c0055205551143c2c4100c000a0351758101000c0d41d06c4c110141d13015000080d194030781c0c0b5400000500011000c0c04050a084803143c00075030000303244526900850040107008140c808215109400c80c0786010740095405650390014101040194800e00007078004d4421101086040d180c14072807140300d00321000c2000f5058550b000112580c5202610102c1150740f1160184003003130f04000043c1c012031003520b011400c160f0348014401240d98042c0780c003080d03402480c001204c9000200071250088001c02006a440c00040301d0034011044800c02080d451280c20105008441300392140040705001e40c4030260641c0e20030051304040c822240d40c031062545503030700c01c0140014540203c0d070041c640340000340c1030645410b26000c41c01400c48904c41402600d140402140e81c02109592103420642c00310200d600c1d111142c166a40b1507444020241d80c2d005010003d00d911900074008400002405000750 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 901590098 1250 901588848 901588867
    0xb0114070501150f0609120804051e010e04021630050904110c0a031218030207210f0323030a020d15060f03050405010204090501081606020106140607060e03 69
    0xc0004185041003c0d82c02030010a004000c00c29203c00c4031095920f03118054101f42444070282000d480803110001c09000202e165a12260b1140032020098a032132a865031b6400010400c180e903d4007140507034810402c020040011000262615030400b152016030105c13602d8030b5181a2000b0f42d0000001c60011500c120381d98050000d00500104680900125000720011416445040c1c09001e032a4424603010000074003481980c0d80b041004940000c028144511408501600c282d048006030850001804140c1da4106c20700403074401521241036002c007603900c031211104850f20180c10b0094080c0755000c2611050b01c41094a140c441c071003500d03400c101c1019400707508403881549000303041c504d5803410b505603c0f85400480c0c92a81c0c40c4030f080c031030700d01d0142d00034500944181c527955000c000200e1544054000c4900902c038a400408488030035410000350140306810045c210f904040341000802000405410000d804580c4295610064030b0701500034110503000401e50300000c10740002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 901591348 1250 901590098 901590101
    0x601200c0910030c060503010506030a0b01090306110903060f0f0c0d23040515090709020915120118110901030c0224091b10030b0111101a030a02010e040b0114070501 73
    0x1164070601c800380805880d2101502d1b517000c2400b0307283d0411400d1000603400b500a8225062103001810005411760f1030ba150401075486840400110101c00506a41d01b0300303041051680c840c51520088030f071030510042004460384c0190040f90b02050108050b042c0c25019071021981000c41c4644030181c0d0302c080c4000011003012181600c4a0003425090705800d1b5140490911451925010b020310500b05000c6d44003c2d0050206c894014231204205010302003594010b100812143c9445a065854408000201c004c4141005152810701d510002c003208400309840040409003000700b02041c103410201d181a420f15016100c40a4074884484d00490300c0c001d29000300c0322a405d8030700c40001841038500c542d80b0314602c0750b004203c8103050f240051013a0f1203007801040501d41641c01e41038100f40b807031a11f031003025071102c811364440c03004c80c00042c03041115045810980140581048a80010b4a000003189011f801113440e200e080c01680e100e411260b04404442c03080341e407102c695040050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 901592598 1250 901591348 901591381
    0x16031110090b0604110702010807081003050a0602120c0c0a0f14060a0504060b01020c030705090702240108010c09060203030414030c030c061501081003060c0915020d030b090601200c09 81
    0x180220700e005c80307950b04014030004403110381c0d4040c2c5424866440f07140301240c520750001d0101c070070340400003004000540240314209503640a00009a2592000c0c007080500d0203002c1d00e113a601150401c80c022640101141c0c001c00c41d50801b4801000161900381420300c080f0009601031140209070030800302d441b1035400140902d00801c02040000ca501c00166138400c00d10003450360650100c00d0401c12842c1544845600154610644180d040b6903160814640110000182540000801400101c1e004d12801c004001180341c2407018500d8070001949130321020b0030207000c9081001242070401000c0003280e135070500d410100c0b1b507100e1005001c00d0301d455003521124664803500c03250112030362083d04071b90f018a0011110b500010b1440d9116001000c24820100500003500c3e000070701203511440c2d400d0910203e401510a80c05100c5006084583c4450303000c0c41601814240300c16640e003c5800d4401c1c905031070580074070b80d802c8d01d09180740100d80c0301c92640c006800c4040100c108034551111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 901593848 1250 901592598 901592611
    0x60702060a17060639150f060102011e15080f010207031202040e18011b08040b0a06060e0625060b0306011505030c0703110703030305010f05010516031110090b 70
    0x110b42580781d160401010744078254885034031421080f41e603c000ba4200100301c2c000e0903030504001c1a4104101c045080c20b810790036241580c0000400c1010310040d000c2003551243c02407008020701c450310452032a40c000306003800789078140e403a41d07000c1020700c041020340068100d120446010a456000040c040e5000040c12800510040003034181e46815000340e07000d8442c00311034040c2566400074400d000000d0102c03d00100c2d074a0f44000c0480b03c10390342d010951076006944030300701854203007408803400f000a441c014090f89441ca00b00004c0381c1c4180c1d010b00441c011540c0b00e50f280340310100540c00f0400c03110f51100d00ca000584800070440c155000d40c1140c0300c20340984107aa80c0e80e070071038074089002c0c00103031300410307020400501d0b00058013000381f410b01d2180c10f215029040743c142c103038a0107000da041100800d68400c0148070005003281508001c2409207481031a081d03030410206840906c00f400102884401401303000041c5c0140120070b60410040020080e240e01420b005007000000e5407507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 901595098 1250 901593848 901593887
    0x170c090106030e0f07150e0a0b0a0c1e06020a03110712080c0d0e0709150b0301030b040602070f050c01110109080418180312050c09010e10120c0806090c07050a11060702060a 76
    0x3031071f145091000042d03040f104e0004016040403001c07070050301c4412310781c482212202d1841c0031414440208450000001d0b000300700058440c4000d8002030708440f203090345c4628064060040600003201550401010840d500d02102e0a440d00c050701c1407580195410220080e060061804000c800000d000081f15480e01052188081682c4842400041c1d070041010602e820401840801c0030040d0040d0020b104003c01031900103140c450b07030041d1840d100101c844e500039007900c2d206981e00a0409902c91030318402000f2600103581d42e8040ba1185101d02d810750b1480c01e140000c12840c42e401f1040c400c41448200d8107442c0f2601e0000c0c00d44050000c030456091034180800d01401d1b00b2810f03100b80341c00c10b842e80c2100074041c2d02004400d07548403455008006021101c1926036400e0300403c07010f042c058031820b41500b0a00c0400a0103c00200260300820003442040b0201d180000d182103020f400c0300b00700000700304070804213025105c1c209010b5008400015240c580c00d40c884010501e08058080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 901596348 1250 901595098 901595117
    0x6080405121215010c020402030f0a14010609030b1003050118030906140322060216060605121c031b1106101406090a09090804170c090106030e0f0715 66
    0x15640241c0c003200103000903100c005481c040f0030405409140070141002c024960443c1e0010741a41d0040352003030140a655810305c8040c0e0342d14000c0c00d82840d034980c0c4003c480e41c1041d60040c0707403007004c0c400503100410781c070040f88900041c80c103200007030340e00400240a0344a60000d5002e110a09a004400041c2e0361803000032528441c58031010b5804c081d250040c619200c1c003488042c0d8102c008000c2e81c00341c45c0641c044002880d28801410194a080002c1c10543c10b070341400e00444106521190141f04155040d07062400082f5005c00e4950501c8030344409a11806400c40003001038a0641108802e40000598100d0308010310289a108140440703840c0d81d10403503d007010580030b02ca0040101e420a0900300300d443d05602420f103074503000d054034640c5941d6030226000c0c2c7d800b8100640e541480000d00340640000003162510113411040100300c0c91182c0c0011510000c0144645810580d464a502c1c03e080d6091001050410701030080b1482c00b41ca51f0b046441c0418141c0c00d10001c51072144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 901597598 1250 901596348 901596373
    0x20301030218060d12021c0201051503030f0a08040c0f060215010501020a120503150a030819091202061813050604060611370311060609010e0a0b03010b0a06080405 72
    0x82d00c0707200b580013403c42e021131641d81e9a681c4d0003141c502d07011400d5004140144080c40340c0011080c121098079030020031682041c0b18040c9030340711200d40340b9010345c00c104a415151400e400440780318100350320348044150b80e18189030280d4072940d04250001d488600002511960010f001031a0036000304010203a40d0340c403801a0383c0d8002c81c54005080617095445c501030300340182c018580c040c41d9080d254070800c0545e0005800e6400342d400444c0c3c00c100129481610821280d0079003482c00550a200d2000307030901130700800380e0302c0741500244139040004482050030003542006d00384e0240a0141c0a0100d1419040009030604480c454050361401c44000345191040d400010041d407010060709940511750444400b003030784012080080300090294500c2c40200c01031040b501030099466000c0388203002a11420704401400e000c0c40f900141c00103003c82c034007624055400c08002180058101c5007540401d014140b90300e4640c2d4061000c003000141c4a4210b80118441c0748504140d83c2c0741a51513 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 901598848 1250 901597598 901597639
    0x90a0806010905151e040b0307060507121716020304231201020f0a030905070f0b0c0106060305060a0608130b011403150702032a160602010b0f031f0b060d0203010302 73
    0x31600b45510203200313a241d20050f0000c40170000c504401510108803004104042490b00310f40c5d90100780012400035010050001c049a981640440c03847d250400c030300411484070b45400041c011440d14007800118100842c02041281c0042c18880d65822000020003880e0b0320b25030034980c03401c0c000c081024010013140018070840d8140508640d6035420301e1141e420444c000c2c5195082111f5900c516180840c0c1103540340026001070484100907592815550116070035920305512450a1509041c1030040903644c05100c101512800c1c580000d03540d860202440220a0a0801404441211001041c455161014000c01700402d0301180c0048920410072005240e0440b072403801030704188001e061100803004085429400d6102c48019800c08000b99401c060410507801d1082c032004034100708058080c01031034442c0034203d8003c04008020004030391540d0a03015480940c0b212044d901c0704005956200f003d00c1a405403180f900c0d2408051000025031003070000303a00c1b41c500205c1c1440d040303955 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 901600098 1250 901598848 901598881
    0x20c03070503030a182310030b0310090516140102070b130302090403020a051f0507050903060a0b130f050a1d1005070e03010234051207020402090a0806010905 70
    0xa00110328260b00c014084070711503e0602d4001040c58010300000f101e140a110007500300500001006c4070010701010000c0d0328040750303204414181040e2002c803060340c000c5500110002090400b0814500d145030003030030001400905110225503d00c04100b03904006081840040c080c1c0885680315160341801006000f01e901d100304480500744103200509103660404e130054440c0c0112001101d41c2d0b611341d4185041e100c2481401006003954981080140c0a025080141030415170f20f4803070303a0b001290f00c9080c020205007000da265203402c0c69a45034a00b101074090b403602000c100c0545251000c502800041c0c8a42074424100008403e00c6100d141c112100da4181400a040101041c03140704e01a00000f8205020701c50701003902c2400303450030700062484108000c602180250003840e42e441400d425540300d8442c2c021620400c00044e000140c0ca500d80f03003c1740c111602c9101510014029125003a00a9006441120001400400050001e041c0c61444d482407000c4e95940c0c031614592039a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 901601348 1250 901600098 901600109
    0xf0e060414120903030f0a0201110f0904050708071b1122060801020310030b070309020a1413181103031603080f130b01050d06241707050f12010608120703020c0307 72
    0x100f000c0d006c584901d2008000343c2c1e445000210705c12070b44a80d40b28858024070303050401408009240401072500b445029849500ca0918296074180084000e0122107034050030080c0c004500704920a12460404a1150b8540100710f110110800401d08500480c8900510540b80c100f00d00400c0c09601030080d248104640c43c00d0880c0c00d851600c582c0c02400001d00004113050f512506000561501d0740c0c61303005001506d02c0c46181a02d00024400c07050949503008403618507095041314010071801250a01541040c003c001d4048000d00003030652080c1c04c185451446200d02003010035400c41c11552154400f0850000c0b180e45025071405405c103009001007444201000500c528036005051151a81c016800040d40d00c0c59003c3c82418201b0120381003d21401ca00001c00541c02c030b604100d01d800010700041c01c034541c80c02c030208684a40000070030380304640c4c0682242d0810003d521400041c466281250b04503082141c68008941c00394500f07030010f0054070107040c518240080c4007000c856 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 901602598 1250 901601348 901601353
    0xc011a03030f03100909060b120a02310c0305040b0709030c060f030e010c052203020a050d02060f03040f02010e03030310060806032b030e0d02100f0e060414120903 72
    0x300b09003a0109240c0c4020850701c1c80e007203000800b01d10b0703c5691180070016441910009001c03008442003103458009448248400c0d40a40d0104005848104000d0000101c41c101d20b0f400100a8450000318032041501c0f15110b443e1101c58000c450385908100d010324000c0304000820748409900b203034421654000502440c0d03910404010b01c42c446c41030000740a24610300001d03040301e03d101f1903003036030504081000041c50204200a041a0940d0340d1840c044c40d2524a1203500e01c0d50740803071001440d500c0b0b982c0c421041503a1a2055442e24021180311800102402d0b980c0c2c5080e1501908100d0045801e81c0029020000c00d0b4207810000300322405600f59106280d4401d107032070000c8616540042889815001e44661601405924500ca00c0c0204581015018007141810001c040320190500039110780d0005d403140c1c074895004aa004000040c40f0804182d030511104800080d03d00203400380502d00c42c05040005000c0602524205036002e00c2c1038a141c2c8074103401d03490260103841c05075549078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 901603848 1250 901602598 901602607
    0x906142203141e03040c030c12030c02040207111201140a050405102706021b0706090b1806040b1c0524040609020a1e03020a270306110c011a0303 64
    0x64190060101c43c1c442042c1c409518418000304000c07a08141c03421a00d02c101c0c51030038001c22030000705c1c41c4040c00030302c140c0e480c07068490b44006002000d490340180c003951780000c10f17109100e4601c00200001d50003030141850042051092030091035a021003010b0020140e01089c00050f503030185a0140350040000c1001021002d141d0001b0054040d162141080c41650003004c180754200c50300d815070252a0050301c4010416040c1d080d84400b4603030003240e40006000303202654000b0000380503154841901512080c000d2803414041c2c0c40c2400182c0d01a80114000485c40034002c01000210001078001c110111040780542c242c40081d220300d6050310025181c0454400c0303a4031044500c04009002240c0b00390f0b2034042c007040382c4c040d030788a4002441e10403001100c00348483e07144503503040c40d26007141b030017205e80d00007406100082c40aa001d0102d0350f84589060f000e010311103000d1900404100301300080e55490021703941c45680c0800c038a50a142e03032162103862401c08041c654038080d0196150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 901605098 1250 901603848 901603877
    0x11d0604050408070b0709051509010809060106020a08182214160e0319050c120d091206020c0f0d1b0506060118030c0803071502090307090e010906142203 68
    0x1500005100c20208200980005020754801100300b2758550000a9669502e80c1d650004142d11002054440d269100c10010410342e80d00040c0280141c2d0030400481d255264210102e80c2011034040841d8030804d5084100c04041c0495052000245800002c00c130143c004403442c82024070450341c5070b0383c481c1444100554a0301502603c0282100141076815007148001c00c00307103c2d1001c20068440e0f601049d501480d500b042140c06024410401c0100681c00203a580104100454041c194000e60f44446036800c204260b0140c445958246042e19046c2203010760503075503401c1c056121030004a03104044c0b02044503092a450015030801c01504890f9280350045d1148a20f82040040039610804c0010100d031040d010741000d001508040c1da5101ca20342410441441c60700c01000c8080d1040001035480c3c2e500182c03c5088a90141021403258450341ca01401404141c5d000b402c1c081c20940d074101003030a20010307a407081c0d10301003040402c104100340c601e03400404524001c010891034030360ba0b0701 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 901606348 1250 901605098 901605113
    0x2070504151d06011112091504050d050d0906030c080112170a0306031104020315130f1a12060c0a0507050a0c1404051503071e050306011d060405040807 67
    0x200640c1079480344190789003082c440991902000c84010600e1600f07014503503910141c482480005e0b20014101c0300101a01c5001503c20740d071b15184654401c042c2184500705100c1034030014540285903440e03600042c148142c90303140c0d251050700010602d05002c1039080c002d101714480e01d1020340e80d018460303081600c0d2a40c00040040c0c00e84180c100c55140720a0030303102d4030040107030003640d54000c01ca03a07195141ca00c0d012100e5901081c400e90040c002c0007280d44001046910f901000c0325421030940410304040001c18044111506990409140030079903007000f00700d50100341c000d640c0300680d541e2400b406500c1d20410385a1030b410746010007440303010912885c00761080c24003030404d80d83d910712107a86004151a0301ea10001001d0b0341e038610414a46814407034181c2c0040401c41e0403004035490400a40c4907400c41c040c00705011749486040e4107400c07100c45244050f042c09400c40303040c3c0d40c440c40c00075002c1c0e450800c46025422440f0015807903080c0ba024041c02503a0003a40356007440d20079640c070007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 901607598 1250 901606348 901606361
    0xc07030305090f070942210b07030f020315030f070b04060c03050906131805040210030c030b1e10050f030112110a03150606020601030203060a021b060a0c030c030c02070504 76
    0x5403211040074010031700b0038201010b0342254401e02160025100410010201d03503991040410031f00c0c0c0b103401d80601d40c00304001040345070710014403400c03030340c401505034014560214030119a03032010041181d643c00c800503144512908074216001c1c0e14143c055a41c1d0384805010b40c0c940142c091004100040c055100340d6032540c481e0030924244044480891011342142c45c3c640c080103810242008596041001c5506044440c0c07c180203600d86500403e521030410b001e810b00305980e807258866000d1003648061400e20005105004030907500040100c2032001460b007070f1103101e10500240340c850142c0101c40c0103c4219115508680c030784111442094295801030f1640484118460741e183d07105200c1c60003541c4509c07031070b808001d0000d0b4030700c04a039103d070429419588660700500250341c0000d0345607401207807403d001d0b80d200030980c20a101c0c0d13440c1c003140d0025413150f9001c0c422540070b180c200d03030303c0c46003076942c01c009090343d01c41c00300c041d26400c080c1c0d4009600691014412400d0540060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 901608848 1250 901607598 901607621
    0x310060c0f1506090b030307021f12020310080d0206010317070201200a050705010207030b01050f030111121905070516050c030d09051305070909230c07030305090f0709 74
    0x2201d81e19161501400071941c203104846083d42d48000f40050000740c0706021043c00154000c43c1880201d0740801c4400d850300d903050322000303203400c0c1441417239120b40e40703200000d000713101e0654807418480343c0c03410b20070307540d00482842c1c3c040d00008000e610b1002039910b049035008000c419010a124000002650211000ba810000503614440780001e4205103100407100240040801540c2410315a0410003150040360464010240800100c1d42340076600341036403c02c40714546100f454400003030041c00b410200100c0b169000c40c8098021007454021031048a0000310426206424454641110000c0780e4400104109125149240746c1d0f1107000c0711000d10078002ca4601c030582d90b000900d0194065958800100c4d0014280001e0400f000502c8000070303802001d00031400c14600c0942190824041c0d07180180e500c508a00c10031140e400000c1d0114038120401126081c00f0301d9403409503101c031000744c0200f810000801e40c030180014080c410b000342000685046c604042c2c00002518038803900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 901610098 1250 901608848 901608863
    0x5010e06160213060608040c060827070510020a0b0a052502010e0f0706090b040b030106110102040e0112112d031509010507090609180b031f0b04110310060c 69
    0x415a903c6031203108050141c50726000050300d031900d88220f8034407868115400f04101ca20600c1000149500244503280450404c10483e46860981501e000c20b29804a5070009074024100c071034a801003030700e01009000e040030000582c0d50ba580b19003502c0059603084020589050300c40312210104000d07030005a030070f01c008502c02d1b12180c6080d191046030111102c040d08140070070000f203908006480010301c07900c0001c50030300d0724064840c0c4440c00148101e0060010b0b50030b001050b40020340c12103000e44452030054040e56154450515445808101200d603603504441883d11ba1502c002e401c05a00461141d00c5140300304051300c0c00100300c0880c0b44d140c0610030450006103c80700b41500780c0c03180d184000005034500d4100d400924503003080e070250b014050a24024400c3c0c1c8600391102d040f144601c00f004ca03940e421000807a1420314100200c000f0707011a0b2820018070766554200c1c0c0a001c601700e40a00244288180d480d13101d2205850071074561000b010100011402502c3c3c04401c80d0003281c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 901611348 1250 901610098 901610119
    0x1b0807020f0301050106030b01112409070f260c030a060b060409050406050403091d1614030709050a0902091c1403070605100b0a0215270a0203060105010e061602 71
    0x40b82c00d44100b80c20103001b00b500e5080040320365900004609010011030b0040c00810440c1d59181c101e10000741c00c02500d00c0f0f1602c00508201c60801805006040c0c0c00200751000d40e950350080400384e41d0200311122002c0b814013010a090000841260343c120040141003c2030455030340600a14007044082d8002d6000d00001942005d1351254510641c01b8a0011495107010303d8001d000008540001910700660845101030b001c0350407100350b02481d040b00c4085c2c20406054140c0d01010041022620103000104012070b09034000c1d01441200d00a40c0e0079a04540c4511040080e4011000d0081d08100001003181640341c031742c1010722400340540070820314051480350550541c3d0100d4829121240c880092141195401080000800041d41c65030705204d25130740000d446450082c1c44c4e58a190306540400e015a54580c0702c44100340300754403520841039184000c0e5480d01c410356403da105e800b840000007035550107911924415080144101d14100c4405001d452179000743d003060340c20108448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 901612598 1250 901611348 901611379
    0x909180102040612050c0a050301091107020a080a050d050f0f0d0e030a0c1403192d090806010f24122315010503150303091305090d1b080702 62
    0x40144082c1c4866680c10341405014aa880c0c145c4402801c08035407000200314400d00240e110041e0fa065038170042001c03d29081d2003000c0503480c021131a0203980220040c81c0004c0100002a4000c10544641e00340e41c1d001c900f000c0d05403054090300345018a5500704011410f6950b140000810310444510310018500300001c3c032a0707103140c10400f00c80003c601d00c0d0150030140300d142424040c00218420085180280c0c204000ea900650480124180f009203120b40e12010801060000c0c0500c040c0007440c0b82d4504800e000700130184612070020035008100003c158a62680d01c40b9003640c464081002c0046204048100c03c000b0200b05c102c200016090fa580e2400c440d4000d4000c040d54007086000250412603201d11442000740c030f4ad2202101c9a140c080c840d0341c10030240da030721038100c0d8803510036440d103400428114401c00c907100c0c1d4494030407844c245522019a100c24002d06d450780484440380341002069030200310045003183c0d03c55110504c0000102c0d040300410a03e0b20242c50040c00c5000d10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 901613848 1250 901612598 901612601
    0x601061b060e0a141f0b04020d0f020a031802060f070c080706120b013009020612010f050a0b0711060403140a031202131502010902120604050d030e0309091801 70
    0x4102019040d00000300b05000d01000b19580e1140c00360311030241c00184002045200b045c1a1a884001d0b0581c86000b46000e940da82d5050354110340c5e0720401403091400000904000750b104e106e030300700861320f84400300f51008945000c1c129590350182526181284400125144e41c101d00d208440c01703401c1d50808240b0f010140551401002c0035250300880b21412180300c41513070f8500c2d680c54104000396801180520050105092200100ba00c00004510601d2a00b000e4604420041e40000c00052069905000c220f0f00c1e60486404d07800c40ca5074540c5400420000d00e000780300741840700d0b03c2031020002040402c582034855400003090185455901ea80d0440c07103400443c00015070303400c405a00c205058002142c41003043d0514021440e00d410100202e203101024001c0b1020081c042c0e12208505c0c3c002d600102403182c008244600c90700314800311a9503090100c408403014050428024400c41c02030165174407564014000d14280455581808a0b5407402000304039100d501c4101d0b10b8020200307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 901615098 1250 901613848 901613861
    0x3091104021303023a05160b09130e030d0b0f0d08090f0f060d15180903020708070f09020d0f02072114040e1003020a0b12011406120c1c061e080601061b06 68
    0x740c0c0c0d20726112705c903100c10440040700620320510325a0801d42e0082400c1d4001c41120300391a44803400207006c6407030070b01190b0401108442290031a07600c02c502c00902139014084c1c40c0c0054122184240000c100081c0f00c80c0108280300b17141c202206009203038040140360007401c018441c0030038190f5400d50340d13070909652503103542d00c0180e01551480c000c0140740d414840320740a050b1a8004202041ca003a2861705a4001441031209540d0b0100300ca48040c109504a0051345940c4101903484444504124000e051181402490040300000912525001c0c5850580c2c00c041456018142403030b066003100c41040080001ea5005620000400103a0f50030360424090074508507800e4441c05400c0c0220044d05040c2c110459403061041120040c0e503442c01261019100c420680c1c01c00c0e11207161440c007900520307200c5a071070088040d103400f0004d2954080c808030743d003a60b141401d1030040b440410b0a40360350f01a501cbc0a800c484014010b40c0d01030300c0703607028148540306502c1c12410603840341d01c1180c12 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 901616348 1250 901615098 901615109
    0xa061409010506010908030405010c08040506040f080f060c0304062304210c1214070f030e010e19090b061c0606020c01051903091104021303023a0516 66
    0x1000400c0c0010314900b40300369980103100b8204441c0341420702a5103aa28000ca03c581c9042001e0324050000b0001e00d40c06071070003082d01809841e1215203c003840056407049001c0c40318241b01c0d82d01c040c64940800550240180c454145e42440d6482c0e40d16a80080d00c891400385140a4003040c1c10029540000040ca00c9580603110203003021480c2400740d9400000e001203072040001702c0c61000040f0b4141e000c00009d036a0603040c0720801c2020000c28811900420360007034071100f10340c91080141604180e540340c90748401d0740c50240351811300e0104800d01c05c4550001d100b001c074050007484000b41e9640a000301c2d10004000310700300b07109001307460390a40350001d0010010f51121403c01c0a681c040183d14001102402c203581820920140c0d40000501d10140c43d04058581e1804810309ca0280d8400200000c080c2003956078a212207065030f81c801451104900520361058103100072086884610031104409031001c101204400f00c0303002c241c0c5818011346a5015860b080c00d07062582c122240c00606 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 901617598 1250 901616348 901616381
    0x6010c0809032d071a0703030e1c02070509010b070f030302040b0408101a0102032b090503032a09060d0212100315020a0f200304080a060f06080606120a06 68
    0x43c54a140d20304000e030200d00000d266010b00414001510340c5117241c2182094a0009034442d042420308801402c42089000d186005018058a584a03a403415270b00416144d000c450036203650700180302c403a440911401e001d140d07040c00310f03600092000100c401020b0182c80c016042030341b280c40c400e509600c640c0c00f40003182d0058114209000c40c0e4020003011002d1398444a58a0801d240040e445e403080300210260040d9044222801c155034080c001c0303d104410808221038002898417030340d2640280d40c0649608155407034a06007a40001c40c4034180c0c00018440b9052607402c038148011504044c0d00040c18503002d10661100f0075004041c13900c41c2054107104900341e8654100b0035050202c2c65007444d01c0340d00400c200d144030307a0080100ea014035020b1811305810840c500401c07502206520310002d03140400500050b60000008844144034007410b020801c40d45540400812903604d84641c4800b50800e0000940615160302d2500b0625403c100f9a214011265940390864900d006001c1d900d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 901618705 1107 901617598 901617643
    0x7020d08040323011815020a050c1b010810270216060b0a05180a0e0312010e040c05030c09150303070b040525060806010c080903 57
    0x70764011684510f000051007003080b0320504003032048119070801d100080300700d000140c5541510b5021010b2403180361504103070400380d0803001c0620203101007803140300342885051000c200607103101c1c1c1440180056240c00035007198005000c0340240b19800030f06000040c2c1d4540c01088071280d030f0801241c3d081c00901c3764800780c0300f005014560f0003c0c0710030f0401000000e407c922284481118110b41e401d44030300c03e10a140e0790403e4055850712010b800b03c2e128500561045079449900380c15289020b81da20310208400303d00303a006441451a000c02c000c0bd10190403130000282c50210701901207603200000103501d00e078005e442c1081149181003204500c0e43e007001282c42c0540d100c6401e6040740b0309070800d01e442c0d0140c071600381055650003441f00b441d1102c18408a00790ba21985413145140c454400446005126900071503a44404102c3c1d251169030802000d00300c80b1080c843e21030700 = true := by decide +kernel

theorem cover : BRFrame.Cov 901438848 901618705 := by
  have h0 := BRFrame.cov_init 901438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 901438848 ≤ n) (h2 : n < 901618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
