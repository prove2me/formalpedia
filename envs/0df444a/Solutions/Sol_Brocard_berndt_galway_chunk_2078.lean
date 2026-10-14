-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:31.380436+00:00
-- url     : https://prove2.me/submissions/fcc704f3-23f3-4c8c-a382-5399e74e5ef2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 373561151 ≤ n < 373741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 373562401 1250 373561151 373561159
    0x50a0b090105031f0f14010b04031103030901140a0309171b070806061903020a030b010915030203030a05090301090b0106110d02010b0a06030b010c151b11031210030602070312110901020c 82
    0x149007203c00002c0212502400d02481b001c00001074945800019005aa000b0082d0040a1840100f015964450101a13601080f50380071400802c0e02590041d1191104900703011959101e84c2d659010010042c0142c40e024030004076200c0500502410714850804901d002401480c4c18207416981c1c0e13010041c40113110f002016000c402c2004800d02d400000c55000c0d03c0f00d071101d0303140c0c0361806900000340a1502124a4101403d00360640c070080202101c1c1c0103000b540c544602d4000480340795004106554244d92519008400108490901802461030741c0d1083c00b6080401d009500386141c0143c000c04680c100100001d042d503130b45040d1011202d09041c006022090400140e81004140344042c0c00d06542a06180c0c643c01076401421450124804401c6080c400310015284107403203d800c0e03000d035032041c010450342d00828040c95400003c41d000b40300485640740e48103010799105980880001d41c1e030b440d05d50040078090043c00c8148560414481c2403c0340b41000035518800c40e00d403244030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 373563651 1250 373562401 373562411
    0x20d0f08040305030427050601080106030b0a05120a0b06091b070309080a300c06020d2c190f0308061306061106010b0301030818030c04050a0b090105031f 68
    0x100110441240d000b940d00c481940d458030754808642c07030309030911084102ca4018111040e40344101611840d841070310161165040c507401c08404034014100741620540208840030041903d65074031048000c2141450010070580380c840c5007110748400050312850140e20300e001400b804900589a000b050440011400c2d190000b82c00c003100d070260700b81e10503503480c050000608180221032108000c54402c0d9040061031340d0090381c1d903262400f0111000030000b2004031044001481c180c00070142c1e050140f070081841040440c044041d842c100a40361000c4c4004038a42c03151001c03d100c441d0054411800c0502d202d04103480e040b02c03e4050080040811411100040a9035100801d0700030800170301e10104200740e290003001d00140500b6030030803014454000000340303d00c0385c0421039040e241d2004045080603084120b00e8119480103981d242c0c1402801030f03504558903284151351280b02d00380310119904440d841170040806042c0c0007680290404c0a5501816070b541030303011940ca0400302d0000f1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 373564901 1250 373563651 373563653
    0x105071218030506060a0b041202060702060909070801081c1b050115090c0207090903020c0613030204020f03180109051c02070f0314120c060403030b040213150e060403020d0f 77
    0xa080c012071072001007001c10001000c001d101e00080c10328400d400135528115541d480d040400c1c2c4a00440c81001440040d040c0000c0050500301c0141c5016880941418208586100040c020040454000c00040c180034010003896a0820441003810b50301c000075400003524250003001e041030220034440b50b285040f0b0903010400700b50b1040703035081200fa03115040d80c2d4403540032501038078141d07070010010311400c100401c0300006840380910f1503506400501c2454550700c18010035412080c050071040d180c0d00c1c0000f0250300e0301d00003811120004007809540e80782c00c5410318000c65401d0240925a0b250418460002e000000c4004c03181080d10080340c001300c1c0e8040c04a00d0180d807600036030318200ea12503000003008010801d102081200070151550500b00c2c14103900c03540030b0001011501e5020b0804500400e000742c0c80102d1010300640302514004602001110038984c541c4a119180d00c040c410b05ca1960b4041300209403d002242e0b02c520b89841e680006484290404018082e00b02c4114040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 373566151 1250 373564901 373564907
    0xa090b03041a070206100e0f0a09050f01050c0406080c2a01090609060b01030b030a030c0b131b0312090503121813090c0b210603010f061202130b01050712 68
    0x10041c03000b03460310b01150f240c0940f00a4840d001500c8243c1a05010b00c00856901205068148110b000700110304083e520551400301406c2c4060080d031300d500846031260140c2c00c080c0a800c0c07140481f40300590751746150040040c206e040003005d81c940948144045c03d00100790b00caa03800c2d404c032031800e000b13110201c101c901401042c03518401022940f8000c011020480c65401010014000340c9080010200f400c0c141504c514062000500103034641140f80d0010300c24160076a008001000c20085064156462881c0300000300c1310400c540007081d03001c100300200b640484186041500d088170425140a0100c0e950301c40f43c41b00c04500703a000ac00c0c051500d174080c02400c0344a401c000c0c501e81110300c4e050b0940c0003c0c00c0c800700c2620001e01c05480440c20b0a0250102d0700107210705030303a056680754203c0a000105101a190f01e5165481d400303060500100307030141da8003411008010f112203107603d10401112018a10200300802d05003003a0780c000c0d0ba00201981d40442c0c001d079104000740745a210803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 373567401 1250 373566151 373566173
    0x3150e19030e1804060506060712050a031103010806190b21100219020f1b10020a170a11070803160809060a030515030f061305030c0106090209150a090b0304 69
    0x8641c12514140310b45608200e548803244c0220b010703c400b00981d4440b00300348a094400ca00019116207800000c45900ca4456001008001100d29001801c8d0a05007490301087d44207a100f2415a8000e00074030061a0f55200a05100d1020240401c17101d0388010101300ea4038810801d400110050b6090240ea0783c406020118213401c40743c104565410005021340704442069640e58014820701d0740c40f91103400d002071507110702e80b2903410401c0c0c958000b00030000c003a040421058114000c10074801c0008042e08000304001d602d505c041c586410700d0340030007884c1e59181311010000b0392021104125910000c02200c145080751520284c81c80c0480c1403a6100303208400d04242c00c440009003d00c90941e0643c401c502400242c00302015440c404410966990204481180d45400c0203000ca01c18002e680c080486192241042e02d04140d00010041e003100d4484d402002e820382c00040100b00d86c900704411368040c02941020728185100c50f14000c2010303480c2d024000c03e010002012905108400030f075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 373568651 1250 373567401 373567427
    0x10150519080d020d08071b06110d050a020405041104150503060621010f0905060f0603070e030a0f020102120a05040915170d0915140a0309050a0b0103150e1903 70
    0x1203585480c40850000c4d52034401e261000001419640441c5a0a22480c443d0458600100c000c20080c1e009440d000014000ca440301c172280340080003066840700b40c0d401403a118044100005882c1d0345890706100959003444d00d0114810820001803156003200040030b0480c030094509903440e0382c4ca98011500c64850f0385014542c042c00340c000640d003e0842240e8a045e290080e0b028446d040c2d0381c000a8040d60410b460b0b050340700080c01c00030001401e081020350b5004859140108034031101c40c0100c0d0401024200903600c21403904a00b90541d44c04111007001c0c41c03440c6201628200f071801d80280745000700d00035615410b45451018182c0340212455101400085811a00d880018195242d654000365441004110842c03c00103600c3e030581030390350f49401f864690809007a15980c00d50003c0c0e0041c04c520f018590368401031008100c080180000180c4902040304195045044c030304541c50060201050352418402d021444000c08900440c007081140d1038400d403c0c44919003944c4804420b98 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 373569901 1250 373568651 373568653
    0x3020106050a0b1305060f1b010b0d0f060501060203070f0b0601020313090b120c0a05041812020304060809010504030c0b1306150311090c040501080406020702090c09031015051908 79
    0x40081250703941d4600070b00c1340c207581400c042500e1760307180b086c440b041c09a5580541005002d0100e0718842105000142c6e54284020000035440c4000340090421074100d1029101450f41c4505c1404000107485141d024260b280010340c20101c40365502d258100414500030031250301000444d4030307079008009444483c0505035003040e0590722808a20010000300c00e02c0b81c0300c4d01022070441740d151400309045030000d102902030720300b8500304800d04c0080d2a00195000f04001c1903004c600100307014040c0032007180c00c0c0e507001d1561649007550080c80400050b26141d080c1c0d14210a0100080d0045001c00e0b1007940880c003e40140c2d603803000442c03003418482000d0500c50510300341d080c0502c0b03c40b4128050700e124028181405844400b07000c1060303400c1710f00ea1600300c0304100a106660054100b40e51280c42075901610f030807a2540032683c0d00c68207590032801d0f148042214080d614041c030405031404240181001100e050411101c40c0110314440d03140a8402d03440c80542100c1c040c90100c0c0504030f01c074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 373571151 1250 373569901 373569919
    0xc060301141003020f0a1d0909060c090f030109050319050c0a02040b0619091d041a091e0102030106030b0301140c0d02041a09090c03070203030c09040603120c0b0702010c0512040302010605 83
    0x407015207426842c00707940c3d04081603401f10111500c0d00d0402980100d05c42802484140c1c0e8010000c84640d000700d280d1603000241003020710700d07543c0900032101d005200e032002c1c64850440d800400b245080c102c502d0803d10209120003a00304400140c0000c40030380445010414990100200d1860710404121031240d8511101d81c154003a00845000111181644d0282550b24005652402c0d54030944004002c071603643c0c1c1c2d01102c40322581d4003940200342c260039942050584020503490368030300084c14120f0313500030004100007901803180303a00f0b090f0103170000e11062a08101c2032003004002005041e00c0c0d2000309100e07407111001d5041d50050034680300c2c1c1c08160502c84000764665006000a0b80c400d0728110005550003904c54148c900030441c40e0000c2d030650320703001440c0c490b9411100301280c0003a0303105000008680ca0720401d1a0b200700c2601e460880c80c05a04001d0740c0c901000340054290781c113040091400d203502900300c45422810100d5080c1c951190300d000c0f8054402c030303409690310040b48 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 373572401 1250 373571151 373571167
    0x3031814240705120402180a09021507410601180c050910140408010504050607030603021804080d050a02130e070c0b042306100906050105030c21090706020c060301141003020f 77
    0x164040396119000b200c258618851088901026200d90b10000b000100303460000b40d220133724441110405881c58020003002090b46080000058825940044076071041004000d240c1d0100030301c44031a0142ea10134810070320342410103452031041e43c1120b03000d448405032040009101d09890052100078115075951140e4460306103020341001d0310f0507240c41c06500c001c60010360281c40742e03201b2a070740174210410f0a070004400b609134600c010019a00c5001c10040e4042e050000d1264501c18403901c240161101c0361010500c00220b01a044418040c80a4040c05101c03500100c860000c50303030180030b118581e6100d00e08003d4011022a05811940c41c06200e112245004079000788200c503000d054103040c82da074402c0d03102920314078130070700d408a44200301140c01c1440d4a00180503c14a000040d550410b1a4601042030070044800441d40d400c80e080c244081907041c0440e05480d24203e41380c1e81954144818002c141950040c0e042c80303003043c00241ea1250b4041d030113440d56110081d054039111211 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 373573651 1250 373572401 373572421
    0xb0306010c050d110c0613030f1a011212141b190501020714030304020d150e070e010f1a0f070c1a12060117040303181424070512040218 60
    0x1134405189094012220280d00909150080c0c4000e600010084941c0a02d907445901c40d540c01c02500f620144410442e40c201940003100440c001d000301a0136071f12806840c185a010528041c0c40c0c8001c10061198000d20030902009407074030325400c1900030b240051222001d07841c002d8440c01038503041c450200218140310041d80a0030000d4043d6100841d02145035512949034442103a00943c0719018107070086c086013404148800e6100c448a000604405444401d440c208265100c0d101c0320f04c00c07800502040f100301005c0c1c0300038244041004032911060408402c1c501858800c03000001000c2890001e0001c0c1d604058000c09900c01459042480030040300b4480e40070f201c40f4030f10701d610f4401003030465210341c02d080b480d815442031007400780d00d59923030880245c0f540501c0300c2240d6403070070100c8021490780e440002e40c0b5110140140000a200a121b040112000c030a0155801c0d0349800c1000c40c81c0c20800b100c642185840c80d094040c0d4a41c400101841182200481d4a0f4001420007100301c103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373574901 1250 373573651 373573667
    0x507030204272307080715050c060f010819030c080702010c0804080c1c0b070e03030417060f01080c090a0c170c0901080a050622020c0303091501140a0b0306010c050d 73
    0xf07402c1c0c804083c0203030107450540d2410036106a441c0e55111031000c01c4401034896176200b070803020f80ba28628102405011514110043d9100c401c4070541c040100002a01004400317188042031001d140350f4400768801800000844401400440c0d00240103c1160701c112b100c0d003a00c40d8801003050303c032a140c41901e03030b9403241f00f04442e00401800000c421030029206007040800c0d801444004186e4401000b141c2090180c06003d805101c24000420407104169079042d02c00c08840c000c04641c81c02000200c010601a071041000d5048002444856211b160126600c82035005000c1800c401020b800c5407404480106144884072140500818440c3d540003401c000318260785144554803110085000c55000b5113066030b0205030788000202c00032021480609440c0c00140050404501c8180340341185d004460b0407a9540120110105155100d084180509204452280c00800c81e0300441c080004a016050315030701d010001803600d81c403852404640070360000560316444001900600491 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 373576151 1250 373574901 373574933
    0xf0609031d01051c200307020c090c04030c2105060f07020616020d0f030b03010c05130e01081b1c0b16050906090909070306020c0a0c060c050703020427 67
    0x14900781c80c1c0c10305610880590f09035604641050511120a0f00880010440b0040400000301040f110404861660015600c15a155000b40c003003000c654080042c10391009201c0c0203040001e0209002090001c0060340a6511500c1d42c420603900030800c0f125410390049008240303101d25001c111041c203e120b40c5502031a0a07800720340d0a5149c68800322610352888031001d0040c0c2c0540b51000300540708845610b5000a43e04001503ca82d042020a096030303200881c19020800001c0e44160013072084407030f5801040c07040da004440354149007400e030702c03400304190340200084083c01003076041e80c0f1005104102107c242c03500030782e0071061030290303045d8004803800c0456506000700e00c116103000300100d41003050000e080714980145881004582003010780a8205407080fa4000b0000440718801002211071b001e008107002c2180c1c0ca4450401c6925421150400441140308000a00b001a50005a0f68102c0c8c0100748049c1c0704071005a8600748100d00c010f0325a0803840d60080c0315014a181440e5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 373577401 1250 373576151 373576187
    0xf03030c110301020a02061f0b03250810290d090308010f1409090312100905010b040e040f060b13090516060804030e030309060708130501081b070f060903 68
    0x41d004202014202e000e02c5403100b015800900018810012444406030b802c1c10a8800110150311824022610b8000b150500f401420720600d401d1142e031041c454804064507440d1420b480e240000802d003c0d135030729100c1d0501011403090000290041c40c03c00100040903055031a40303458078205000d0107040100d00940204a242001040c1c141404a403401a64400070104c54510448014001500b00082141103980070900002c4410100b02c91054020724010058482107401c03c0800070480350107034890480008100010400042e03600d0503039a100d034114044c0155000241014006001c07404c8100c1c0d80311103a0658484402c0c815402103d5141c0504201d440d410082000300440f00140c1c062030011403d003200040000b48070f06a4000e43d03040c0501a02d0800c41d0b000c0200e441c540049108603400a0081074454042c101c26030440300501c07092a054049040040300c050000041c1034141c680740c0f50009400050140d092014a400d5a105600300200b081a00340240b00401004441c81c0da = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 373578651 1250 373577401 373577423
    0x8040606151b082811010c080a0e0106090c05070507090b09040b040c0f030b0703200a030207030203090a15111c0c050a0b0403020c0f06040e06010e0a0f03030c 70
    0x1035000e2001c0c0d03041c00c103007180d1905840c040c98403900140c042c0c80c40200f00d03003128040114040900c0790031a5141c0c042d114481481d40d0b0b03141c200c00039118104407910a0ba00380c1c5006482c1c0c100300d500a10301c42c3c111040b200f000032001d41c0f0b01d008a025100d1604411211414180c8914031964068010544a4050800e990009440d0f41405068400c0b52008980c4003842c1c4d40800c012039a0107028941061045807411802c0b41e40d012503003541100c035401562861101410010000e0b05030207124a01904164611402840d40e1030700c610500078880300508140c0c0c00b20340d50b802c05d13000300300316454454014010340140380e4035101160b080d1400b815490020b600d14002c500c0c922800210358040c80c800c03560000c40320104030000c48600c214044d06a640d80300b1200c0c4400811020300740390f4000da0296029080415100f0305004078072070400441c1d07005510030003003080001c40702c0b50030719004502407801d0310340100554000f070803183c8079070000d122280d5040d10003c00c154010100004503440f41c201d07851 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 373579901 1250 373578651 373578659
    0x207051302031603050c0c0f01020a0f0c05071e05060403060b030c031203010e0a0f0e0d09050a0308030f0a110c150a02040e19020c03210108010c140913020a08040606 73
    0x800da01050300e0150072540d10321200f100c1e060207600480e5000c4d1141040c1c6082103048981c107407502c0300c03030420a81240d50000c0c001055542c04555264404581d0a00c00b0500d81c1c2d5640d1984e494000b40302c0c103c21101d01e450300b200010189043c070401000000c0101c0d84840d03d074240740006100b101c0e82c1900c00c3c807960031403c243e804d02240310841d1700c00784214241568a0104040c03084200104052030166441130101601c152622070554540c1c4200024145c1c0440c011000d009400e140c0c024610038810a0000c000096031202101d038880d4008440c074449488400c01080a00010800540c40100c04120000481000a914a940500054010b00d0303511084001e41c1244031b2030181c090702d071032100b0008006030441210f41800c61030440c0f0051030800100c002030f007107410500d00d0800001d401025002012149020705000d810402c00800122010950140400460342030410349000049084a0980c2e9540c8541c960010394030070a40d074401d481d4400800075813086404445080c43c20001103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 373581151 1250 373579901 373579939
    0xe09180a060e0c130207060f06120f11060309060723121306051e0609061008070221030708090706021b0f06120105090c090d120c05010606020705 64
    0x144610410001601651180d512075030003420b8503032064055031003518900034003912003613040c122842061900680341c0c10b0a26042e0141c50050944509007401d001c4c0500c0200e8181603200300302d41c0d00c01c007610700c8001c8502c0c20000300c0301d10788040e60f0f00074804402c000109801080041c0300d23071210781c2c80d04e11194040c0007040701610b00300300308400312409000c000c1c100307003a201201d60410044c15201054452665519080e502c0c111002d12211045180b244411108400101e8010380211080b0380d507450503501140e0b0a001c081062010001c4d0780b80800e0f0418024048810301d518280d14100c6140c241c0f02c0d8400495005640b502d000034800400205480d0020406c00c081c0c0705a54080c000081c451040c8080452580b428140e0154070301403003000c6556800020124108040c81e40c0b2031641c5030404002c1e00f04002001801c00c95030402001425a60303a140641c026584404a90074860070300d24222000010900020115842d280010034050380000b408011980d0031210b82c1901481c22101c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 373582401 1250 373581151 373581181
    0x60e0310060b2104080304150b041d0111092815020105040c150f030c030f0212160903050d0525061b02011104050609040b1819090209040209100909030e09 68
    0xa0145d80302800400e000420302080306240f0280c61002148401c1c90390300060481d2203417514010f480c11034000b03c049401c428015029400703d42c101007408e03d61040c0200b0740b044d03c04414001c0000c240401f003041c02c10f4000c14600a000e282c000d404201100c0113002e8005c1505230350640c2d80b000304440020789a41c0081401c40a40302d02c0c1e07200d001c41078144405601030308510000c1c03000c3c10344400d00321188140d40d2010b40010303d404403505070070341403a840814900c0d8150030010100260203c0a00c049000080c40050700b204d0780c40c010391f5850001071031440035403021058079a082d0781514528140301191304404010108004101c3d203007160300304245d0803030740300703010301c10541c041480100040e10703002004c0d11940401600114004102d030001030075000800d2400204d10320341071b0a2107000351440003c140b071031000490411100340941c0001c0c055050080000380315801540000c1c40c0e8a00c00c1224400500f0104418821174405160151890038065906406881c40000040d82008a1860 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 373583651 1250 373582401 373582403
    0x1424150609041d03073005040b0c0a06110706050a0b0102071e0308030f01060801140a0e07140f04060215040b010e1e0a0608010b0904050304060e0310060b2104 70
    0x90078904025202807102030031074809604082c88203001c0c0c01c1195401030004082e8107100d15000700300502c00d0103000d810a945a424540044c401300341298000750042c007100c0a0700d08650701c2070380f40d161f181740881c170b06100030390001c5c0101c2c01c00c0a41c0030446240005440700503c540c3c800d10103503840b0380f144021582403421845c01a80440d10401400031556040d010f500410f083c01b0544603140d444ad074403103038010f0f25140310070403208004101c80c5501002188c054506821147d41444400b00001c40c1c458060145401039500400403c0c81d4070302a18150040004203c51151151903004001080382c20612950300035001c0d45070450207034518109803a2140b9032206c0700c038003140d00b08801203400360f000804c07959507040401d03c2d02c07030001c00030b4414074421008404080f402605044100e4251142c00d880c6500400c0d20a050000050010064909440d080c1c90411405d10307012000929100c6082901807007140342041c040342992188006119070b03640d812071240c2c0c178406c0c0720b10381110081c00c80e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 373584901 1250 373583651 373583659
    0x1c1e02151609120f021c051b010e0a0611010c030e03030c0a0c080309062509050f0301060317041d070c020f12150106030c0e030c0607142415 62
    0x10740d4000500101192591a480c08480254441c441d244040d140e8500030b580700407400095200b103141005d492002e2040384181c40200c05001c1c3e486a644465260701401c0080940c940c542a40e44910081000508003c0400400300e644000107442143d00c00c25600407035081140501c40c840c044e0190303c00c40c2c40200011480c5a44420a609641c3c004402442c2044a5440440003140c0481c0107103020f44181e50160029080031000c7e01880180031503143e1307402c1181c140305000140c201e08840200c400c20307500908540f00c80c1c3c00290040810341c1004107404840110310710000e44010251042d541001070250702010110b070300890701031040380c006000811074140400141421500d000c1040c5000e840c400002c485203c14609040350f0741c003000050384401004006030750340340c060f401c100c05542c100f07040e003040243c0100b510307504003030885800f59100080c190108214250b4100d0115080c100391050b0341e0030510f15085c02a0014044129981080c0c0442c0780103803c2c1d4000c0d9070144d0024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 373586151 1250 373584901 373584943
    0x70e07120e030a110c0613031509020a09060f0608071b0c080a050c030705013204030b0411010e0915010507230a150204050603041506050a0b071a010501051b1c1e02 72
    0x66140c00c50707058409c140d4001c1d5074880e00325100680f541d109101c098180c2c0310340401d284d03041c00c8804442c40040e5100100b0803c8000c24400c1c5a500407440c0010741d1103a040e81c0400c0521403d002d84030216a502010980c4607881e444020b0180114031100c06640c104c0640d41c0c000d60f560011500401c215445160703809080a01c5c15141100041821020099003541410580d507500d40360ba080c00c04403425a1444495952a0b0b41c540e44883c1c85030024408950420041c24850740c0002040d000d0511130781403040c0000c0d140d06000700d41e2181e141e02c1009c8010303002c61000401a450301c5441d5001c04440d000d020302c02c51001008540280c406440d0041d11850555540b034031000500e00c9180d08030803070242d8a03540030030240c41c0c40022a01400d107150550303545038814602034200028408011300a81030074401805036a0340142240c504c038101c1d0b281d001c0064086a519400c000641c0409010f044183e509680a2a0004102c460842a4410001403125a128103903141c10040541e05c04950002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 373587401 1250 373586151 373586153
    0x2206170d022d01090309050f180604110705031b07080102031b16020307060509155e0603020909010603020f0d110903070503070e07120e030a110c061303 67
    0x10040001032401d00c510104100c000c960401c1d0f0840700810820340c0051744c0b0a00c10f00031800c2009440c86064802d07540d0302e00c055002c944040c0610001345c892840303581c440240241d280003840555000c59005000d9031780e06c642035840800c3d440d080031b143c4000c50140510000345140107109803486215240c8190074076000307407620310050307034440c0a00c40d900d1488031a024002d030300e040008801902040e110b450b80c07000c0e0340b010010bd0a65403101c0002032041000b94001c0c2014071000c10b00902c07480121127200c071143d00f58242d186168411484a4104450314060b5055030848000080c10340b0000025682529104104c0607480740910310754120b00c2c100010000c051003035006025100303103218101d0800c1810301d20041503c14820002800642c08144249c12740383c14882d940c000c0c0b00c101c0081034001d150002800926600600b9501030180c10542584406211b4200038586809072054a98440345170368041d0115140e07840109481c03180d003000700d2850030300100b10342e41036102c003122101032459 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 373588651 1250 373587401 373587433
    0x3090509090a120908250906060c0b130b040312050a05090c0f0a150306051504050109170304030c03050604060e160306091e120305060303071e022206170d02 69
    0x10a01083c00308410010000354600782488540c80c1001c55800c11602c00c2c030a03801c0302540040503085468600d02e4800c040001d107401c2402c0800c01076101c48611519034076210352486e5100b46150141c1400da0300000c01c400c00d5031003200d4104a180b00d00b01002140c441d100c81c01c0845804640e200c00a50187c1e9507241d0a10346030340d5408503118020306807054140c8401000307002041040741400840c0d100d000038846460051200010703411030301e8901e401d041c1361200081c01521284149800092450b4a5101400c007d004460166402205101c0080c2c0e89103080c82d42d940c821a0141c803044c5c9402d41c4c0701400800410310205141d100d001c040449030454a80000500750000111a00c0c451906441482002c035150f640c03030305004400044200ca000d0b00060140d27003004001e81d01c00d400c20400e25002508010b139018900c850886070b420314240c40d20120315000030400e245a9030980742144641a01400d0b0001c40c01d48800d4081200da80b01d0600b282940d03184101c4429003d604100d03e0f941030400c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 373589901 1250 373588651 373588673
    0x120c0b0a020304020f0310140c0a300516030f0b0a0506090301090203071205101401030809040915230919050a0b010807030b0609040201021c0c140a03090509090a 71
    0x1000405000d2105c03141c100003440d142280d020903114586881902d0008464000003c0c2d2000002d10342d180f5044078007070010076810380d8106900c041840c00002550300481400c07001e000d00002c860030810703424429900360325441600c84640010782400020a01c1c0205800360400000c4d0141403d040117060a0400a403a08480405074140d9604c1007880c025a4080003c800140030707003412440d0201041c10080d090504844900e00c26a08062074101ca0744661000e050440e908030151b292942102000540a006603460140000c40c04016200c040910341c2e000c80814010001c1e101d60750344164a13001980403003100e01d04110303041020b42004105620b01c10070981031017001600e000505a640d0090b00e01e60130380112140350702c40c48082c01000317080403070240c10450807501c0e01800d1510341d000035075807001c2801e03c0700002a24480e400585000c2d0b0100314145034816419581307003060000483e503640320017100f6000600100d400085509009203080d004a0152000d820f4001d141e48130301d03450039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 373591151 1250 373589901 373589903
    0x6091802010e060d140403030b0111070302060f0d020c07170703031b1e0305030f0604110304062406050c010b0603010509040f0503040b0a020c09060621060a09090c03120c0b0a020304 80
    0x1101304034001d03907040309206a141c1200840300f030750140d0415040040c212100001c4450600024100341c1c0380301100014880201e9504550183d030b83c5d1402c4000020703d024424641440c0d078004a0741a004c03182c00705e1640305403000000102c84540e0010141590342a45102c05808210094031385c003011048803054409150245d050842e0151001c0911200d01050003030680009001000348000211040c123102d800c01400c550a20010785080ca4101c243c0c030029100520711903030356881200c02421b514003502100b20749001c01400968503440a03043e40e000c1a0000d4441d4a41011413000d4079142050341e050f200007605d091041d03580c9964003902001d040b0300a6074180700600c0b00041c0030250100900d42c450b5a81c2c041c00b0054606400e00144003c081d20350351044000740410410114110dc540c403001d60211200035581c0c0b04c3c03401150341c400185d003184003142d080002210030300954030440d80849220301c000c540c46608040b400c40b002002c101c0001c00341041c010105590b82d031745402a6400c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 373592401 1250 373591151 373591159
    0x11d0408041a0409060e01233f01020a0c1401020d0c0306090e01090b0c0703030b1003090c140a0e0c1b07080706020f031204030c080a03060906091802010e 68
    0x42a16104410030400e41600403050b5500c0c000f500348000000da02580004281c207070390ba0185541401484020402c50100b050044482c07075002e90000c2e40c403598009007400402c0e00500d02c03141d80038280c2e40c0458041035020035245500008507990103051007182e014000359940e41c10b10380c81c6a5505114a51707404000003141d0f400303001e020080c88035845400c030300401c641c800042c134a1a241044080d00c16001a10040d030f458208000045a0903018503617012a0325101c0715503840c1e00e842c0640052081c00700c4141c01031002d001c06182c0a80551107170a841c0d0003001e280744410399460740340394144100301c10a5042184040100310701020003181c0d030382013090307078588a003400c0c81c2510710840c8580c6a011180907610030741042000e20300c21b00c183c2d409400700740b02414203c804070380c1050b642e03c240c0c1030804210700d51000050030b0512a041031a001c99000303154a5032042c4009004000d0700590041103e0186001c0c00091500701c60300c5080782e82c004510640040580e607030010740d2041441d04d40d02d508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 373593651 1250 373592401 373592407
    0x209010e13050709051005010c03092606010306020903071707090917070c0905010b12060d030c080f0304030e06040815070e0d03020106150804020303030109090302010b1e0108060306011d0408 84
    0xa00b040c00078101400b601e2070005920b19241760003521110b482c4e8812410711040390a0200466070201d8900306a5802c0980d411070641303000e203280441c40c1ea8012401d07150203480008010080582c000f89a1048120200e808160300c07a618000502d17601c40304150340340d00c50300f010041450203822110940f4096200200c61084514510078250301030714040740d5080030f2103420300400340b407480b61a01501074141640d040c201c1c1c0c154411481c48002d40620b01c541c0e01542d140702010f00c201d01c0a9227540c0e000603000e44030080680002202e40040e6012008aa05524001203c1c01d01005440840707841000a029245400390180f07200d03c00506401d00b00550098801c046448043e15018400c2c400d60002031514540888072103d010280020f0080010580501025950000c1924103440b0845000901c54000f1b02d0300340c3c01002007803003040c5c11051480d518401841090902c6507140390a8032185001c0d507580040641365a030034001c3c0f40080e4894658261b016081c9107200c1c1d4041d2040c0c0c00986 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 373594901 1250 373593651 373593653
    0xf060906060b0a03050705090f040b0a08011d0d05033303030309030d050c09061b1609140a090305030114120708030322030e010804081303050c01020c0604030209010e13 74
    0x10384072560840d500e562030014041841e180e00d4820103078000603a28140d0b0600d00e080e030015005c11850142d8902c84c0d0789a442d010b802e0f076100c04119004013000d074006c201d203082c02003105400317424070b40c544075690254815002d405400350007128890b07290074024010303003148220400c00202411135901001c002d03910a411580c0c904000960040d0000f03001980c60b07810f14802c1c5016540c00800a041d00403003881164450b071907540c156950380301c1c3c005076564004041c4100c1707454800445103402c4195100c40b030016041c84603a2102840380104c41107524156036184c095002c1c0c3d4000c12000340090020401003102c0a00c2900d5488065401010800e1008031b903c0034500c0d10341c0d40d0f04804255000003041c40302041c00109048480803a501d43d0100d03c40c50791b203014150700c141604240c148000e43c03001400708445801101d0b50100789200402503141c480c2440d59842c4005c84429004d449040d5480d51b052500100b5034003281c0e40100790400e140e0030031941c226001e40180c103007101c40e5040d0613848 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 373596151 1250 373594901 373594913
    0x9280309061416110f030f0307062004140103050c031911040b0c010e07060801060504090f02070f060603060605060906040902090d020d1b0902040602061305070f0e24010c0f0609 78
    0x40e280364092071001c1507291881c0200145045d000d0300d683e00c268000743d62a158400c0104c140c135500c4c1e8201c04001840d0050380d060049a503071003082c02c07044000c002000720b10406951210802800e01380e0b070401c000daa40c204105032520041d40c16102d44146481000c042d00e410350821104000d20614060500703507500d54415032a0010902015141d440b420911f60f103000400002004000c0c5260501465140010291103849140070b11030900c0d84911100209400540444520f15404400503080c4821420720200500e002e000886802e41000030000302c0c1e10f00b02d402e6030007040c002446c1c10f1400d498404418020342c40102000d0300811220440360260b910603040500d07013409141390980041c45942107502041803900928003070340c41404180001a4000f680030360008400c06030400c001440e08144c0c0c540081940805c580100c440d9004c07601f017441d45a010b0081d05a0b07003030068090302100e030100c900380b440e048950028031500000f801044203005c80134903450042c40300092041c1d481c0c68207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 373597401 1250 373596151 373596187
    0x2202130303050c0f010605011202160c061d0103060f0501030506030a080c0a06060e04030527092802040506030c0a0311040e07110601140d0218092803090614 69
    0x94011810210343c9292030304050140b0200819180001c000942c00c1030300180004100e100c41d07041a5070f01080e4044002c50714120000c5a40c0c010845480060b50f81c14024910690600c00421694000c0107000030b0f540a8000d20058407901c0009100980c140b2004400130007000b4807407075040c0320b01400c000218000f10001c002c0c410010000d00400240c03401d0440c19540c80d80d000306080a0b07014104000301e035010068810944904500d05039610034403007101403035907204440692140c683d00a000a400d8035600d0521000090720040811407000030b016800c0340140d20401d60422420400641126491402060002080d007000074003910302d06000015904141c00410b0140e000c1e0f001d11011540044400e0b0050341a0002054150f0428000d04021100300820a0069106250410455807481d02e0781402140c4403001c4d1045143c00250103956142e0741c16045614410746486040d0b440003820403081c02d0ba015190340f40328601c0c064086404150b0f0000b800e449410070701c042a41c1110305c000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 373598651 1250 373597401 373597403
    0x8070f0201141e0f0402090a020f0c0105100503010b030304030203070603020a1803110f06090d032102070605061c080901180902070506011701022104050a0f050303070314010522021303 81
    0x3c0c040070300c800d0443c8500c1c0c03950054180c2d078084030201d04000c010382e2844d11096104121807809600d90000a8804826000d02e100104141d42843d041000404500402d0401c039901140240038080f440c0050607201d10640c0406900b50708907040070f005150180d0018080050b9501d0620703c1e404003410b4403214102240c008a440704401500070000385001e500c541400035044814500c0d141d01c2c000024513849501100405101251b80c85041c8112200d5070220000c01d81c80065645600520f0888d00900e012240f1500c101d2081041801400da5001071008160b4003a030b81c141f40102031401502d6401007402c240104821700080440c4407a40c030700182c1401e81c46400103283e2541003041420310001c400301510800c0c3c0c41404071100111420302150261030708041021400d0702d85d41000f504107d03030300102600000d0303110b0b50102002000001540b18043e60340e01044136040020b8840b05000003031140c03c0d4840e1201d0801248503001007584441c1065040340141390050101f60305801c01c2d41640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 373599901 1250 373598651 373598671
    0x2031b030403120c0f0f030e0c0d080c0d140307030b0a050a08030912030a0f030209040f0513050c01033612260906041e150b030d0201060608070f020114 67
    0x280e000d0801c0740c640120760f101e1210f03040c0310b030302e058460400424402d44140f07640105a00c8d0100d0051081003405501c020f003070060080380d8520114103264105034007002a00410340b0070000c07441c0c4010320030030f5510444001031000034515120301030100c014050300c80070207504c5042d0080000300365403695092401000142d01460b102c600341d504000c240d0805643c00c10440d0001c0203251301c20342d401812402d02c8074050400586820318000428010068800d180750000d00c0d0409004d03a8054403d980001e040c8509c003112080000c1d84011003d59940c000e0000340c4200080b90700401e41c080000d0121011a0740c150203060f040b8a131109042c1e040034130403407404207554515214400c2e800129002c1507030003813988103c990503e014080c0e40c2d941c004201030030b6591500741c0c107a4204601c950741103019401c64005003d08112102d12402006182c2d00c452280c4200b0030003a00b80e034018005d40c402c54a240c1c480c0c032425503600c00182c4192a81c0c034503020855594502a4140030300341e900d054050201c0745 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 373601151 1250 373599901 373599917
    0x90302150c1f1a01091a0d020a0c15090803010b030c130e01080709051509250302090405060d030806040b0a17030a080106180308071403030a0b19060e0402031b030403 73
    0x402007281c801c07038040703100746011040b0060b050740c1001741801128002d405a00b108802c03285a43c051780204600344420500014281d0401d580c00075400510074040c1c881c080302c0380701030b441c000225580c526000b0a40c080c10b200420286200b0030186d0340c0400440000d5140c030429504e8540c101e8016005440241313814030040c130440804000080140c448500100902d051005280000504032080241310340c440c0000900064000c181400449400000040310080725010140180d00b00d4054240280c0c50302001458626113003180c0d41509405845039400d94440c0c034148009131100c440001d8018245000c001a80004130b155004c0c405c54203005161070300c1402800801d040d8060380510200706250300c0c1d050940302c1a43c14641102da1050890303660348090b00c1d15001890043c061000c44e40170200401082560766084441185000c40e501180040303080c4e40e80c420a400b1713000700700001f1242c0da1540c1e00d0307040035801560000c2c0700031980d01071710350254010700d450341c811501180095064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 373602401 1250 373601151 373601203
    0x409140c04020901120b0a0e040b06010e040c0c020d021c0b040b0702010504030f051c1418030c07090b13180606120f032f0d090b0307090302150c 64
    0x140840350a280c0100d6095291000070340000344410802010000816503904070025199103500340c40e002800850700350b0301103180034100048140340445603140418080891050743d442c0c24410300d48030680076101d2598a803040e8003403010082260100300e8000000d000c4080c0300c4640c4070b0b611040f1901c101c00c0da45491415240c089460b010140810382560f050900740400260400700c201e25080492801e6a107070008210010854402c60303034030210040c902804419203800c203a0700184941040003010803071089552066689202e0442c56440a030040c0000384402d441d15040a1190704004001c0c41c81080e18019110840701c9009040214044581c24001040101d004002c014107040108205038082d51300e50a440040d07000700203041001d148180c1c60703281180020752107000031681300c19024101002e51680d4034101d85910750040386101900051100e48c800440744120265982e00105525581c20321204d0f50500034440750303c44d410702214000140030490380400c81001c02100c0d08286031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 373603651 1250 373602401 373602403
    0x9020c070b03010b070807170412110a060816020109050102030c0909161b1406010305061902130b0c0718022a0a02120708120a0306051215060a0302040914 68
    0x8580c1c4404500780d42800100001880c0d1000e480240341c000c4000743c1e0341d682601d82407000e0402c030410007200e05400309000c964031030f601011100341071060b1024030b002000c072020407500b1600c0340b1074000061414000585450f129110b1408030141500011580c80003658445007a030700200d50a03011a82e0100b0500355030320b4030440c010f0b003100e00c0708088202841540c100500c880caa030464079041c01122a11403041240044010175281c141c241601c41d507513100d1901940300c10b0f081e1041707160811a4030b24402c0c1d6041030f108440c040d1101e151a0f18240b40b601c50010b202e074101c04072144442c0210080011108a030f00c50b403000c07a480500d40180c0d00c507280740c424681100c9020080d0b44068602042000040000130309486068044403540d2420300b0132000246000c00940105025024a40c601e40511010030302500c884046034406018068a6406008800c402800c4a20103030717014120b189001c01d0070f102c80f1a004030740540a14241070722900440c0035107802032411a0410354880003040c081d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 373604901 1250 373603651 373603663
    0x20a02040e101b021216140a020102011112060f28030c0f05010f080c0f070b0907080a030503190f020a0c1203020f1b2401080f07050904030e01030f020409020c 70
    0x50b0710f042d9081540c10b400e500a50b510310504900b4a94003000031440414400400c130304d0412a44104840d0750458021074150326094520001c0780503600380042caa8046540e0b1007503e03401204050000415a990340420008510781c0780c03816084104000f50040d0700d0812445c200500300080c1404035064554a00320544a0250380b250b0766954803524240a41d030b0744900e2a403480500d602c3d110741141c48034800100c0314401e03002c105580b40c0b4000307070040c05c110060594030301c0342d6982c41c1a00c0000e5a1090f03101d448841902e002070009a0070030001e03d00d00701008180040c11b0410754000b5000320510b1019080740c1c4568006804540107400490802003503042aa00c412428507095003065252114250f56000b005412a510140b41c40c140d2100841082503d0603104004e4009400b040320703000010f03029500380201c1a01d80a0610070803060900000c503807084650141409016603210703182215040b000c542031a0403d40c031005c130840342d08050700141c0060092031130300594500256503000d103080c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 373606151 1250 373604901 373604921
    0x61a18041707080f030709050a090b01030f06081e030730031103070509030a0c03210801050607020d110a03030809070e13020f130e03130902121501020a02040e10 71
    0x50400c00044000642c020103440740b91500412135500e986944000341e4003407540790001c580100c812280065220225008032251240c00c0c0c0313003003101060b0304400c0010344041e40a512000e074400c800c2c201c10001030b41288504104004103581c02c18401e0780d02c41003105042c24080881d04582d001c010000d03045640c0080000c0050709040041000d4010240005c0c0401442c501c10721402141e030b181551020701003603807452380c4071481c0c2c000c0c0c076100c0c0b525002e009a80d18100007201d00d98481a10054056400715059860084c4864242000c030317400c000c0c12042c241021100c0024500e9480780613120180380001840c0f0a80301c42e0058904130100300c2c0f5003a06540068405584441403110000c0c158803950000e03034043d95030329141e1501201040110100f0141e241005103484e10614440718044050300c9103020440702c40d944141e131102081c081e40516140c51100841600100b240d104441c80d141800300418016120421000d40000c1c0888160050860310354104110250100e2807c4c403905440c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 373607401 1250 373606151 373606193
    0x1e0b07050715020615090601030609051305011409060604050a1d0f0d0c03050d020a020f0f0705010207061716020c03100504060509030301030b0109150b0409020c0c06090d061a1804 79
    0x85e00d0072022440e00f80c24040d800c00c1c0600f03564400300c2d1243e40710341c01c03650141c800d046040c0b2142c240702034520700c800d444403020f8030b05518000514044080c146000b900502d140300080c1516103e0004020050038050220640d040e43ca41030f44004031000c0010300c04041c583c00182102e0f0805041542c24141020000c0b800c0054191030031380040e4111068a03e21951180016181d4025510513442c020b640d114810076441015061f40001c0c0c0c0014000c801e80d1000c2c1d0075680d41030740ea1002941c011005a0780a10240302800000300200558000d0003282509031045800c55451140402e041448a400034001152900104400d1040340c4c09080d4102003940005c51a41d03245840e110149117060240603502e42c0c403900c8030b107100c1c010440408042c000801c45680d4403076444000d60029486442e00382c8090042e4140e5030500e203001c0741911045000070b491005a823003181c1e01d8100a003c0c03122584003c0c020107059030303866101c0745281c000300204403000c88000d0910f42810150b0b00a0541d020700b039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 373608651 1250 373607401 373607413
    0x140118060f0f09050606130b030a150b07030f1205010f0e09060106020c010809011b0507060e0109020a062618060f04080d0b1206072a05071e0b0705071502 68
    0x50121140c441d070116003d01c080041c00703845140008a81d486240c0f403640380451000b0010421003050306c000d40c018120070310200654190026192000f00c11841200307101c42080c4010001b09000e080e00290700c02c05443d00003091342c800107002040720b0003a0414483d00080341001d004640024441c3e03504201070800400c200d40c50084000c0da503c0460f68520304101100f40820981c640075040440090a40c1c1e0401501400000004203d41c100210684250b814403441d88440c18044c42034484107500a0480120301d0700b0000d05035011320710000c0c46010740441400480c1c03e060180c50301c0f070050503085208010354100f01e501c14607040015220000182800090000207040c071012100380b000550700118044003120000303090030340005801146030086004010409070300600c8003d030014010f04280d000244400c4000481d141d14000911503407125a0500400c4a44424010000540d440d0001d507582c80301c0071401135803c03c0300f0884080d445400180302c4960320b1428841c5240240c401006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 373609901 1250 373608651 373608659
    0x90605040e150a0e0c12070c0209060415090504060f1410030b04020a180506100e0105040b0c160906030201080c0315150d0c090f0e0702071701140118060f 68
    0x41c0780601034003808070240301c048159043d4840003064401000b841e48141c50902d0b111101c980164003d50801404444441c002061140152000d00c2c40c607801a102d50503581d52281440000e000115240b0450004441c0000d000001d038044e0a00c6a1f202e0f8502003100a1460320320b030306075072402000c0c00ac00720b404801c0002a02c3c0c10b611610849810424900c3c141e180c0e400410254040b603003003440c0e5500c3d040b424078103031074107900018092482560031a1103000515811039129071660b088a0025808020820110010b507014201c82004001954503841d0f00018180c1c21a4055102c0ca48c2c0f140c880100b0410756800002007503014401e00b0b065407540c6401d80050001032010030071644038030200701c0011900ea40b91001d840d02246081000c210f034401409000d402c10b0307110b20658036032000910010883da500c031150755009030815002440e050b4140030020240d1203500c01c0010b0299a1203806a00b80c03080201d03481e00074441d0400b01c4440c10441d81c01c050075124641c004610301106170000300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 373611151 1250 373609901 373609919
    0x1111306032a050d02211501021f06050d030f0e0102060601170a0b0918070b2503050c0102040608010602010f0603080f130509040507170a0309060c0204090b0a050709060504 76
    0x42c0140704810b00d01c09814903100302c2682c02d40203003131800d01003e101007100d642155500700c90b00c41d03145070000303200840c0d0b4617450800d0f0b207207032a048400e0044e0000d03440341c1c03014602085182042058014040787c030070384400100310003200b00c0509a002030004400808000c0d04a440e01d081c4410030320191806d4504000007a142072000c2c2030300056041c0200003d1003040700380d8086650324100900a52440c1022003191341801d10720850411140616000003511280007000c441000480d00c00001c0c9101260400710786907820b04c40d0640c144481008080e403074503404c0c401080584032548508585504080c002802c540c006401004079615150081c8046402c080c00d50707170b03403050b0040d449955000c42d4100d040201d100340e002030340001c10f03001444104000840d004c0240c600d61001510700c060255490795840c5042c01d00070f00403c406901c2804030500c00e60610007045e0018001141d01e00c01da43c2c4660110504940284807543d0b0740003841925036128030781c031000340550b20300035003020b01b045501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 373612401 1250 373611151 373611191
    0x106080705030a0f0e031c02040317090a12200118030605060a03051504062306011d09070305040507120c050f0a030b010e101a030a1d0111130603 64
    0x240c081c4000030000561078001a08a03c03001c1038004010b010541000501503541c0e0024003105445c01d021418074940c07042c40c0c2c03082e9401c6a4000700b41444018440b00c141c040c50340000d0300c440e0030041081020071001664aa018a02c0348a102c50b800c1d601c0c0030304003510000030400c441504002d061004003515050082d100404c0d01d40103140040e00d515500001241080d050744010824002c030f00f607607141e00300948032462069018880c14440c192140d020404850001c510000d58059941d000c203103103500c58045101c20b400701d10501109024000c0c0014090300c0220741500c0000d403194204010810144400d1000b40032409900700b01c0100c5e6a20100180c01c94010180141c440e40016422950307441859001544c001c1801040f0b07586401321640607240c100e1700746440e0007084c5400100c0e448815541445404501e00c21400e54465008080240909440441c007100880b14001750b8108203200e4400c00e101c40350302e0703641d480f417410a80e03076800005503000d1030038103217450305410401d0b10910740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 373613651 1250 373612401 373612411
    0x2703120609130321061505030f0c0310060c0201020304032102120c0a03030905160b370f0315090902010e030102090319141501052e121407030203040c0608010608 71
    0x1300d901c5501101800c0002071841d035001d10b07641c0c400042d41d101d503690040002d6000f002041241315484ea07608400c0c0209200c1a10002410706200c0c60402001d03203d000803445051051060304c2c5400c1e41c940f651455605070107000a079540348003400f150b0b80d81d010030441c4101d0105c2692582442c1a00c0d10140d1036000440020b01850380350201d2008001003400102d00071084506d190402079100c14429059030004004620307180c00620311540d0480d50000e504600906000c1801010381c0c1b500c00840392000b07421101c209054603501d910031200c03400f90f074400140030117030000591600300707000041c40342c0c212400f0140a43d00c1001241681e440c0407803c1003801c0403802003036001c103150b89002584428008051340c1c05028400c4100d02d000b50b0f0007046412541d083700c258904801e00040078000d540e010b00782a02c088203d41c1206ca0b032a0144013011890b03038000b000011b440c41c5107448449015011545100043e43c0001000104007656080c24050140792a10261540c18800060001c0b02d001d0f01e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 373614901 1250 373613651 373613687
    0x31d04060608011202041808040503060718090c1112030a0c03060506071e0f05060402121f2309070302010908030a02060109020f04090e160b0901020627031206091303 73
    0x44c000c0190740f1360707410001c4130200c3c68419802c1c4045508000d07140f07800501078140f2034002d84020800551107600c0e0301030b603040c0c000b0a6022071440c000e101c0d0000d02183d00300405110703d24000e1f8481c1042441a030980c0d2140c024129568a46515514100c032050f8800100b4145080380608c042d48840e0241c50070309a00014201380c8070b51105031800340b8800c5440041c01480700c149070030100480869524003a5100740c2d80025259140d0513001e86403510ae00001c0211111f1210000107900340344c106480700d480f1501054100741025440041c3c0b2801118103440701c2d03114000800455034002004401007036000003031820810203e00003911488184246005a80c020a0840c84414400121b4006000c0d240c4104911110100c4036900e074070f0b030b02401d40b2820608490024518201408072038001c2d0052f4040c00c4141d03900103100780311814180e800030032210714084568040000f00001c12541040c03168059051420104202a0032401040d17070318045c06001452001a401042440c524540f0030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 373616151 1250 373614901 373614929
    0x7050607060b0603190524150d020d391409120d0807090f170f010c120b0312090105180423061207030b180109031d0406060801 56
    0x1041041c0075007115240780342d01c52000014050000d002c8640d0003031242588105001301c0d50b814014840c401010301244400042d486c240c040c480c6841c0c0c0306d2040551407010325030b08018a80c10808200d80000b4208600195a18402d1030b40e45040c0220009403440da1a80d1000c03c40030a280d49854803c40e50408244508404a03200d042586825200c0002000d03014000303514050070707200e9444c400800448045078481010515651080745003d041c0c3ea1000d013940d0300750f0b240803c8a01101001c51410050f402202842c03000d0701c500b80101c60021141307903152020802d840b9800d10855541001082c0b01ea4405203046000d42e1800d400d4410a61090801907211001c44c101e8007441d0845c5800c4690151924040000900b440d42e2181020602a40d4050981d6564024490030031084a0310f0000c0d60700030032040000580740c100c80c0745c0c01460203010303081035100c100030389003961050300b400c030f010400c400d03005070802040003a034a00703030402110180b01b06031030804050031054044c00341aa822400d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 373617401 1250 373616151 373616153
    0x3081c020705030d05070e09010b0f0702040209030d090f0602010c081803070609051b0d0f0602070f17040e150d031209081804061212030906090b070305010303090f0807050607 77
    0x3581540e03040380e004001c0c2d80d541c01c0468449030040070110f6003200441c2e00c00c62188258182088800c0c10b890243c40400e1600038890740000c07040d044050200d82c4503400300000790700c60714188807180454086464090506003001101d0030040701e280c200030300f1a8500360300150880c2d03002c0d1a4030b4000300410004018032100c41030720f5056100c0c0c0003010b802e990421840104000d00000e41901280c1c452009000c10298801000107658000d000502400e20715406007000c10f90036070060940381d10612901e00190307a50769403050b1034845a00c840091010120702086560358502002c0c0d07111110000c0c03820003000c0080000c000848061028082208810210300c81c00201e62000300250b400c01999a2a400d0300614114101d800160250103079040c043d0004000348024042110158030800c00240700503d00c5080b4010608039400f980c0f8191110000c3c0003040418a20750b01510181e035001c07a496040d400e016044102552000065491441d000c100d0080041501c1c42964811120340c0d03959062 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 373618651 1250 373617401 373617457
    0x90f06170c1909091407050d0209151c0f061d1c050f18040606021c0503061504080c090736050303041203020705150d0e07090c02100b03070308 63
    0xe15000103c41516001d141410310204001e040055a00f20301100c42003501c1d80c080c001d02c400d0036840250880d4840c008540d21200d074281c805161040600402480c0d184104003d10010790100183c40241c3e00f401043c0501c0a1801400070380130349009180c040e030092545265860b900701c85a04075120b88140350b480d495100750121071007000441981510307914512800c084032200982454441c910302072002503800e00218262508804250888a002e41070230825160780e44000c105540c03010030000e1003401c0b0705008020b000038102d00341c001d2907071a40000030300c40780f90000b4000c1c8043c0704c0804600382ca401c42c0c1304160380d44000c50000c00c2050301c007075003d40341c0f40301034681140e80e0601012030041403500c01e5001041941d40251708494486640e10280b060205400010700001d40080088009000310381d0003422055107210112406540da5445000c11138090b0b112050068108651a01c04240940a40800c01408030041d1210354a103544200c0d0500c9240e184401e114003000c411507281030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 373619901 1250 373618651 373618699
    0x30c090103051506030a0e0f0a031b030504050a030f1e02031009020d140a0312050601080406020a11100203010906051507020f01170c040603050c03150f0d020604090f06170c 76
    0x220103001a501c900b010104180600400f20101031030748140702038408d11380e0b00080c00724040c6415440d150b175014070714407044020a524420583c24468100030004040e19076140100055006100c0040c2508540c90280c841a80d01c80c032070b0602d4911500c914026941c0031807a0b603e81030142034005940041c500c0440c0045140c06000703414040c10300b80600150502040204142d84070b81e0399590b1442001400340f045071f40540d00c203400114040006070019240b6802030003881401d040800200c04012411480d2070281204190b40c15004401006009102e00402000c2d00d1300715000f12001e0b051800491207400342c003202a00c141405580e031310090340907644181410490500414081c6008821920385500500c511070001e487d000001d103005002e007041c0c0b405004810303050f650548100341040841c9203003000700d40d8410018040c03c1c2c01a03682d900240000c2088880114003400300743c082e182211029800510509460301c802c2c0d580483c00309801030005002c48102034540400040c6140c544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 373621151 1250 373619901 373619941
    0x9090a18020a0b0705280f0206070510060603060f0e1f0509070201021c11090405070e030f0a0204051018020313140c040b01020d02030403140a0804030f120302030c09010305 76
    0x3800ba00740114007100410000c040c4140a941121941c0040944500820301c82040101da003132001d1003a80700150b140120b4280d450300003800203007403400c1921400d04140c00303215000491959000b04102c0c00f80c06009100082c580c00003e0402d00e49411044510420020401e510314103e010280952882c5818218007404010b005003242d464035002c041d00030340c0207001e810281c0133403402a42d04103486014030200c955071280300c3d0341030191032018400548400b0300000140030611078040c05641302005418400c0032070f80300404103201d8600601c0103c0d4405005541104c0d03080744203011100e00205d145080c2c4810403801070b40c994941c019102d0030f809030b650041250198000c901c0d0300c0303000003456500c082401c55080012850050040e69500392a0182c4409030704240700c100007060b5a1f0b0b070105403c503204c4050720444030b150f40c1c901c001940140c1040b0380c071608507100c01c2c042c00551155a20307080d41c00d0408520314240340c14101440c1c0070b4550301c0c90425454400040c0703011102d6a80310004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 373622401 1250 373621151 373621159
    0x270c09120f0803280c0507140708011506121103040f11060d0902031e1903020705090c0a020f0102070218091e010509010f0b0603011a040b04080c0a090209090a1802 72
    0x906000301042c550340031441384144550590302e004082c02e02c191090015080168846070702d001c40f603590740310f070800140054500310b005034080091180028000c00d500320038100700c81c0303005c5c13070401101802a0410703500e5240b26a10700403240018011010460344c019800880e0183c154816142c40c0102d0841c1c402c0b03054000a001c60400d100c0c1d2200d40018a03114402c409461807100d0907074070036210f030801d22a00c1c00305134031049105140e00c5885401410490007031040c0c405064503900411035084081c5d5405940840010b051400c1990501880b4400c01d5007000a504e0022582c00043c5800b000c140c45003103805a240120f40f050390100b0441c5601040c0007440001d8454603000d40d1f0013000e08580c045e40c21750820580710108201071258107940070307000b42094110307400c02485201c1803c080e100031031280c20070440480d052503c507020340001d000980081c13072181c4102003032050f08050755028207000c0d4018841480301f03035180360042e44d1100c02c202e800925028810300d030a42c0c07854058030107908 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 373623651 1250 373622401 373622407
    0x1142118030c0106031a0f0f0603070b03150103060f0b0f0a0314160801350a0b0c040302040b0607030c06150b07150506090108100908090a270c09120f08 67
    0x2451040d0401c20031170380281e000d250820b8080e0000c2c9080e1804175003241c40310b00c0210020708010030310711040c1d400c03520140499091944400d014445a40165281d610007480700300030308450341e450301480001e890240e13451008a49041401406070044100c0061034207008103e5240413803003540000c1c0f8121700b400f500c4285007407a103952040d58068070340100c0048c001d81c0020403481c0d898886214842422100024400d60914103a5900b1b03480c560300f4800303806905210b6010992011f50640141c1800150a036141d14520400c400c48800d200400d000f14001d0000300c011980000f02c031400381e504108003049940002826198104207a00820501e0202050410611030980c0151122240001c030030420307915103904102c03082c1c1c800d00c00e580c400d500c100c00001b0382d809103400c0304442c28464685c00b403d02004038000b503410007158000188865070000030b5140c925a441c000c00aa800d0300d103040104d04812400206915114080c00e035900560824031000c1024442c00012074030b8000d072456403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 373624901 1250 373623651 373623667
    0xf06090b01060c1a01050a062006331003020315131e0506060f0705030f0415080a0504200303040902070b1006020705030a02040f0b1306050114211803 66
    0xd0050040c0c243c1d400301342d582d911601e00001d1200c46041c0e81000b024508079901d03052080740c542e800c810a04803e00d50400c84203d1031407080154034020440c001e066002a140c0083c011004202212640061641c107980c5850745d40f6400304600c0340780002e01d00940d0b0399940302c00b00205448101031140c0c1080901a1034540500030303030f000d41c0500b03404c0b02036a6103411184a400342034440640f0f01d01e0b4002410400c40300e00c0c004400003000e01c28414001c1c1c1c3c4c01c040341942c422600390082e62001c0380340d80d981c9005200c819441a41da40d401030117864200402e0429490301c082450402640c244811b01d4046e01055603030b4100b09443c004c2031040010340d0b880140c1d2030540740b08a000d40720540301701202500030400d0b90012845105981000e0020329aa004039000c0202605145080042186c2d0766258080c03c0d0300ca158075510000a10740001c5426450980010412007003900000c52030300c0140500d10140b080c070041c241440440c060305050740d44075000f03402c5000f0700c00010400103203c009100170b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 373626151 1250 373624901 373624907
    0xc050c090a0203070e01030504020604050103054618120309080f0c1905060f0a020d09050c0f0a030b1512060f0f1b030609091009030c0b060a0e040f06090b0106 70
    0xb51103404c865540c0403448484100542c1682d20030b840003903020a05003c14005944682e102c181c1c4580018a480c0b041c1d1222008903c41405000740e030180258118502d10700076000c11032608120344010310400c042c180c4940108040113030381900426003070140340000c4500d0311a400402107190803040999982c81c190b82c003450304d5030003410300041d240030f20440f05c20148000d601c0c2705141d0307400c40040d040c199030f003121080403640b0040040d99590741c2072141228600951203091a298401c0f0003c280c80030808081100720340900f4510340c0b088082840134030025045540c500d0700511140e00411580e0807960010341c2003443c1030801c440502c605020404c61000321400a4040c00603030000f40c40c2600c0d146a801c900041e003039003075403c0c41410030100740359050020102e81e200e0a10700544a02c2614a20700405885050b8002e030002020710554100740110340745d1a681010080b5484040245413801c4400021380040002e07211802c103002010070710001e508075000e403941c0030005070701340c0d030711f40e2406 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 373627401 1250 373626151 373626157
    0x1119030207021206070804080a020a12030f05010e07020c0405060a0e0f01030b060102030310030f210f0e0d0f030c0f060606030c030b0d032007030c08031e04060f0c050c090a02 77
    0xd83c4038401c8000c0d0542444000716a190203418241e98441c0681d03195100c030380701c56200d59140c80440c03046404841c04030b22041c0c12807d6000311035401107000700071103000800391031b01038101462a00c1c03281c0501400303540000d0940380362030701610003103820b50f585000241a1942d60344607032140500300b8100145044415540c60603288103854008240d01c0e20001280d59000840c0c0c10800d8072482c49062001c00d100c0048816504d01c110301c011007201a03080b03a00265241e50302020042801c1c41c1030140fa403500003641840415060301d8000c03000c0b050b9100d91408540840b0082d003070000e0310384140e00f071140084016241540140b024005030740e171020001c00801200b80c908000a162050048803803034400100341c0155090342d43d4140711400103842e004602c2821100d01741620810b0000000504560b030840000d18400000d1610b070172040113240d03c0090608030300040703802d00300418415242c0002ea4011908010b00d0941e1188000d4500f00749880c8040c07031a07903408031a0744100000101e181e001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 373628651 1250 373627401 373627403
    0xf150616050f0a030f090905010b0702040203042604090c0c0b1b07080c0d0305010b18060307052115030628061d04110d0b130309050d08070501110903030d1119030207 73
    0xa03540301b0654a160b940c0488500380501a09403c040255802610700303900590f42140c011145400003404082c12100030804600301090400804a403c00c000c00e898407500d0b03216107482c144045180c040d07560b04079041c40000c00441d0b48260400d140482401c199003605e155a9101c00c1240d80c90310380214056072514428500000070741083c0020881040c40c405448070840349066464100c6072034070801c00d880d00020034080070010280044c07a9101c1e00712174410003403c1d000781582e00740d041000f0044211102208150f001e40e0000080c420b05801c40e0040e03030109603000180703403c507040d5040c175400584890f45c09540000c1d40646880c40901d692680c99009a11031042d0b0075440300080280a0302601c51b0038050500003000c40014610441005d202d51191311a01c2d1a151a0b51150002114404401021f81c1c071703404003081b001d041150910410702808060100700c0d0404001c00c0010359607104074012105500c1d1a2691049903008080948070620844481c0000080b11218024000d42140c0741c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 373629901 1250 373628651 373628657
    0x40f0b15041a04060e0d03183309090905160602030901020705030c0d02130e0307030f11070302090411030f070b0705070906080a021509180f150616050f0a030f 70
    0xc94034070891039003250129010742e260b20701c084202c001000046d001d1018154107000d6400709454410280b424000060901c01c01040180d050500100b00c1825410324070b40e001c1070b0600504c002c00c50b045620503045414006c4085400411841c2c403c2c18140031285202c0c80c228480d03800300c3c0440d0084040c05c0f54210a030b00700e8200c2d0340c0d82d0301055a10303401c5032007081c0c028030800250340c00740c1000d8840701e21980039a40301054400c3c04091480c6980e00c240390640000b040d12021070300c01035001c1100c500c15010140203008580c00e507000034000d07000140c80100602d2600c0c01c1c1802d513032400c4c06845610041c01080c0c40040703030b032003024842581c000c2108607428000c40c440442d02075140d106420944000d48010f01104d00380350b00b80a04a0301e01c50a0000b906402c0c0030a503543c0d80ca030070018686103d280496462402c1c500c1114091080141144c0000d01014a0214690700c818054606500e90625090000e80280c10010304010100c00301c0381c410300540e4964010705400201c41a00c0c480700d40c1e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 373631151 1250 373629901 373629929
    0x1050f1501080606030a021b16261902030f070f050109080115050405041502031e01090902100503100e09031e0c100207060e0307060f0501140d02040f0b1504 69
    0x401142d2422040329903540c4000188041410407010703a0152052640a038040d0003605400984d045c904003030903813024000207081000f801404032140c070f410107a81c04451000c180f45038401403551140c025840c2680007004040003501990780401c00742180d041030b44180c0d031a1903250410000f18003280d00070503010942000000585280500c0303001800c66603010200f08440c14201080080c000c0500180c4020b95450b002496001d1130388011030007a95041c40e503003071500c803000c04c102981d4016400358130654034005910000d80c44605a021282085152041c1d40b56921002d4100060240e000729010100340c0c410000c0c00800000145002d0828040480320880903090030406440b5100e080d6649402c22522203010000e02d80280c40341030f114004c085055007010031800d00d141c000354001d07600c4035110b4030100d0081d071180c07240d035015056400107114041c1803600461880c040c24007009010342d50b01c042040c200c03034060f40480f005800c000c14002004403003c203420802e80040c014011401008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 373632401 1250 373631151 373631191
    0x90613050901060c02010215130c060503101703120402010302040b0409020903010b03061b16082d03012102030307050a2f090601110106080105070507050111040e040b090109020301050f 81
    0x1c03400b0b00c1e00036174141d00030402960b170603204040300e81d0060305094003601010000b0b0f0000703081c03d00038800f5180560f181130b180c0c41c0c000340054461207154000c0c480c5008148011048260100850f40d03134000c562a181d405440b02c1c80124000c1c0320310f6202c00000d20000c43c0104c0c1d00c11094000340f01c440700840083c414a215038040584a550540b02101a05a0388420704441da4a002c054400d40e4940c40c2030300d05400841c3c54152156000e11100100710310000400e00440100820300c481c1703800a2003c06065606000001801040707d40358080304a1101c0c481800b10b503010401c850006130711400ba240380c40a246481e01c00f29440030411082c00e4403808110528080c00807070000003a00050107118240c98110041d601400703e00000c084a54131010040f4002c1c000740102c9010385401ea441136951032590400d203007140e8082c020500c80d03d800304410007860500c44c01d6641c2180c6c000000d002c4035102d00300381600518010b44000d406508110800075002c10f0103d6107803107044881c03109801c100c3c2d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 373633651 1250 373632401 373632407
    0x5030d091704051c0503071a070f090308160c0906090903140306030303060409060f0c0e21030403061805060f061e010c08210a060f050d050304060c060209061305090106 74
    0x2e5005040d000400c1c21000300312059070103903604015025506a03407400c08a0b866040003000c20404400d41900a4020300c5040b65200c2144c914403003a628152500b00c0c2103030f440c40c3d42e500c5188007030710031113038004150317010320825160800051005010812401d0f82d81c1103584040e1500ea8800c0e004103045800000c451042d00044a2040703100170081c500c0c0d581c81000b084014004c2440c00d60311250b541c80c1c1012043c20911036031003426419120b0301d10a009010402c10a400503640b030382c0c0d904001040780c00003d14004291010740e40d01007030100d482c04c0030f81c8102154800b06140581681b051009015001344007407081c23030142d5070076110708400101e46c0209003c0010180c1c41d580c005407040800c9400300e0115409050f040c40c1800581749000c4841d0311514041c3c0081e04c0501c419944ca20701045650581031a0400804003a604501c3c140c1641d00c846849000c4e5100d00414030580b00d5800c030070050710358100e401052000f017001d5110009040314480340701140c0036940c0603000c01400491a680 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 373634901 1250 373633651 373633657
    0x1d040c09092c0f06010e070e03010c0306050f0402121303140d0b03240a0504110315060301050108010513030f030f0606030902030f01020328110a110111070c03030e010c05030d0917 79
    0x410b0080a84c0d03481c04292450b8000d00400610801a00340d0805c4d0b1255000c0c000c0411150003580c0100c0c2003070506040003c0101602c2190788120702c10482c80030602e1401c640103901c045039081d21004131042d0f04050341c138401402d895007209100000c510902c00d0b4568040c0340120015012075400c07100212580711419500010161041960000115900b140740c11403a880b502c507412200384000c10f900402d240c01c1169030085125228802002401d041c00d10400d8010031050000340032a04000d1b400e01181403000e28044c08008114000c2c0340514041d070004551005030800401c4800e6907840c0040c024a07d5003001c0307103c0d025030105000001c1c014000d81e40500100039403090415149480c090709180440980b084007a19600c02d84071000900001e400d250940da12030240340b0a030b460b8a507003150304400c0311a4103800244500000301c2c3c000300d00001a2a41401c01c0c402000d540d80040e2810480720038020030b1840006100341840b007140e088120071621900512000c05800c20040710140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 373636151 1250 373634901 373634923
    0x9030c05060a0204140603060103060503060118140c1c0b1c0605100807050d02010905040f090c120308071b050a051014011208070309030f0605060108071d040c09092c 73
    0x2c00380385d00c01070f0603180040c01150881e005040c005099590b0b900441d003088426030044c2c5513014503600b113506580c49409091002034203501c401070340340340101d200754603802590552442c3c40c3c0d40303210580321480560301160030410024803800c0010381c25400042020340800d1308980a50910303001c0740d820301012903c0d4042d034120700050710029043c102440120740e0320360000e074100900c1190028264455205116100c0d812200201c0c1070603482c180390807810b20310780c03040d0101521a204903011031303802511590841214506018a828607984001041c45001c801a2441c06010340641c2000302c001500d0750207454050382071000c01c80d0805e038191507010074070814500901545448000419003401401500d20074207111010527126212495492a800340c202d40066460303080c0300c010741e000f0181691080c41c2d490f107081d18620880c0319429409001e078006014a0f1204c0803200154090080d950103414031b150308108454003124012080d9400c14081c0c3c40441444140707039400040420006589 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 373637401 1250 373636151 373636169
    0x702010903141501090510121505060d02040e16080d0203041517040c1406030705071b18022a121c02180f0405150d080d09030c05060a0204 61
    0x414035648401c800005854460300303032030042030240007903c80c48000c0d26010340f01103400060185010907011300c01180075000314452050a054003800a5000c1c40034000403134903e000840d050300d5103000b0914003001c1c884000c0d031090621900c2040c2490028801c0d213003004d02e00c80c100c125503840030620340b42e0311700038501c0b8010b03001040305000f800c80304001540000344070b00d00310f180320f1a604000a001d281c2607400703c1d6143d640341010001c403090744079004441c2000721401e030f10358100002c02414900c1041001860440c2251186a000c00d071007035100300031714032428800c440b1412441c424009502c1400492030321107985902c6400a10071060041900c00718500600c4400d070a84d10001440c0c100c451026002c01040e00c100084403103a0010340070b502249150241206600c03010007130802081450171740214540010800ac1c01c1ba20360314505106800d44041c681c80a9038200000f0a124080307032158900d0418a00304200740d400380c1c42907036480c01103094443c5c81c0c8540220401380d105500c200420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 373638651 1250 373637401 373637417
    0x50406060e0d0c0e100e07050a0504140a030203030a050705010e0a2f150c0d0e0114090103090f0506060306070f0c0204052d0a06050105130603020901050c071514070201 74
    0x60341010824a54928010403c4401a6503211104140d40034112454038a0360301000013003026808034000a6041045410540c1c00c042a20000803d07a0280d8800c1c00c49058540c074100c0d6803501c400284501031a00a07040d203a03100c40740c1a0151031a03000300b030100ca0b04d44ca4050400d039150404035050210319032110183c041b581401c0c074514103840300c81031000d0143c441c012509c55595660642c1824030036914072410388031034800ea1101d0034550442a41c005101110b008580240e0b480494906581c000540054554541600403401051a0140100000070003005031040c01000550a44141d004600311049540c4026007215149003050341d050205507031409032401450716400c0340d584051324034000702d841501d2040300c0c001209100c1d90f9440000c850800d10001140b14000c01c1d0242600303081c801d10300000c9691081c81898948501001c165000c60b412403587c0c415030480d0190603040c0103ca8119440703030740d803001500000303440f0f001080d441c2d000b10003902180e10990300709070340585442c24 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 373639901 1250 373638651 373638677
    0x5060604050108060303040e1302040c0c1101140c030408071e060e09041121010605010203120c03101701051501030e0c0d03030e0f06010e0f0108280602070b0f0105040606 75
    0x203550f00d02420b1a41c0c107020912000c121000c000b40303043d100b004200c417100705420190050100301c3e922040c0c80820080d02010110101e112800c2400d1030075801e01e003214414000c8080681c007030084040c560754600000400055522002545006540e910714544103107494055101c02c590115104140c04210b007031034004450315101080c1a40240210040e22840640d440003582150420768100800c0e400c4802c3c00c01d00300024480c00c00641001e000075841d01d00c00500180c0c01040042000c0440403000001030003601820403008010050341f505511100b1040e281240070309401c448034200040704280001c4990310900410700d00c000280064a084c103964030500c418140c00303000c154285034507114504190310307041042410343c501d124050301d050f504000c49083c01d0180a0900e4248140c090014819240041000341c4000424042c4042140e10300704a900310b1148101d01800a52000c288141403040f408101485100d00082000303403607032590108411100c1d5030103000001219404000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 373641151 1250 373639901 373639907
    0x12030c0a060209061309090b06100c1e020a23041803300f0b030f030405091e10051311031f0906080c03060c0c150a02073003050606040501 61
    0x840003c0014040c246405640301400141d580140d00800311155117000c0c10701030090160001d90401c41c1182d1519032310030b4403200104a252600c5003e40480d411003917200c006a8114070760191903074050254035003140d079076030b86944040700c508180903142c0d4640840001c526080c81000b400343d903482040003055450791022655989500868036448038021070b0300c6d41f200c821440f80a4100d0341104041904982d400d00031055500c44003640d4001e500101036541c501d01d010042d6803d4a806440400c2ca42d92181d00304035249216401100c00c040515090100d1105d4081d4035a0503180b0a440101c2855a40d42d44001211040804600e0640b014008110750328003c0428014951120564107425500e8003511700880304142d0080030f283d03004511000003800c0500140d684548140c0f00c20342000106114541c55600b072190307103c00e405807100020071407d419415641801e81121081034000070805004e0140c03048480044030081c800f81c5c1d070804440c1b203806514890000a885d071820545084015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 373642401 1250 373641151 373641157
    0x60803030c1c0908040f0506090603010302040207020127090c0809150a090203010e010204030218010308031909060509010c11031c0509010b03190b06150304150213031112030c0a0602 80
    0xd9002820300000c40d00080c0c3e0265140e118064490a40d8940c40d110080e004880d459008170301496042c49219800d540305e000783c90440b1f0301904c025031b6500342440101c032000304003001400c080031824402c081300ea401e00003107010760f0349002c0100282c0b00705403000c1d40d2a0108071003644d034075842140040d02460301204015040601c2c080080395110303442e030009007034514121a0b401241c0d07010401f0800d40c0740030383c0c103051110885001c5640c00c0d411511038900c03510000340300011060385250300a076007006590085808942012003045541041004140a002c030100d1250001e01c5180c0c0b19291050040b007158030343d03001100d08000c0c544050080d200588001040115155610903610300d8544080c0500251041d40c8503070360300f880e4603d103003140b10600094a0f00b0300801803511100a441070010449800c00d8101c032a0405180420b5074000289c0f04945403503042c0d1400c01c03400001c000c2c0c031070610480c0000c212616414489080c41d0076581e4091501b01c00c50541c009500000030452603802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 373643651 1250 373642401 373642417
    0x1050a020f2a070303080f13020a1707090f05060f01050c031605120304050303010906090b090112020d05190201120b01080105060a0c0c0b03091c08011701060905070509090703060803030c 82
    0xa000624200c19803a0b82400c0070b651098010803001d03010081003d9441d0030248d44a41c44a000c1b40d40658150089504d00405000d501d0144a481810700d42c14182000312500404a82d80280035180c0441c0c40013001e40310960b03406005c0e00d4150005400c540c020400c0e140d0014842e0015810007044009064002c0140d200589150140422440240e01c010b001917200b140034a004640d43d5141c0300200c81107500c142c1c00103506034a445812403140c0e4901e480385045661090a90038981c0107400014001024940020f240388281999110303030000c039941505429000740ca440140d001014403801c15218000300040c00210f001005118928140c405008604051310700007480603090f0751004901c01c003a0308996064800402000180c000402003951492054048a50f100040c0c003400340404106000b0240c1c03444001c01104801142580b1100090046c014140500d0404203c0a01254002c5c11103a0280b80701d080081c50b030b03c0c0207006560031145c990f802589199100c000b09540c940203030038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 373644901 1250 373643651 373643707
    0xc1d0409061e0606080f0603120d15031b0f030507031403070b01060e09062706030c04110a091502060103110d02040c020705120c0307090f110a1101050a020f 69
    0x244102e10005840015400d0740000062000e0603c3e5000d040100000c110020b00d064401c01c20000d510042400c0c0f0b400701d118180c80e40c4038480000c1c1c100c0034081c00d03014200444c20038200001881960710700c5002010f04803800c0d403101500d540c0710100800c610b02010b04143d10505041001031407540c05003849a10200540f801c040d055511a15100d40a91000c4000342401003403031060319005030340c0d503003141040b18841c0400806003401c42004452490fa2840440d4810006280751410701502e8840b5400800030020209004001c400d5500106013020001706003280120300c640034100350101802d031940081c10b050f0729550f2002c140080c0502d819070001c034a98101c200503107403409800c103c8050780c0c0161181500780400d02c42c5134a030064407020540d004079410380311070300d000c1020703815141c2d003813008a040110300c3d100b103020b4039042e0f00030b110300400080d411001503404107820030700c0c2d41c120000348902d480c0c110405050740241d1a151100040800101501070440d01105818080d411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 373646151 1250 373644901 373644911
    0x110f0a020c060408030a030506010e09060d080d020c03030a0c050412080a0c151a100e0d05070e070503070306050103020301030c0b1c050a021206030106060c0b090313090c02010c1d040906 82
    0xe03000c81c6843e00070b5400150f030755001180101845801d402040d6014600386040e86407020307a0320005a0f003c6010301020301502e824080d00050204c03540449076044144441550340d01d1078504080e9480e0b02c00c60752440c4c0b180c6031003400c10f040ca00c640c003290300711822400848100c1b4226100c844490f0f10940c4d1f80c0381408614010800040c21900000308401418800090f004d00001d031180747c04064000c0709072260501d11564081503030810b0048140301010384d845440c03904c462070242c3c0380007202d411451413a21003400b00030700180d00c2001184580c0440d83d05200300c641da10015402c0c1d001c2030200402d11076403031800381700300d2503482d01070f207144510136990428000c5000700e02800c403902560302480f2950001280c1c2104030411906503040b50094008010003031401400071721615028500401da01959404119480000c1042d540c0342c41d1809074014442c0e54a25114009015aa001030095401c042486140382e002c0d00c0c0304030700708820b40182c08a040030882003100501100307800303e6003107640b1703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 373647401 1250 373646151 373646173
    0x903030a050d06090c050406020c0a050907260a0c090e1603020a021e0705041505030c0906030a120206060406091503020f1201020409050f09070828080a03060306060504110f0a02 78
    0x7900404642141701d484061b9a1810204001d0420000f41c080e907010b2000481e0412103501e4213040c40303900518501e07080d410a0542400c2e804080410004031005030700300d4040c03104021482d0b104140002264403004400c1c1c0c0d803907026031001801203a2005101100317100c10000b4601070f0300145002070b40c2d481594109400001400d440741c245050b0740204d0341c4403038014840344c103040c0700c4c6183ca05451041d8507038003850040029518905c50003654010030141d004a81d2a480c01c0266841c0b8a5020310800a545110400296035400c2220080c0c49503041c1500003c02400301d10600340300f40720003101c0144030340c255028080103d14880c0b6071a000701446040c2c103c46142031018201510302150302040b181410b591069000001400d451040e80102401704500340c000a0045544a504010042965000051009491a000f4002c0c040c94400119000c0082d49540071a00746c034031031042000703860b0f21001400222403a2885911b100c0d00100140c80c4c021ba918000392400700860300c1100c44010203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 373648651 1250 373647401 373647419
    0x150a1d0303040c05030d0219020402090604080304090c120e0a0b09210306040606021501030b06041413052e020c01110a1e05120609070c050d050c060c0903030a050d06 73
    0x31101070314001200c03c000e020520701403140200a82c124401000200002c01e44841e540090620091049600280100054599200359401000c200065a4407980c2e11000305d001740040580960000750090300c120070411341481203282c007910500040c14003d50036039901c06116409448040305110790307002d03c1c0300003454802c110390800c8011001d50316410414107010655500350800010342d0012003501004e51005850306044a1700014460659111000410001d1035104d000450504510003009100d01e0f241d40041d07689481403048607a502404060814024000401c8143e9081052840d0707030404815005807078000345c580c0001030703201ca0540f020249075000714800801b2800700300c0da40010040141c1c50b030101c1146410700c40d24168511600040c4070320014443c070701c55020380c008640382c14419001000c02c6a4044229000820040d0015241d50844070f00a440c9100d95000124010946400e032540000040c00660502502002c00d403155000000302400107503941c0800120030382 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 373649901 1250 373648651 373648657
    0x40c1203030f060609050307090603030e0d0615030804031b05150d0b031b01121103040f03030f050a0204081605030604020108061c12080f060d03141b01020a0908150a1d03 75
    0x82605c6800e00f42d4034001c24035051140039817255010034038098040022036000304103003035200b4003100d1120bc0c030b00103840e0001c010708125860b50b138206541440401080340301801841641d00641a611101810740b200d0b084d0705980d070090941010b028861040c59485901c00b43c4000f110b140c10114050343c540000c240f038019511074281c01e4103c05c118102c0603580080448003400c260003001c0c00301072502c90a01c013451102910084c000740c0e13044448018503110f68840c5502051480d418040c5081c025a5078000c1c0d001800b4004481c005e40d21a04112510a05408200c841c00b40150000e903450383c00544030018014842030700011f0190000c2c030719844554454170007030301c50001042596501407004141800042400c841e0809180500c10f040d074404040610151f0b04d4a0540d098414000301e03000140140510440340c0d44880503242850601900076207019082a9600884d241d520013a190b81c5207800d09a011103034407404040b605210740c54004004828003401084a1465600c1b152455a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 373651151 1250 373649901 373649909
    0xf1d0d21150302010f050c1b04061707080c030a0c170102070c08060f070807081306020c0316120309020a090c0504030b070512010e0601140912190302060609040c1203030f06 76
    0x80700020240119078202d0715070b0513004aa8035100342421400008199190030383c0e1001d511040c40d0504800c010740d40c80c0c00ca5400b501c2c0040c000401d040f00b4103c1180d884104d0f0199400c9401042d07200c0300c0e58240042c0444a01d81c2041030118441e10f002c007500e5000c00b200c036200344695020400c460114000701c0e805401055031400600b900c0c03400e035a04c00c1d840c000103000c210403c8a4981030000b42c2e5881004503810241e803200d040c54150a0346040710007440780708013130100b50001140c2e01080d100f44198041103540070300ca0008005016040842c100d94107044001d41c881d2800c6814080c0c1082c035480703e21321004904103145810340340d88841c05080b9080b00c582e0002003000800b0703401c110b410354000e401000c80c1d8202760781f2420300c0000130b0407103001070040104000000c1810081e5558014032095800b03a89801d950b02015011120400f00c100c400040d80907214a0b0041030303c1d410116400307881245c210402414050030302c0190008074100342c3d8140c0406884a010203203403000380c46810014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 373652401 1250 373651151 373651181
    0xb3c09060603060907060c0c05060f180301110d02030a06030b011511030a05031b13090203182e15060c03110703230309090f07030b0628020307060c030f1d0d21 70
    0x9142e00130cd1100c01003140310181c2e01036410822020240d56001084e209452803800c0c1c056182d03074400120707800807d095030010f803518151034000955401011fa24078607442c581d0740c5144001c0c8110304400c1e501d10a03d410107000400404c00070341450540004810500303942115549004500f640c00c4000c1c103030310b4111200c1e0b141e00000380401d83e8802c00e2038001c82e11682010382880305000c00700d1010940100b4071407989119540341d141c0d100e52070398040c140c9081048603452949407180401000c520b0a05011070110b00f40c075140c8000724200003041c00459a014803001c01d10405c800182c0580006e05019010074171040c06241c000d641c03100c00991141940015030580ca2034501d02c0203081d03130344070784d081400354404100880b20a40700d400c0d5070700142524012a079840140c080101d00c0c1d4800c02001030f1006280c002c00248941d03250300320035a80d030345080c4c00707214110048010325440007040d0103041581d8050000024458003c0d003da0364880364070301d01403040009a0207070000380c803903844c400780c0c103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 373653651 1250 373652401 373652407
    0x180311010819022b0b01020c1302120405010c020706021f0f020d020304110118050603040f050309030a05010b01080c0a080412021c0306150503040b3c09060603060907060c0c05060f 79
    0x4850b13204024190400359424280480304441c00082c0d100c254a81171140a40c40d260719400b42c0e83c0c0141c048640c241c1d000b004a01c29443d1509089000700894000300c401070090382030001e203180c070005091420507c0c442e00314031442c1d1090085402040f148081804058090100024002a510145101d1801810004003071280d07d0001000740c108000c04040158a2a80600c882c0d180ea6040d02e80c41a4010b10094142030307541002d1307146014100401e0340c1481400d182104020040d0032000940d5000e03251208540c850080000075802040114800513801c0000580802c85c2d10822014403155801552586c00c01c0c420a06003400e0f01a01039404a80c40b09030400c0514a055008506800d05e450842e003103013002c0d91140d0200601a2921520030200903481d1881c50000010244401c80d6411445170443c03522080f070546142140d50541034090600050054100883c0c1c0501c500d001c400a410700d1030038108103441da5082200c3c03d40c4c600e820100042141d40341c2000400e0340400001805807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 373654901 1250 373653651 373653697
    0x20030604060b0301260304120c09050618060603150613060806040902150a02100f050421020303060d05030c0a320c0402070201030e1b0118031101081902 67
    0x815101d6603400a555000104010061041007400302c802c103640d250204a0914440b0140e50b01d13500894110780c040c110201c90100801004a264004483c0d04040c140482d554050400c4603030014901c86001b048a050001049403521100842c2c0c4261030485d131408804a1002107032607a007081c0001201c03072043c01428030880303030866050344e031280301101c00b80140156a40032503a03148100ca04041c4843c4042240e54600b4001d00002e5000c2c0d11198042001d00552007411000e090144d40903902c4800982200c1081a81e041502d5004c200301e4005500d1500d468084c000d0400c11510255510b000c2401280a1a0070a001d1042114090109031141d0700c008080e4602c41d20a18007910501d04503064560805c04008c034824400c001c041f2001a1039144a0006a028002e1150190044d01400018502c0042080300c9502c3c03908003030707039601411007905135290301903007807030101900020034003008404e998455030015502041c1916a00c4420b03004c4c0d04120160b030007040303124800c1e21810a100c2c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 373656151 1250 373654901 373654909
    0x90c0f2a060203092505010c05030d11070209060402090a0311030106031401091e15020a030b061c0507110307060e0f0d030606020c0108190507020f0d0203030f0a021912200306 77
    0x104617400300104841d41c4c040001140e4600b0a11482050306000230460715106110007801544c44240c64100309000001071003084034a15070140500301d11403004c00c000b00758242070501c04d4074081031001e0078580039103040da00d401910492000f16654150340341e02d004000038a0001c01070a10440720800880c1c40031180c0b814111a07007000b504010701b58010f07040300c4042507240c04144442d07441d11200603611102c1a2084025000a403c1c26402220024005804000c00d11074203000050308141000f1a4489480840e003150740c400c03460001e6402403200e840800c0b003541c82041c14203813107404c0794842801c400301e40e4100a07141000b440840d0b81d94904100554051014604141003483d01c803801d86044040128141004d01580500a07503a00005030300324000c103c1c1008004c0a0703000c82e440558180002581c0398411500440541400004908a07912078000d4032400103a0111821640360001403c9038071100403200c400405072a22041d4007240b0801c508017802c0800110701b45d07524a041d60500c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 373657401 1250 373656151 373656163
    0x9090702030f07080c010b060406020a031701080a06050a0204090e030406030e0c2b080309100605101b08070804030b0609091c05130f0618090c0f2a06020309 69
    0x940250740003046249004440d0004507565075502151894580300c16201060062000d0341e0056000200024007003801c1d50001601d401d2544650b4402d040c61140d103403050601c03007085c440c1e038070b55600c0b40c445400055071503002181e0109441c0ca0050500b5559011003003a1950103994240e1038000080c24441180c1c1409048480c09252009004c0c0a00c50008030f544c0313504540c6440c0034504140310180e810000c45c0b4074160050b400c03510141e12400c0c18601c150311b50300f40c4020b1884880c46c0040000e040e082c29000044d1460381600e440421820541c0280381c040054101116030380030030003190001031004400303440a140a501c070540c0310310b408414000400000b420101450707000080a0600d401e01c031110f808110b0152500f0340d159003000100c40403040c1c140d08450f10108460001040c820303842030641ca00c018000084200351555441d12404482c60181d400c0d0010301c00500c01e40072607000308100d1202c1460107020b040d107020440d0558452111001d01150903580000c280003440300c0030848 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 373658651 1250 373657401 373657411
    0x16050319020a0e040501230727030602131701060627030602090303090d050a0b0718060e2b0311010b0a03020405040206071e02031c0e0d1e080909 64
    0xc080201103154001900c141c2c0148541ca0020662000081c10007400307410514584440408114180806144c08000303010301301c4480000500041e04849640940b0f050361004800711034644060605649460000e5401520401300070030100400146a04c0582c0605c40c0300d24450f40009051401c008008120300f04001c400000c40c640141c01e40d4100e0028070b007000490f54414801030f6640d1502c00480d0450189030130340b96000b0780000c2c0240601c280030031b2001066110f106031400d541d840007401c1c4c07140c800c503e03141b280e000703090301050004500074208006130140041c0340b00c0c0c00e40a407030030481040b02ca480c40c0c20300c800d520454000405402c50404820340417150002e2041c418038101080684444d80f001070311403900c1d807001c5000e6448002c00c41d5003854004048103284015104100c40040e15000200d00038490b680b98480d400c041d2018440390380d002d03076907511034030b001000800440500303c050507601044000c000c1d001c1d03054054031305100188111281d40e111041807080003400800140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 373659901 1250 373658651 373658683
    0x140406080f1302060a030c0e120106030b090f070905040203031204081921050c0408030313050c090f0403110f100b190b1b010f020a12150303020606060714160503 71
    0x2d8800c0180c1c1d0703032000d880881c000b610300040ca04440350303001c540d1824003204d1690445d1040c80d00304882d02040d0011000e60b40102e40910107515440310481c1d0700e0310303045501d81007074000034800e0050f0ba00e503410060300580028102c1c2d080940b5984000c042c00004e550480c2c81070700001e503004440c0e04030318190a03071000c2c07800d1010f4009040f010f01046080c3d1a6140311400c1e95960004190b00584c0f0151000f5061f071000b180d803640b4100c045c80910b468001c206554511418a4419080c07400528042c420030040b122188151166501030302c40049224800095020750341065800c50700070082c11099540d06440400e02c80401030501c004180007446111081000382c00600c0300d120b040d02201c400d0320241d03110070750007130301c00940701d0042c01001e40401c2c0c901d00008840e00d03040e40c815802c0072001c40e8144200903004c0141100300308c01165100040c0541c20800018086180c15805081014022070119004200e40401d250600441d04005000b091640380c2c2800316040421000b8041c40e1200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 373661151 1250 373659901 373659931
    0x1203113103080a11010603150204050306181902040e0604060b0a1e050d080408030f0904063311160807080f0319030207020d0b01031203020703140703140406080f 71
    0x40c4519102d441a60981003d00905240e034099595003580820019a000743c0c08035695044069514065806441100e10034401c10f40811682c0440f0902e0101c0c9410b960014030081322682c8030504032034040f1030141d9001c3d54807100c00005603c2030200c80d10803803140c54009010741b031440804c28040015040160390551016118880d01c00300c03a83e08080c2d45080781d0b00b02d0000c0142c075001c1d829125503000646240804105d03480714003982030151941500031541070000036110710b01c11105000090400d070303200121303505a4503d030341d8481102d0000c04051a00401102d2148403140c949903a5480307024400b803000c101041403184c180724481c0503161004c01360819410076520541d59004031011174480807108203e89903007030b010394121307203440e0b40c05404400c15400da824100141c503000d12065480050f440710f20b0701c0d024804c0c801c81d11029855210b0141c1e540503203c4101c15508001030440520241941c00703040390038a10044e00007030810359503c0080345003a105456015001411540d0945504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 373662401 1250 373661151 373661153
    0x90f0c081509040f05160f060801140f041a03030c0a02030c060c06070509220207060f06081209060d02030c0304060b03070e07111005010605071b050604031203113103 73
    0x1982d180d074000e5080161407241d49140d08000781403401c0c44100e508a050340c50300c0020140200d6000c08115400b0f52596440341c6c0e82c4000380000208020b414560000b10784400011a240c154402960400c41e00009000304070080c012a10315400f1200a80703440d48007407040c90844c0360800844000030002d942c22410b04020040701c941d22203028043c402071042c042170006c0c0303a03201ca802801755122101c90141518510305101002940650019254541804d120f00268909800f40408841c0d140c00140b291444498000c80f964100b0f86089500020401c40c40316002c0c842d0001c3c50143c102044426500c0c149890501c048401c200c0c03040d030090b0040d07a01000b140300c0e44460641c0c4a00c0a040198001414030391860401e00649158520680340c4030001c101c0c1640000902480c900c01c581f0804211410346040411230814491182e1145041105000247c952418054403803500d080106115401d0790a1702800c0d04060b10b02c41c12210007104002d45294682e952156112003102d0842c502130031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 373663651 1250 373662401 373662409
    0x2031b091b04031202100c08010e0f0f0114030304031a071215090c020c120319090b070311030f07031e0c0f0b13080706060e060a140415090f0c0815 65
    0x7403480094003507000004c01a80060003800300d400d03400f01130b48041044803a2050090b109800170300904102840c1000001d807400079258110f4010804e45101440580c40c00c1116403500d4240640c0b5a003500081c800000040d5016a01a00c1c2d000b424140ca480c40c50000f500402c01003502040d0b0031014123100307980642078400348010043d545185808500b1010801080c0e291450f03d482c4981c210241846517a000d00022003c0d203e0414000c4c100f00346116605801c8807010014080c500c1e1903801002180c0009002e00c074040c0300c5460b8030b0281c03400d01807420103031589500401402e60100d48020482a62103070a515408082030181c00c0c405414074403034980307500d0b01c0d1541ca0020614061000402c10030800c07000f2004440364800b44140e52000203103400e138040d000700e00c5455030034071891004c595a0f16207420200c0561711203610f03030480807202c0d00c1008042c01410010301141040c12801150f01d11090280d06660b403103820000c2007108040c0f800514500000303007401c3c603101c218055081e0a41d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 373664901 1250 373663651 373663657
    0xc0c180103110d0210030b0906010906020705060a02070f060203030924190f0e160906031a1e010b0c0d0f39030207150203070201050703050a02070302031b091b 70
    0xd0011684030002e66418003050084801c0c07880a90712071450a00450300c0c0d42d16401c9050139000c240e546200e903440c2e00d40155001c5565000b0180580c003c80d01c144100d05001d0f010301040006841141c400ca0340d140030400215003190461070040c0c00000802c0181c480401c213620182115120002c10760744170f503124401c040720280180500c0700f05c102844082801603000b4000b410456001002610050102c03203550300c4641001c0c0000c3c100790403000640e40b44512805007140e421141d040800c180311288038030000c500a1a000d504070441c0c1c600d040030724a800c0e00c14040c240c503400c016a80c080700c0540c24507002d00590b48008128403440008034990f8481d0000d50120640350b00500b00221550110948600c103011141c558001e240c0240b040c16800074041c02100e608010106400d50451801c0380c0b20f12690714080c2c0400d0b010058880042d01c280020402182c0740d00c1030700d0041c0e850750f00107410001c06950141406000c020320035000c0c40c0c0140702c02d4000c3d14003c120703003d580c0a0007030b40d038440c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 373666151 1250 373664901 373664903
    0xb030403050d020703120c020a06180b220b1303020f011b030b1c08040512011103070503040f0c0e0a0f0204030f170f0705070f0503030703021e030c030c01020c0c180103 74
    0x1075000304004c0c08150140754400b03200401030034244800800d0040095aa407920b8030305940f16810402e0044902642414a10240b034100c0c000b40034a6448200500c000080c01e82c460f072403072022043c0ba5004c10402d0203064080c3c1030b05030b6911440f07a541d0600034900508001b42540592504a8505050009031811021007482d41408683c0d0201200004d10703820300802d41c0c4901c170072628140e07010000454000c0080d503c003101c280340102c201e211920b08a805c1101d00741743c584802c0002c40c000c80e0040000d15407103813242400c80c200c400702e55207101c039082030350307004003e07241402050018001c2e85011b4030b031004410000860034185591111003209481d010081c01161095010000409803441291501407080322a00da0b01c020711b2800a540b61014410700d00700459500000c202d61501104592034a0f4142d401888503480361407124401e0031454ad2011910300c020030422486800502c06028a00005000182c44400c0502d42a04140e16480d40c148500141940301c001342405900c114196 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 373667401 1250 373666151 373666177
    0x11041a09011d01030e010e0a0c1a0901030f0e01020c0105090106150804170f0c0c0f040501140f01020c100215010e06210a020a03150b06130311060d051f0b03040305 72
    0x4200030b140168000c080b44003541e0101d5003044546001c81e1000a6010503561065501c82e840ca030352024083c0d03940e41005107110101008018040c695846a0880c840030109204005815803070400c4240c2264401c0c03400d01c5107a5140d00400200740307003e105e004003c201109000c903410030070010080480000030001400004a103200c91800c45901007524042914002025910509114000e50310207081c040c65108194640520701303142468040d01e81250002c800400c1024030100400c51041039850039141144207105841041c1d64a8411071110018160042c04044000f540f14075120b042c16003095030300645100a00065488942c0324501c800c140300c0703140c10195030039841142084841200070354000e1075900080280802090f0502d4441d0420408220410b40d400a000c014041c028213a4a50101410104040342e4800304a4400b0080185060b20b01610001c001c003c841d03007582c000007000c1c51010256a80303007611900f18003500200301d0f07003811844c282d60002c00c14480c00c00d0140f16 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 373668651 1250 373667401 373667447
    0x1b0807090b340b0f0103050f01110403080a030e0313210b040201050a0212071401050f0705040605090d020a03050a120507020d021c0c0603050a0b010e090601030203070c0611041a0901 80
    0x1220b0750030014060341a512500c5007006040811140700d20010a000903940b5000d2261050480c85051060b4061185080d078810709181c82d507114645075400400a000c1455103815403001c0343c580500040c071003c1072600c1d8401c20541010000d080c04200030000b40d111040311145013011964514503164442d0382440c00503521006140102c0c105003908042d007026901c00308100c0d0812008404618000d650391008001c169a00101d644180e03100303803000404290100400d20806100314028800f0940103082da412420702039020820911050740300f5121500101c0d50340081011843e6140c0904084d481c004d42043d140d07400040710702190b00c1000740f1500042981d01030311102540007207865900250407440395582c5000c0a00641821144960080d00e01000700201d980203800d42e00b161500039107542503507683c03440194000d5001400c40001e120609100e040000c04900a880105c10b4807100300c1d440d540341103680c0000c800088c800855140b41030102d0f22050368010100704a0b500710a0917000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 373669901 1250 373668651 373668727
    0xd0203120708070b0c030a1a0109030b1b03010801020a0207050a061b02011e110f071206020903031902010b3a081b01060e09030703020601060804061b0807090b 70
    0x3d01c502000205000b0148040080014174880618415140ca03070052240d001d45d12030018a03010021801c5000c40c04800041c0041803020030080d5004440105094000c60604100001038000340c0c04101641e400261540100c4e6041c403112005090594511586031308002d000b07460b2503284426210180c1004900b50156803040300c1c02500110500d512076586c1171341260041100004440c540443d1041c0c18001c80041c0c00091400129005218920b55085880c1e6981010b50702c16002d00b945440706102e95950341c480314030300c0602040960000584400590700740502000300c04e552041024038082c50401d01c2e6420a02400100e03550034180480c0e80b0385160190b042d0042448111500c0000c5072440c010703040560044055030035041c20040c182d516101030580e00d20410000600607003000c40100b0107940030341041500a84550b50200c1c0303606161170031800c43c08101b80c82d5000100040c00b8032107007a80242c1c0b00000790160040261500300012a0140d101510ba020303c0302c1d80c0c6011011076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 373671151 1250 373669901 373669913
    0x1f0f090c170411030c060915030901110301080a0c05010c0807020d0201090b130e06090603070302090903090409060c030c020f0712080c0709291e0301020c0609060a06050d02031207 79
    0x40c8071103403824088002401d050038402041030010740168080d02c20014541210300d04001a94a10b00000700204a050382c88154075100d41c0000d00051300c59902c4000321103403080c072a401307903018100c03000c0101030010300303414841c08058a903803200d4103100e4801400804200440c0c11120b07403d030103490503c0005031510040303c100030507500414140c48081440016004007015103000c0303500f50214042075840741804c02c0010201a94041e074107501000d82040142484410719030f001030b52070140c0b41007446030720200d0181c4000090807250680d5885080400d81d405100e0104801c201b4402020310410302141c05960312014085e01d4040402a4624800c00120340115964480040141c8515036900d074502000381c8500c50145020180b03004184000060704e400301d05455400520404c05400c5e014840034103114400c2c0740d150555000c00084030094002c126941c0612043d000405c0240382c05d400f1002110b6840e04214420074080f190710015075000691540060040d10071076036105550702e00a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 373672401 1250 373671151 373671167
    0x106080903120106120e070b032a0d1b0206090706050904020f0706020c010513081c1d0d020f0d05270306010308070618051009032003031f0f090c 64
    0x12082d0b840000c0004580e0b03076808204010202c02140e0140100a1400011360300c810803070242e05564101440040c09403000d0038808040d95880c0703680103014040004c6c11075401c0e484400b40c0c0b10119241c0f0f08010b0300c0310010242007002d566601c0a4013603400c200c00d6044e1500c0d030502c00c6071701b00030300414034001603a2185d04444400d0280342c152513482c2d000d840c0c240041e40240d401c0200d15481c0c0700c00681d050381c01450f00046070760b10401151400301015480c810868542000c10182070303a400710b04030381100c8801810303800c01d10100100103a00034581d0003842c000e60844c0740300186d0020080d0710185a001402d881d4250240c1c8a01e0704403c81d40c0d403940e083e442490703140b5030b8944206c800000078803141000410581d03025030418054812190b0025840415028000b0700c20381c00192a418001c0e03a940c811100e0380e20038540f002c140b01030108542911012210300340003603040001801041c0d5801e0700c04400e940e0960f0340f2216841d01c0c008464a40042c10320031107907900d40329000851414414825 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 373673651 1250 373672401 373672417
    0x4030f021306050d1221140c0a050d0c090e040b060a060e010504050103090512040f0807080a020f240d0f0509010516080a020705070b0405040f0509060a09050a0c080a02090f040206030106080903 85
    0x3a9035150f808190840003406c1200b2030890b00c14007c0c0045410698204129a02c00303c098850600d040340380700c401c400900c0301610100c10006098008101c9036100404180958010f1281c12414240282089012000b03a072021041c4200100c8400039640c002040c0c8040719424240029000c0190514070b0400700b07040c060200107000001c001c900d464410226109959131001102c440036240c2000e10303a01e50451901a50080c501c8400203103d20b0200f20090789091033030722520028500200b8202990401c560010840d511a030702c80044c01c601d0320841d54443c1c0010000d01560400c80c07120510980c00462101c1001118400a5840507607034040781c140700c0e800723400c40320543c2c0d0728150118990458007507544650709040800c141010a4052603000d422060050075541d2560340c1c4183c028440c03080120380c3c6001e424031950110b140018040010400c4501404003000c040c410000e602c08001e10804040881009000241c0c039450260790650b0803500301164a6240d00c0c22891541c001e00345 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 373674901 1250 373673651 373673687
    0xa0906060e04030908120a021f0f0606050a0e061903020c161e0b0a020d050c0a0203151e0c04050f040e011d060a020f09040b01030b030304030f021306050d12 69
    0x9100400da03104c80108112603014066600c0322031850f035501171600c204400400183e00400f10180303401400c48120752003601c2c8040018098000c4201c400c15119140d1144001c02c2d408100d07200f505400c10001000240300b03c818500e85101120142c001074171405078401015408504500288020015107912101018100301d0303495407a0a0f41050340601e22801340800404200040d81124000c19241d01c8000c0d0b40140020702001c0c40110785a410041d00d0900300d20544d01d010001d40c030305012031380c55500204180101031804015840060300542c0d04940c5020b4a4010010721503400002c1c1c0d01912012a61199008041000200540b0180080c5036240d480c0c841c03a014140c5048200b6000800c02030b00752629590f0749500c1904030701550204090040d82080a8010362420750b00c10600c510050400003120745100c03021904c1d64026400855507141001241020b526040c4c800c004a600138200c140061070800004c1180700d50440c80003010300100c1441c4480a5000c0d010503042404501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 373676151 1250 373674901 373674929
    0x5070f03110112051e040c090f0509010b0303090312090103020d050106020a030e0a120809131e180809130618020901090806060d08031e13290a090606 66
    0x800d124400703803034a07240c0c580440e80408998011503001c0c05030511941440003032410043d2903000d59548803000a0044a00000c2c910010034504400e2040d01905c0c510400d00144500d0b14145040c211261280114800c0d0302c00d05c614142c980e8000344a0003904109066642ca0300c012000590180c0034580a4a80f1182010004500a9800166000e0b110b001c0c0d0303950501d8814600600969800c2c900840c030640608094481c0071501d20001009840da01a1045035800034a1140d8000c89441200c1900907100d00c00c0c40c0828403541e80100390240d14403d0f80641140c2c00340e901d074001e510170040d08a014075111003840c40c80c000d4076030045004281030590b03c080202001802c0d4000e6100d0351009001c103a05950106000200045041c45101b005d80200881181a1100d41441d08001c0c2065100c2e54102c5036612400d42c10700f4498021207800f40c10b138400c541a40360070100c2c0004a051a410b0402100d01d54644041c07080101d60041d00845000400a8089c04c000c0d002c0c10081d00480000d040c64 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 373677401 1250 373676151 373676153
    0x20c07060f1215060c0203190f031710140301020919050a2309061c0b0402040635030702090f010306060503030717181c0308070f120905070f03 63
    0x80380720034144025034804410a00b001d82290488400c0d0f0707008054009034a500384802d038050303018800480d000074221703481c942203000c8035696500e540c241110301c2c7c184680c0318003c040c3c0125800300b403585583c20b080254a0509580240e4545034450804106146500848246c500b9811240c1016000d0104494400c801c5101c0d84c0c0b000c018410103001d6581c2100008080c20b0305060380403040103a1800207001c041402c10000c11000151140e54400b44c040d2410100b0765042d1042c804062180102e100b191070580104421144654400d144032034095958002c165040380341d200514024001c0c825a484282c0c00a07071a502030380310002c0d003001080092100f89841034401604030f0f0701c58841400f045440d09e090544038007907000010520301d5400d062020544880010b00302030341000d01e031054a00021000030300c00b07215140d10300c850000001640e006040d40500100c1e801002814001c0c00c50500d6600109480790000ba000082c66461102c02c00b0482d050156100030141460034000300c0762a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 373678651 1250 373677401 373677407
    0x110109170c221b18030203070509040303060b0706061d0103260c0304080c0a15120f02160f140c01020706050f0d060f0801050703060e040b0a0f180605100803040b0c01020c0706 77
    0x40b5205400200300405480d02c4c120014103810015207034040c019000442c90b100620032007100140c0210309140c0c5620011401c1101d210242c081e87d070040101092040c03a2981d00c1100b0004110b198041415002c010b0001c200321f25001d0100303070076003040b10000c400c480005c102c0342d00a40010440d503000006000901180c001640b9090100c11510141c0099035200b06000c0c078001080c0401c0402c0035070f1000a00d605950f132050703050203080b16015140c2100850644646098400b00b121036258041c521410301100c200000114030104008115801116001035500d10003881904100000000e180e49003505034010740e02d1100b2420307000c0c01762f0350700d903030140d103460711140070390900f84d0320f08400204518840c1c003c3d40200d80720501140d41e0344d00c0ba51a0442102002030082c1c101c640c075807444292021f00782c03040c200d2601c16500145280d8006103024400c0e9080030781001058000c4d01c40904c4500404811501100c42c076100f061390307a51072000d80354064080c0c6504601280244100002c010350 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 373679901 1250 373678651 373678691
    0x418081803030a110601170c270103061a0405010503070911211602120904020c0f100b131e0902120d02011401060c050c0f030a0f110109170c22 63
    0x40b0a030190380ca17507a00c60003041081244511920724542c0032083d10489402c0007000c0782c100c0000655890610300c1c02c807401800b00102030740200d8080c0d80e112141541103d2401c11903080080403102808294901000255a4040c1e40074801280d130751180d1941c10303068400103d8082c40d071405c24206920300d0014200310402070480e82d01c440c007600c03150f821100c0d501c082080065102144081818031814905010013500024800c04070b52003903001000c4155400c100840f00c020742a0408074481c2101428006258070512550740c4913400e100018922aa540400c80c041025144000407a80e03a28000103440c040440081b000500401200083c980e5041d082040307a4034603801c02c1c00c0070780d80c0d0b002c0803207012036803440191080d080b45881c81d24600d8800603074828050b0040031140304034015191402c2d26905098126101030b4001000641c658101c039480000703040040340e075011204000c5080d9180c000007405035200d0000030403980c0200b0003821031480070103200d5000304050b401c80d00e10b101d01c010b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 373681151 1250 373679901 373679927
    0x402010807091a0f0d0f0b010e010509012a08030a0c030501150840020f1c0b040305040e07020309010305060a152109030801030c050418081803030a 65
    0xa068000040c003040c0a071010790101c500440001d0402154040c2c0310445400c00c0251131034180040148034007420082c020220070039090f002c0050074030400c50001d0500c8508171555810700106221092047c2e0b08460711018441d0f43c182c4044040c40030b80e2030803004524844d802400014040140040c014040d44210850743c403c4d2401c0011340d880c2d2039900116075100e02d0000c00559824005880c42030705980c4500c840b01071801030340417240c140481c0006114001903000d0000b0342811440b05519100d640024911001d541c2044101703800051a1a81640020081d040c4029100814201032203003003100e0081601ca41c2107402c90a154400075280c1d84408507a0b40040c0c00e0001142c45d51810f481d10404582038100600f000d444424400c0d200c0e4141240681c4040407009220b5400311101e00486904a119550341c42543d8110302e0310540c100c190790021805035180142c50703805040e4056071540349541295603640c841d2440e403110700310083d0444c00365030180004a01d48a820b5004441c103a424 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 373682401 1250 373681151 373681157
    0xe1f020c030a050a1209020d0f050a060c020a0c0b09090c070c0504020304030309150515191d01061d0303091309150f0b030a11010e03030c0f06070809011401150504120b040201 77
    0xd807642c0e404442038846c001e034080d501084040c0c01400082503840c808031014803403000c0d10840c400c0340e240d04003101c4500210390007503040009400100710300c04072200042d244800f8494200340c0717503001060f91030600500c1080c030a1800210b80081c0b1400000040003010001d20a650b80c0c9083d00d4020080d020013102240d00c0705044d001011500c07994080d20744601c4040300c501649841007810001850707580070911100f00144000407601e0480c00d0220110178002c1c2c10810003e5240044c0204003461090443c00d00055100003c00f02e60b0b000b2080b500c6008080350122412500d9090580043c03a021038010712040d45a0048090350800383c00c040748a84100e40d0400200e40384400b03054440a05070802451096030360341c04411580134442c045840c20018045074182115811007515102c1188803021007544200200980ca60780280115800318403400244001f5010450148903407006001e00f00b541455510310302c80c030601c200152030007030052a0740348440e25043d0a100030140025117042e800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 373683651 1250 373682401 373682417
    0x70f0b031b27060901080a0203060d050f0609060603070608040803190906090302010f0b01092102060a03060819020108070e010525050601050406030f0807030e0d05150a0e1f020c030a050a 82
    0x21614106060701c0b13400c1d0701038607007241e01c0e034031115a0300c020340c0010500383d8000369504881001c624108210114502d0b614010485401c0100d905d510f09a0300030010303440399105410900c9050341c450710140c0c01030b0348140482d41b030303031035441810151100411440d21001d00e010032074801d2100e541c0201041c07900a80080041ea50340003807150903680c4042c0e01502041c040c003010001c0890084414460712038208008500c0b180d1503000882580c00707911501700094035403c00b402580d030144990f0308508002c011a0803020010b0b4006000d20340020440801d205000001e0340250f4091000c848940340c582c1007503090442e844100d03900c0039090380001c3d00c1c01e209a00001ca16403c02d88944020380e50004444820301716280d41d40754030303944110380450030030001d400030711303600c2d12110b56406050784154050280c40314968a002e00316030380100040085030603c01e24000c10040459443ea90489000000c0c4110580191b25000380c414244d45003440d11001070709880095000014240c0c1d03001c01d69a01032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 373684901 1250 373683651 373683727
    0x60b0916050d0e0109330204061b1104020304081306051905070501061e0311030105010812181305040302010b010c02010f0c020d150209010809070605040b0a030b030d02061503070f0b031b 82
    0x101d00a0b80912700200d50419083e0000102c1c2d50303004c4013400c0c45500700a0745c01d0003800104080c1d0708252000c50741d601000c0343c03854103c044080048040d11480c80d105007013081d1013040c0e45a071a003100401d400c4c03202c000340c2c02c814080290802c01c082c011075511003410b0b41000201d440c1600d8240700558802c640c1d00300e000070074a010302407503049801000080400403403403035042c07085901c104220040d00701f45210000c03040c0c440ca03c25118550005200040034600307400c000e400c1d41c0010240c1c9042110005507400142e030021010a0240a24909103410081074404100d00500802c0060310b900319040300c00445002e0b54005021644080e07890034000d0b00c413460200d540d29a28045c42000c1541030001344510740c0400054114103031709150101e0704450000c00302e802c04010810303040040e000041002a0022100120644071703800394000c040c22441c0005403012005580902010120008041413158803041d00001d070701180d2488076581c0d80e120091100d2005054054405405000031001c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 373686151 1250 373684901 373685003
    0x902030f06010602031309110406050c160303030b1f14090f031b0102010c0206010308041a0d14100f03020a17011401080c0312190804060216060b0916050d0e0109 71
    0x2c144c22054811003412706c0d0403e002a16540c02105414520b4419404918280c001454102c00214029100098070102a100f40100301c1100003020300c450660301c1011441079400818940d007a541400026101d0741960b0004080a03030603001b865152150000c00b00064018201440720a20240c00070040c84d48880c40aa85a034000d11000c0c1040c8014041000080130100318050b4003120410172600e4854408801802c032078400c841d10080f00290000c000e001d8202500b031300c0181003050380c1a03420740c1c0740d035000500d01c01da540542040403035107414080e0b040701d0035003141889990b00260903155684480c40d0740c0d981d8004256051007407150203c50038490ba904000c40381a074040761504144544a12001d0b0780150024104480e860b43c02c0142d403942d0340c036414080516612802c0c1c041000d400c668100603000d400582009903420b91103124108880c0c0040c1281d5140c4405540860b660041102c01401045507039405054008040343c074030840c1c11650703003650400d29404c0b800415001401c041c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 373687401 1250 373686151 373686161
    0x60108011208070219030305030a060906050a0918171c090803060d02011116050312250c030f080904051302010e0120030412021003110403060902030f06010602031309 73
    0x14030076580310380c100100812031035401000040d0000d00481e0600b40500e544e0310328154a0781c8181c0000d01c0110270f01c94a203c0314050900203010302c200c14051a81000300288030040c00348600000c1c6a07494118004d100d544454020401c1c0d0411b402030340480c000d801d0181c290b0700800c501174001c60f696640d006412114480c540940c1e1f00820f1080c250399034807041c4000c0c128045002da040c801004c0d9080350104007007261400c81008021400f94052401003450b2618541c0c01102030001814029800b0380301e80844000d80b224041482c41c00d4140702d90401100d8840581c2020702001814500746042c0120400204035802e801d0f242003040ea0742e02030114101240c1e550009002802240100c295503105204841c0449009011040306405072654945154015800b400c061683c1020082c00d500d0002480c858010390f504041c00402122940801c6911890000502603591084004259201003040030040c4401d5800c58201e541c6881020355250070000c01c14000c0741400c2e0020500700414010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 373688651 1250 373687401 373687409
    0x60e09060106050409020703030b03060c0c0c220b0607080c01020304020f010309020f040c0e0402041401080105010206010f0b0a05071202070f080f61060507140f0304170606010801 79
    0xf25420300b41802100e03000307580008002d41c00c15803540c800c04415601404180d01030b030441d504c90b0765588440444142000714160481d8412018111075050020300164600f0308450800b00004440305013000281950044840140c0441408941c12141c40415802140500c0c000c42d03482d0040807201004505950420400a4110098442c004820706103070300300d101940071a04101c0b0000281b400460126041035020000c10907100e0b4940c41c855811240881c0941400c0c406040b03558102504482c140c00507100b6071004000008143c60018401d5050b82c2c0e429a0200d6144510303644040002d40e11001c0d070180b004145441c500000d03000e840040d04051030018800607050844012200c02c980c0d030b01c902405903491003400c0a00c0100c2c00c40522600280c0c04403e041c80c0c40d00e446203d0001d00251030b4541100051411109000d039030f8001c0103803412a58001e032900441802034110074108245030340f2000c41c62201081c0402c4211b806904002d0f6401041c0440300c3c1c5a490000440782001d003131013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 373689901 1250 373688651 373688657
    0x70f0617060f0f04062117070317060102030f03090102120a02041d060a030f080703030e010b01080f070909020310050102100c090b070503130605090f031c20010f060e09060106 77
    0xb001c4405030070407907400c0380900301c018000070b19240d444044c80d107681c11400f0600310240062040b0020841c4454a402e6a011401a40703410a0b05503600a4a000c10702c040d0749404c44142e03400035000381e100300201c2d0f07d01100c3c040b010703880b820020281800b030340020600b41c3d10a07a54000098003c02c0500c04e8800300c80c0b4201100a00e60210300f801029541c1c0680480d0704180006c80100100da850b40181017281d101e814520364600007400d00030102c0b6524680e44500740d0401c460711240780c0c1e11401298011001821400d01512000020781d40f074015580007000c25400881080b06810140203210100c1d4001e8003a945144400d043c080d0480340c0b40d01102c0f010903031000301031104d401f886c4081c0c1055407142c41140e20b40310400740c4040c03500105902610000b0070000f0030312300500340301c0c000810035401030b401080c000e800401e44200004100d81130108012440d22000d00d0b4900020200c8580c04400c0020040200e005001d00090442805400380c5905c450000c2128014001000b41c100c0c1e4440e5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 373691151 1250 373689901 373689919
    0x9030a0804060e0111030a0f030b12060412090e01030605060d0c0608010f120804090209030f07030501021b01020c0d05033103140f0708210a09050601051c020f010908070f061706 78
    0x1180580c0c8e5000704c44035080c101641c0345680100c945030645c0a054402c8000001c11346490a403410003c002401002c60741040070a041c200320340d141c41c20072076054070b40c03100c00801c141c8d90b05004034075000654030010708415031500c0001421070700050b2241c103882c80366010813803440c1c41d80300108510543c08401000c502040104005415242e030161082c400f004040c2e070100c6840d5113545182410542041d20070740d40c00a21031008403005c00b20040290310740d00096040074601200c1d15119480281c0b0b0f4170a000d4004000703030904610920188000c9441858030101c00350700c80e6501d40a282c00d444c11004541c00e26610b5100d86008420356a00042644c501c0d0324094040e076a003141030f009000780303101488640f03a0400c01c19a00ca01580d22079404810002892a8142020f0785008810f078001d5028030319401d501c00c038002280401842150301a19154684008440101c0780c840544d400791103e40a011004114070242c003203010112000e07030352104c1404010110090740381384150b031125804200f1f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 373692401 1250 373691151 373691167
    0x41209060c08030406113a0606120b150d020706051806040314070b090a020a06110304061103040b04032a1212140309010608061b0702120309030a0804060e011103 71
    0x280c10003462103042035035040c04d000406002d00c1003416000d8618a03996031445580a0482452080e1501f81440c1241803010a00d0400043c0c41300312903203400780d41c540e02d0f8840309007107450b1612004002c032040303003410395101f070100c180e000250406041154881c1c144404114400b0b40c24010b80c00269510000c0c0425469999042d01c1c0c410300140c0c8501c075110b00340b10f0302d4041035441000920480b4910003902100c621407040107041011078200030280304e600b0841e10340c006000411b80b019179000b0b0404820a60207450311626501595100342c40040d070004001c8100f081e601913825020f0319041d50700386004440e59880c01e090038540100d0710140d80a170701038008501030003806110046a8200015508a400c480300c2e104d82c030407100c4003e00c3e03459103c1040000d08c20403c080d4070002802280305807000d0705c01070004038451640003900c03a0290401d2800300e12028030032070703418200040c201c482205403841c21a071503800920688010039201c41520007a9401400c2c009014210f00001e1480c104070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 373693651 1250 373692401 373692413
    0x819021503090f07030c0e16050a050c07050a06020325020108060d080c0106141e09151203161401050712180c0807141012050717041209060c080304 65
    0x1000b84503400c2c0d4800c8007180300200c08284041e1003d0750080682a420f0303400c140c1c07450100d200103403000c07094812043c4180d48090744030055420011003450416a14039800340035929106094011681c045030b5094005210b0360000018031004050607039425684092582c418020502800d000c1d000c2490303034000a02610f03180c1003801c1c44602c5400f03400e040c01e200d00d64960860b400350300060140150303d12620610320301070010720900300003a1154516211254045034038581d000d40070595002ca4480341c50b4076a42d0740218100182004001c60342c4401202c1c070700c1c031400c02030080c09850201e10310b80350290106043c09520321407041920390341480002944031400500c4c00c0c403200502c0000d041005400200308508841c01003103413400030980d042c10401c0700e1040242010380248141c40b454005071540d0f4006140228000120358001100d596020301030300c1e400e00700c51a100d0030070240340c204402c004048190358100320b490f5807000d0b0302a41f0307204107552006600c1c0c00070f018032000b40006000161 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 373694901 1250 373693651 373693657
    0x11010302130905040b0601020c030304050f12011e0209010f091511010b040908130801051605030702100f0c02061f14030321150f0919060f0801020408190215 69
    0x21100c1d450310599642d100c2c01c004562041c0d03401c0318a9039034030052007400d40e07041084010708181200550300e000e107064001082004220396031030280c00242080310300150f0a41c03000b2503c10703182280e080c5c50880c034460000254400c0b24541d0219041441402250388100440d00070b880c2902000b0255201c2030703c059901994140312241650f4a0381000c00705500c582c080c80124501c103208081c2c854442c88000c0c1c3d201039954214480580c90712042101540844a08159042d46030400550f00c1c2c440311400c0b1305200502032000e007101d0400c4840344101265501c13103442201e8076070942e051500d1341d4003001c1000d4900d858520552107940014040440241744a00303200d00c2c020200c030b20f00300c8094030311105540718040b6511b400e01c100c0304002c404201c091001c5283c1c0011150603045488140000d50f070840c2c0a00896244e0740404060003010000781d2001020b88a024112607440d40d4424185002c0e5210b801001082d019801407540c8903203a003000340081a900502134282c003c017154020700190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 373696151 1250 373694901 373694917
    0x1608010603080f131a07020a09020a020a030f111204030b09070b19090e18150702060a0f09050604050102030a0b030a02031b0105070605010f03231c0c0b10060905060711010302 77
    0x240d040d0f08001040503040200490805c07070641c58949070502c5004010014681e07900ca002154010031600d40e4550380420440400c980c10300b4005001140c1c828103c41d082c80d020f50702c540740c0c42124104c15241c0c2c0148064012a0312562002c0410b41c0d580c00802c0d00c6400790f1180b400c03051402e0202442c900300064041001040a00e0a2442c0316a034090405091105a80e010821100381080c120b004600340500e03d81080c0c088401d000030305200c0c100a42d600c4004000c1450f181d41c41a080d8400c1c56540c0220350760301c2d0084204e458078205820458002e60060b101511124a01303a24a601d90901251b20f298203500100a003813910301c2d0205501e0001902080d680c1000700821070382c40080c900340f15160190034410480988181549020040d0280c5044580c2d40e00f40342d064800030300480000e01400e0942e0120320007008644c1200155002c127102800145800112001c000a15050490a1040307a0159690318003180d41c407002c8c03180c14450108007615007801901901e41e50350013500180041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 373697401 1250 373696151 373696177
    0x909010e190501090e0106060f090513090501020c06160c030e13060e07030e0106050117040215210a140f0c280e09060405010503072102060c1608010603080f 69
    0x2200328110440708a0340240c00000752a41d48182c0051540c2c0240f03d4100501b540e81080242c41c0048070000e01400340c4c0d40b042c82d202e0541940d04c040c140e5115040444010340c010001d41d10b502402588540340d081c101c4d011a0002141002c801038039115955041043d038040d203481c08603404040500c0140c1a5001d62902516200c0f10001003000d62a40960f1044005681c0040c9a0b0710260419083d2140d42e48030604002508003c529001e5500c0119500702380d04a5014105030080394440c403444c0249200400032035400000300081389100043c040c818080a00300700010036524050a546840981d040c440c0403400b580040c160000d50030003855110170503080c0d1030b1803589210320041001070007042030b40001c810903400078443c2000040e03243c004504560500066040c90082a520400362141b540349044030300401040d00e12078141d40801c41d8024144580c0da030061340120355078000c0214180043c2001c42d400080350b6034107125510a81c2e502001146c50410398401c8610160008036100505c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 373698651 1250 373697401 373697431
    0xc03190b030109140d1409130902010c02060301090f060909170c0c0a1203033806091302090108090d0c0303050c0904092427081201030803061003020909010e 69
    0x402c1c10413801510038482203008000388001c071030340100030418020300840900d8061000c20f4082c0d840c056041e13000c00c00e5400014021085000480e4000380c000c002a4201c0c00c00400401e0b010103a0f005001c6100800a0500c805035a030701c07544040390416003002e080200100241800c2c143c0071b00090840f032000400711294228444c0c0001e03100201c40c0e1000030320f140c5c0d0841a004050305030087c0d1092003c1c044084080b10545007030f00d800001d20144e03000c9107240203034500706113a61315400d03504c0550001d8426007100e0b1040102c2c000075031240d40002e010a10702d8001031070b20700300042c1d82030711000c0e01c0c1e6400c10b50014980c5c054000e001c1c003920419040005125400700c030b0300e85e4440c40321034a0040d24001e0600f50308a80e6a048600302411400aa9041c03950440c200711400003542d001d46202500030f40c802d4141c0c02c0481050060380343c050061001c5100010502c1104da01450084100b180d00e2402220000425000c0740324100280303400036856401003094400360314200b644002400d041e100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 373699901 1250 373698651 373698653
    0x90a0806070806040b04090c0626191503031b030e060c060126071e050a06030507030c03050105030c0d020f030a03020a0b010b1201090e0109140c090c03190b030109 72
    0x81460801c8032000005501e2204000191406000c1c0c1402440b00f918200280501600c3e91600280c2d603000380d10a002003181d0201d40c20302e11030308841e00d458001091820034140311700c9200452801e181d04584040c00c00364022840401c26082008030f95164a071200e070000030400102c0c86011040041c5c09200351840503412a0302c81d00020b10240140201074030543d0b040915031a6404401018005040e858404d1800d10382400190034040e110a584040c15040102d14004251ba820b500116003009625200084030794168000e01d001d41c146880520407001e0240c0118121502403091070740c90740c409404003c0900348640c0211015002601d0014511000701c046840c00da040c3d41c0440050784550038a806100322500d0f200c2c0903213440d090407803904941141c58420010180540f07400150740c1d080d07502d107000e0254040701c0000ea00880d0603001d4200001802d4441b144d0000e0a07014105107170000b840c070b010b290f080701e103d80c03004125072407052000710000001704001c00352680c0565032005810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 373701151 1250 373699901 373699903
    0x302100501060302071a01050303070807050109230601050301020a0914041121132303070506010b030a0507030b03210c1c020f06060d02131b03021801050f0f090a08 72
    0x381c042e104a07200035035244c00c0d074030b0040511040c01c2160b140c40792080c4014009664048100c1d1881604410034035124061820064014104640003c100071950b500442950030005401c40b4001d00d4035090f01d140340c0e80c0c0d409041c00e0344074814041e000110440c6003441081b60380a00c80c90302000103000000c3d0208400560b0f40300e64030102c0300302040d90061039030102980540c100343e544a9901c6890204c0272160b48e54581490340c0714103261440841e403044048078070340c04000b60303646e40303422030101c07851541d6416a4004d0f9130b00c01d0318041701203800e110014210740c4c000d0188213030b2204040c004003a8059906103c64080340d6031080248115010040b42c458094200402802c014824070818800380b032001019142c84101166200d0980007c010025660366141d06a042d003a010f03284458107030072400881c001800040141c08401c44a140c0502d11583d05a001d01582420080c0751944140444019a4103000b540399500e0207860402403030900781c00c0035000d410a91000fa0180e5030564940f8245 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 373702401 1250 373701151 373701161
    0x7030302121503010b010905090f090f1504020103050105120d0f0509040630080d0f022101060206070914060a0314040b04023a0503040518060907080121030210 70
    0x84a03059a003030102c0180740f43c20300ca040700e00341c000d090030010345203040082411040014965800f0603140e0b400692444000e100e40ca139000081c900f51242140355502180900070195801d9001a1500002041c1030909409011480805500409500c103143c0340890707800b40300700c0da182c0812806200b41d9001392560300805001d0000c20200107003002401110601c0c648141e039440c036041095034001400300d0103e8044620050100c000410103164100001c006489980d48000100c466402a6400103c01100c410305a402690030b44002d5214180300711940c9925001e481156034407201581c0e1907182903001001100540d08020602c000303502d40320444024100c1d4192600b260b01c5040204616207203060080721881c54421072055044480113507881c040c00d50b290700700e050760740c0d0f0800305000082050700c0c0144402030a4882107401e07124001c10504050b00c16034000c503403007008900c3d0b950003540a6070503940c0395020310340c10001c0c813140b080c0b8034503642006a041d8002c11030050000c401c98080c0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 373703651 1250 373702401 373702411
    0xb090f0f01090b0901020703140706180803090705011d01081510110106150e01030902130e0102071a0106082d01060c2913080c011d070801180303020703030212 70
    0x122040c0c01c0c100424544401408018035920410110000275007100b0074074000a00d00840d00d4a980441ca8620000c2c4204a414003041c0100b1003500108038400008501c20501c900560310060f50b150010350765250083c60840808a00c104c3e03480b62540304016181e03004003c030b141c0c004940007102c00b044507008001d016400003500007401a121a0090284000900e0080c0f803031804407400304001421800c410703460740d0416458140d9101550740300308001c0c06070000c0740030411440d5030000746103000f5800241d0440e02500004202444884038030000d0f07040324410385a440455a07061042c4119015010740b044000781502885c8240c404881d410310b001e400613403a0a030303520029040c006480c00360300005c3c07191100039629102d410425030ba001600300f20502914140c81e8070604d4030f25103500481450f000c5030341c43c00e408104500c40b950451003d0b89054030945a4460b1600120b5090310500c00480100070b0050616000182c0b00e0340c000c02c4c001d8041d20300181403035000c1c900d04a240c20b0540b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 373704901 1250 373703651 373703653
    0xb0607080c01090309060c0b04030e03030c150a0b04060302060a030917030a0c080c13061211130611071203050306010504150207090501061b1106070503030c220506070b090f0f 77
    0x1800808144e08154050064105401c0040d901f00155690001c4141300034401002c1000c131001000440e102001a40e40c043d60380f5080c0c40c660030200829042c010340458460300701908060040c0c1d410700b00744c400c0750103aa03009070074107140051841c1e05401412079202d040302d03408021080b0003903590700c4002440c001d202800c00401c3c404190f660003482a14094194421150100603148104110f410000111042d41c103180741584070815158000f07000c1507540382000200010202010110f1615500036241c264480046981000e40d4040d55003e080c003450790711401c140c40d601c0120780200c005d10b510100c1454891300e0661142400300a41001000c1e0f100035910110040c000c00c14070740a403d0140419180c000384004594800101c5114510400340c0085512111546030340c5503441211195504001100da507403d050117803182950124122008004e400f1000b26980450141c143c400c840008160034100340594032801d81031000074091019900c144586800480c000380040c4c244145050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 373706151 1250 373704901 373704911
    0xb070c080601090e0a060c050c0304180f110406030f020412060b01031a010f0c02030a051903030c0309151a0307090209011d1f030b0303181206040809040b0607080c01 73
    0x4000d4600d04001030300090400c90502d90755071185030001929014443e080725010551400000041c0e40f0391081511030b400c18080002e010800400070640d40c4031108080d04100000f04604801204a81e4520a03204d9008020001004560300c242c121130002031a0410043c82c140d0344c1c24440741992010385046529070b44a000141c215a054401d007102005070000f0004482c0d910000281507101904c0382c0c400f8003549002c00c2066490070402d00660507480380440750360159901c0c030171000740d58242041b0b000905050002c0515171082c001c860055511052100e54250041c02d118060440031140c06103a4861180c80d5149a404100004c003c200b20350005907204c1c0004001480c4004884010f4a00c80c082c55440c640c0780c84e014946003800140500030b090001a0038403c4002d41541d1148035032501c03005c501000d1a01042e040984c0255040301e0740c5a4500d1881d0010391070300c0040f80c028005040a000c07034051810075410134801040020007503880d040c0103030f48404c400e400401c1d2014142c2e65071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 373707401 1250 373706151 373706159
    0xb06130617010503030a0f02190b0414030c07091d15060112050f010b0304050709090302030a0807020c010c11040207082a1f02090a0b0a1d04020403030519090b070c 72
    0x84800c981c020000002503001560606001c2980c0c0e101e40c400c00c0c030400001e518003803001482442012a41a0418a45070b13902810382003a0030040b03410f4400b903807004103201c03145000380750000460709000b50390000f40050f5032a00048200400321404010445255150a144415030a00507102c440414a10701303442d50501800040800f04812000d0525a152000b4000d00c440f0401000341110000540980c0d41da0760341c0b50181c10881d5030751001d0001800d00000000b00350b0080003074604901c2c0c030b0752020010360341c4540481e0703110f00b09801a80862104c3c0704030001328032150b0100759071507400380c4098a00603256481c0c00c1c490f4405003a50101d00c180d10040450130b115240001441c40140004000c40b106c40d00300303c0c0b0300001ca80004071401d0341c0058001c2c0e61351a8138216000906814000342d46614501134050052030300041d901c2e070340109841d00106946002d02c02e4500b500d0f0140d032043d00700401c8400e021104120001c02c0400e03c0000000015200641401040c04912407070034000c0c01464 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 373708651 1250 373707401 373707407
    0xf170307091e06081317070302030c01180b070c0507080d02010516080f0c07020406050a0303080423030418150f0e0a050103030e06130504020a020721020102030307120b061306 77
    0x1031994a40d80209040020803090394418510707500170f042c00700d400400201c0e17841c0c54140440700024482d944e00011444d0402e041d000710141c044042003000074440e03031221240448030501a50340080c0422141400b29100c10f201d0305146182c1c17072041d021282c521b501c41019502d0b2003460515540141e4441040103105040c1d0721128685c030940e410002981d045c4500443e070581c0000306081010600810814150768640d08050010540686044c82c0c40da2079040090900c40300300c1d01514030202440c007242005a101c424a5104c8001e08080d504180c20b21551002121980803009445901d50240c90b0241e00340c19424001044040858a01d1525180c0c000c408050003d20302c5a0f1245081c00400100b40c0000c040c4980c02d0089490b5070351207402c1080c1040340e803015048980c00c9440880c1c441c40140e000039085066600743c00320b209103a01c210424400c46017408100074016001803004c12030090280010825001b186003000c944040c80c100440c0d0303517410214100d060003020220801c074041d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 373709901 1250 373708651 373708679
    0x5010b03030d06140303180907030605040207380a0e1005091c0203041505090111100b04060b0f1909150305011403190b0604020f03010b040807150c0f17030709 70
    0x4130076005142801d8880441d0034506d90303203098482c02001c2c8000051113891180e400300c0b02a0400401c115218001401c11165062b0a42c02a103410f070300d005401d08055401c004031900c10b001308a400600c0ea91003005020281c011403449403032a00c54054243c0200406000301403044c00a0f10007401d911440300c0c141c100001c060040300f4290b410400043c040c0c0110710300c01075102c2d001820f0513650344000f5070040300c00710030350440c4180c0c901901313a02d00045001303604210303018001140c00307010007521110001d8981c030449141c0c007910030303040198a22607545004042c6a100060030320000c12076880328582d10020030842c04078000b90380e450051115110521205080c1a0309800410b03012100c16010188007550100150843c0072640002e505941d803901140c2d102000d180c140d035103131359607103144c0b484d6504580118006400741000100300d8040c0d07c140864003070f40ca607a810801050321388075016800c10f030b05026036226420320740d04218070a24000440c040d0810380e5404c07030174520b02100018001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 373711151 1250 373709901 373709939
    0x6090d08090a020616060507350105120118080d0f060803070f0c0b0a091a09090c030712050f07020c0111031218150106030b090105060307030905010b03030d06 70
    0x40c0650600000103030004040c4410355041e10340b950b90b1006214030116030070411600074285410f040400122503405010022091101480da113505003003403110351040c05d13604010790341c80040040100514903100090707001c002e1004000050340f6051186200c201d10100300c09440b4102c1c00100003181c5681407049600c20b1281440400005081511032501c0b4072032118050701d51040d605098091003da080003800410390300c5025542c480354130310301802c0050144600001c8112090a141d00754040404603060050000c01d00d01e01541c400c2c020445503003000e0103010400080c040d015184103914402c103402080406403244007485d100c00004c1c9491040080b4904004000192051001001040e990703c0311024001c10b60603510280d4144071100c0c15455005244101d044040c88020039021481c144c50440d502482102d5400061044080d001e01c10f903500094200000741c990b40c071036403151600f5442000040b0340349070007100180ca1600f000c4400403080e0b9440e1000c1240c2561541c02140c41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 373712401 1250 373711151 373711157
    0x1b03130c050d0f140f0d0e01120c05070327090902030c1e0618030706091502010506010909180c0f060f02011e0e0a0b090114011e0902090103091406090d 67
    0xe0b1040350358401c54410024002070188103074060a03400c410090100e2000080e0705401c079030300a00f1003503004103940241c220710781c00b10b400111401e40c241002c0c09100012101c5032541b5140c0003c0380d40c2202c80000b000030000010f2088110030111841c0c07080c41a00034200d0765808680c02c01c0d86c2c01018104042101d40034410940394014105840402c0d802805c2c540044132019110220300341d01400351401d9551244e41030240000200300103030031105a90503501c60424001e02d0711040f9200740d00300e403010358003140414130ba903a041286e030402d07810a01e0111402400d8000c204415561111001d11580202950710158a024480c0350790100301c00c40e400c08284028400e144404c0301c0f03004e0168181c4c0784403880645070440b00107020000c110100d25240d100c036400030603181c8a03511758001c2140441107000101c00311300001c1c22113916000144100131849a008586180c4038606009600c40d00080d03050640300d0740140e0228a1107200d002c000400c02d03000c0e2880345880d44941d41070584028607007043c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 373713651 1250 373712401 373712419
    0xf11010203090d11010509061803040305071e050a0f15090e07020a03030b0a0b090d03020a12051305090606121005061605060106170403080406090f03030b0f011d04051b03130c05 78
    0x50400007508c203400c4001012a84007640d01c55119030f0541c40355401c0500b092042080021350001e40c20120440780380313451003641c0700300c0e1510204031821a075846085405820002c0034000c1c0038491041c5080d4214508088501a03610b14009000100854581c8003503005680d03401c06140e01270040d000c10720400c60b00c6015040c188100c2900d107004540055005000000e1441d040500800003140c1045d00804101380600701610014980d5000d00c161b4050550380c1e810004442c02c0c8211854019500200b0182c02c0a0442c03492182d0f81034000c260440300021064005280d444481c003c0002e000c8604444140a1081c1000b500c0c0c1038040c1d001d00200894008010b6038891110755043d013040c2d15161a00329500d071030030440050814100003030b140b08201c01c403400402d605035204030000242900c40000311040d810040d100e0ba048402403c150300721148100c3e2152901d503004690000060802c1280128820f20741181500121100312540a40c12164000c0c48250210440181411580c41030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 373714901 1250 373713651 373713661
    0x12050304050d08190f060f0f14090105010806040902030a080a0302040f0b070c030f0f0b01150e01080705041419060e1f021207110d0c1401110a030f11010203090d110105 74
    0x540d0386000c01c1c0d6002d0856071441780c5500343c1e8158109100415000d80b110031055111039030740d00031006a208070000c42c1d0301a40d050030340b81000c4181d0341c1212816150b95526030744010502c4043d081e2071300202ea0500031404142c000034031190140500340304aa40068481c0c1c100307003000c540e0405641001440d0f19040c8504000640070031103050944c0c0c1e002441d4204460b040c500b0710b2168000d14001084190480300100f4800036060521100c0041ca540d03003201d610000d0015201380c0c0003591038100040c41000140150b07068064000f002c054054550b500301d00075030510b440700d0482c9800503000a681621040f01d903103004030f89802004000508100e600042002c042e40e203400030751101221845c0407407690700b4030038046a070b200624000750121660503500e1800e1540d500680c042c980c00c0303440f0446510b510354801c00310b03d410541140c0080c800c9007000d49040d1803c0c84113101200c100000d100c0401003880b021b0000d18040c451440003041e864031a10b001034400c1001d510168000c1c1e160400f000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 373716151 1250 373714901 373714921
    0x1008060412111507020102090a061d06030903120f060306100f0e0c0c031b0120120411030d020609061b0901030b0a0504020c060a060f06020a0605070c12050304050d08 73
    0x1030308050080c10b2034821140d219415070309101d03e0342901d1003800c0032a001c00034159010b4000741078080c021645408441c3c0c860b034054500c01c0422610140001034a5806030981c04e102000390b400420400459003048070b40011061004411034900d00107254034814031aa5003001c00c540c2c3d0f00b282c20310007542889070a06524030312131902c0380704400040340c03040041a1094800402c42d43d00701d5045040e03070742d070303030502e602144505c0341ca14000341c034542c60803500e6400e0b42c1d6414400c014001d4240f001d0781ca090300a2458001845002c3d0044d252000d114010010b1b95a003000641241c2c649600a04494546011003500706580180b22004c1c9210821522910500713a400700d804900090900260321a21a400306030306007040d80003250050320006106410b4880040c0062050000080c18007a0f607448030328aa001c0500f900c40c04001da8403000c44100040d001c3d8121546c001d21505e089010070b0b20719100e6420310381c49940904042180001031209005041c40449180d4115003415125401c1a41d818 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 373717401 1250 373716151 373716173
    0x2703080d0b0d0b0a090606170307030906020c101404051906080a1e0504050c04021b0106050607020d020904110301110d050a05071e091d18011a040207150c0810080604 73
    0x4480c950b90384070310172000c01a040d07004c40003a021102d400400c0507000540c039540c0340d20850b802e90201b0341c07051000903a2480000e0744000e0100142403c00c140c101101c09551101000034201e6070342c0c4081c4000729040d01c070851840e1241040301e01c240c42652a10b80b0141c1125000342c249880c5c0c504000240419241060100c90094604070002034580e0b654101a402e00700c1c41c5e180e0551150001900b00d18010302800314a120385d41c000020004141d4800404c0315610510320020740000c90300c1120070142c604035010603441030280040203050404800001d0854030180b2041450308400304101c9c01c030010388c0c0300e400d40c0305201d50004c0146041800f0050860204d2500710308550b045100450112442503080c0b1000b0f00c918404881e440d510707540d40c040e114104a0b01c1c0c01a080c03155041d80308501c01400f440c00044003d401452031000c0c2d0809200c082e522030300b000d4503140820940c6085404a40c070514041011a6444049c1d508020416002d18219540591004d500000c01c0c0b0010484c04121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 373718651 1250 373717401 373717411
    0xf050702010e06161a01080721060b01050c030703090e0711072102030708060105090906010303050906181804030801080c03060606340201121406012703080d0b0d0b 72
    0x10703c0d02d94860000080d00c03084c2c4100010305840100b043d04040514a45900e4140d5815070103644a01d0b84500028020903100309174100745422644660011034240e92100101c28018074206107400501048185140e106210440024034051030400c0b0103407c6180864215503e844c0000800e0042c5031071300e41e20622030290400c00b12441c4c854500480e90b030180c84094681c09015500995620005540c81e100244140d034025180318000805180c0c0120305541601c1d41903d9540c2801040c4007405000d410500319840705505d440b4020794a65242802248819401c10b25842c161a0619005102c1001030b07020390b0131f507030240901c0382d15071f64082030343c0e030f801002a41c0c0641c483d00030054030b1410310f412940301143d512a1804440003040c01c11140b0300c501d4003c2c0c851601000001d1103910465242c10b40c001c03003020255010440707642c0b00b07024044801d5605603000290040c0b9600010b80003100c0d038021242888006403601a00e80607000340414001d080b00d40d81c0c541c1e02c050321180101a00101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 373719901 1250 373718651 373718659
    0xb031911071a09031c0902030706030903050415050d02280203090a06050d02120c0d05060612041b0f0b04090b04020307021504210806190303020c010c080f030411010f050702010e 78
    0xc0015120300080081d00c01e141d045c8010445402e00c01c2203032030010500c00000340e02178000d1590204403103029014284c1c405500d035807a1894603280038110a5209271401910080280c104441c0300d064419002900c103001c055501003100d00609411103c0c512003004220080d5002408010442e507502403040301295034034245a99a5004120100c000703120b4002c0d00d40c0c929500600307000d01c507070358000501110a10b03003d0400484d00c45004201c114003074042d01c45000c81d80d400c00240007a02c1c4410240c1103621381100101240d0700c480c0a08002c0c0d4198005601c0302101240070802d174144c5000d610b1030050152411469070501d4a0b00070348607040c411200400d40307040808602049480c0490760f00c819000042c2070003091050100410303442040e2135030b6104010302c0000d402e0440c0d625001004403179241d00100855074000d001580e10281941c01590200014010360001d050000300951007a0700c0340c000d2401007080080050306900079120042c0410000380300000050340c026144c0b01e00303030304111 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 373721151 1250 373719901 373719953
    0xe01022518060b070302032515090204090b01080c0f01140d09020d0503040602030703090905060d02040c020c090c130611070b18040c0c0506160818070b03191107 71
    0x81005030280c441030384140241c00b000130343e10051582c040068401c4200c46034058800e103280c00500d414110640c00080c2034250010700c280c051101650140504920143c004120f410064440c1c1d070151409038422030749030700142c82a45051424541c092504c003003d0070504682440325540c030440f40030b02c80110f010f043d5580300e54070039540c81c14403d0055a40c40821240d5882e01d6150094aa800c1480228085503550300040b4001c0e10030700606200f05070290003100c102070182c0801c070140114070543c1007035010304400c0c03400a46520540f648a4543c03105020755440c103140024850419a42c800c00401050062016003c00040361000c115680c4120076601e031a10fa68041001144210416a01c6413a00c41c0d8146107a402203141c8000314091016600c65645450301c1c0301c0055100c401c64000501c035400000c0100030860000c0e81c1d8441c0503030440d82c0b40340c0c49000800032175109940d41620580002a03c24125206e805011140400c6881040c10601942d4130038060070a0204002e1030300340f6030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 373722401 1250 373721151 373721189
    0xa0212030f03010306020a0905060c0d030c0504150e0906040902091305030d0e0c03120a0507080721051306020c0604060f0e040f0b01020f24040c080a030e010225 71
    0x208251801074080140556603541c3d60725068000307601080c10f850115811001c0059a441c0420030348104c5150b14001e0040720218280c2100144010742d40700b002c0c000113100100e4840d1001a0681c1c0904003511180d0450880800304114203000524070351040303042c86030700d10041c1c4660207490b4015088441c260043c455900c0e006055020b9000014402441d164244440348800a40d0f0b1041c40005d9050352600106911600e00c40c0c07080d041c002012580810072480050b00c0380c00200b85080c0107498040c00030400103a1520b07100341e0b11034914009000803c2100c011002c1c1300340e07040100100e000a010000178517001c1641030107540b0800042c011404009000345000308011041e42d04014410032504503c41c210030018402c9001c0c25006100b511614851403100091310700c19440d1008500018030035400030b0282c020401041228244621000040e040c0820800301940e00e2003030f2100304400d802000020702e401440711609601d529100c043c03031121210205250b041d201950b007905483c03944 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 373723651 1250 373722401 373722403
    0x501050d0308151008010e16091a300c09010903171216020d09050307090e0f03120a0506040203040f0308100f0e0f07020a03120203060a09090b060906030d020a0212 72
    0xe020740707a0481084a14040c00395400003441c0d059601d803010110385512a48c1d0416590165041c40c9000308407034001c03c1c0120444022a80c9200c480b20242a20345841800e00c542191a190301c00703042180d8210804041c03800c0d0740e41e803d6000516070200ca0400c034251000074000582c1d07110151081600580200520701c09004a58401a004d50035035518180060f20b64220b240b4164a0381c014040c0b1903986c0c00041c40791140c4030403100010010080380742012241c600611001240c00318a115201c40004041000d101034090600341c0c0340107a40b1468140140700c291080200307041c2c880e900c100200b100050040c6000f8008039054a84005143d0340d2a8414030840c46035080203031100c26825000405094043e007084c032503c0d200c3d40c001c01c01e0300e4041060381d0320800e284c00140483c11080454040b490325a01465100c40020098101580c2d1440c030f40d411610a0340303003940d1980d034460420140d030410355141508048264010035a240007040025160070311100e00034032407640c600d20001c130804 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 373724901 1250 373723651 373723681
    0xc051504080a0f03140909063a0c0504050408120406061710140c1c0605060a02030c010c021f090f02060a020d0305060306010b03010e090106080f011e0501050d0308 72
    0x303000c01c41d03000d0303a05400c240305640c40300f2038200d0015250740420f10000680c001959600a4050501c44143e00d400301000f040e92503044025550050703155420400b061403441080f01c4000c1c10001d000c254205040c840c80c00c1c010354010500071810725007880300044401084075400c1c0d4111804807003a486a16183c0e0240556920001c1300c540101510780140b480400c00c4014016403910401101c0800300e01000b600f0011580f01d1801c210901c007010107014038845070402c01451050000c2c1e01900c4900080d03603a0080720250005900124028807000024032500075040141d000070000300d251400c00c0c0900110803840c1c145140d0300d48622000700410350361580c0d101980185007179207400603a04029038403110342d40501d00082c00c05021841c43d04010824034185c134090301e0700500c1c503820700e1a00d020a80c0040c180500f50366841c0030018440c80144140b00e640c85400c00049a5000b405160501030224040c401c01020303d80001000aa9107249160f0803895040c00d164155070f458600d0645424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 373726151 1250 373724901 373724909
    0xc050a03202409040515090408070c2301030f1104090f020c07060c020307240806010c0f20010e030706030c0210050a0c03050c0304020d031116080d0e0d0c051504 71
    0x2c1140c03501d000540228041c041c0000306035420010369942101e60101c4100701e00f80d1030740011401000c14013103406440142101801070072100d902659840d490101031950007502e007035500e880c0140309850361340740c02054140715503240d003441602e0000b09404406d218520a1444203541c0c0d68202c00500400c3c2c0581d020130780700c4070582c0c421940d500000303003181014600491190280c02d4010500c10012000003100a9140e802c001624804140c181c40c50300014000340c0c1403101c0341d18100700003001380c10581d0900c3c2c400d0031f18003c5036403803090f269000030010740007034144224680c48810540300000e400040301d209280100301034071031481c16030030aa210000c41c90081d0602041160f4404190401d0b03000c80c120f943c04000980c5c503599102e41c50b00003030301d00a42c8050381e0f03190800032920444a0041c41c200c04c01c01c2c1c0340303210b401d0b0900082c400403c0e805031000b0340100c50365440141c2c120958005a035026205208010029035802c428142180580b07842241e0094281c60890040410758001d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 373727401 1250 373726151 373726189
    0x150a1701060e0108160f0e07080406090b1305010e010e0c130e030d020403050d0302091c05032208010c0f02060c180409060506041118011413030309030c050a0320 71
    0x1c0d58441010544a1451750860f035035403e06514001030074054400d03108122004100d915003542c80d0120121a00f410150080d5001506c86107010701007000c080d152401103d6045c1d11041c0d9140350311700300e070a68000100c56600d80c0d16004520510300000b0400b079068020031112940d02c6032004260000900e080c84074076070a0720000c1185a8803040303580c010000d80c3c0c0034500322042940d4500046041e84540d415280d0000c0c4e0200a0101d035000030040a4a00f03482101686d0505141e11964080c03856403d00005000c0c4606104024100080c40b454248000350b190904030100e2000300a5076074ac40c003070000ca480d03083c0010400c1e400306005040c0f0b100450018818003482280f418828043c05040d01d01c10701ca030385094101d64008040030203c44000020501c0c62120010b900010742d441109880e6184964104202e00e11010401d000400080c512a031205c40d14581141407411100055420050007003520b11001c0c000700d40c200f010301400c1c54141040c1054200360201049641075050388113180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 373728651 1250 373727401 373727429
    0x52a010c02250501050d0f0e030f0403060e070308090907090503030f071b0324180501150e070206060d2301050115020c10030b120a1a150a170106 64
    0x30305030340810200750211907040d2201ca07140d400c500811401c940c0e44100e44c0854010852000d062010f030300000040142c002000070b200440d00c14840c11a0b0018888007501000000e0034001c010f064030600498000000040c03130120305503078031003595114601c0344e40d209400700800900341b0751084620138080c0c1030242c1500d45546011a107840c517a00b04240499034151034005c01144500310038981811a50000c4d0500c501e01e004090119181e0a08185500f540341c840d02c2c1109988103e090b0b4240203807103100000394001010b1000c400000302c03508032180c0000e510080c000025070020b50b070740d0054012034016601c2003061038610322202000000203d90310303a60091a4241106500450482d48100703510301172544070600480e100c44500288950100c646820001014401c0c1d010b05000350b40070b0003600801001114003031410002c0d0340d0442c0c82d203001c4042d04038600c1e54034030902d401c400c104201102411103000000d010130040e004140b08a01e4450031601104004d41103540240460303982c02c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 373729901 1250 373728651 373728671
    0x2031207030e0907030c09030201081008010603050c010215010303050f0f0403061415010c05060a0c02014115091504090f051608030a080a1d0d03110901052a01 70
    0x6600d0402c10291080340d03490002155980a070207040314440080d076030f100c0e01a00710790041d5011000a021140300d542c0d0b65601082d81d4000b442000302440c01607000703042e070009a0000902e030030074075081d1a54031070080b03004000298006087d00c803002d13503a1001581f2448101518600d502aa07030000c0c05aa007001002c8071070035240031a0034021484605580a40c0c03500f4401510300328031401c0002c101e54407540c002060050039510038011a0064400428007038a9460551101c21601400800c0144007900d403e94a440403500880d183c00602005505031610103403694103881d046c81041d000b00d23500310000360003004405090f0030b45103005000f00a0420710341002e5101c0c9102c40c804450f284507881d07071300c000d15102072500d4044032044002580b6284400004442c0c03004082c08100540d81c0300c480e03200310f482c100c00d40380303c40c601d1000080007a64075000300101500c41030346d840303543c010007041100103e0764020110351030641c0d0449070b04400092240d8100c910101d00c00c0c0c520b207551070f0440d050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 373731151 1250 373729901 373729907
    0x911120a02030a06210212070e100602010506090606040b3f34090f0303030e0c01030c02121b010f020301170d0915051b0102040f0816050d0203120703 66
    0x15000d10803100e810400c5076150003000c0c5176050404e0b12140f18030b440c400401300501d01001c00d58010307040d050070b0b100c81c107a039039103458030002003590044500e980140080c040fa80d4244550350784400c0c00c03242e8410609042010a509115902403c6c0c04018000765221810084105c0c41058081203984805082c3c007100d03a0038001c03c44400401201c1c40e031140807403044800074803102d48a00010008038820000603000c84070b2144910703550b8083c001004000074003982c1014821700110b00940780070541c0000c480f030313003404c003030000e40814141854040710182207980002e03a00924840088120340d5200100c840c603450310415004c4824660030030000700c11510750703500514106d07041e5090700c0191a2a81c070030a0303202c0340011090400644108000c00024030120724001c4070080f28105140380007401c2e0410300f00b2410f0002c0240c4160f40001d4100040c08400d01500c00814050300a04080d001300f0440c011641100d1240600c00c654aa240009544d420300ca00084080c3c0a00300c50b80d00d0405240c05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 373732401 1250 373731151 373731157
    0x209030f071701020f030f0711010c020303060f0108040b15010e0d050a030306050604030503090108040f05010207031d04060b0f0901051605010f0b061206012007060512010807050102070911120a02 86
    0x10700040b001d5031001440702c00b014002d9030104411106403a080d42d94465101d02c070050020204400c024250186082c614020b1081d070030306ca26560702960385d038039190040c05183e00003030714402d0410a56008000c00700d55403105198002041c0b040001c040c941311030049503400140b9004540c031019a000180400c5000541d5a00c190302c01d44061040660307400c00c121460146100107130498008211090075580f24803141944948580000d401030004ca803140c0b4226005040106c01003080440d0b032039101c00080310340094642c01150144609030038001394080380d000d040402c520500005c82d1102d107507805482680c0c20742542c0c1401c1018009903040c1795020f041040380b14007526280801c489151709044e4200c0380c91041400b00340e585ca80f101401154106c14842c183e181108004e1103441a80c0c000340b103410000e01542d0745040e26100714955540300e416040c0c2c41146039602c212400c05c410790300441c0e1041103e40c001b2000582c040307810a0f040191003950040344e10100d04100300f1194104540c05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 373733651 1250 373732401 373732409
    0x319060501152d2717060402060a050c19050a03020705030d02100515041416050a091e0506181e0904031b050102040906060e040b061b030d09061e1406010c060209030f07 74
    0x203c503c0751074170344401502c83c0815517020b9044002007111580c00340c0507a00500c8046000c0d02101c854240c2c90700e18032f0503420900e008803940d4014140c444c081c0350b410003004015100032800341c0111030310b02c0c10281d6a51641c0410f0205141c49a00040c022207104031040c0810b10094001d0191410800b0422101d050413110090300000401c0b0015a05200700305803002c034005601c1e081d065a0070016820042c1c265000b049800305c26107030000c6201c4d02d981018103164002c1c040c0c90487d5400010802101c440e0b140c1100f003002c0c0714619807080a940e0401d02036041501750070642d08100008032003500e50a040c00014010750f000040002d03414290358810001c54406d5503640784941140001c000584072550082a444042808888803000200001c00b610075098001c591410398400e000708240e82500300c0030b84003581e44480d11528000e05001c450600000b01104001c019103d2001c40c014a00103442e01d03040048029200c1c5c04c01c581c0354119580b40100404464006407521440c80d42c1703800a0003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 373734901 1250 373733651 373733669
    0x5100c020303040b010b0316031e0c051c09170702031002180a0501021f05151804020114130603050c0c160906090c02100b0319060501152d27 62
    0x70385060203401e5134090080300c40100c850211403001180035000341e400c00c8100034044030307101703003102b105204115454481d61956511a0030110f0403088444001e00300207801c40c18160b0aa00042144c03094410143d1406040342d02c841160000c645031107010b21030601024070025400907001d00340750442c070454000320b0b22454550380340e20049072035a015450240d526414030223041e1500342e440d0052030b03029015201c0c0c54030b1402503000007059a010a8446440c912008060109550744040b440c1070184005001b5440c2038000c11f60820500d4440c4900020941c2e150301040b11409100d046075080c482d4002110f020101d914820f030f440001d43c1c401d007000f503803030402d0004030326000d030050003206811134000e825254200782014010b0241401607540c0f60160440c000d240411200712039100500401e800211503040001d1101806d42c00c41103031041c4014404009100300c840b000701500604030724001c020601c00e9100c10f031070741c003030b00e40c0550800030386411100400c032000b0300040b040320188c074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 373736151 1250 373734901 373734923
    0xe04050601090e06060d211e0216061b0b010b0c1c170618070c030e031c110f0303011508012907151107030f03140a0905100c02030304 59
    0x20800b14211031040d20a0440c91304030b40005411840c10200c0c407005240103841880a0507c1403000d00d40191103031400c00040b501c108155141100034481590841c44540000c1882d11480030b081c06040c992032051b00c1c10800541441003500840b00030b0000000d41c04001110f540d40c584581c4407658020301020102c43c0718200100880a003400c80e243c90413802606c4a0300501e0444110303420076000107020641212541041a07101c20140c1c0c40345101d00e40540c1c8108042c01c0e01e180040000c1c5515007014480e5028645040c0100b00e140040c900240c0b09040c44082050301111050800440803038050b0180008400001c8040f002c003038107020302000d45e03a2510103030781755814084901c40540c0e5003100315110381c1700005031002210080c01d4103809242d04004865400f40442c0c240c40303906040c0b031030481001c2002001c01d600025400300340c112a0030b042c407a2010385c20300083d2916004101500003030301d40000f00300388001480001080f01c0810740038000404190400f80d5642d00544084940001071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 373737401 1250 373736151 373736159
    0x6010e0f090a0b01020109050f0d110d0509010503070201090f05010510051503072105100905242412010302150a0e06031b070b041101020c06090402130308040e04050601 74
    0x290300495030000c0189208560384410500d40d00038031070401120f056668031138040740401c2041007112030381c09a0b4070007040c81c0342c1a4a00208403003450405501d10ba40288503c2e1015904241a81c1c0c4145081c80e0090326582c075070104901510811034041c02000384000751009101064200520420300700400c811007691714000d104d0704908064801c0c40c20a410320101720b01600c44d1020240280003c0c961842845403080d03040d003100e80644400408500e0400200300c12841d038000c09a22810712445011100711540403203512100761074080d0b00c0b8146101c8000701d855002e54411480d050401d03032030340e01e03400150304200a0507003c1c0016845400c1c04580c5240a40710282191515115946d80722482c502510502c42580c00c064200026800740108014082c07100c0b07000713440c22500a01c810400c038101400c0c000c0c25000c14072100303811904034201244444e100e800c202c80c0388242c2698016030b6008058007004504216030401003411400180000e9107070385078208079001d10b0291040c3c0d0241d0342d071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 373738651 1250 373737401 373737409
    0x402060d090507090515090105040207030c02060c030c060a02070f0f060e01150f0803030103050304030f020f0d03120614211501060f0219031707030b040c09170604081c0b04020403060506010e 84
    0x146c10500d0340c03103003034000140f0940c242600a0840c0c00d03c039052100c120041580094943d070003840c4d07000c0d082d90000c035008010482c00c04c0156088100c41408616108141d240c119044100984c06007034000b1803211201000741c0c45e0b22000d440650f00300208412403140844c0d850700022445580035403665004085540400441144d0480b94404000d40c9010f285a4440035021910101aa40144940580405519019032005503240320313680e80300d0860105c410080480b5800e8100340721890751110181d110351124544461210300c10046a00700c07090683d2003915101c00280c2a0034100301080c00010300d80d0308155900810748841d000d507403802540c3e0f680740424130385042014002170301c00e50401d58692686c09504d500000701d80b034042989004440805c05640ba202c60100c0020090541009640010381542c00c40b02011406440d143c10030751078403d07590103420404000910120980d501c02d500c25400007059540281003591125502d08080700101030403950b0a01042c403816103010b0500d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 373739901 1250 373738651 373738681
    0x1150f0f0e040c09090305030f18030a18090603030e03060718050f0f090103140c030303150f0a0806090304170d02070e07030b150a1b030c06050402060d0905070905 72
    0xd14100380c0c405034a056800c400340500034000707541c401449000402e030a0040e024003030070b940c02500c6d11581ca00340700c005802400802480846a6200c0350040c0e0401c1001000700d0340c540d041480c10f03841c0c03c84030b2100c0f0200c0344155030144281500d0044004109500702c10074081221080b82500c5075507407206401e80b20500f840c00105400030589800740706502c1d101c601e4071181403014020004500c3c0e0640804c0d0814070a03003003510000e0041c1c8807d80320040400000900510507400b460a40c104180c0c0c2e92441080380e18100d10404001c0c1c00c100722034031890300c2c400040c1102421540141042c01d1903c0d100c2c0d0081c004c0411404910140001441d00040c0c440080e0381035034000c0900c01d2600117504002d010160a0004064441c032100000e6625135031608147d000d20714210b681c138000c06d80090400072142510040740809819150f01007508018809000d0350007041c042050b40d5948005851442803250303036641c045c9480c0032740c0c05100d0f002503d801030700c07143c0104002c030780c60381c0954520700301d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 373741007 1106 373739901 373739909
    0x41a030a120813110123030a1b020312180c060307050703090504060b030f070516061e09032703140a05060601020303010b0f162922020609130e01150f 66
    0x501027808c600141060f4001035140c40e201c240501c8209800508110b0007140c0f1501107004c0b00c07000d0041c80c00d0362000601d5540d0b41e14041030050980e8100b8841540000c00c020004501400c05d881a0030545052070203450031031751282180ea0403100000c00c2035040020038000d200b20b118202400f014814411040032400d07044034008014580c0c580c03405001500c0c00c00c8000400306c1c2c2c200d602c41c8101c840b40c0451060545a1a80030207081d03205130300060195001f5100740700e6030300700421800c04061291044d12040d0f15030000499581c082030041c00f100705030402c40e2203400041c203001002c4140d12000b2078203865902c1d884d0351000721880c40b48040c055040e044081e911004030b20120ba03111040f40344072000714103243c44500003580c0c0c900d00203010b004d0000754600307203544035480c1000320760420005000a8494030343e41806400344102210103a940701c640800c41c1486450004d041d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 373561151 373741007 := by
  have h0 := BRFrame.cov_init 373561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 373561151 ≤ n) (h2 : n < 373741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
