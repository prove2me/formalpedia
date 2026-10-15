-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4662
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:20:05.067289+00:00
-- url     : https://prove2.me/submissions/2a2772b3-7ae5-440c-828d-7a66d219df6b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 838309352 ≤ n < 838489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 838310602 1250 838309352 838309361
    0x423190e060d0c150c030f0c0507031707120e040b0d0503031f1203051903050f060415091401050a1208030103080a0905031e16030b01030609021216030506011d0a091401 74
    0x204c0700140c60983d04005064015a50303045009480c50b20b11186640ca4860710385136011804020651940c50081c1583c01c50200c054032800e80c1c0007001000803180085020b080d20302c8070140c21740502e081409040040c50811280c1040c2c64100002e5451030755101004040071228180b212050162040e003c159107030f010229200c450b02c1b94460039a0b44000881c468070500d204484002050f0074481002404c20041150b40d0304213000b0f4402154070b4410b41440c90490310300e604107180325454907010410045114a489040310000c0e201206416251203260b03201042c2914013030720804007000100005000074000f06100040352510011054031000040d051443c01400324520311914611401c0300c040030300000e40814a84804404e00c5840c5a907501900b0005200c003400d819622a200d106549840b1880c1c1075000780070042d01c3c4a41147c6114050351049400b003911540b0400c4004600f800710081e403c00c0302440c80400365099500e0340741c440007408a554040307071030034844660f562105509009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 838311852 1250 838310602 838310639
    0x6080f030c011407020a06151e0e0705071e06090209090105100b0a0e060d020d15150201090201082208030901020d05100f05150423190e060d0c 63
    0x610341c1c03070390401c0110303081d0744401061864042540c020300140c5600001d800b080e0540c00000456000b81c80f506940164102e03500902da440b0741c42c00011802e030701e0109407805a900000b0b01030240d032180300d400c41e014080d8200080541000c07180810100b081040e019a00501c560b0001c155040b069012885031442968030502c00d07910b940600c540d142803030a42c68094010624044e0500c030819200070102c0d0500c421090140c040044e50141000054040380c4071b00f601c001082c0916141c480041d001e0b50301e07174070a0000038454000e04102161043c02100714540d01651186140d482d804007414449030f030006660b209400c0ca007410400920003c0245200d1480040016283c000d0070342d42c02c042d41c2d402015203005c10b0581000f4829000311540315000d6600984031162008003810760000b20784943d401c554500008100c68422011070350101402c21413041d510166050580904a0060742980c054480b09684000000c2c4e02c50a1815400c1d0966011f248107a00003039841c03e204030121103144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 838313102 1250 838311852 838311883
    0x803041703040302130c0e03150601030c120501030f0b09030a05040e060d050d020706170c070311030c01060306060504060b03090a172701090b0a14161a060111071d07030608 76
    0x3003506e007165411120074191100103070050800d0600035a418418040300901503410700d40c0c0c0c0c0143c074412901c01d04200c40310400070b0804000300d5842e03092a90307000e100e01c902155540b60305400102444c170003000f551001d00c000e0715642e08082c1020301d541005440201040d0300a81e00080e150b0105008005400f01182240c000e03254150906000400ca40498080625200c0300602442102200402182c91094061130030301d800d0350301c081815055118075001d1543e1723582481c40c00310a000d6107034400803c4503021a0104100d982c0d515503448140821100f440f1140c1006940202007001c03240b4980b01ca03400c0304070042ca44623219102100501c162900140840100704d80200382e03507040312403000a4100001031274102035110f100105141c40c80508110222004203600210b40890f00c21880c81c0d40e800317024a03036072003980307403256000301011181c507800a160701394243e20010010401c0303000d40b40d076030303070f010310000511400300315103940c040c0c8103004044e84c03140300061012082c001890a490740d00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 838314352 1250 838313102 838313111
    0x30c1e0e0a060903020904020d1b081006120213050403030204230a06050f0313110d030806010e1e06131e061722020109090c032004080304170304030213 67
    0x840c10300c8942070a503000a0140104520148050798800300c50a03405a4100d0f460b90540c280c0345801103400d440a500c00c1640700f1820000300b0801008a82c8040b0442c458104100455680e0b0b0f800d4010001454003940020801c11000c1800300380d6003146034060300070b04000d890140d40301c4a034101c1c151112200c810f44911111004941d01d08002c00740d004011030b180c042e042c003a1407025442103200251220301810340a00700d480420150903140c030811000246111184420740c1406003c0482c00c03a40c0c04d00054041e49000c0d000c2c03600c00ba0324008090708004288007805001c05000b81540195038007003401419800004020215416808108a1150803010282d15004001d0309032109141c4107a08250380d08104120700e400703500e40d00d068082c801d00041c20f4240500040e584212603401008005040203040000e55800d9000f46104102c2d114110308420f6510314005104d00640c080d280307898004100400c0400d161200440200c40340206032494640d603580003d910200b0450f148440c1c40e00d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 838315602 1250 838314352 838314377
    0x6110c01021305060f040509042108150a0609150917071508010305060c0327011d070b0d0221090106031505060d06020d0902040513060c050a08010501030c1e 69
    0x81d0380c0b480080c2400c0d18101d04000009404208500031030007428042d10b004c400003010b2200001100394100f90581d0200b00b0f03491200750007407900d070089130a5080c008101e1511001424030301480000c40d0259620302401c2070030401451260448928000d0400210301c070049044800d0100188034016070500402030710317141201e44d20000100510361010300404000401c00304002140f41680305242c1c0c10390030364030354424aa6030000014000c142e0801c0904240d1420a40f00540c807801c407411740217000b813110241542006556500c10300910902940900c00c850001c0415009042c1d0000200908040d1101c00102006d14600441d2460385a0b07448070800c00038401d084610380304200803030900384034500c2c00c1c10100b1650310f242d8134020a29640003c003912004450f62011507950780c01030040c0003e081040348440b010002c1c103030a66166103000005038040c1d001d1350072102c91800700d885441541c0c0c80c101c010341c020301c81c02180c0c2c001d22403042d082505615404a40d81540151510382c01801d620 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 838316852 1250 838315602 838315627
    0xc14010e090619171014100306050c16061a060f040504110702031f230f062b02120c0d030c03020a150c1202090a0302060708091c0302061005010f0c06110c0102 70
    0x4101c2124503804586509219000c491215407c2c11741e40c00041c045401c0e141c041c0c40401c54800d0024241a40000300301c110100200d540180459003110030108181042000402a661095130b01d440c03810f1108020402040c14140c1112005400380720405060414540209040c8804401e00741c3e0405008000420351040522521704114041041340007804003044441c03066034009892100102d42a41c00030700240d48075561450b428a044529801810100540c3d054504803410b00728850700b0250300011802c0e030009421152908006e0004540200c2901c054440d012010815000c5002d000b0808010808000218207001c0500c0c2001071151600040200038004804100b120365004001c68421546c910b00d000060ba0380450b40e25603184424038003503d203441074044441d0404442013004402c0100c41c82060f04c4240290250313001076544203004001c801280c0242804254a0f415850902d84126031503a0541d22540f0001004251000044501d0701305040d52002e0740e40014114141c0702 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 838318102 1250 838316852 838316861
    0x20a0812030a05151e0a05031b03100b030307030503090f07060c14150118060e04081b0a020114030414011a101b06020f160c14010e0906191710 63
    0x104007002e00000b0055880020004e0703403103a01c0412148417000314400310380d55406048004003001021202a074420150340d00c40a070750610214402d0140700a4030615070300500070180700e41c0e00140a14901505c03560b0590300ca40000e0070780003140c440d6044a107640c0c0c404206290203802c940d00c0701c207200e00c0700d40b0300641c0c4840c500c0d0b0042620742000e007c0b0030131220000020760565054540303420071400c902d14001d0062103184e02102d103100c401c90610041c8807a0b00c000700302c01d10000041c00f492400e8605103d946000d000002030000e04a042d0224050808070055a00540b20b26000340c4944411142c0b03c0c01c0d950040800020440c40d03c0c3c424070140380500068800000e10b0a01c02010208103241a00750510803d0180801d9000100e060000070340408969620164400200100c1c000c1d081204060070303039008035032a43c3c1110180c009c86602403204500d6603d002499814039560f02020710081c000c1880640d51482e841070001719125500219554001c001d9070000c2410503001e0719220141d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 838319352 1250 838318102 838318111
    0x602090f0303130e130b0109061e120b0c04030f03030e01050709080703080a020f06011502100b03030d09020f1005030a0b1c0803070216031a01050a140904020a0812030a05 75
    0x25481084420f0b02e00703402c00f005008980a040b4401910b5540180714010003c400c500102054146000814507210075403180041d40e0510940045101e680080c20780c488080340034450f150040c5442c110001001e000342598001e021070942810503580355505080c40d00c0403d01280441e07124000c1d841500da00b4450b4070741c06801b81c50010030507031401e402c1c03944a190300d000c0602001d0002400c502d20a00822080c0bc2c6a2481401ca910943e034803403031170800010040d091030040c040c034404007a8200d001e008401c0d40032070050103185407401080740d0500400c44a84126003000410402075081d90f00c00351141605403103034650075940c0c900618401708540d0b2800525110f001e001d0704003090358a84c0c180c2406003503480303945281d50303803503138441a0b01d40400f0070703102c440841040101200b0080c19070690f10342405800f80380c00c482e07602c1d0010401ca0310450b005503903005c000441c0d01c124030314011543d11b40040c009001510390b181c4403e102c9042802039841c0c1c49240c1c40000603c40e03120030a20400303501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 838320602 1250 838319352 838319359
    0x10c121202180f010302090f04020714070609030c0812120406110d09020a0e010e011a07020910050111070b0f07022b0c0909020609040b1c032001020408151e040602090f 74
    0x62200310400230b0645141c50000e103010302d40c00b0070741c181000360188006803042030410850310700d540e60b1326000b402030240c0d000c1240c42d00007019001520307003000901845a00c000500c5581850211403220340c007050000c005503100ca0f201c071030300780c05410380c000100f100043c145400b1442c59090300501800c2001580303d21141c0e0089001040b1480c2d441c1d044a042d1422031000d10b03806d0b80400004e0005009a081c0a54400340b0502880903c03952b10540c07404aa00a884a09510354004010340d100c0d0458481c0074a0b0741410080c9940d038024090040c580b4034802000c003203041c01080c4440285c0040c2000d440411300c3d088860708240500c81d41484010514008217025800c2c030356000c03402c98016188898007460b29000b1034805503882c4404014110808074500c0c7c1c009c0002e0800804c980d1810840741024603034070b190320052101c180200c0d01568440801004421450101a06841c0b8003c044101c100d0803040000e2240d490341c0340903801180140400350b120840001081001d002c845100c510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 838321852 1250 838320602 838320607
    0x60f0611120a0e0117010603140a0b0d030e032a040e0f03070b06041b020d110d02060c21041b0f180509030c0d0215070e010c121202180f010302 63
    0x2410800c481c111094000c25140c440303c2844024010703141c010f26210145041702540d4000700d10786506500005c1c1c803007074800d4603600365190326040008541200d0006a088450401003401207409801c00161104020702195425250b140e01290003414090100021044400c03d1103040e01d0140503146080041c0030141c880e10014511060341c81c0b0544200030000d481d6030340050070f0780d9950391040480150240281800c0c01d105280252511101003030f10010411181940c000454006100c55006000b82c000780341c030b42c03121000720040c4e4206181503400c600b40c6190860160201074404ca008903c96139101100c800340b0052040b5a5400350024080309000a40c2000800d59400790170305e548031600d17000180c645170f18203d1400c600c0344004021040c850a010280740650018120082c10704c0c0c483c0807501c81d20b500300116403102040110500081000390041c001c144c1c40841841281c046003401c0100c1d01003054000c0c2a60081d1804c4d985a0444c054141c03000d0820303100c400d9294074246411072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 838323102 1250 838321852 838321873
    0xb030d050406120f0204050901082505130b0301091b23010906051e0a090f0504020c250806040f120e01020316081308010e070b21070210060f0611 64
    0x50a9688810004007844c4d00d600b50040041d10660489000d04030151564010790307194181680d44600c1c1c00d002081144c8400750071910400d000c010300d0192280104040c085124440010018002ca460103680c0765603a80c00078000131711420212842952032460902d40d4a291410400380c138000c01000c1000c4aa00c0c4841c1c03400c1c0d0383e00c410400150360032401c20b661079044000725940c00c4980c200e45c403c7c0a12000a0001d1481d400c17400d12130440d035541c00000c554644400a1009038090340310344004584c40b0300ca446000385100c1071082240b0003c0700492190503038074080e5030304d041d034181c1381602e20340c0701c1409140600c44018204210f0a5150410b81c0c03142d025440001c1d507912514071081462010814500204200f0a0071602006171076411707103c00c540c8402c0780358000d01403100210441d00c1005c00000b031105035a815196441c2c40c40c04004c1c407010310304661500d007034001006101180103643e412190320142d8410080500280403441e0300660070120080c01d0160f001c404e10b01386920414401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 838324352 1250 838323102 838323107
    0xc0b0708090c0907020a06050c0306121f0e12041d01080a05071707081b09010518040b0c040504090507080f030c060c0f040512100c0516170c030a030b030d050406 71
    0x400d400300050b5a0f00c0d810342e0b1814000c900345104c1343c0006148a0601c001c4c00300f51041e52001d103021715000c81e03d13513104812003007c45540744507558034074010001c00b0f06803002c0c0350015801414500480d900303036407a080322900a0405035205402100c010441c0707103849145800f0b1080103d0142c80004014114651a6101e00c1d5842a051041d207409010500080c4003001040c461080204401411580400c1218041c102c144070100100341c05813040c0701c000142864038018154004000d0301c1000070726100c5440300142121300a14820f003407001004001010380b07480c4a1507002c60f000d0001b60601c503060101850910f0090306424925034400d200784c030311780c01b07020507455000070f503280106a44000c001000d48c9540241e0b0305c19588a02e841c441240680e002217031411100d1083c07101000003c06102c0145c40754003130401c040003d0440d412156000460360505102100010318407181000c510012440ca036601c02c0c1c4d4a10300107502c8002c050203d0404204002c041843c5040040c10941003a200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 838325602 1250 838324352 838324363
    0xa031e0b01081501030f1131030f0812010b09091b0d09050106030c03211404050f03100609020c06010b030402010804120504121113060806060d1e030c0b070809 70
    0x203607100f00c159070141c00c41a030090780f111005109008091042d4030701d804680080784c000c0590303850f1010344a2424015169014480301c00401c21300203054030326055480d180401c402d40c3d9401c452205081007042020103008644038000c0021924566031a81e13114103114801c00c02514125100d0950b40c03181c82d40d8101d50003507c05010420000003801611400c1c4103000d4041e5a002801402ca4440040203100e0030320f00b4107001020301e5003800b125081c1003c0868881c0d41d041d0701201c08038401c0c041440300e0726005514482e88180101224100d030007101d0103004854050740202511580001ca642c2215414045c8900401ca0035007601e046141c40d400103000540003c02c000d00300180d085242d60614043c80036103002e09030b00309500010140a1620382c080303036142e245c5148200410403400080d401c00340a542d02342c0f079005024010740c0d2600750502c01201341900049443c0340e0b03d0070841a01e850046000f103c00c50095503070140c4200309080001140c0d501030248410800c0d0a030400010132400502c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 838326852 1250 838325602 838325611
    0x30e030606030c0409050111041509170d0f02011407030b01020c010e1c03120c02030301050108061915020109050a05060a050705070c030221011406120106081203040503040b0a031e0b0108 82
    0x4c0103d0300c3d4889141807401000325011101c0c0400c0081004503203003a4050300c40500b05940c0d02c0f032880d02a25010b461015506104c00b403803890b4409c8410040c040e100340d01d091b14986050002040c0429400704070890040100d91070400a035880c002c8282a40c1d0400105030b4229081c00d2944891183d034010401350031443d00c001901c0461060000201445100e07098000c440304a420081c1e00e64481c0000d45035070081c4035560000e000840411051b1030559134a01e145090042040b00b03941c608840d40c1032030313007850001c0310940d5600d1208002081050044400c02c9100380c0c09002c8030302e80401c0d007104480700a03040c041000418070030480080c45c101041419030760100c601d072030503107030800800803240644072400d80d03d542402c0340c1140a102410750b903070140008a800000084078000c4882c04c8130810700c80c0620640c41180c0c554841c0c84000015a08180130f0020f030303403825441c0c202c40103095110b802c5540000c0d941c0d103130b20021032540d0304d010070015203a4a0180181d0f0003000000f00004409072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 838328102 1250 838326852 838326859
    0x71a041205091c0c051816140d0506010e03031c05010806060303071113020f0a08090111220924060e0a05040c0e03010507030b040f1404030503040807150504030e030606030c 76
    0x10190004c0c00700d1200020b00521004094070148100c041c030342c030600361040d5800c85003000c0c1c00b00d18800302e500541d4124410040101e030036040107254120340d0041e09003d401d8905015416a106805031400e0000b0b140b0011003551840212541c6c4d480d2038120354059101c0c001641000381402140c1d03901200321911142c01201001d01c000404000511110144c40030350009440011199010403030384c4007800d10685d064498003525915030390400c0c260f038802460322035000010024010a0f013030328100310799403010f200c4050402c0b40c1c4400780304040b03800d8444040341e00b00305106000011440c003858480070700810310740b158070316138403201244030100310b8000d0328443c94545050800641c82001003010304c280c002c00034400350402d080050020540d1050060096040050019950395a8050405c61013815a140c030401d0b55107403400c40d042e03000034008491400040100c0390200d0343c0c0002c694034140500f1030000702c4d81842c1c603001d00084034400440e8000d802c00f5013000499a0b000c2100d141c61841034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 838329352 1250 838328102 838328149
    0x112050907060507061b030603150c0e150d15080613050303150423090c18010501030e19031808010e0d0e1815040e1603110105071a04120509 62
    0xc5c5096070160a2040715091541164a580d200499150300094101d80c0940c400741440c0e41307614000800d840140300e0300b80104010203814600c900303006440400950380c0080d000d007052003e42111050b1000000c5c0008441c4c1288420300000209114143d00010042c0c0c0c180124001a40e449490b4003009000030301c48095a2506002a125034001c01564204d072803003811250a41c0710684015602500c082080e44950301b2105541d081800e0244a00c1c54044003050903686003400442c0680000034411115024140f920341c800e089541d582d0680714840d803166140c2000c42102038044c1411580201d0ba40d030306111009070a60804541816903101519001910304c88280104140740c041254178841c030400d890401061108030009015900c2040784d00380440c460343d0103150745d01d4074856003511154400d0300b000c00c0021241c42100e0401c98040c1000b604124403900c2c1e610030540d114600009101c002c80c104810400e4800030a80084481d0800c14101340d466004114054446400340b1084c0c02403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 838330602 1250 838329352 838329367
    0x6010306080607080405070b0c10050c22060305070f0c5a0302071203031815050606041a090d05030a02210432090903070201120509070605 61
    0x650010400742014404403021030504410062001804035020b50703040c020a07402040d00001d5400300e0b20304241e51030042000c282c11240d400003e04002d410300000241c10000d00f01d80903400c091340c80904226074000043c96250540180a03600010a240100121940300c020459002039a18400a030019009802410903101742c20904292110b0090000554880082d5070354562140441030300c5150a5070100c0d50141c1112100b0084040380240503800c11801402500c2a0780348103100d0364024a4007281941345401c03440030a4441440a48050004400300403200400d401034075000304d0162000c07480e0902e0300e00041402d22510381d400309070b25000214941c0568031128102c92003600301059a503200ca008002960b034100e40c40c0003680f9618044040e10a00700c0c82c07020741b0700700e92100345515a4500448610a0681554640d440c1d5000314025006c0355511407424482c420f002c18001540c0e903402500000d09410700c0180e81d901d0080c105401c220000310301041d80412034409042c560b448210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 838331852 1250 838330602 838330607
    0x9150510091a030106080609060c0d06050a060507031b05060c0a0201110301080a1e080a03020f070c0e0714070507172107060608061308210406060812210601 69
    0x8a6a0111440508109044880b031082580808416030124000c006540da01c0403120b4079800104c13907403082900404001101000c2d1540100608100a0300018a907610f410000e80001030036007002c0001000401c0d00c03400c0540140f0000d0349120f41e000310f00600c000a0361120794070040100340c6892040d000c10840706041c002d4001d0400e1452550030320780c0341d6841d0f850256980001c0b0704c05413a0034046031510700c0c0112a00c0c481600300d43c1c20900061620100110a40203584884141c0d220120f04006441c045044020300d140a015030001c0c411003428400300003845400181000070080714200004000a000060b14100b220341e09500b46148042c180210f9081c4059070001c041100740300c08a1107100c064050042c400c6c184100e00800c251600c07030300501c0c0c0c0d03040200c541d681e401500d020f000e00420980005803440c000c2d65815074841e00300c040d0400403180301c1614120384982c3c94078000d200b44001031090f00c504011400c80c5908140c0f05910300f00240f440c8000ca000c0d010303518004a8403a0340f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 838333102 1250 838331852 838331881
    0x10302090d020406080d02210d1a100f0e060414040b0103091b08100b0906010c02060c070801020c01140c030711010216150f1803050d14091f091505 65
    0x241c00500400c1511742d51840143c0340c0b44540d200c00c0040c0520783c00a0503000d080c68541d0081012604041d003020120a44200100300d04510326001c2c6040601c900d00e181e4032000d03584900c0b003007035440503040d00c0301c0000a0710f500c04e403c44580c4a26401e02041c401c2c1c1c489440c50107886581100d011034000312510040e401000d2580001d40100855402e002d480f030f402280380c41c203c071008000c4542507500303202250101e844907000f10758421085004030300e03d0361080e102010941d0000f80920701c1c0900d40c00300c4030b01e0100107a001c180c0594000c2442c0070f441c1000c0c4181c1003041d0140c40d0900c854681180d507460548030080a002c144411405640c081400950580f881d4000d040f011600708d80503420420142c0020080d4144141e04204861202c20840d0190b040300c2040461612240e10155505403440c0e0403050711001442c1d07856000c44107070142206168018054213018044003180704401c1d002c001070b00066000c01c1410065403c000940d100d400342c0906a0540000a054840508121004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 838334352 1250 838333102 838333129
    0x2031e030144030a08071b0f171809160f0804080d05100905090a0201020d0e060d060b07030212120606301e0609040303200d06181a01030209 62
    0x30b14800b07080c0e4024503001005103000c1c001516005050b903030b803c3c0200c854450007030702400e6015692489500107503c0401d8224810b01c58038140030b039414030740d0303410103140c02c1124134100c42500c45400320554100100c0f5907801012199610680d02c0040101811158103101208104820380c40045c050205400959000d201001018040350400301076906540d00780d80030311000c0e40e18003004101c445200080e10b02a050381038010300385440c5811400d456082d8480c000039001071040211892054044c0705100281c44010105030f00c070b0000c0d090080c036000200c600b245842c042001404111001401140d41c03040086601c540e562144442601c408551580003a01e400d00c410021110340d031401140c1c2e07200d000401382d4540600d02407441b01001000540d2841e070086590300c040b80c003080c804e800800902d01a142040c080c1040401c0d10410307540a002009103195454500384148103800f43c411342d4040c5060b03814041200702c4004a6480358103a602d1a0505500040d01040c0307440b01481d21510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 838335602 1250 838334352 838334459
    0x31e19111b0a030b010311040e011503170403150614010c11060d020409140403022817040f030807030e1503190b0a0b18012f15040302031e0301 63
    0x60f50307407850308095808a52007212310803170400d00301000664052064484a1500c0100c03898035a156403140380020810718000c1da5080000c1101001003140c2c0e003039440b80c510001200040301450302c2c144021080706070401c181088807856034600891002c0100d50011841211466501c3c100310048100a100b103a110b00041801c280c40450503858504070b25201e94000d4080e281240c126148aa101d20340103d1900c601c2d0074a150550080340b1410700b01d00200e2020844c141c50300d5111030b140c00da0f620103640304490110001400703804142c1e01015915118005455112074030300c819800d003c0341d000061414100d40443c01c03031180da64940b60402a0908005001c0c440e104cd240e4000000a9000d20020028558002c0c00c00c4019440f07144c900002310701440c80841000383c8844818143c404014040480d032040c0d1140c02654054101c41070b01a62183e00156628440d074050703001076081704800145c1c54802400100f0200400d5408209103c1d84450705285020030324410020035421820729000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 838336852 1250 838335602 838335623
    0x60d06061412030f1b03130e01060e0303030c040b03090a021f08090c0a0512031c020301050909010b1c0317010801021e031303050903031e19111b0a03 66
    0x2031480955842410640c800c2c0c9994800380c10300c02d103090f50380c45070f4401007070050703810800d13903102d110040303414164039100c8000e4919121300c0312001c01c031405542c0c109a021004010042040ea038014981e901504e5058000e1421460036542c00052070003203200c0c569600900100007882250240003400c925036000306a0704820003114101203500a02c40001000b040e80324010490800b000070f55218401d070014201c00400d400c15042c00211800444003c0c41440244019142c50402100e003e03582880d200d0016269031429040142d580c50143c100c00c0300781d1424a820302e0315180c0380303185141d00d00d0b02c009043d12a103561070216040030300030118981d00c0b8180c90011440d5901034006100c2e2080e0702d0020700801902101707510f074600c02918014003580101c00b09200083c091405483c80c10001400c0c1c9082c410390304e21013a610b41c403441c410010f0205c0041c00740f1388000440e5001d00014028640320b00c40e95440f028451b5942c00800300700118642504c0b034034100359030f401810400396500c41c2c1440e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 838338102 1250 838336852 838336859
    0x8090a051c031811040f090b04020d0512030a090c0501050a0206071407020a1202030c091302041e05040c06090b0f0f0708280206010605090d170904060e0a050a150905060d0606 77
    0x250001e200d1130007038452402d1040b0120700300b002d40640038200341c200e80200300710f8480d50308110340c0c000702c620100e90600501140e4058074120101451041c5190b04010801048500d4280080000381d00400d041c0a824410302d9141ca40c001101c6500c409603040c140000107d031a8103c10030300509500a502a0841c480411180401500621618400d404542510403000700302706c0d0802088480e20b83c228601e090000c01b62820b504130001d45d59960180c091030034a201203c40c15280100c606a44029040b0410400c00b64025078003801400c000d001c3c2800c0201d0f0030b448503503d200380c0410a05003540800d070002442800c104851401c15180525000c03c01e45504204903801140405809802840000900b660040007118440b250040015444003d80d40d0703843c1c103a25403c40b0506501c8410f03c0704554a0311103100b002d0184c40c0052060045180a0314520300741e0304000c1c02c3c10314850502d000d0040d0101260805002c0c4ca00038040400c1c00d030781d004d020171152400c0b038070f01416079418a00d002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 838339352 1250 838338102 838338113
    0xb040c0201020405041d120a03060905070c0516050a05211905011103011a0d1b050403050111090f010f0e0402070c0513090b0109090302030f0c0d08090a051c0318 71
    0x6000b1910165024884820a411943c0c81014008120f808a400105001f00c2c8800242e0013080c1c550803a0030300040c40e5840714068021904200c0740e103008102c4c0f0710f620304c040c00420440c20100f001e41d441002441828480881c500e09841e11402d405818804a1503001d5005041400f0040b1500c404860800071403002d03070000d440c080c3c039080e1119460142120f007941400c20481e41a03e101003200c03042240804414409503116180899080d952420070080981440c5c018070348410381c0742d0702c4039201d41c25410100c1c211810340ba00350b48820000c0116590a8031041525040342000742040808040303009803d503045501d41c0c40e9940e010307100003550000c02041a0320401074807403c0c0c81d880002d4203a441e02c1001c9401c10140a440ba00c820801041500429005540d000b4820301c15241420740002c182044d5030081d05803080715805c9241c140345560f0344115486d0744144060010700e005003403a140c407521040411403140d0910101040314070194001c1d004440001d02e5080745482c80750f032070f0420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 838340602 1250 838339352 838339357
    0x61b0702060712020607110d090e0606070204060303350f0c0c06010305010204150503060904080d020f030a0e06060102031303080a031e050f0a0902060d02090d080d0501051f1b03030b040c020102 85
    0x100800314089101501d01201d001407044041c408d41d8030f81d0013030942000d984160340c50f4024400c0350f010310100b01e10300040c0c1300e9008210082d07102c0e48480124078500c1d201c00e00da001c0304080c000400f0300c1c0e01c01001000400412001c1e08200d058520000c29220304030b07103a0a51051448114040c4241c40c00041040815030081040300c0c6900c43c1c807110364107440000c4805100560310185d012480344e01190205000700001c09090b02c103c140186800d902a8201029800403104c0c061031580c0c0c0c415441142e041480103940c001070900c040d40c90a07013003007400c50340d0121030700000d07144001c0400d030411100c6c06a40010700c5a1040f40000c0500c0502040e580041c0204444003a2040c41583c04900301e10300d00d0003041001c940c018900d5007041218210301000f50000802130303500c41102440c3e075001c85c2070700004241c44d12590388040384540c14041841a448403403400a40c010410390454000c081d4030001003056000082a41d20705a40b81c4d05089015101a01c07066602602e0070008020b8107805500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 838341852 1250 838340602 838340611
    0x406050315190209130e0f012d0209130b01090b04091a010e1c0c0302121c17040323041706060f031c03061d0402090603061b07020607120206 62
    0x64480c042e480a40080303090b402410ba80c2c5400c8124501e00d91045d0740d403034000c01140d40e0140103c807210319251201e2400d6407581400d0306d080d550b0600d451202c4c0c000304400513042d04014030056203800406404135001c01c00452807082141da9072419201c95a100f440c44400070710381100503684a41d02d4500c81d20080c038140c0c10b04d40419100f01400715003540140700420307005d0001045c040010360342d450090980c0b03a0401c000c07101c07054001404001030703807104460342d031b180510001007000c070007120b00d03120561501489800500c1061006604000040f503101c582c001d50519214444541103504a0450440340712115041c003004640401c1c44a190503034102c132040c0f0341049405035241d102c1485065000c4005086d01034202e0680d1802c1a4900b41210054800d280380000c0c040b6504e400641401e26441c2080c510079a04200388401c0d0710300ba0840c5074018200702c0c0038203042d06100108540d8580300c40b259242e8070341c010070540155941c08003038582c01d5030840b0a180c40b4031040c4400a445030000ca4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 838343102 1250 838341852 838341871
    0x1110a12050a0c020303011e0504090606171501150c06090312060506030105060d1d01110304021e1809011d060106021905060c13032a140319020406050315 68
    0x4001542d991070b070380034100d20312580d0340240d071469007082c0d81603420488a002120444510700c0001955494078031032102c0c41750150303800040c11818060004001468240601c666038024020390100000c450001070450300046c0802ca60004540400d031440d0603812000341182c0c3c64610f03c607040c503800001d200d8412014440c00c020b2180c8070400c001050200b0300035650031007024000325030002c040b6489551220005564150302c0c080452100f8250355000c40a4540700c0f5010041c841181010440c91038071640006c04540451061b8011410450b400c003120a0390ba0300b40c3d400f00d440c0003c01e41c09032028034040d1040a6040240c100c54a950300002e101d404e0051052959100c5080c90301300340c40c81e0642d03026000e8910fa07114554a8503035500508015030764040c840300000000303100700c10f07220340c00b0820040720440c226200018982003115a40445405203149201442503a0301107802034158101060f040d040780030138008100104415000507402d845082c0075907441076007d1000500c40c10040b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 838344352 1250 838343102 838343111
    0x608160503070621050402010c0f2a050d030309170d1a010c0f0f0809183718060207050a05100606170702010f0204062007030305041701110a12 63
    0x4200840d904100441040003130b450490a480d24141107802280e04a4014501190414501c2e15060281321041008440108000080784c0ba07400e01c01e000840f0041c1405601d407043c1e4900000310f0800303514140024109951100f0442c1040804070003a5202c1c0da1a0f82c01c07940320301c01403000100814240c0030089960781d0182c060030481d8410b00c0394240f036641c00400700180700074590b54080f0601d0110b00c01c48500c6411300a655031078403418641111844004813601e0a41842100415284409140000c50951084005141000c0740c1c86490755009904d03c0081c610b60280d207075038624200208000c18950001401e0380a1050016005034803034003e00a94032423134502942c800407110310303124203008502c18504001511921005245c2e000c4c4450002061141c0300603940d808030307402a00210302240c5072001b0142d072821940c0c980550469448000c1a106003142c401a00d0740c0210f201f002c5c509210400c950068020039000450a160300342205a1164440700d00903111f0790081c1004040303985803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 838345602 1250 838344352 838344359
    0x608060303030402010905060c0709020d020712080702031804061a03100e0105031b030102130f06020c0103020c06010905090a150b040e06060f0442171906060816050307 74
    0x7000300c9016542c140c51701601d10785020184506074119020b05102c0d0b000e80b031400a000a001d00041000741242d040060303079500c0e01c0c43c164a0010107403000004020f516401c2046481e000001c6461225290500068500644000801601d2107070041307103e103141440402c00c0960000040d5004010030703146541000e8491012102e150f40910a4644c198000b0910f01446800320b84200310a01001c0c1c000740ca46020013030751071403860165000510042003000d0400540f076041c80503540d9130400346000d614003220a4034540c0e5651060040c211943e82d07030b1f004070703c42c000100a001c0045501c09035520b10001401007450003403071007500e0302e809517050a500b4040d101002c20128401c0b08010300f0340d00145910327802d100003401c090b00b140c50b807410300d44288440405060380e02e17200c4680a14440c121000780a9001032900d1042c1d00031290b900000f0300c0d00c080c1c4031010071003081c03085040102070b10507019401c4c804084c00d1998404191401404094100b58017203c0e5140c042e0f860640c1180c00b065135 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 838346852 1250 838345602 838345609
    0x22d0304050715020d030207020f040e060402040b06120f270102030124080708070306080a050f010e03071703100b0414011d1305090f190506010906030312020a1116060806 75
    0x10903600f04401600311920010101d4000d9002d4407900d0f0000e4507810b18882d014020404a807514405d00407540d010300c0812086103040c0c0940752401205540440c10041c8030120900024400b42206000f40e14580000e40d0140c402100782c850130300000c404250800200907a03d000754028000c081404018101c00308003885150318035000016582d442d8006950f882070229040040600114100340e221000020103010807c9445a560b00440240c14010401c0140600b101c0c00e42036203482d26041406140041921800300b916210300d03110030140c1d00d075039492140154901c1c0380c004076240034022401040c00100303a03000100d030745400c0c0c0729090740a65803040c0e510443c1c00641000d6000c02e00c5c540c800714085036038000700e0300308100608440500710403000403802d00c4622641c0950188810f00c1c8402806010064240189108c2204110603800c54a00a0a000c0c0c01e01140505c1b1740c001444100040c070603c0d4111000305260151280140180c8014000390020b128410025000e040807881c82d04c3c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 838348102 1250 838346852 838346879
    0x121509192d201908061e0622060c050613170c07050604120312090b06010503070c061401081203060a140d1a01150302070f06022d03040507 61
    0x140340c080a800030071a0031080e400a010701e25801c2802d100041010b0500d400120090114802e900842c030241030300c000c4005107442c1c40180b0301e610404040403421980069a00d80d0075411005507401c1c1c1d603e690300e403108004c01c0341045a01202c03901c044800200c0c21760146e20300140744e2107441950707840d840d41041c038200c0001400014003000075a10020b41005078004c0101f0200d2003500588002503a248000fa04980060b480101411705060540c82010713400740e40d452346101100700c10050840035441c0c0071403240e0b0041c2490306000001010844e000d00451103440d10130340c40380081c064181c1c040c0c102c0c5041d0100b8404e107000742c840d1000045041c1c0504007662300c14540039085840c0903144c10300c0d83d01c00701208a625a00810001d2510700400d01551075262101005503020441c0e52411007041c143c01d21401c00401003501c184140c0c0001425070103402e0180d03400510142e101c002d01890003076a503a41e042042c200a640d01070352040071046a02031449140039005440c00ca40c1d5840c20904c100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 838349352 1250 838348102 838348151
    0x71101020a080a0b0a03020a0312081014220f1a0307210204021e091912020409050c041d0c0a05030d0503100b0307020a0203071a12150919 61
    0x141488006404200d03582c1c860540090700030009001c0c281d481e00844c3c540d102d070b03400946840000300b03103d8101c03503042050bd54010480703160b540d41c0e00d8504802c1d400401c0008403202d102d0090110404640c411040f0340381c7c0c600340c040c03408000400702d4a050000600c00400c00d00c24810323001102800c60300c0c5c01300302d1204842d56001c1246081100c4051051030542414003264000d500b03000c2819420101d0a0b90500215030100701d0765110762981c00c00c101d03c00d1440c0c41410010540d2424024440101c0d0510307030a03a41900d0105804180d850f017207091040141040350010301d03244180341810802c001c250788c400349a0b0203407200c085d40402802000c8c200c90117100e030582e112040030a05184181c000b5a407044081060380b120039124a084000ca900a8919000507404040b40d00c0039482d050100c03900421035020042034032040440703004032a00a8121902c0300c032401b40006150003124400078107001e44001d03d500c0c02894080b082c4500c2d0801000345215252802160b4200d029084d50400c5d1013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 838350602 1250 838349352 838349357
    0x506040510030b1f0921080a0e0111030a2106030f08030c07061b0315050306010b0d1404031806020303041e0f0b1023060412030203160803071101020a 66
    0x6216458400d50141803610f2141d81c02c08964680f020b040c0d07070f41c2100c1149114217035a4851405242507484004111026202c0c0c0c0700d03a601000782000100c200301280d40e00a0325041c44c40c186c080d081d0058a810041c0400303031401c1c1c00001a02e403d160350001840d4140580c1c2a84403640700c0455032030740c0494030107000040c1245800d220b02004507110070301070756024081c40f011034a800c0c03060703842d4015a40d207010003045200041100c2034170160540200145691102da02c58180d40c0b924000035030b100018854003400c0300001500c00070044e000d800068542551550401c900c1c10301d46001408101d120425140300d0344214000300d40b182c80841121300858002c00340d1450043c48140707041205140740001c60303410140a48010006510896251248407000c840f00c11251802c001d40e041d002c0700f4994040d050000c0303101101641d4642080c0c5050700c00c0840b00b0100d1540920f003d03840c5215019403c0d21400000080e001000001c40045d07100303a09030340c1c8403420000d801140300e0a1b4054490900c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 838351852 1250 838350602 838350619
    0x126101509140703090c090c2d1709030409050c1305090114130212190f0b0109150e030a0f150603030c0b0403021f05011d060603010902090607120e01020705060405 72
    0x722a8860b170000440d060045d8807a900159031500160100c843d9502d902000c20b00c420881e10b00741c80136040303c003000b07000304540d00344102e14590014210002409070141c61a4032401048401c60304000742c0700a400a154100014181085050025000380b040d49000d030815802c00704203810501c0c4074504840f600d42c00c42000050350020480d54801d00c400300c4480940c02d01c83d095040004001c0c050040d00040e075083d80f502042401d000035a010780740108500340c10410114450707603000b0340d800203c0c0c01000d00050000d2140c030080750030712020240540c0c14820380e049034007070240081d402d0503104e200300105440340300c05513a20019110148005008940f40318101c1001c0340e4540305260f0b00901c644150b40505503a6006500326034130709601c02400720358907001031002101c550356900400c00001c1c06003040c6d00c0c001d00011540e1005004a180540d00407542c102141ca8550969190b6980b00c0d0034068541c2221000910a08c0030000450040c0700d425000a010305143c8121020f6400282501c81d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 838353102 1250 838351852 838351861
    0x3050303070305071b0b10141806060c010e160f060804031d0603180615090601180317070519080a03090203030d02130e070305060306012610150914 65
    0x20010030008150b4414000010401c174125000c0c0c1041c011801c0c86040c40d0303907040c2041102c2490081181e0014806209490781d000759940e545a480213001c100d030b203a001d6044e40c82002050480c000c0c14100300e0158240781e820b002408022455818220803001c40300c0c10f80d6952a9a0441d00815100d5000420b143c0400700b000710b440b40d201003100f070314616075003118102d0301d80105440740d104403000c4400f201811042180d6010078407010340c01504d04d54031400c0045001d40042d1294a0140000341070016807a42e0080b180c001c42d086070000c0d908510107d460400d00e080c000d9440d44000c60440e4140980c103458040000001400c00311190048042030034036a032110190000d24050105a9140c4000d200d4403810f00442c0c0002c1000c20140b5426002c9242f034010b01000f0051301410f00c0003410f05250400100d40c8002404a045820388841d2601c03a030090b0000c05008039025440311600e0040300b01011b042d80c059003000c0c40403000c0c0e601c201e0381c3e1607507000c07a0300854010802aa102000d0000840d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 838354352 1250 838353102 838353107
    0x40b01210308010314150106081006181403100e0102191d0405070203130b0915160807020105160614010f06141b150f0a0e0309090705090301240602070305030307 71
    0x1c030840900008840c501c6d40300e248002e210440983c46900000e020104110341c030017081c55058002c000e18200407002c0450319041c07440d998494059410700480301d035405e44466030200080207080414410070028084031202042c0031b03500c40040c3c65000c68000b8602200580302d4000100c8100c944a4040c01c820702d50410032010704405000c01046101c00d00141d920b03200b504412200500030804415555003141d0148055802e0440800307000c0c0d5000c0c411642c1d580310301008180f078a80c0c042031043c1d86920900c01230b2854000e550076040c0c0c0130304500301d6508000c0207500c10550300b4001440d55409030703a80c4440c0701c8480b4540c09440009a01d650082c0104001030002d028240c010408101c10812082c0c403040c9400c9840d80106032000d600c80622041c0401204903c2d003001e88250103000a25903240b00c5030f6030f403068000c290f015481c10360020307010310702c42c60940d0f0220100400a1081622030a8811144003000c4200048032405400004040380001401c0c0c0850b80d1000155081d0354071480305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 838355602 1250 838354352 838354373
    0x20304092d050c13181d0a0f030302070c060c0b09010e0c01081815040b101d130618030324060c050c0a090203070e0301060b04140f09040b012103080103 67
    0x36681c1ca9a003480b082e8100029285600045d000b1902801601c3c0101d1260400303030f0704000c114001c218034484482c007030f5404c04070b90a08040c0d000000c60024111600e0b089000384581c3d5406000c10014440c0411402d5000614001860044280c4007041c3ca40f06182802c031a180b0701280c1c00c0b980007108019155010700b600590000841902111114001d0011410000c604603003030303680201c1a0400c02000012000b0036040300440400d400c3c19810800780010410494008800380d0401100040340c0c074150300e515180d03d65106c0c00038405480c0840c046499070284020440200e8103011405400d07280081c4680300c2901c003200d02c006001d28114042d200f402c5848400e0322540a0188204460785030070203080010003043d2401030352480d10410007082030740d0540186100e40d040500c100318240e40313a0b00380d0313068945111064032003098403400600c1c551100752030190032198280411040c41030b141e400b50304841813001c04103800b5023400c0b4803400d13070780048038011b020800710401400070a449205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 838356852 1250 838355602 838355611
    0x102072102040e032107050d020d020c071e06170c033310081315090c09060914130308220c03050c0103021201170a0c06020304092d05 59
    0x80e840141103503004501079800000340d07200035620000d140b1903612108003000c041c0d01d0740070507441024100403000805610032469100c01454010135480310118443e81211061408441203800040e50348012000100d000103116282e04410000000c6480c0501408030281c400c80180900641d5072600303501d02500050604414400c4103104881d06c090007504001c100d005099201014000403420070185403040c50f6030004015103d800d11400f041200700b07040c0c0389580000041100c4485402400c014801480d003c0c10954610034000341242c0c03e944001c0548000550900c06e04444900a4003030500030b440045040d4008441000413074031503e442504440040260810035030381c02c1f20300720780c103a000c40c0a40d04004104020005c202e02000004603809080c2070039410400400300c01400380005100d0302030070400c0d12300c2920048000b804645038440d401400d100b200360b04c909000790303a0b81084c01040301861030031841c41003807103d402d22040020054034240c0c4d0620001c11503035015190161 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 838358102 1250 838356852 838356899
    0x1030224093304080d03020403020d061a06040308042d090b01020a1406090c040c09031113020417070b1602010f030906020319050c070507060c141506130605010207 72
    0x4142c154620a04110280b0341914440c10310703103990414010340d052003900c030003100915104100400058075000e0b0b540040c16081a03000490160201039800c0b0283c4141d00f1580c40580000d0200c1041800d03800703042070303501030700181080614a040c4034601d01505680d001d4200000c03841004030005541140b41c0888044c41074469001c03042e9114003508211201d0740d19160030000802c000d58100b042030758050f030021030f4184100b0f0709588014041d41114040508800b400d040c00c1419626a00094110ba800042c011035849544d501c01405101e100848115035000b010f0001a2804e860f4068440330090719400544500342c076401920000c0c000003002c01415282d07143c0c40c000c10254405144a6103600481c4440b442c607242c0250b049820081090306034140600003513002c00e90004484094484609100000324110705009a8080b440311380d4410b81c0c41350418924221980f0011180550800c0d00c1c0e840c40902000ea491003568000c0c0240f60040c2d000c00d004100d440c445400e05012204c110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 838359352 1250 838358102 838358149
    0x5060a0501261005130b090619020901051204030f020d0203030f0f0702010e1204082109220c1e0f0e040b2d0a120b0606070c09140103022409 62
    0x52400f4140c440c02c440c690060000d0280002c140088074542541c8101040040d0103d440d003540308900c03008005084009039a404211940c3c56402841112000460050410003502d0a850001e100664035281c0200600940d0003401030a8000401d80b4090004506842c1d00c603a1086407100d07031514010b254030b04540d03c0720600980b810092212410311800c80c1c6032181e50300e0420b034040303180c000102d5881e60560b4042200200d88225101070351940341e421140d04c2404450b01905040d2050b80e4110001d10b60318003000004441e411800750018100414140000a0f07841b0340d06072444c80c0c07035000fa2804280d81d040c0c1103029141030350100c108401c0007040e020940c421290341604105004200f017603410150420300c42145031480c941c0004124040c040c2c0c0b940642580da00c1c4d105d41010f81014001c100204040003040400b88c8480c02802c00d540080244d10b41c0e43e084601d500034203200a0303000d00301d1031b80307000d9120004224180c04111600d000c0351401000c5020702c40e0003648030b10341200c0c04094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 838360602 1250 838359352 838359373
    0x409020d120807110a020d0602090603100302011d01050d1d150124050d0c05070807050303070e01030b030703080906210103030207080d2c150705060a050126 69
    0x99030030400110307015801603101e0500803a00030301514000340010051020005204595440014000c8080c2d0741c165418551000725140141c080d024880d001d42d48030f00040100290240c1710350b0281d0440f03000766105510010756541000048254440c501c0c0000c0c420404108030a00c19044810301000d00a0f084a50a600d959a1420007030600586d00440c03010340b004100b18800010910362205030b540e9072051040c0800809410b1303208048024104640b14042d504010b401030703003610304a94000d420f1075501c541c0c529080c0d881c0c0e4012549900486d205c030180f0015540b10748201c1d810340a001c1c0050560b00e0031078461403080e8000d62080d6520070300410000c2d244507001510800b200d2004401342c0041d50444c94064200395044e004400141d0068040e000103a0307001a17042c010010801544100a05000b0509554117000c3c2c001b82c1c0088010600c2a82c0c0d0380340d203004080030b90040c015640d040d25144c8498060750002c0c443c1d20b03400254102502d003103030010b45012200000440841d183c4001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 838361852 1250 838360602 838360609
    0xa09051806120f10060303180e04031103071211060a110a0e06091e120a110411070f08130807030b01090e070e0c04032a090b0301090b0103060f0c080103031409040902 73
    0x1400001d1501e170402041095044070038070300c210811070702154115044c8058180621001000601088086407036001c3c060001d004961804c0d03003000d01c4e500a0a11000701138042c02c0d031100321640c0c034404c8100180c00071043c0e03c100d403003500008500314500151500c040f07443d9038140c4001035000008111000d529076440040081480454442e002c91254420400400000096030041550006038000d800a02d0711006c48080401c120380014400c0160b820180540c041c40c034000300403155002c1903409101d41c0760007800c0a41510034a600caa00c0d2900052920b030030342c0e440000d042c2a40c010062000500b03a41044120301e10308030880d02042e507500040c103400c40c4d090718031103400d2400080030703c2403042a0307011400445440e404030a02c1e0309040c811068429481c803503404264ae4400d030345061994237420403003c854020b0006041c550f10781c00e02c0c0c0002e0048003500e08a0510302107401808501808a4030b040301d07055120b101d2904e09995000006602205d019603005035100301480043e034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 838363102 1250 838361852 838361863
    0x120f020106170c1206090709051e5118160210020c06040201120e0313050f01030c020a0f060f020403030e2119050c0607080a09051806120f 61
    0xa0b0820001c2800726854028440e9801d107000b6041d0180e0010303400c0104080340051040111b8946060000b210749c0d030400305044004626082081080c40d00c020300c00400c18882d100102c07400303003040100c1c0c501004020642d151000c1000458802c0040801a20b000e07001c03c0324025842c0b000d0a03826209004004003e50480d0480300640700e0584c50608400880e0f041294140c00c0025043c01c510b0607450a0060f5903c41008000904004040da01c0603240c0304207402882c1c12440c007000f241c1d143da600340304a52030004a805500d024101a80092400f50b02c80e000f054203019854001d0400751000da00c4840701f034100c8901c00c2e02c0b1552a05030444541a5910060005501a6071032805006500b010804040c500d48914003083c003110007004200e00e0041101740c240810000c040720900500d2034000c0c2040024403150b5403041010407040e05002c5504005c080c1d61030355a8520046948550404c400d001e0203c1014111422500c00500359040c040e110041c001480c208580382ea00c007400006107803e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 838364352 1250 838363102 838363139
    0xc040906030312142202030f011b0806041a21070303080402180919030c0210080907060215160201091704050406050105030103114b0409120f020106 65
    0x10b9800a5a800111520710811045440318404e441c4282094521000245201c08944a241c82c1a10034041156000c01c006541c042000009001c07264065808059107404c1c0044c0c60085031b80c4000150f0189058483c080e081c440300c0f0035016860890300140082d81080b652180d161032010700a002104030308000290007144a6900e540316440c051042c400000d1076a036039992408149014400d020602186804ca804006512401d000c80c16040c22180c0d1102d900b00070390005e41c400040404c0d264005203052080d5048403c42c2e02007540c403174040781d4035044030801450340c0421034045540074044e990700c102d020405200100700d091a0361158403054910201b43c0c1200d400001c0e00301308504280c001c0c100140400d091440c1035615603182c51460b544206c84261058038084400c5070b030984800e21409018080d03030302581d83d540c0601c41c81c08100a03d445a0030440340c0d4245165641d1400c1e0240c0008140d02004442941e40d0050042d00e10410341000642555244d820129265074407160180340c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 838365602 1250 838364352 838364357
    0x1f0210090c050a140108040303150b0c010501060e030a0309060f170a20040305060c090415150305010504110d0f06090905150106091a0a0302041206051b0a0906080c0409060303 77
    0x342c503040c200015461140d2003200740030442041c01d1107582e0003038622603000d030701403c0c00314030b000c0603940240c00c0f00c2803508020314905012a2600b2800c3d41580094107036549911000500740c01c803400c05568aa066a0080004d18030300b03000d0004038428424181941e925040038401840b91075144810000700700c0e800840702d584c8cc1038100708018071221a038041c00200d01518501421500d84540700c1034024004462101d0000f4503000030380b1640d02c00300070b40802820100c1c42a844020303080c003503a440c10007603002074101030000c81d06180c144202c0451405881015240040c3c50f98200050049844060f443c140e5810001610400d1809042d0b81c141c800c8000c0c0c00c0c800001c9411041960046c0c000c9001c01408040c2030000741820061042c000c00c0380321105454840000d41103010380720b1600310440100311020748004001880d009140504081c003203e201a04c0c05070303001401c80c068004540c000070694802044154000c400690b049800880c034180381540300c0250109a59555000701c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 838366852 1250 838365602 838365623
    0xc050f0a0f020d08010602070e04140303161d0616020321040501030609061a0c01090507032003010b031902030c06040f06120209010e0114130306021806091f021009 72
    0x44a0790500c203c00b140030740341c1030440c807075410031000940d940d1050284900f00319074000450207204505801900340340045040f80d41e80d10301491448401e80c8414081400715074180600c0e10702001c04580550300502c09807405040003518411607040b0000c08400344c2c3c040c001c13901c100c00e443c03220300e4000309803404c4049100d59071803401e4001011202668410300c501842c0035400d000703c00d840300d4840e9400f0380a0508603103035448080c140d030040c110000010300078814000c0c000100000740c3d50300c144100b058092560025860020300d4261030b00707011940d03855003062542c0d4a81c58104511032134a0350002c0c0c2281e40907400d00303012a86d03551058019203074403c0961010044035900803455907038090184030940c05c000d002d5001900040d000e03d8120705024041080b03280c003500140c1030f1544040b400460000c455603a083c0a0300039403007019180c6001412004068160400201312051000c02074011000100400301200e0101d4040e101d020441c003d18140c001c1e130034424054111842d008080582 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 838368102 1250 838366852 838366877
    0xc020303061c0b040803092505040e03131e0506030c070c06020a081e0d0c030906060b040f0b0a020f0d1107061b14120c01090b060103050108100c050f0a 67
    0x101d0b80c2c100400303003040c1e2814000242e00007140150542e400592120701c080d100d44920120500b0400c10000200080341c0514008201549051079003040350750035030f4204850800006407607220b20420500803204021883c01304094024442c58841005007d03490700c101c240c440b40010300c95441a1004c004074100070460200f030041803a984401031107140024082c0c00ca19590309206401468484108105c201007040d1034400c0c100100c0e4042c07075800c2070800c0134450503203010f4010400d54005513415843c21801086092100e0f08603415125003020340c086c401e20300804175805a00203500101140268032403500044c0b020000003483c0141601c1d42040100a10380c22880d02c07840e0390004d004c0090020b56014a8050416201e0b51180c205e09410b001d4100c8108240c500b140301401c4540380003000034020340c0d01c081035002001d00341c4560640d064a8442900440076181c0038010b100c082e8211010030442c0c1c80c05903000742092180c030f00f402400c0210013852407809400c42041c20011030005440704 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 838369352 1250 838368102 838368109
    0x2032502150313120314131b0f03200a0b040e0c0f030a0507020c030d0f021b01140c070308030a0507020c0d030905010e120609072c22060c02030306 65
    0x3101c0c25001e40449411468040020b400c10964550040c000e60fa0f90b503a0440301d284680c0220950001d200381040b000d0424810810b540800104160b4080c0084011405e0141040b0118002c94001000a210306400d6071524800481001c100100382070402c884160a511664a50001862480c90160700c1d1845d0164010600d8030050410b2414802009910681000394003517076004545180000f401e541d0b20742041c2c2c9400301030003502d50701d442401140420780c0d0b0701040b908100025a400c0d646004121891055280c020516140c080344c000c7c4c0b0a41c400124182c09001d5644120301181e0341e19659442c0c80e641c561098880742000d54070340003000010740d0100030302145900140d6402c50800d906d5100180701c0941c2d402a18100701c02841c0d02861a03036030303101c000480183d5900307540141c1412000c10360b48032018171607170381c4102459100030080e100d00c012101ca21420441140300995514440c62141020741e01c0c25007841400380c907842e010588500c80c154840781290005c558900300b001c02c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 838370602 1250 838369352 838369369
    0x501091e020406080411030f120c0d0903080702010c03090b131a0909040b090709020c0d03050c0310030308070318030809010501050402070f14120d0b1302030c160302032502 76
    0x8503200c140108810090198400903055002d038102044080b01e04403180001d090400500b40f0350518455004904020b806074801414000201c00450307100752002402a20514002d20014214140900c403440155000f5015800c44030720034036100100030303100c5100f1034954200801c0d0800d0f0407498076090140b12000c116048240c2a00003503103041140c0740e00062260f00000b80002e242a5a0b04086070711807108021407406091500010f43d2140d070403010301e0b50380360824204036001905050210b20351010b04021030f8040d0354062442521349080d034034207071843c00001c0e242d40201580d416601450000c1440c0030014280300e559271780028140f440c925402d40314181c000622481c810803089000504520604404940c031513480c014042e600c50110307041451151880398071300307070004103540c0c410a158000c0035081000c441c484050860500749100b2400300700c5400c070120100b008140c9203a1025000c0c092098403a2048926000140513504441c4a0303241000f1414071034280319500314030303041e00f4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 838371852 1250 838370602 838370651
    0x50c031005160311040b0a05070606141f021203010306050a06241116030807050d030b0d0b15101d1519050903030406090608070c2001020f01050109 65
    0x3820721080c10708070781d062041d0907000d00040905546800304120407410000b03440c020480b001aa640710011032034041d115030300003501150b080d482c080010400c070301d4050a0203410341006d090b18060450701211481d0919a402a41056119408080541c00d06280045000c0d501c03d007000700c1c0600348000e0b060117880c1950088184076003c404c022041e815402c07508400050945010b01d081c0545951140c18200c000241c0091101102c10200c10b018200c0010811588900202d541c5103035581d5040f011200381c0740070141e00179504400103000c503c02a480e182c20000c0c00c1441c4092858110004101200490240c0081401119040d04a42c10998001141c83d4281c40016140300c00703500b4941c40d03218a582171000e4031005081c103068a40710b0b4060754101a40074003181d560710b032510f00180480e0b42c20b00c40c50000032005400111a41e119200049401d5400b018500c05a810808003640020701c0d01d81da9411480341d00b15417080c81509000c0c2500030071341e48100151000223001d04001c44400b401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 838373102 1250 838371852 838371883
    0x110609010b1c080408011a01020f070f12060b03011a12060103080a0311070c030302030331031110090f050c062b1113050f0d05030405040f06030c03050c03 68
    0x1c0e801c1d00e0b0703111000b1180c5900d203208021484598186040003003801140c11080442d8a445501d4035081c3c00600c031014000004d0b021550fa04405810080e9900d44e14007611803808070551041000300300340015140080e1060034003040e5240c50101003800c581002284201c80400c3e824540720505000615119548281d00035000079815510350b141075101c2c888604d005c040d82d400f02040c10210380c10580302041d03800300b001c191041d503030304009640380c005554142c0d02091602c4207550344e0b6000c40c0d0900d201004800340640c1c400ca41c1c0c50030b1341c4040094034201e080c0d0003610402d1046c102d052040d07040d1107108168100ca81245410a2403401d071400c08882c0c003900c0b0400404a1166019070006112210010301c04901614141d041e0040d003100b00035194048004125102e800b038080c082c1c0f4003070303c4098a001c24155807403004c00940c0d401c0e08101401d15001007205110b1820150800b00007008911400300e00c196696480052500041d03106440c241c1040800304543d16051085990039422031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 838374352 1250 838373102 838373111
    0x8120a060b040b19170108150a09051c0302040f17070b07020d060c0e0919050c0415260c0d0e01021306300603050f06070c0b040f0b0711060901 63
    0x103206500c0344c80749040059000a1a0a001c2c4a051141c2d83c810310084042458000c1075035101c000584d42e4001c04402d01c040141c00c40040c0c03c50103144075038404140c01400400e80410038094401004031808100d004041d02000041080150028048000c20030904c8419844226080c42401c1044640000380c4e8a5010065a00035980704601d0014240c0c11140010381032a4030241540e4000d603400d00f4036007058100c1c04003c198840c0300c3d0249201d8189080038805a5a9503403010003c0c030490041d4105c4007520300c3d2848106100e0020b8032208003404140f50000c9070590304c50034a04104039039104040400244500107681d0f18040c40d040a02030400035410401259240c0e00b601190380198020082598032141ea007807001c420151994941c0742002480c03511a10741e00c0040c003000d02054441d4850103a6910346d062000444903c2111140da0350000d3b00d6081c2d6a0703258025010303100303a410040084014003c9000f52601c07a000e1003c0e510b900419005802c0f4003410184010081500c50340361 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 838375602 1250 838374352 838374359
    0xe09090120030c0d0c0c0212070602211b010e1510050405190e060601110610060503040c03080301180501050319020402030a021e030108010e0f12070f08120a060b04 72
    0x307001c1110286207105034660b84940d15144541e15600451484d401c943d0b050140c0c14000c65000a03041004134000c0d43c00d400b2008542100a64a151a12078000141e102030031031151b14519002d125045002c0c0c400c800c0c500031035440300503901c2180007201c0103907954038000440d40c82000c105183c800c1c103201040780c1603482d02082c1566080800d1044078003603521940060300300c2c804811360001c540f0305030000f004800b501504655441c1400c40710303140070844004002415400004581344250060100d100403281088012551604040c00c03c0350804a4401d000c00010303d41c03005103019040155024403442d0f10040c182c000c0d14010b0b8040c0b406908480c12031240050110150000103806550240c0e4030740711000400000d00c204801c0705414a4104903160789207044a0040d03040b200110000d2028800413045c01da190412515a403117294400b41260784111580c2010f801c007035000703041036007440015880d1a071440d40402c6a14140104900411810840310310482015240011459040504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 838376852 1250 838375602 838375631
    0xe031e010e0c03210d020d05160807021b1203160303020306030c06162607030323070801030b130c0b070309060914060c0304050a08100b010309120507060f020a0e090901 74
    0xc4c02140d54840c20307000110035420001e15011942a06890f0408001e1481c0c10140918201520100500024000303008035408500c0000c3c4030580500c10311010070807203055810000e90000100d0082c404d40800d11000e030b1180031050041040e203000340c4025940b4175200c4101414081c5403519030307102d1b001c18000c404046105c0c050038100340b98013200002d80e81c07154644a0950440300d20b4130110a2200140307603070825034103030418204507040e020310300d10080041414111050040301c0701d10016209000410200b0450845250403440040300c443c52030301541c4408070758200700e4000b4401c035000002c50108240e4841130900c01856203240c071225540c141020050a4030914005070311440001c181045c02d2101401158021309000b800c0301c0016544c0c0024689500480841104003880c2c1583c1800550107401215141a031104060801015400042e901340c1c1040000781c40284d6110310f183d480f169180b00808020704c0545440030311184620401600004c02009009a641002c00c9000c4599 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 838378102 1250 838376852 838376893
    0x70803010b0a03060812090102011521080708030411130c020304060e0609030f070e0901090308160509030115080714060304020607031107270c0f0e031e010e0c03 71
    0x11442011030742c0c0d4461002084016040540100b0010f02030322100303068441e03481c801043d000e8001e0700280034204d2a0015000000c40c144100c1c49a000608404051003902b4103e00041c2d0b84103c402c2e07802d000868661050a400440302100c00f0160914500c2251038048200034a02c16400703001d010110b60020000d44074091480342ca4240f010840700c03032045a4038a415640d00150103800c4640038500100441c0c0e490341580300d0b00c030514841401044d40d480d818015104856019103e91146440d50381d5030f2000c01a049000b01c042050034059214117540c20700070300d54070b01402d03007040c89064100310580b4100034080d0700c194001030984800c03004645034074060342c1e0700039012500030340c03200240d040589507a0408181d5010398002d43c00d01145184103901003148254540c05490010311201801204607800801b4200205c4ca4000101135260321400304851820f50103400d0f101c0b0742c2c000380c2034054441880d00701100c00365110302000920000c10481d410b441e401c100c00404603418400030086282 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 838379352 1250 838378102 838378109
    0xb1003020f0d0c0e0603100f0510050111030f0307200d0206092404080f1209010b0a050f0d1b0924060906051e0c01020901080105010921060908030c0403110607080301 73
    0x110308100005e5280c0d4042c090a22044032190003401840f00e00f00741ca00c0241402c0741e541c0762000b480100402c09512803840040b140c103e0100451a04400c082625040d800c010860360421101900054151140944000d1610114001407074494000c0b071010382811001050040d6542c00304000a001e045c25800c6d12440349000d92540c0c04940300e5040c480860b00c22030065009800000610b41d2050b542036030760f94031800300300300204428410a420802d04102c50321441d80c0c03191144d04c25546600c0e100301e40e004500c5c031541c4880b4200e0b08070341c0140840c81c203992001507071941d10b10980c000100c040050410b843c4601382c118070014200a001b03003d408540c052407007040703c00718280341c80c440f804450880d003502401000f40c65803031546600d800b0f50301c9006042d0024400c07200006595001da4054401e94002180314128501209045c0c0000400c28034252111611381d4004004250311000943c01890000301040d81c0d50300f1824010914003000004a000702002c1004101090622003a203055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 838380602 1250 838379352 838379369
    0xd030506060409020f09060304031808160e100f120303050a0e070e0901140103151a091b190e0909071d071806020318040621030504030b1003020f0d0c 66
    0x44c0c0c101609605c13014062040c0e480c0d0000000001c0c081495040f08550840e8402c900c61240c801d0b499001e066100c0011318000d407007401c202e460030f00000d0318400300e1a5009900004102710f042e5580d03080301900c14507500000550000500f00003d26525001e0180e01c01d04000007400502d650b2036085982d101682b1031880d051031001e020840e0401c00b900314038848a145a204599945c6078240140310a981141d07000c25a840c2070130030000480300e0f141d50b40e01d01600400001003980da0000313140c40500c01003d45104002c04100d0f4840b58403078414030242e2002103030344881c2d80000e00818020280703009001c1170700583c09500100302c440c0c1104014200d01141080c000c41c070744c40e01c0400380c5030107080d04501c4040640081001c60141e80c004050900c0c0710406105020707000e4604284802c45009010304034020070180e1211080d000f20442c0c00e41568883d01d04146030036074a4446505107802503d00c03401e034201c80d24080040d4902000e01c400b0001c800c542825504920340e941c0034540742c2034811505d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 838381852 1250 838380602 838380607
    0xd110714010504030b1501030f1b080910051302012613140a0b060a050123071410020d060b0f1923030a0c110706080a09230d03050606040902 62
    0x650b449101914015a48203800c20190f0070050820b041c0807400d0100749000910340702112206102c14012514010203440b00d481c1c1d0300c624204200c6600350018003140c52842406105070b029042e9210f894032480500c1d42203480c01905100050104c2035440f031202420362000d14040614503101d00c156000480f403609044c000084d46042039105000d00c041c400d05010780600c2c0310911820030f469610581c421a80c01d500c0d141c548005480d5400c65400350100302102201d002484900100100000c501502041d41400000d0005601d408000801f506603144c010805030707101c83c041e01902015113201c16040307003401a0107070303c0f40060003820580e031401c03507003000321a1301c280c0124540b4641d414020790221f40740d1041c2c00c0490041d801641c0c40e131000b615200c201710320307184183c001800100d2080d02070112a8a0048102d8541c04040c05c5621680d690301c10010021381d036200c1c0a40707a410384020141000c03824800c0305080c0301d180c0341c4103828181414100b020542e103220490b0b05a400603200141c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 838383102 1250 838381852 838381889
    0x203030115180509090606090c03071b0204090f0507080601061b030f12050106050418051e040303060510031a090118180b0108060906070e010804021c12110d1107 71
    0x421000283e4003464120f0794401c03d01410313410101c0c0041c4581c01c10b4682550945035070041c82098070048481a002854000503115154210303840020520b000a10100d903c98003074446e00c0030340c550000200c4c0c09070700c20303001000780360300a01003240140781505040c4000200030f0b0030710340400a0084002c080050b102c291440c41e0780a16000090030045410030015580c45c0d000c090300a50207801032002401c1c62041e6042444004d01405110312075204020403101c260340026102040080c02c200c0925890f0000402c0c1030712090b0103c160b19005a6000c2181d09454140d403600040c0845a140520b40c0395006016607a2011103680d406507000000017220b510342c0110311130080b00101c000700068180000090406030003d0f07a41c2c0154060300030340c0d40907190900142c400c151440f031924049001c0030b0001c1d02515000405004862540d45c468842c1c00715640d99210305845851504081001c001580308008400c022116803a0a00d05080c3c803c01856201241e6910079480340c42c00c14020303030b079505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 838384352 1250 838383102 838383137
    0x90705041d09030d0c02241303111f0c11060601081603061208070203190c120303021c0501030308060d050a08030c0f07050c03061b0304021005090d0f0c060203030115 73
    0x19040b02d404c0100820400038280b4000751955200d25940343c85c00000c40101403c092203182c081e001d28410051650664042d0381d00741e40140061591140a019910411648030303001c0b0f036220840f04d44030354000b071242e001a40c0a4641c1d02d440b21140319590000080000305d0760081c1e415600817404600200306414010b00881c040c0079690480324100b480883d600041110031005806460310840c1520104180945081c591f2149214058103250341c650b401c0000680d01103400103140e00a141c0540350078183d22829403000002d584400c1c00a640380010014190312a492a42003081224440214403041d264261b0f0340400e0308010781320034400004509a8104201254043d86042c10096190300803401c0c529210b1401c030b04164041e00403803000400400450344510b030b09202c0c1c441074500b140c4980d028040f04140201042e41844410826000180d5428402000751882141544284145071801e40700c0304c015071313011030203550052005100240803c0401c90404103a0700d00311400c3c083c0107058 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 838385602 1250 838384352 838384357
    0x51602030f0712061b02030d0f111606110913023001080d0509060d0b0d08190e0f0102030307142115010207030c060c06021e09090705041d0903 63
    0x440642e10030200300007000008203c0d01040c960092500300f02861440c0c4401c000718400c100e202c40144c20401000d00d54034800d5010703905070748140c00000b481c00c01c8ac5a4112090344101300451403245a00f51980c2004400c0c0140c40c40500705081031414900c003031002c2842c000d0700c3c1d6078400003d41c0225090b8040841c8081150104035181c0224000900001494088000a00a20001d03009040100c00c0090081d4101c0340e0005003e03044034641410780701e154000349600c200c1c09911082c1401d07004081400703a000340080c0014004031210048811401400b1040060307411401490301050401443e038010003980d60200d800d0600c10480914803c5030070343e40c4540040c0015655400c203d803c0030041c0174551603c0740e24002c0079048124903000c016681e4070214880104260100306041c03040900c03c6000c070000350301c00c4401500b04490030300c104203200c22070075503402500310101d80724034140b07003c1c00c0780c540021480c1000c45c035085c108280709880f0154140c80c292490f0209001c0362541508008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 838386852 1250 838385602 838385623
    0x60f02030c01021c1a211c03150f080309060f1b0f150f040206090a03060507050d0501060507050601180e120304020a05090c04050d08070614250801090e160303230a05160203 76
    0x200c0130180503c0c4a402340c020841c0c0e242c0c0c0303070301000c00a101141f040401e00707100060300c8122000b10b040c90007031810030449520299000c1c00fa000244005442055a0408980c100508a000e84120148000f14501d080c0349203c0140c0c0840c606418883c590007240c00f85c640154058891a548540300000b054404506500007003605251000300904644d110014000501400b2804d010a9030307108000c0b11540036024014042c9c0d0820001080314040062b0502171800761709501146100d4a40ba0440c2829120754440e500041c00008000440c42c018a2850140408035003403241c60401c0c0000c02207500a48c05528004d1001003440d00600c00c1c8403040d1208540d006c1800e0107883c0c00004d408451003001c3c0d40703907004a01045903603501403014000300000054640d403481642d80c0303002e8024011345801c40c8080194080c0030078003400e0a00490200c0080c6029861f01d07941b0494584869240001e10f01001d02003240c00d0000c580499802411038500070f6401405004421843c00004d080000e40d42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 838388102 1250 838386852 838386883
    0x1e2803030e060a0f0501050a081e010605030d03060905010504050112030c0f0c080d0905040e0d0804020d02041407090909110603070e0604080f15010807060f02030c01021c1a21 77
    0x80030000b02c1203c9820041c0d88549042082c410b03641e0783d10901c01440c4030380c064120160084003d00e906140c410305040304d050620400441c0d0380f039450011900308003140244c0c0000a40f180c1052103001040c3c0602801404242c50070007840d807400b000300c0c1180807208030040400c8008c541100501c521a00620125a00800a145200d545028103a5200360320400742e00880c50080b4000f48501e0b0610807051602078510241220310515202240d98600041049078424601c901440260b2564421120140083d40046d2240c0c20701130009011071b492680408101410502100c0c0007034050321800c0c1c03803000181c1c0e607103071039440f407801c1500c010840d40e80d8030350400c01c08240010031620020b403ca642304600400d588814075101e25116102c40e00b4000c0100c160f1280600300082d51040c054500d039041d161065a0034a04402031040c2a45d004050f140d440f42c03440d00d9004d40c2800f42d40301e00d03800c6074440c80300c1241940b2510041444070703604101640c0614007040860103420400e00500c5505010703107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 838389352 1250 838388102 838388113
    0xc01050c1218090702060606032805040302060717060604090c0e030a0b010620030f0a170103050c010f020d08162706080c271807021e2803030e 63
    0x10004484400e1800b009031203140c410000c6001a40040750365070044401400181c0755030b03681894959003090303a0244180c40d410050303d984984034039100b0703030740a1440b90f8064059804e08040c0200070a140d80068811400c0c07030400d206941d41c0b1001121b0498400e07282c08140000c49103410740318010b4648000307806004850002e000c229030300c84014181c0c4c0542d00e800440202545e6441d2141300c04c2c26602c50954010400b2802d5101e01802600716200e8030301d07010000146031014608a01400c2c2e10440d2150302c60b403540125036070030048000d9007074050b02c000c0c04034070900b0400400d105409880c10414195070710101c03940314420401044809040c00665010003854044126904858480e82001034062002310f43c800741098119031240d03422a00115085100052100100070b4180700940c0c09030040031040028208449164070402403500600b071144c11f1121083d080300100031900794581c100c9118406942c6201c2022a41031001a030780c41030030500307803130264000d0482d200c40c02ca241c41003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 838390602 1250 838389352 838389367
    0xa0b0a0b120a050124090509194b0302030d0c08061002010216060510173406080c0c16080c01021504060515042301170c01050c12 57
    0x50358105183c4a80002c00c494020780740e5014003804040e100115451490100b000301e01282d411994000d4080b90640c4c0318400d00862020510039525402c9440d075684031000d04290902e0a041d2281c0c9816514250149401c45c26545110808001c2d4401d40b0f40050014818035200308180c0e8201e100f209000c015218021a018103008001c641042c0706060070f01b04010b10500c1802510003032200c076086012154429a541c10150078018a02d1903502c509200000d05c110b02d00c40e1101748915080080d04004106690401440c00442d40401d00f9584661018111303966803081c9000b00c40b0302e4540405152902c6000c14031920441080c1e100c40c2c0b00b02c0060452032100f11f04080100d401c2402181c0740c10078042c0c016600d45a90400900703142070a280014003080d12600601d0b4040d40c003802c110003001202000400702d5501140c940e02d5140c08029034104e52601e01015030140068030700e02004194803022807942d031109801114100400403924410b100010041e100095030009650303a118044c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 838391852 1250 838390602 838390639
    0xc030d02030c0f030708031b0702040f02090108060a14060a1803030e03160b0307050903010219120e06150411040807061e0f0c060e07050a09051e07020a0b0a0b 70
    0xb14814078071041c0901c20488041c00030002c102e80701554052001410360381d9800104000e941c020507010b0900508000740340050340c452180c880a01554500143c983c040c1000042000740d0080c401c2d070003500309031340502443c18400700300b0f90903800441751666200502642125007842c6c0c032185c415240040c82c80441010742083c0303071984101c0309404852000401000049141000d4844c80c00480820030101d07901a105000420a0b164090005482e200180728400300030601e915580740080c0110010600100050060743d910f0745d0351800070102c50404a41e000b07044805613040302d200759641c1e210407180d10321000955000b4044a01500c90745a9100d1021300f00d082103035540350183c2c4414405101d82806614148066500f60b6070310803000416a4401d030041c0f00d58100f4100038880c003440054160340d5080d06ca405403060382e4022a5900705160314a840914000358040c00000c03c8082200702e650001c0c80c00724107074005040da00a41c9403244514010180609895040807500200707200b9400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 838393102 1250 838391852 838391857
    0x120307030f1a030d1b030c0309081f06060c0302120a0306050a08060f070c0f0f150c0e13140c0d0204170309010f0306120321050420060406050d0e0c030d0203 69
    0x181c042e0280d038007015120b0070803901c44010004031604580b1700103181c0f0109100d0010700032518030170b040070313142d0726103441c09503203811408988000c3c1102d01046000707000c4c1890003181e008100c1420802c4940080e560060748aa414a00719070b40f01c0004210f0148444c401c3d0040c00c001c0c14064191108591685001c076103520027103500c0d5a031050401c02283d003440c894442140b1080d001030b00d1811018299442c0645600c0004d42030311004040440c030707945100d0301d1051610300c5d0441d44820b11603441500500c808180c41402190071185040307128000c1180e0310813810b600c10310a2140369a5030551622142c003e02a41c3c00c0000d04012240e0000f499010000042c082040300362100924086821000c90a0302c0c41401030500240106403610300190103041d818115101c9800c4511450300c07a400d0203422248112b400307842c0015000360111203010240c2c84152410001d403100303407400b414008c3c0609503200c1c281c0400701d202c0d50340c8006030001905101c0b011500c40b0047c00e40d106100300c140300950300e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 838394352 1250 838393102 838393151
    0x30f090e060d03050918100302150a0e120102071703060108161b03051207090e0a0203090304031419081b071202012a030305040c0512120307030f 64
    0x141042000304085060300e101912440c4000c0a240c90b02e00e5aa404a1303c0c1c0c3c02c04404250030068942011641c107045440e190710482c000c0250800e518907600411084c09140300290042c0341081180a8100358041000800d200f01900c1c0040c0054110066a00901c10601d01400390a1000700880686403207000842c010302d0260388552290702c40116000b400c03a66404500c0c08144140c008210071321042c40354121446c002d061943c10401c9580d185c0d5148001101d0100014050340400d1104030003000b20f0030340041410f1011801c501c1c00040b03440d503a100b10702029206150380b5511549000042044a008811107450303d4440b619134500500540c10120b401c030045404020300405242d80001c9030b13801c959042c0c1600d100e00409400549041e0b11000030090062001d00b82c504484030700701c0c8510101403186d41c4c0054146010300b801c2c412244150022407040e923001480501036400001c8141d0b0015080d55105d82d2038580c2601a070040600c40306e00c85009040400386001204c2c08070400c46c0a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 838395602 1250 838394352 838394357
    0xe06040e011e06390b010909060c090815060d140610120f0b100f080a03031a0d0b0a0236030a020a0b03040c030f1b081c030b030118030f 60
    0x4490325020141e580c4d2801c901a4203d0500149081c1e42100100ba00c00c0ca41501c040500400c44440e034464101401c8240c0202075030680300c031034030000c10101d0321586500c4a454a1314075446070500f18000e4644c8800b009000c01607101501045243d80c484224003a601d500c9140c1c0005e150101409645440040381c0400a6141c0400700041806d03244034440040c1ea40300e58078421203201c5607103446402c0b4018060080304400d40d140481c00d20341221040001d001d0241c02001407201c0c6140040c1511441a2102e6a20880582c00c01d00d5031280c03031070b403c50b035a030010b815282c565401c45010000d000c0c001890038940c030007641c8006028001d2650020046903500f110498000708000d040d514004590000d401007a00c01040050b4a0404080c41c0c1251046d0407440880f41d8030f454180c00c08101d250256036102d1094100b103110314008280200820090001d4074100c82071036182c002e011010307074002051580b6003603030580c2035900394032141111120501c20b1a02c0d88943c10300030080c61440207000d01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 838396852 1250 838395602 838395659
    0x6011b0f150c050901050f09040903020a0b0105190e040501090b270303060a030219050a061e020a150c0314010303050403030906050415140702220f18030e06040e01 72
    0xc411207640940c288542203501d5040c0303004481001141c0c01d80c84441c075100560383c02d1009031442d0b40c45020b54460313503000782d001344210169410030141f6000d060b07000318881c0710850803d400a0071030702103000480d0900301010106580d1800d055000d40040701004050160000c2040120480c40d261419511001d075031040c01c2900d400e81e9180e07640300c00c2c2e9005038000c0f51030a0401c01840c00f852002c5100120302c003410400382d0f8070004190081d045030804404503105501010314144180e02c00f8100081c0c0c1d20007841c200200d034480c1482c220500c20381c40699a20b40d607048800d035001360020305010450708044080381d81c1d28180200b45401c14001100041d00907a00010b20601c54020348094800350300008944140b0701005a8801c0c01c0015003007180e8000f4007000015a69001400c029010304c0c046203a2007464650044040320211a01d01e2566031a0100f0180c0c8020380c0144030090a505081401d5940c14100020f00980a0340e8000b149254403400082420802c103520324030351652a80311240d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 838398102 1250 838396852 838396883
    0xb06011e21020c120901210b01142a0a0803131a043203210108070b03010302120f0a060605010e0904120806190303050c060a0b0a06030506011b0f 64
    0x1c00d80c0324202801da410780c0504c0a919803d02c2c0348006000000f01418184d00704c4c81e01c241000720090b1340da800403d90700d569030700c0701d446035030081615940c0c2002c010406190841e03d8440800500d42e0240148010415004640e1000b03401c018021413070750400f4085481e45002c42d24080f00340b081100860b150002c01884503075180c48005414022640103840e50010402c415616481100c0303a2000c0749000124858400200424002030580d01154017812041e00c61071004002d040c0010b9010303903004c0c0d014103401c2041030a52000d42c0e065a60440b0b02e0649020700d403400390f1900b05c0c54403090195014421411042002a911030000c82d4401c0c2c0340c44210405203803c0200841c0222400740c0107002d1720b48034a60a510484841d9403041c0000c10143c0146003a0030720450004254108a010a400160724103c0120400c6600d0340007014901c1400110210008110340311468072810040c16262800b18049a0180c40d01300104001c040341450315500d181070550400d01e11800603203000351900d2600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 838399352 1250 838398102 838398167
    0x3020f03010603080316020a240c050f09010e030a0218011e03020108160c080c0a030e2403070c02041e0b032d07030f1209150c0b06011e 60
    0x14101d9130002032050640e03a80601c4010310b0b03669444481c046024034640100003c40000c0d01c2059400c0c0385803029010a2415031100c1128885003907002840b000740170070358030782004a049038400ca1003071034000c501503411004a480c20031980c000039030000d2070840c0f911019003050082d504a849070102240030001801c41080000024003019000401c9c100010340841d221480b0006100145d140100344290729845d860102e400c41d1a240e0744603003010041c101419488000c108007074008644160510600300030400c000100d8482c8052001e9010001442d064021060840c4031900680248208200340b03040e040703000d107060059030034649030041c41c80640c1000580b43e04422850320104030054001030340300d0f030301c8103401c00041d42c54031440e079020000545054180020138401c0c02c0c0801400c042a0010307040c15502d400403e4440003c0d0340d031411003030b4855108800590007540080c042d403a0074004031114a4005010a520748022401c0403007594040e00c010102d00700199110809620045034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 838400602 1250 838399352 838399361
    0xa060c020316080a1e1106030612070321090e06010311040905040c0315090f060b03030d0219091a04150c050f0f06060f0609090a090b0a05090c1008130c0504110403020f0301 76
    0x1926400c9590306c640c601d420040000c6401404c024564100306074420041c83c40c0941d140c204071101003544144041f00d0142075615040d840c21801c00c4480103007403a12450700c805009000314105901d071506104959031840464000d8038400d075091109180034100000803246c01e200890b882c10300e0340402c24441050303202d0390840b50342c404402040c50301145c80f050094010a001076506010410000032025102c0c0700070000c140c0380d83c141075040600f0b020b014100c03c0c0598007552091b030328440c002e0000c60059046a00390381c0b00703003d510345400240100b00d0b424612040b0080c003501c1500e010451483e000508944c0f20310442085811aa54000030b010744c5002101c03156803c08401c0c88071f6060340c1b0b4481c0c42254840013075138001414203207a4541e40303a10f660548604c000c090b910410b111000005012205003c00150740408020507882c00090a1007030080011400880c0c3c100094100031448410300c008202c020001d101d84454084111100c2c0c0c0240b00c100d00c0742ea0880100221814103026 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 838401852 1250 838400602 838400663
    0xf010902030721020c030a080a0c140a08072001020309011b0207050d0213090b15060a09030237080708150606070c0509010b1b0a020a060c020316080a 66
    0x80354259105001c3c240d07800030f03503c100440c205940074071954008400410240c041d00b100e03540c0742201c5040401e9020201c0304d400010404102201a02400340b80c455000c4030380c0510070786041070255a910380100c4600e01c02900484002c1328010700321140b050150007031805002c9000c0200035a00c507101100d2000d40382d00d46204d0158100c3c04041000d45000024814607034000b0782400d101d0300e207404101e030448860080407a0828604401e2100703000000540180445080d50000e260541c0c4e00d030050180c1000c2e100080c03046801c20b402c600041c08075070710203d02841001c0308409428070810328050081d13660141d082c0a108160300010b1031880000c0720013101c03046081a8003113445500034098950f0002409440c841f0881c04000b90030b44072003411500a00c40c9400c809c0d11020781c1c03481c10780c858820040b69120b941c099100000560364201050003140e000d41003000000b80240701280c1424604240c1b0703203000724145800074118001040014009204191343c2d649a001d003680f402e4500306805 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 838403102 1250 838401852 838401857
    0x109030e040c0512270309060f07060906092f06190c1a0a1416121d0d02061f060302030601030204031b0f150c150b030a0b0f0109020307 60
    0x31800021820654400b00c4180c50034a4400e00d813007040711030344c6036112041d5411000400d0a140f03088140007001c407107000d200d1350140603526141400700018064001c00043c004843c4000078500200709496100c80d406a034402002d201d4001141048040c4c903034444540044274070b1400c80c0c0440c2094100c0c0285a482c4010045824009008188000007442c00208010b00441d5058040441d92400fa00f185542005001c980c480c48c02c0f499a00c241c9845000030b15064401c0c2080c0210881490700c080110346e01881d0080080c0e4030b0340b800304003900c00c048864152402400401030000c40206610b40d41c507085408840140c0ca90144651644208514100c000c60030a6000c0c403065100c0e800454003d14149800360400c5c1d01c0303446510320038280485400c204038031100300b00070306031481222400401440200080744980b80801034040b01c04040000c160780c2d00c10881e40010000c8d07030f100d0807546001400710b9102c88980d2410b04c088044c295a20001e804081000142000303c9000301e07446407203641d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 838404352 1250 838403102 838403117
    0x1a13140a060e0a0b04090206070f030306050d030507110613140f010c05071208120106080921040e0a020d110a030e1902010c23011a0411040e18011a03010e010903 71
    0x4081030001000c96150950740182c0706c5903100c01603035035000a05200c502458644846000510b005000c68802da07000b42d0058100403210740c0401d4028003610402d68004811034001d01c0c40c8400940540700b20048200f8500e09c246c4c003c2219141801c4848905206503100c0540315840c0006450820f80740740d00414540c0300b482c0900c440403c051500c04042e10689a240c2001100c03a210051040240c001c0000203265504200c40014200700035203000302c0d1000048842254071504c042d1134811800b039a01c0c102101008540d488003141d040380d41d88000320fa420040119005e6a5910039401489000300190911a202d4040103002c244114400041001e1a829220f01d40c01034034030619145042c2c940701544000032141215141480c80400fa81000000c1c0c1594810110558804807441d03041c0564648840d01e40046d21541c119011340313000304d010f8015a80e495030000c00113140404625201d50800c0e15880355441d03512a02c2483d01c9040b8024002041e912005a0803600344120140004000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 838405602 1250 838404352 838404361
    0x11106010b161e11031b01021c090f03060b0a1a0715020c0105160f081605030c1303060501180207020a05010e030309180f281a13140a060e 61
    0x905619151842215039003036500600f038018603c140141d6040d00d04080d0000c1003030407490148184000340703d2090034201c80d005501c0000f0742d40d0340d001440c07100381c4803000740b043c520600a55446009205101d58102c000b51213203845009464102d0303a00d4041c01802c403010035139010a4164070030840792400c0d03041c1048034540b2540d05c0c61507152180014a41d08100c0e082401c80c081c00b0f601e105820200c44800300c00303004e007001400022800c99007820130448006001c0e059822100285030368009260079a1691510240306650703219908805420001d5070300c0c00401c104490700105d0484848028120581040e103421405a02c41e10f40e00a501c00c1e4400002c0c45290702070410148981d00146c00c4074240b0800030007240c00121a8814102d84000780d40810100c040d5020007650700c030ac0100224190001c80941042d007045050714601460740d10f80144c42004808030440c8012448010094032018607241c03120001010780c000d42c003e9880200002490401080c0181000c40d40c0d900310404290b540e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 838406852 1250 838405602 838405627
    0x80405030f09040b040e0105150f030303011707081c1e0c030c0c120c05040c05131701020708041511010c09052101111206011707050c0c0a06050405011106010b 70
    0x12021042d4800e0359040800165200c2c6d100380c0741020550400007489062101f03145c115100d01690b194030a90300885032000c44e480210540c3e045424400d0403410941d115901ca03420504107422040305446444507100340845034901d4000010245e80b100300381600c1c89030740300c10304840c62004800441c05a0003203500007441601744513243d5005014041c1c005403249c1c0362080f48460040281c540c008421000d100d00e290502c02c0f00408216800c0030741c5000d0410400c0c01d07004600e03124104074000034100712500460290129640c265100d001d2070380e10381e104c0751448814030035034881e0030016078070303240d0000c0c202c40c14801e540c030404a90300c498050510b0b2908100240f0410500c0000d08020004801041c80090040c0c0503660825110f4a4454039548609104514000c1c80141040342d603001d03240b01c18681b401c4441d0002814030305180e9a4070840212850300f54040400da4100141c400c001400d594460090402c0e20400d903103c20780c10744002407003a80c809083c0600c0c64441810406000703c0d52 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 838408102 1250 838406852 838406857
    0x60507050a080f281a0d0b06130b0a090c02061008030910020708030301080606120d0e0f0f0a03030203090a0902270d06061d0a020a1d01020c060712030c080405030f 72
    0xc01100c1c03003107240c0781021504851804d48400f91401c0c55290b088000c10380d1540c0c900468900c82c1510312400740c2183d5200e000c5641c6010700514003482035100b4450a49015800c8800c21600c0601782802c104e81d1801e5410081454040f20381c018010034020817600f400000c810001c0380d04540c025820310342e0340da04008417030401440c13000c1503111307018000a14290070302c007a500802620b80540006e10f0541d050124040088142c001c240c0c203c5440000c07110b421860110b60100c09031809000c2101000125144515020900764805030000b000400c01d5400001003100e0601594600242139a07480d04c03000342e001c1c03440d20401c01410705071684205041144000c600440060090501c10a0b5448010803600301e6040094200d90340b00652600820000142c0e8004190600462528048441c018054801c511072340d60100034000c2d03440000c0c1c0c0308002e0008032440051089540d20002d10304064411454145071001c03a04140c0f12112550003460001e102d6030304100610716200040cbd290328a01d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 838409352 1250 838408102 838408111
    0x90c030d1404081b0a06110601031b08030d1b020a1e050a080d0204050102010605121b060903070b090a140d15150308070215031909060912020a060507050a080f 70
    0x1e018080050b0f00380303080004403000325a0003040304003485211305104080030079411000500c64a101c131504110400103000d411241c000b000c8401d0301061030b18480941c00e103a804040180310100304c5003044010350b80b154041c84003014001c0700e490001803069854541c0c0e4800a040301100c100f03455070300c081e4400e40100091048042c0c50307411945680d040c034542c01200e01440701e1503000c2020320065030244190400760030f00300c80d02e80750141c0101c195541c4007420542e0f54400d800c2c8452a01194403402d0550f0300130340000707090718902ea48415a80d4450f400500405114805030580041c6c0c404812000d48112500680310000b09000703a1a220368045080180080c259500c1440b10542a000403135000518403c1e0103141da036014038010440103030020141480030610030014069690201300b0201032400d4103900c04241d003686400c1c5100201b01805002d001016801d1070200c071907901050843c81e09220740d0041180740c1300c150044481d40110894000828000000f1652101c150316401d40d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 838410602 1250 838409352 838409387
    0x5060714030318070503060c180406030203010203070518060f03010506030702070e070e040f06050306180c1302040f080607080a090609170309100e03160f141005090c030d 75
    0x140440c01900c51659100300c4081a03030309100100b4028444040c40941d00519040740101b080c0d04141120740074034414001c000c410f032140c10506094680715130300500011a00140215100d1510350f8011700186d114402c0c000503180c4083c021754451420b00180c0303268200450400d070841e0309120620001e58000340c00b480541c403d18200180c2d080d4a6800c05128440c80e81c0e0b2408040c29000c24481510000c40041031700e1401c020082c01162400101c1a130701000b4034202003401512100000d0a002180d03004d6a0003803840300d1800c1d440c40f515001001255840c03214040c095a50364a480e4a07481c00780c50070000502c040c00411a03c09240e000503220b00e0150800140d01d10280c1e0b121440504505100c04101c00c001c020031400700018807403413039401c040703000600918004200c0d058603880f5081e2101c40c1c84040d00039803801d00043c01c084002c00f90f0311402220451015409882e80d0ba50340364a02c48040f4206000038004000115496080c14030140040a0006484500f035510300821a0038141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 838411852 1250 838410602 838410623
    0x809010c0c081006060f080906070f0909050108030307110601060f031e0e0c040609060321140f0c07120f02101209030c05010b0a030b0c0c0304050411030709140604050607 75
    0x400c06414072841c0c1e00c802c041c3d100055070f189000381c050500780280e58800144041003040005059001c030301d499000441e4508500c07070041d051001c0c0d9251000b60001a02145014004540750760700100541c0910b6058603259103080c0c1d43c0405654072182400340ca40083c102d44800790507240a60000d800081150003201d0501c500382109200725100741010b03034825402156907408a007003502c9035101501503400148845411030300c07010f1000301260640008461109590004e0320310600e2100380794400b15104580d039001c00203280d046904071903c4030322907015401d000112400342540c403407150b41c2d12080901d0401019020012041d0044007000240226146000207856061141140951190f15440c0b521003090034200e085031003082c903c50050403445d03c02d00202d072015501c03a030300011510f00c0303d039240c2000506600310b0045901c0181c2003418a42440401c040c8000512701c510880d80d41da03080c0c160384044454030300640010751600301074208024003850034044010451a03001c0c9900d41c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 838413102 1250 838411852 838411859
    0x8150c190e040b0d03030b09011712090d0f0807200a170703020a121103030721021c1e09060f1202040e1003020117040308070804050c0306010b250809010c0c 69
    0x440810001404a0019075101400c0040340383c82d0230018007421408400300d0446405012841d50f90440102518034810049410101c681e03c40810b00e14072a0301c03000505030481c140c40c1444064010203401c030341aaa08581024a03228210f94012079808000c0142c801186080c9900700c2c0c5500d87d59a03080b8901800c0030104c09626401881401001072042204441000341404a500b2500f4460684203800410400010440c1411680f14130030210303949911004107005c0a91400e07a5a0040c9200c55134100034641d00d00390468040b4500e0080d4502200001c00214001c0303800d40e000b4081e12010800040300740003c0782c41403c010b2003496190760014985900c0781300450f001c0030b084a05110107590640c00b8821946d000c01c000300c95040480640060f81080e5030040c0c041c44c001402101007148500000c0e0500104001095800307034054290f407001c2d6103030f40c3d00318442c0d8860001c1c0701c490002c1075004080140403000040c405034005051030304000141c1c0044905810300c00c0241d400268484010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 838414352 1250 838413102 838413109
    0x90601020a0b0f01050114041d10030b16030c08060102060a0203150a080709060602150c03040303020f070b0f1005010c170906040e100504050c0306040b060d0608150c190e040b 77
    0xb075019000356110419150314020005010034900901c40c0c1c1c0c10030051000304100c1c0020500500c1c1c08a5060700303c038556032550a502540490ba9001505607a2040c05110503884808500284140c1aa0f024440c01d480c4140c03e5454030020345021b0700503440100000c484d06450707409103800c40b40c8240242030354803056000030a62401034106c1280c5130002d074400c0119410700e104601c001d204900140c0040c120101040c0029140240f100400d42000000130f020144a83d04031084014a240c1090b141d442d00d0420000d4000c0c00c4990035804210400400e01c50580310744e0460807100160f6601c110000190340c0ca1240d0702da40780795040090428001a00c040d5104005403028004036130100740700d45011400801c46406a80c40540114900010300107584480d00840c3c3c1e000c00c0655000c01c1d4081003202103681403082c0c0030300030440d51030b200011810501c00700e41c000308a54000e0015880c0d4503a18440c1c501c46c41544905481040d000c00210040e9001c1c1740000f14084008200140d21503052021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 838415602 1250 838414352 838414373
    0x80a03111e060123010c06020d0f020f07062f090d020d0302031207090501050724060801060302090a0b0604051c0b041406090a02011b141915020315090601020a 70
    0x34800d498100800501513224001c2c40715071070a01000c0c480f0500b400f250006404004030500107040d20307400041c241081241c90304020740311000507500715a00e44080b1800c074030399042000103e079080d003001c0404655807a0b03048034860441301307540f022200d049030905081e581d0780f1121009800450044080e00541d40700002c00c0401402030300615656401c21000c011440c4008210f40300b0700001c2102840180d90150545508650110f403450f060102c0740d90f072a5040039889070010003941070103c0801d0040c4107400c0603007100c0c0b00361004691610b45036160800d88500380241504120240010407003841d201e8044c20b00091808645480c100d03141d00c461409007411102130380d851290700304c0d412103030070100046940080349030041e10303403c803455000030a01103070030701c25104c1312071000580c0007030040302c0301c0b01031080e50030500311031005265400c0e5280c145050075058400700454480346d02e003440707a802100d1007100008441d12001e100e038401c0107000b0101408042c114490305101100003a143c03c3c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 838416852 1250 838415602 838415653
    0x150e060d171605100e0d0c1406150102120403080d021303080708070c06050a020604032703150501060507053012060a051002210c03070309050910080a0311 68
    0x803038012240d00e00304945803444c1410f0080c140380c5401c56510303000d64040341c003e003009807d1078224807c2c19541000b5801030300c48051702c64140100340070f00c41c042000910380c484107182030302611200711918004078254015844040e0645608021108400742c1c01e9000f0300b483c14440816000b5241c50740c07a60b12003a04480c5086607102d400007560001d101e0101c86000040c42e461400614103d0111002511054007910050622041d060b0310921400103560b03840441c03800040f076070140c0e692030504c440080001400a0555850b0034004134440c0d00c0b860484500036040300091070340508000388000501503c0018450307a403d003151036065018508000c01c0401030319109140c480c02d002041008940381544814802c40b9801061001e890b0041200c0402c00c8119843c00408640140072a8061164445606541c0070004840c4105034001403e2010340b0b0007918042210f5584856a01411180d4018074903590311040110300000e20881074444030407815130a540c41c22840c0e80d242c01c01da500804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 838418102 1250 838416852 838416877
    0x31b030f0307050702090a0506180402040605190f0905040c29070605040507140102070e15030102040e07020c0402070809130b03010c020a03020f010219050a1103040e0604150e060d17 80
    0x40c9410170b615001640340c0c0c0009401c4070800181c14910001030004203030381d140b070f1a02c8030308400040542d590750380000000c02000c2c0c00c000401034558581d00880d916409480a00071012402041116652040d1440340780c4c0440d43e0b5a4041c10700d01428038036070001c030705d507032004220100c0400103222980251196920030080072a883c1094a089800d10301e89800c08459031001d20715803170043e80d00155030b01c101c0e9403d40300c00310342d5250760440440038504489421307003560000500007174a1403800300c0c2d58898217065083e2045172044104000607881a0503024081503018045030241c0d103012441a2201d0075500000142c07114610f002c603003903500300d0070410096005441428113058050220000c50002d0100840c80c014641240c4c4118400854504040003000309200602600511541141c00f41400c1101e0b1110351b120f5500035600012281640103c0c281303041e01e20002d0404d4081402e8441c0d0030b0403164117585000c18003405841c124404e0758019040041811000321040017080072100343c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 838419352 1250 838418102 838418107
    0x4060f1b03240b0714030c160b0a091401020a0210030b032503030f020a0b0405061b071a0618010905041b060507061805010c08011511031b030f030705 66
    0xc403006402c40d02070b42c103004500300b01c001c04036041c440302407209401d072034209150700d48480d5642400180e043c00141c00d40154803000405400c21000040d0800c10b00300101000000141ca900c801980f501403204003001040c10444140f0100320f0054146081c864184129040b0480e242c002a440071002c0c94030901207035852005c4a0141014001c4400c420412040d105907404988290300c908429440003030100b1056426101e02644240704580754107030000412403046c1028245561200e5054400501003820035120903040c02041b8103441100d604400a05081c1007031540710550f201c0300401055120b010140715916203800f03024403501900746c2000005441c5081c0c03408030000c40064800103800001004100540c903409004c40e03405aa00c0800402e1072810a80e0410b558448468014240d50070082d00c000c00079072003103006048034030800e42c02803a012480400c0c0c566910b02615178449070010448082c4403545840a10f83c480b906004072460041c54402080c0c60303802c252160340009200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 838420602 1250 838419352 838419401
    0xc0b0606180d1a0106020d0c02151b06071227050c04090501020c010b010c02030706140f0d021809061507050304030503040609060e01051305120a061b0207081207030804060f 76
    0x310400c86015011500040c247d082c0e5044000d010300301c500100038440c4404000b141130b5072075440181d400c0318000c071400c00700d40c1500701720b59600c840341101c050000580c0081c005406000c00d000744a4a00360380c80064100954120307080000019000040d40c0714400d00b001510303d0f4480e4880d00c100305014000058607251600d08150a481722100041d0400229842c608003680e4081075410803180c503820800c3c44c40c1445c400cbc2d18000d01034079500391001c17200400d81306c000c5181900140180c1c40c00b00b03005014100400c0410110a80995025030000309100b00188005229401005000c0c0604220390615076a603680d42c4c44c41d07219400500016207002d004003ca990404030210042409003446800c0c200d1540f8140c006803072600c41c59200700410b00100e10800b07001c3c4045410103070006410302030350720110000d500c074585a4a52000506c100740700080d51200200300b2030b00480c409000c0901c0c0c4003003a10300b01c81840c1c01030706c10b984a0303a882d0454501020540700303500140030244c828850303540e42d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 838421852 1250 838420602 838420643
    0x30a1b171501020601062001060b2218020702030a1202010b130507021207030e03060f060f04050c070b19060f03120e011e030b0301051905070c0b0606180d 68
    0x985010150300c4501c501c2a51070707801240f100d06660640ca00302d005d480a1012443d0004804500c3c0b009035480c111020890f8400d100080140302c0d0308040d000c0405005106940145078148110b4600984804500f041204290003d0141c0c0740010206c482d0b2120b59118620400c100b1420203015030741d2a009254030b4100307045541000300c10990100300314030b041c540180d1250000070140c05e9200b0005100001c150080c4e00b60060900050100d441f103180010038010301d6817007502c40c9442540c45440480303251070580038443c800d031500002c00d810314403981c2e58607407802070203800700186404d8070809600001caa889a1030003089000315902d540c1e441d5040560041005a802c40c04014080c08188120790b003003001103206241040c000c0340b0040da40a030071801080c004508690550819060100155200040110b4030700359800810480d00c0d9480d003a2060041c0740c1380101a10312100000f0320920b480d001034210194580184000c450709078002030805041075a0445420402e07102082e2a4107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 838423102 1250 838421852 838421897
    0x50405010e16020d0509010e150a02011a0f0f0d08120708150f220f140402030d02070806040807110d0f05010f0515041509090317090d0c0602030a1b 65
    0x540c9400a809184c00c412070040451142420301030501000401000d49612503043d1203910f4090a54169180c220f101c1c5c00a018252551301c40c00142022125107505103021254601c00d890020100c1f80d001c40544280902048184000e6903140010311040c487c041c20240c80d64445e941c10340e00d5400c0340c41d0159040c034142022821950080e0450481d05e8410b40701c0a03410220425500940c13403d230b416066911024060284910b2503150904108882605c0e100b032459000303520840c00d070758010200c10740c22070762415035120304002c0703034011408600801c0c06140285111409048051100c521400c007003a18080212021138450b10f0a24004062007028800c05c3d00340c180e858020710150030444032104014502101440c07041d41c0e22032550b0a40300c4c80390301c42e600070001e0400c04c3c80001740c03609003e46141e800e01038100c4e1143c280c2000480c000e41c049001c3c40c4020050301d8802c541041600d03000002d4000900d02460716596400b80704603410007040003500b07009207a841080e0403040480990100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 838424352 1250 838423102 838423141
    0xa1404032307091b0e030a080c0d1101020c0705010c03170118050a0b060301091116050304031502040b0403080c1510080c0a12030c0c0b0304120f181e050405010e 71
    0x2520f489884039004403d003801d403044d041c0742d203000e6038242510313400613043c140400c000600c1108006280480c01c5804150b50181d10300f20784810310704182c4040c0b81401c0c0d21070141e4000654011510511103036005801c0b1078851400303450300c10349145070381c0040314801500f078008544500c00144954022102c3c2d000b0140d0140e100f51062000130750030008607500740418015841030b5511041114004203449080c0d44195100e031451001240c600d0410946a030310a000c2580d11000070300440050681c0340c004c0b90200e840d60088131b80342500d5a01d40409a80089003115064002c41c041d1071070359250620014001c415890b0101c1080e490600032904c5c11205000b401c0c003503d00450100300e05580000702c03821540d0107040103c5000b100c4d01c3c3ca1203800304580c00552407100084140000c0c40240c0054004c04002d0713442c2c41440424108090750869652418a1640b502c640418803500c4404001d00840c0143e80c455000c1f81030300c0740300040680314240c10282038040400308100d200a96450603107800c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 838425602 1250 838424352 838424369
    0xf040b090a080c131125030813030804030e040204150801050f010c08040b033403050f090d0c140a0501020c19081204150e0a020307050a0b0a1404032307 67
    0x110380e100f1010400c40c1201da9910181c070745d40c800304203441e43c04480c00c4a88024030301045070320200007410780c0303004408000030039000140722900261401c0c5101e41d0140d82e8940584a072138103655196400ca03204108640440e401c580c00307200c00100c20030a200307000c02807480c42d1509900c80d8100414032541000080034981000b4031880312101250741c0700e007241c05807243c0c0d0107a65502e0f522401412060b01141e10192880c03c0d00b145150556807000100c811420302c19070301400a61210340d041c0d21182c40c15980d000c415001119040c00c01400f444404001034461000190030510414006082c5234040d14240c0f8140d40004500701203040030300020500040002d80c3703154000f905d840c0d440d0700f806285844440c49030800e0108080c84403c2e5418a240e0042c1c86060100d0610204043d40703d01041030300303d00034441c02c0e0000c145031a03d200420180e502c50008141031081d468007c0342c1c42029125682c80c400d108200110100d072710405040e000404904c401c0c080a0b0076039100c50700c1d02c0415401140c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 838426852 1250 838425602 838425613
    0xa0911030318010507051204181b0f081e100303091d180f2a0a0302060306040c091208030405061018020c0309130b0f010302070b01030b0405030f040b090a08 69
    0x8010320819444001c02840c0c250340311748452801e01e240000450b14001c0e11000407500084511038114180c012040712481801402500d00c4280c00f003009004c401c201040b8801d4020b10510710802d801548502003214002d41a01c0f1038082c40610041514400c520301c2d2840b00501c14590841180740c000c2600c07814001d02c99005001c00c0040140280c40e04c0e80c555070500500c0070a603000c000f500c03081c0f0064015241d070311203541400c6100a520081c18544080840810155843c200b8901001c407038001d80307142d103180c3c0c900c4100302c000d000b00c03003107038040c0a003018011070203050f41d07031004012500c40c4034000e42c4d038240303828140d01d40107008120340312850b4601e0061102ca03080084a0b010b90b0000080580c84620800f1068118010241480d421415100002c044512a604a0551030038151800010044008011426071188401c0030b40941101c0c401040020508101c3c1c55209005d003091b80c0c1881c0c1041c4c80e2400e01d0744990700486042c031012483c8030403840e01d5100e00005145842c01002c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838428102 1250 838426852 838426867
    0x504060222031e0807060203070507020f01030c171b040801050f0919081b010f06060305060102070e15010c02060c01060509012c10081905070522230a09110303 70
    0x1c0240da40c014469400802092101c010480c8600950b6441790f8800b10954072482c004900030840d170440e81040c8c0c40340c04c14060b8105554002c0c1320318013036203d8695038001404644807002c00000c03805402c02d10180c0050100c4803004904201074000f520b003550010440c1d04100708498105d080260000b0342c2a006116034421140881d008568441c0e840340c1d40315242c41da1041c000240d1010700e924040030b54204100301c491144503a01060a6403030640341040715031500c030300480c0d40355640c1c081c80c13956014281c0070510704402d20a183c50030040515150f91055100c0e40402d50700e40140d00c030b0b12006da4407403c05006030710300381c24030902415000d540142d08559240c95180011144000000880c00e008041151039030708640c45409013a50f0421142d840d00054001c01d84604181e17000d40d0580500440400ca5142540e400c031407420101c10841d015204004180004000b00d240500344840c6200d01c102d0342d048117000c807a204510b10800010070603660708242e40742514003500544290400c01c0090b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 838429352 1250 838428102 838428113
    0xb153a1802120c01020703150b04060305100c0311091302070807030804151103040b0403090e01181a0a06120902090c030601120902060415020c12060601021002040e01030222050406022203 82
    0x46c0c11a50804041e00100c0d102003064001880c0b4581e1040d0440d003070540102c184a00014110380d00d100d070702c0040051023101c1c80d0841c11a07007145107a01c07614400300510041840c042806081c03000c5001c000501c0c3c02c0b12541d072582590302110b0100c002c01d800204220600c2260f0507458118110b684080c00000c50846810080d40302c0200000c0c070400941d40454181441750340c1c504042d041d8100c0205580d41c446208404520003078043c614a01d0070503207007007400100e14141c6600c120001d07007840b8140d4104082960b4030a13007034a007c510280d540076202c025a5900c6101400b8404500115580f42020b100040044803c00c00401503181030a800c17000607260101207408540040c03a9509185130520001c13420700e1804031800740c1c000801d00c45e040f0421008100036000701000d80843c0c64050410a40310240d008901c2201c4500074860010005401e28142a12584c041081d070301d0000c10814903101d00321003040e94141c0b0090340c08600c500380c003170f44100100c00d181c1920340840302d0710745181d498 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 838430602 1250 838429352 838429363
    0x1240f1209060b120105191a01111207061b0309031202090109091b0206060a08060a02090402090402070302010605011407020916020307050a060b153a1802120c0102 72
    0x44044103a0785500038428030030254018284010700810300440d0f41c0d800241c0724083c000544149880710250490f690010f4480e00c5040440140075002802c121110706c0103403840c1c00307280041941806070029816802030941c00410302e292041d140050411070062500303e440b41c50b0303a00a0145440e001e140340100e500901714800c00301403c5800750f9525a0000100e4246a0642c4103121a505100c1341d40c00b0b43e41c0d1807402c0b01c0c414001790308490582d41e54904025a040c4540316061494000d6000700d0a4600c0e41e800130720081d6405000585400c0801020404a0b807010a007034005135550311060106680c00325200c0610324807025441d05081068001802080c400b61000c00450b02202040c06224028000d40b62216044415a01804000e06001c1c01600c4449002882222104070040e40c0d00ca840e400c0d5001a15907503540014400ca0003441803d19405401c501406072100b09034403080070aa00134003800174280b8a0301018a0b0b024170500c00138542d0300307009240603000a401070010f41d074000746 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 838431852 1250 838430602 838430627
    0x31507090e01051f0504050303040303031e0204150c11150c15010501050922050c03150102010c0e0d050c12010f050c1626033102100c02130501240f 65
    0x20300c07413884200850a59952150b0390000d50140400314001090580550100d150b005400a40248111a1640d103001303c0c410350180107004080000a000d10b50300c12006100f519204602041e9620011000282080c508401d142c401110001700020120801d20482c0c80c0c1c1d40f04805c1c1201d040d410a00042c0075406050410f600508c0e01c407a150f010650402142c2000c411880740401c0316091080508205034030458801030101305004204006510500c50700569025035901c81c0c0e084440001040720040c4d0290041d5054812061303401d2440d81c0d140c42611011000c94000995250900105000d5500c0244248081030083c0845000e2184185203401d241e82c0c49802001c010491603d054042d400e0302440b410018004820410390241802c403c003400302056181058041e41601d1000307840b0700003800250010341d000c020703038806401031402501052004280c820b030700e54000050021140240d11a201c0d95071080321030103e00200300762620400c460351030090035009136510007034100040140b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 838433102 1250 838431852 838431889
    0x6011404050405070309020108130305030a020c01090b0f010807120210111018021804021302030601201b1503060603130f110a0f23040b031507090e0105 67
    0x94498010048045401400000b030081106081040004005001d09a012400724124802149031014040c03134000540c0c0c2d0681c1c030315107141c0e103200e0001e002e5001007508000d0340d0348078204400020b001c1041107126800c0708000d00c4866140a10062504d4020350203900c0030102c1041e0350015071100d00c50b004103d40f850802c0e10440000540403450210200c010031411880c021801d52118410310500e139010340202c82d0040e01c400e0040c0b41c02d10010080d10000d600a06680120410061540280d5400032050516000c40d40010f180c00c98801c600c070059000c1a041744500040c1d04504559401d01600b013560411950b448450126042d03201c080c0c4800e100b5174020001585000e000103111466a0f409164800d01c441c045c0703002e15141130400309483c4144982140071130000181200f901c00c6583c240c00941c441581459112405103c040440c0c0d042030f01c8003a804041d4130200b00c1c6c05480016001c110b0050303c6d007c42e0050551150342c100c2e46c02002d08100411403940c840c03e941c484400c0d0035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 838434352 1250 838433102 838433117
    0xa09241b26090a080307030917040602100504020a1e0305010c03050603060f040f02040c030f0509190b0a18120f0e0108011418090309040e0a02101d03031603030e0111030601 76
    0x1540d01c0c2107081000184155130001c2000301440d4107820030107049200c1c259403d03080700d810341842010b0246020300c20040c3d004011961502c1c0c000e402468201380080e0a83d00c034591102c1040002c4010300702c0100345c03e0f800303003401c008001c1f00348500320751b198142c5010402401e2070000661500000341101079100d07908408101404400340d11540390f40c0d4020010401d00500031400b501520440c0f03100342900b807510f400504c03007000c08101c0040404042c10620701036507990b035541102e2100039040460b8a070756030080c01c880c0e900e450010101b15014003680904c000061900801d4600711034180e1301000200c140d00f000598007c11807034151a6010316011003403200d000403d24842030030000f0401801e408050000050002c0000d0403207035070a99040c00308290565109641e0f0082500c000c2d00f0070f1b1126242d8226520031080400850303c0c00014078410340125000a03e19000300e4450141d0403009042281095090b114040c03620a0000c001d00400d92001d02201d801c4c04018030a50501400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 838435602 1250 838434352 838434361
    0x1080606280810051608010531090302161d01150e1801050a060306031106372d140403050f0d03060b040b030a09241b26 53
    0x55403111005006003000f21104a5451443e200c0030b40300942c0c0061001410790500d1014912440000781682d50141c80ca07800d045010101c01c105d1602039849035050194000308003c40320040c01407540f401d01070743c000d160903042c003004000b4404071544081c01c9030f2000000392400c0e05084540604444945d140b4981c0d07404103090030340380e01d2071440e10719902a060b0b0701a107142e050a815850b059030020783e0212905500e50b00250206c42c020b000c060b00303d0050883c2c000346868503200504c03a01c200e9000141e030400c0b482c08103900040ca201558484009040304504500c1d0740402000541c12001c0300d110250040391a401d001640340540356810405c0748002c030140c045003c1d081b0f8004641c050110f854802040d07a01c507890340301544130000024280039002600040d25416a000e8480040d2001d03d140c44140c0c20100170041200700b250b010101007050401c01c0103080542c1244c004582011941c0d194000346020680740000f40d0106101064000342400060307503044810926080034440555200d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 838436852 1250 838435602 838435669
    0x110307030c06181e06060506252f0103180803040201030902061c1b0e0315060a030c1e0923151017010909030c06020307110318030601080606 62
    0x302e00320060903130f0030240c680600c0b0300007425803ea521409040c0c20400c050f1100d00b042103d1084d0b403508054681c0200d101d80740010408031000403d4451000c00c01c8c1c0715001013212546d480d88200103130324100b41d8584402a5601802901200c04070b0f840d9402d4000754a5444a400380000742002c0c0c10542d54944400071921600c08070741e0713501c070222240801c9a0b0078010b0a0040d001102d03203003090040360b14110303441030701400303582146541c010003911035aa0f0324000c0e21030f4107400605059014100c4400000854442034420000d04001c41c807100c414003924100022400e000d038441d500591800d440150b59141c0d80c0740701080d4124800180c4201d403130b07003c040c04104943c030f5501940b040340d02c00c002c00c801da0402d00b01c11407a82d0f8a4159049684d0701c0d9000000c8400019000d008100200381100020310564021540b000385401e0004c0b503110003901c001d2464100030114840c0c400141c01c8650285802c0190030700401c01381009152516006c4046024540a884820816424909030040420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 838438102 1250 838436852 838436891
    0x50904110d060e030705011401080a0b0a0f02040f1d16180305160e011d010b030402061303030e0a1712130b0f03010e0112020d030e121606110307030c06 67
    0x20340062081c48003483c034548090300c0340e01910342118998a002c0d40420204514043c040c101c1c1e00040c0a42603d038003039200c0402c00d1100500c0e0945140ea10b40c0c880f43c20305ca00d840608003500444000003002400c1403400c420b2220a52080300002c8070300003c11110b150301d40070000d403000c068901600c0400f200e0f601c0c0c4810032456000103011307026800340c4080c0b06940702c1600c402c13030b910118400c407680d985401103d5a0712520f004052089001d00c0180080401d100045800902c0a8050341c0ba00e250f441442d0590079071904128000b0708003491501d00c51500311205409012045694000159440c54880ea20035000c2110381c201f08012031207040306590b48005800400e02c801c2c81d181d507101d070303001e1034207141c0d10074000d58403581d00140001c0351040c00003082818031f542c06000030b800710703106840960b4009095030700507501c035501100403440a0014081c003100c03040c81412039609142400c1010346000c3d651180f10329590b1003030105401081d4454031885519070000c0000a4440c55070174001502c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 838439352 1250 838438102 838438129
    0x50c0118240201050c0408060c07020109270c110c101701090504030f03050411130b04141015050304080a0e040e1c020c0d0809030106030203011d120405090411 70
    0x440480304116980000708220484a99900810480e030721241034408900503801460400c3d8001c03070025064011501c000d00040d0300505140203a155103807101c00c408061003268000d048024420901c040a05000380740f146140b50500b0b0300c1000d0040151036070b8041041c00240310380c020304103904100f405180300c0784001c0c1d058040c2010700c0d078580c05400040c0c201a01c00f1000209242800d6aa83c3d203c1c4c0b040d9401668810750101404041504100c19442c4802c010201941e940b07046c0c1310b00b07988520030781c071519140090310400d070305d03000803c0026038040354858001c0f41ca440c54600c0c0d610341e10404680d4040da02030002919450050421112032410210303131074101b403a02c0c1c42014503c00014111070803201030303041c0740040b40303007440304903140e9480700211500304544c0040100018203ca014005014018000045c0603589800290a44500c1e281060208070090041160701ca01441152034100c003400d880f519151904000c00d5017104000c10161800d10350100718a0b1641d50500c1540380d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 838440602 1250 838439352 838439369
    0x4051309020409231203150105090f040204090c090902070308010e1339150c05030708030f0f090d20190606150e0d06020f22140904050c0118 62
    0x140a05050041c0c20251134005645078410b20846122a00c000001c0f42d1244400608400d4002120300066130310380c0040e10341591001e00440e5441154855101420040241e840041a0031211400203061020217410152800b40100304403008242c108529604560754144401020754074075002080c20300406200a007040c464000381e050f9076000d201c0b040740349600c1c6901e0300c2060700940e1034948a0b507001e01c1003a051011504d14590190301500264509900800549107011050ba450f4160740d40101da50304550407401040c01104425880e41b9540050010002c05021a401001411140c58107806c07849014540201483d590018408071111014111b10040701c0c0b55180341400c00741c540f81c01b072442041400c6400c0340c4498407903010300c0703560351020b02101c1900a8544680e0060b40c0070703030500804202c0400c504d10b1010105441d07036030208440342c0c40209442c01e20411402c000040007011b4801e00c504424000842d0002c02c80c0051040b090a005d125007801003c036288802590340142e49 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 838441852 1250 838440602 838440623
    0x2d0e0615060d11030a05070c030806090901020408030d060f06050f040909020d06021602120c151806040312030f021810030e01020703320703080c040b07050c010207050604051309020409 81
    0x24800d50300e0010f51700502c1452414010703640d84200484038aa0011400350004408002040381d508061904c0c541240c6140009803400751942c400f5455544280a1201c1e074036903503c4100042c0544001c600c000c0e258901e002440c1401d01480e40300c03e400745000340030380b26546100070b01c11035543c1032202c1141e9910100c02d54035001b041d1401c40c0c4000400100364001c20540c20521000540407442c030214400c01410100c005404001c0c1f820283c0084901d440d43d01e0b0913025010031030f55000040c0c0021480b41c1a040020365180c10300400303503003040d00207401042c01440040c21054243c4a80c03003003200c0c240ca9807415100d8010048025010003080d0140e694070014048085c182d209642c0b410b41704400b034419006074000502c903912106c17070343d511801042c000d00c0860002442000401e81106450080d41c4c02d00351a80c4200007550f20500e02110b140d071007032026082c0d550f01800701c030008000883d50709003403615000c042003c0b000c0510411038201d545034521021551503a00c038001c916046401c0c0d61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 838443102 1250 838441852 838441871
    0x1c0f1e12050403020604110a060c17090a2c070504060e010c02060301180501050901050303070f0f0b0c0711010206090c01050a0210050408071505090a1211012d0e0615060d 75
    0xf5281c080540d8196409080030561f100641040c00c0e640080341c00783ea840b8122440542c81c0c2c0206861210000000d9040c20004000706646030607041001c0d00c81d120507040c0c20842c42c3c844055801c260714020381441c0b1104108403eaa400c00181c03000c440160900c1550b64040000480d0f00c2c036510030000f54400004400490001c00b01d600900308507051035010000740e42c0f13a00c104940c02c907091040690541c010130894001072801201d02507a140b0500c0c0c0c85a20000300c0e0b559074080c00084901ca00a0741001c41e620302400b01c404400100c180081c00649200c3c10101c45054813000c158030894188040010a400440c0c401c10446a1844020200300040e080918001d5103a42c403090042c1c0c0c00700d4049404e4605425113104850003840c8030001024410803d9482604142c003820100d014822490b9440c10056001e01900e28500b0000d1820b03a040f900c4440b01d0f4074004004c0c00004902c81c034203584103030005000500540c200c44604030680d0075030000000503e4a00c500041c11020714249110382 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 838444352 1250 838443102 838443107
    0x13060302130b0301051507171809011d0402090903160c0e0606160b0709030209180d05091806040b12070302010e0409020f13020f0c1c0f1e12050403 65
    0x104050030307200c055084810b5480d0800c1c00280003c2c024550301c003003003690121140300b48200400e030043c4a511541e42c0c03040d001c5c940c05250b0300802c0000f4200c282200120031146000708103c0c1c05810700b50811300c0003142c0b804601c1410790300140000c3c05001c00c0c1c00820302485082003500c9a64000c00c010f03841c1c5403002d20701942840014854003040544000218119241c034000b80c0f402010f642d84c01c4000403805482d041c41c1c115010b42840e00b441401e00e400704c00b5840d44c81100344036a0070020710130b00d8050248010b038640312032903220804001e03003400b45078039654072034903602e244015080d030f421040c0d112000054001c145072410160f02007a03211003040f0000021882d542201d000f6241c0000d551111403e0006075030b42001c000b5406094010103da480c6442c2000401c8030b420700c0001800d1241c1010075007201d40c0500c280c42c01030b61100481c01d00c003040c48107103141902000e240c010052400f800014110a48100e22400310b40c145110204000744180e500c0307890750300c0040007407281b4201403c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 838445602 1250 838444352 838444357
    0x1305031615061a18060403120c050609010b01050a031a27070810122604030501050c0a2309030610050108151302130e01030803160e180c13060302 64
    0x100c05070301e003070040028800c5801c03d00c01401c205a010201c4c80d0600c00c1424140740e8210b103180355400031040c0000304c003042440708081828141a216608159510300b001440d140000f00744124aa040c120b60860b0707641c0c8141a15603114030350070b010030b1124000d1495604050b81000c00c1307400c4002507064900000122901c1000e10303199010b15a0541c580103401c489030340f400c80c0c00d500b1017094904200702d20751400d4042e07880580144040d008a00320014003000f032036000030182106807400b040a01c1400f00030b102d8660850100f42c00e0b1841e045410310041c0028030115511864501c0610030400c92009040031244580e0008095607041d10b0401c5400032200e000d40a40d600041c040c2002445c4c080380840e0401904c400202401c612541b404842d00c0030754080100d0280c0c01301c2040d00000d5a0b10355102943c080c511990302c1c29124507013421900140c1c14485842800c015136016000310544407003941e04090502003000f204548d03680340c003070381807803280c840c100810040f00100000c0195050f0301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 838446852 1250 838445602 838445633
    0x5031e01020c150f16020613080904060b21040b0c070311030703050d060605120f07030e0a060e06060a0e010306200c060702120403030504050d03020c0607030504090b1813050316 78
    0x402c92515103644d85170f400207a6114003a000580c3c01000032901c030210000b6803001a52040c440c4904d088081d00c0428251100b90703001120001c170204a9154208180401d542180440c11200c4110701c0c05840788070344c84c0300c007034680c43c81c115001981030b050601c1490307500019451041100d41c0d50340a480c005040f0351180507102185403034041c1c0490214440c00031640c10101000510360302c0e8032008490802a01e01070b0a6609240d61064400b019400600100300018014407001a0040f0704400c15401c0c44402070903544200042d070030a0055484540351103040d640c200000155414a408640320300703021030204000c1004001c6144100f45000040940c4500000e84c00d413456680200041e41040c0100d000090220f20188070034072080c10600303801410381d4041d104072080c00248001081040d88000d8090300051400513042c0011030b40d40c040e0032581c0784299600b074100354440c40b401e031020384040c000c920381091401080c010701c40204140c40c003010069540b100320442600c0c202c0e100034003c02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 838448102 1250 838446852 838446871
    0xa0305071b03030512180a0c170706020706050d141603201b0c0406080d0306051c030e1306180b030304030b0103022806030605030f0705031e01020c15 66
    0x303841980d54420301c0e510001c403681500c80c3e60a00880020303851803a40020040c0035003c3c40c050741504101b1040140c0405207015040c0d0304100b506050502041c81130340e0003400c1080c0c0c002c04040105e65030019140b022150149440e40c1c03200051302c801405840d0416038560952441c8003804151144642c03040203003e141d403010801c4640d42c00300b4284656807070410800c0c240c0f042c007401070f10200502c5000100741030725040d101c29140840006044a15a400c08041c035442001401d10840c4c040c806c4c400600401c0312a0000c02246c102e107004a0790341104000d080009442c5011a940c68403d1111040d02c80b000060002030f494501c008442c000b03d503c0941240d041070703c221b83c00c3c24007008880980740c10104034070b03c581c01c41d000e02240c260704251006031844117a10301c111206011120f40050501d80d40c0c00310b082494041010300e0301500031710200341c1e9084240d0070400c60f40c0020309050f49a203034001d101c1041c2100c450b81ca009004800242031180225800e0301e114a1684419610603503d84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 838449352 1250 838448102 838448123
    0x1e040b0d150506091009050d0803180a0206040303030b120f010e0712150c1110050411061206090601020f01060306200f120c090d05060403020d020c0105091509030a030507 75
    0x28650381000c1c4028420960060402c000752078080c00c080716101410341031400c0c4400007a544401154400300045401d40c0d4020012061180c40da03100810011882100300c010400c0380025000200c044c4201c1c48014103055440980340c5480d214400030a900701d0030001514440030040c401d1b180a058400d540285d01e0043d2180814410207400d83d00240b640c00a07450b1100c08000d00000c001880044004400d004400c080e1030000d140030000d2021284030070340045164102445c2c004001c43c50240c45912504081c1315180c4c81e03502207e802030380240308607120b110580b64140140d0a11314007026110140d400e101340030080c0060b94120b0300c0362440b803210703d40c8820300315010a2190b018450409001140c100811030005500341413054004055030078882c078046040700082d04d48126900e049030301c6d402c2001000141901400220b0b00c218440c00901220300315240020320b6449001e00140c07051030484000d010b010500801d490008a015040b03071100070407428003400642008400b1542032082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 838450602 1250 838449352 838449371
    0xc250b0f0912130306020a03140907061205070806010e1c05030309070b090102070e07200c1305060d02120708010e0f37150609020c07080d080c1e040b0d 67
    0x2c103040741e140090071441a2886415907541c11301030360025000380d04254550041e48502021151518020f19201b8001c01059203000c00280c80bc141101034400014604800c02c111140c11200c169030158092a05180750403030b410000f08914041c07020240914030ba1a114070801c100000214000c81108044483d4180c0c0d40680d040584a10003840d40180c02150f8100a0300c4112003020380c00440d0340c00e00300510504086180700003846601c0b4268140d0007140d0580560511071564518002c440109118600d42880800c122000c824002800b507000d00000410003c0c1c18401440507200410003400445100724495a54000c4214480700d00d000301d81071020840d9145944491109041055071015110002c8480c89109035407401c0d507495140c1e9446001480003440303040e025004150740181c481c0780c2e52034000c0c0741c14181c3d001004103920002d400e62409400200c0540d2001c103415405a880020b4070002d00102c058031000c2604200205000c034507076151002800c002c2c1c0200208100c2c0460 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 838451852 1250 838450602 838450633
    0x15030e190b09160323120909100302060a11030c06010f050306160f0309030e090403020318041a061b0a05060a05070831020a030f060b090c250b0f09 65
    0x314400d4000300c111030210f0800004000100443d05844000f0081d0980f6041c414035a00303009124001c40e041c07a0340017030004034916000c20100c1d0442c0c0c0e0b84c806810501d0075540401c086101d040149000c0c4008440c24180d00c42c8108116003400c42d0b0641610b10a507500e4541000c0312400d401054460f01801000540300e100c035000d0039142400703940c0d07000002c045401d8207030002c003008bc40c00d030f0801c0390382021100c00d501c41c1040e0601541c4258015607a8440850021140315280c1e80780610550400c0e07400d42d125104042007040c0b80204135407032580c850800035003814018482e41c0d42002402119a8001400004a0b10610403000b50700c0900c440d81e143d00085851a508640f5081c030701d16000010362284841040234141041261159003202140d500014084204d40c0d10031249150000701392010000310303000f44103200100362411003403801d004038141c60f50302071032259400c65032110040c003188864141902c82010f1300a0100b542030f0408060300700010700200c0780c5a26522884100000500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 838453102 1250 838451852 838451863
    0xc2803080703390807050a02060604020307091701050a0f020a0818100609020304061802060d09150f05101703120a0209032b08010b0415030e190b09 65
    0x6525035900d6a4a5a070351400360020b01440c00041e1001040e6440e004114a408103040d0080b201602c01c42c0003030750b20020003800c15200410300b0007041414066000c1464000842d55080801158056120b65500e0710881d1091219401006d051000750b034000c8843c2c006600460040c0e2100c01d0601c805801000ea050a912540030741e800007e02c26400190090300e100c4020003d14000f500f80d54490041943c1c03c02558000d800080354907500009000c100845803241d0020f45041044070003544005400245c000d0041400b0700c210203460f10842000c10003104096040d00000240801492a503201214010074044a19a1410740d001801040021071068183c0f5001c000200662030107050705d01768090030b200074040d01603480c2c092014442d41d40d028480c0c01c1c001400450030300054204030355041ca1088000d60160203001092006128428680084030150788443c040252404e20140c0c04600404010810804a005404183d0b034102c91040403540a240210070b1400d00e03032200340001d41c464 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 838454352 1250 838453102 838453183
    0x90b041a0f0c310503060a0608120d110a0509010e030105010b04150306030210180902040e010b070f060915110309030a0f0212040e0a110c0a021909020c 67
    0x10a8200000d101c100070031000b8650030030b200203c00009034040c100c00c8451007500c0030501c40d005215905100900702000941d5004c50030000512406280c8000b241d00c03561410910b81d1303256000074030701c0044d02c0160400c881c001100c051050340c4945030380000b0000c1d00b0240d80359000680749070520340c1c00d10781405110305a8007020b41d054501490020900a803651144040061649409000001d40ea50404100c0301001a890359503161003e4100f000c40807403c0c0d080000c0d5148144402d002000b140d8040311705440c2d00f030320a165500c105040206030040c02071801041c0c9800c0c0844c85040090001c4603004501500030705201d81600e10014480c02d000407245040c2e250b2040c004c01c0c202c54800d0403050041d0101d40103581c0b8003007400400071819801508946407030030292081c020307822003510030b140d12180b40e00791107824201c504a10a8640003403440103071140c01081506160300011000f00d000602c4100c504564414002401c251240c806008681c0d20a02038100002081005a60700402e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 838455602 1250 838454352 838454371
    0xd0b0609031b0409020316050102010c0807020616140a0c050708030a02250e040b100501080103050a030825020a020f03070506250f060e0105010605040b07060e03070501090b041a 78
    0x4080040191034810303184a0031a03902076141c4c402d4101613103091180e1450f40d02c080442d032030170303900700800a42925400c843d1803003000001400c1181d000e40c08a440380c0c02440c150348608034148507540403140c40c41040c0c1c2c08820b04000080b200c412a4100c07d00c0ca203440e1040051307601059a600d900703500c074062401d050001d0303041160001e0840d850300c0310500001d500600c000c0241c60301d800d29030b060b00a04660407240c2d05d107400c0c00d10000c024203110181c0109401d2074134040d03940c1180d803001e4560102000080510060300040b55241d2800c2c081c804c500b1801000d8202e0258003044002d542c2c0c155a6070680c007a03180c0342e50303110850602089040c25141c000c0e0030700c4d1a05a8100c002c001c6000210b000003481d200c0c52030710100240f5142400000c0501401c000724140b007031f9420140c01c440043c2e1141041c031208100800c000700c00201550400c9802150000b81c1009054070079041d07110360300000b0115481e1195600030002e5000610303009602815182031895210842d560304a94281c0d5100030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 838456852 1250 838455602 838455613
    0x902181905070918060306060803041809020f060a0c02091303080a020415050c011e021908090c040f060e07030213060302032403010f051006120203040807020d03050c03030103080d0b060903 83
    0x25004500782c0513007000c0703800d039001540301e560343c60702c504445503500400d0380341e0400102080b0b41009508a0005510411420444500e1030303800100c4164440d05018010480484e82001050044005001180e00504a62120324188001c680d0311352000c40c044000c6003c0d040841d80310507c038800d41703068440d40c010414140303101c0302c0c00b030b15075800c19854140190f48800c890341c10030511945800c1c4a1450040c05030704c480c1d082d8180c150451000030303004201310001c020401e54020000d0210507007081600e00080344c0703024440138070241c84184c00400d064070f00c00c2c044c044002e6141c3c1c01858000002200c0906aa031100d00403020392000b52444103a17045803000804c01e0f050280014501118003c0000805c0380b40c00654405541c3c040341d8121080660f0a0100201038010071082c1c00d10344144001c5103075140540d201c02007030281100190091600b44d0005003058011422142c1c402c03079001c201c0340c81c3d41e581c0c90003120030752001410100c100e0a080760cc07080c5003811070a503448030b0342c010007401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 838458102 1250 838456852 838456859
    0x151b03010807063c12050601080a021815120106020712030302130e1501080723070f1502090f060309030304030f03060b0a0905090c160807030309021819050709 70
    0x111381c00755100307000140781c03019498080314010003020014200650000441d400783c4208002d0f200300040c5101c511510f00b0802040300582c3d01c6564144d0042c02ca00d0010389550302d0044481001c1c0c113091001390481c00c000080701c070b0302007808060409642d69101d418000c0e070f01e0745012038850300c581c412001d11326420101d410019010b60003034a2110f11902003c0c210320f80d01c0b03003404030021098507207407500c102d583c40e14440e035640700e0700d026408250707420600e81403030050320b00d03c10b0103a4440512110030004640107081101918504184980090b0031308103803001c40203913900035800110a00d01c648203021601d07030a0f081c158141c91140885502660850fa6151420364000e05500d02103410107a980101164540000c0058080b0b0f40044d900c502d58903040c102841214a0054005280104284908040790b00402d00d0072080960285502e5101c1e202443c0544c06080300c418000c2d40001400300302d55104407002e502d1480b4074001d02d80402e0100f401442141280d1050f144078000901b205002d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 838459352 1250 838458102 838458107
    0x60a24083c0129030616050909010b070303200a050702061603120b01031109040509010905030313030201050a02070c0b0a091206050f130b131505010e18030a05040501031a03151b0301080706 83
    0x30f86c9615045e0801a00d04241031000540d40c07102604a0401c0c000c0c0884c4030380c1030651510540310100c05a0740021126080701100c06040d0041d01042c1d010084001003a80c07c41d20388a050f0b50008a1000782d88000306224540036041144080030015003926111003807819600c20301400c00a0500d501c00546000060000d000190100030120b1000c0e64946002000103481000114440d501640c40a1288401441c0007425507030050b20340001e8034018012000402d2006044804468071070385145d40c1d074012030401380e69030a041c3c0c0c8055054032075110355400344160b23a008103110706290050030340c0550302c0ba100b4103031495152f03601819085074400000c0c03202003219540c0c1c00c0e150150a10b070044000310001103041d64800d8004c2c0034402082000e10a41c4024581c01444c0304200802440c140f4128080003051805a48a09410181c0b2014000b070080b56503032250f100c01c4009000e07036210b40c06100c20850501d50944000200d00b072140401110f5409600550741a0b4100306c005c3c0c849a0b00d0440304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 838460602 1250 838459352 838459381
    0x61d0105032d04230105010b0d150b0703020109020a08150a02030903090415090b01050f0d1109030f07051011060a090303020903060a24083c01290306 66
    0x780c0c5042c04001a80460841c08440e414032032071003444c0140388000d8101e40c024181580d4001a0440c0e810200103104101d021010703240f50034460707840003a00d00034a560000d2071380301991285d0743d5220001550004d055040d00a108042d009503820955250340302c82003070361003100c500c0c1641c402c0d0105010640d030354490b0b0000c60300401440104c0b410459404002003c6407620003a05031401c412080c00c0240909900800d00d22000034209581800041c3c18540d0003442025246150140d85000c00a150340c80c820940e42c1641c8042d044890755203d206102c0c0c0d90710241d0190364424036282c030a2002a9100344104c0c12015a00ea000c0c007a15140c940c120b00c00780160700021401d050b001d00c44903101d03440c10460130f403007442d40041c00300d03204001410340700d6034080c0e002642e803070109404000e11843c1c6000920118140901100742c4086007125030014440820402d406250599080e40c1256404150441513005c2800b0b80e507540c0001d21041e280c44003100368a0b0454160300310100046404210888 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 838461852 1250 838460602 838460641
    0x3020c030111090306060a03030206040303022b0e1507050a0c1502030c0406110c06180a090f060e0105040c17040f02182203020c120124061d010503 65
    0x1222150002240001d0940390014004282808007081d4032030586020041c1c946c00400c10f9604030b4a1900b180c90080d12968020000f400341031300002c100e86545207400d440030769024401d20107000704110b401090080c0c65822007000c1d0341d00c01e6180d43e011018410042030301039080f9888041c508810000c0c281c0c0c482c0700f003000507a688400c200d180c82e200341c1c0d240000c0d84180c440c0000941d03035605104001c0d099007013002c2540e1003075014000b8100b80e17888a00c04c0741c13502c014002080b40003141e424009060740d103050708441c0c0704908005028031808a65007000c8169509a958501d0700d03a00d59051004880192541c0d10000d40d020780c1c411142d0f40c1c124210b641241c0200b040c10071742c00d05600440d06075200300448407170200c0c070001003001600386080b6110500d110120300758502e01d00364400030759810442d18164801d1a030300c520701195041c25031250760700d044c2d46031502c12007411003058420a03081d42d00c541e602090303003500308a00d15420919401c1207410305031182411511601e11010103104c5026 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 838463102 1250 838461852 838461857
    0x609170106051908070b0403020a181803020d02010b0f090a0b011107060801030303050601050313030e06070209160f090b16060b04090f1e230109140a03091a1603 71
    0x840210b02c6854040114a9864181108101d698940f440c01407506405a0041ca4060340901c024401a640c603050b85048501c49aa011030140c40303814004001d200c4a80411080d070f010450b00710030540c022818400d80e1600360000c0101090b10400d00855590000343d481c1c0c450a080c000441240303c96005108840041c50a11440c01448110303e10700211500b010000c40c1120700100105a0305010f11b96120742c0070710f0254214100000a010321001c00d0800a05110742200030001c01d4031100c0540348155001014501c05007001e0070007003008000d40c4400400201c160400340c071309502959140c0100d83c090350030035240041142e01c00c4150a0f0302c9200b1500c0545800c0780d0492552039010381441c0c0e42c00303681071700b00c2c51a0ba86000755a0722003a46101811200c0141e04202080c03003841d0440c0526044080c480d03d003407403002c0c154010700301004010641c40d8130f030200c20700a03175000455614082c425181c0da21580d0b00d82403040301c0f00000949601399294100542101f139441010034400b020b110b030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 838464352 1250 838463102 838463111
    0x606040b0304060e19050102121003020f0d020f040609020705060a0c08011202010c08040608070e0a06021203040807020d0b0a0b04050105090705070302010917072006030619050405010b0319050106091701 89
    0x12072100020a4840001b600e1580d00483c003c0320b454060ba04164201d4454022000507601d140d01250718101605101c40c8180288802041952580303011103141020003881000b1594071000d40800940003c5000d84580c860440090585000b510420411490944448185a182ca070084c84000d030901022070410101c600d500002482400c064806080d66845076525480c00b00f80081007241c441815078459088584100039254002c07a0903521102c0c4020b000d680c903a503e04207940e4500c80c41038000c0d00b1804100200f42401102123040c3d01489000005000c0401d9410400007030340c0b03007800b401e54040001c0c80840ca10341d0140300241205442030001080314002621425950094010012450f2500081e041c04200b454003d030100c0140032818500c07a40b40803004180f5038080100054007a40c51074a240400b00800650403000b440010f006004035a10f500c0640610781007030b51200300407000100304040d01003c6004850507600d0035940e08010a00c3c01c0f0484060304114400d08400b95aa07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 838465602 1250 838464352 838464373
    0x304240203090904030801030203010e0718022206090f09050408030c07020f030109140f0a0b060402030c07060501120209160c020118240807020d090b0a09080d030902090606040b0304060e 82
    0x100c1a803d440349000352641d1990b50b00d07500625080d5046603013060384c250400b20050140850001c003e09009c9001d02d00141c607400013541800460768a103110350400c4200a4000a07244d2340a045c0c20183c5000651009a20340d0b80c180c4070064407010344008040d1001031001403020b1100001074030b56180020301d1090107001c0940801d00716800c495040e40e050385441e1119451120410030f8804540e240c4008250008460700d8083d94408050a076611a980000110310302080302002e0390300d8540c111130100442c0d65030f8050380c2042c030380f01403049003d01c50040c006804103c65110b000b40040d001e841c0c0034921095139004485178812041b42005102428038080b030030b02c840e00f040c10400305904085120342c10341c00d20040c0c03a23000700520b10411980103113451100168801055001c68140443d6a9103483c14404256001c19054100b0702c4a031044c40004120164990800b800f124001d50350001d09440765018020544210f008000c03e0450030404140000c1c210b900003801d55201c1c40c00d403041c0110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 838466852 1250 838465602 838465609
    0x40c15030f1d0f0313030f020d140609240a050408040b04180e1612032d0e10170c0408191208040312051b0c0f0708030424020309 57
    0x1c0030301180c0c680d03031100030b484800d450100024050386080300011410a20740d880c8002803041540401002025440c1c010070071510307030105032441c0356841a4807020030031907180c182c0d03500c41041300c2c14000d500ca403900c043c5801520148010058240ca9901d0788a40c0d20000040090940640112403c00c010000006d40c20207030406000030b049070920810016034024820020360f0740c800302e0080e1325004110701c0500108404080c00454903030502081e19540e4900b400d0307500c10361480d180a880c03801100c0d048101e8040b0808210320424a44401c0c1d140241d8000340135003040e40d0600d0b040402d42040500307a0380128400b04543c1300c0381c202412890142c65082d40c0381405401089035206252685000b0204807e40e00d002e860f58010345815551880c1a071001042a005010050303012a650030200d22550240311515a144a10001865a40790300c054035540e913284107210040f10380510366000c200904040115811141c2504036a001e100f85485001a20807500388400b041d4031082104821988 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 838468102 1250 838466852 838466861
    0x81305010e010207060f180201080408090406030309170a08031909080a020d090b03040c030f0204090501060b130e160f12111b060403082208040f0f0806040c15030f 72
    0x401c0080056110300241ca03008090718902001c4860107814500c2c89000e41d0390710030314102001c0e0246000300460311241061070041c031a44110f180c0017800c0010120600d82c00031444401c80740134459841842203c81c0850351124560803004100800801c0402c20003041c184603103000e0040c20200140a441540c2c61002951081000d18056003068103140b2285400c20724100007812030090301465850a9036a2307010b6428940401003401c00c0e4149210107540362030780101c010303d03888002003169a0b00c80c07030581c227640c100402e9400d4200100402142c000e00b81da9000380a0183c0001c00c0c6544840c008050b40c221005601d00c004001c2c6036000382001361010300524804001c04118140d41d00d01030108201c41104240f00201c09a01500502c0300081c0d01203a51948480d80801040300c502e81743c80d800c556112648070260130020701040102d542225156140c0403100340c0444800801d5132405910346a4008540250201141e902d08000e4405507150b01c901001c0c1501c0c0005a40030034003003040840d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 838469352 1250 838468102 838468121
    0x1030504200a0503060406150f08071203050922320402060c0d09180207050303040b101a0904050603071802030a1407030e100b220207140a0c1a070308130501 69
    0x6584920302603208c6000b803903409001d00f0050880c94041814185202c0e0f032110144034102600307401c0344003002458480c0040d81c100c2c21000780900ca46041031540341d11040b1002a541c580189440070034688030903031010580451064200340b812007034440c49004c60070b45005000740d801220801c101172281405210704018482d1640303503400c21a040c00c010501960f8481011028288104280c0011031000401d9980c4503602086102d015654040c02d44058015644020741c0d6031001004180b00004100141c03210480944040089955140c10176580700170520400c2c00c40050f104489000f808203800542c1d0041c0c2084010500390320b28249882444000c4487c1000265030f118080c42040c814807001c43d40d07a0415030140203440c0c9290029000c0710034486100c5c4240703469080341e42c400700b968050700c0400c0c1e0051a007600183d041849a912080201c6040340c22500c0c4000101c0c001020780c80105040c0a9100d801303080c40915641995600400350950b100e405401c04420b000402c24000e46148 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 838470602 1250 838469352 838469363
    0x3030c01150f06090b1b010603050607021b040204051c0302010e060403050703020607090b03131e0c1701020c0a0b090c1020010506030d0810120b0601080601030504200a05030604 78
    0x161842c00d02d0405954100d50072000802c035030035404000c04580344098601a02a00302c1d0025003406511509005103540c0c0c0c0010070038040c0c5401c104c5002d4020a40c20900300d001142e2100c0a0240c0d01040124400e500809a020301aa02d8172000580c4840105111522a000020340410701325641454610204c40440c0050030014a100408d82d045c0112034008c0d107142042d242032070030502000c4290000409007418030780600303942c00c02c4c0007410a5000c020300d07203c05e54a504ca559400c005420812501444040801c10840780e04500014401c80d4a0391010720050b2074004540d03030b03035aa00100007500030200c5209410a0403c1c0b075a0320040349407580c4140d01c800c1718003403c94150124000307480c20310154991500c0100070050720040781c0c01d2141101d0745002803640d5180103c03650000e10301d8003c01000d800060bd0f260070132003002d0b420780c00782ea000d80340d4101c25a0780c03100440550301c04440c000e009111062043c1500308000c252240b582000810b0128880d459802007450b00c1402c8400390340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 838471852 1250 838470602 838470641
    0xf0f1d06070e1203193f110417010605120a030c080415030c03050a2a17010303031a100e0904080405100c02040605010c1a07020a08041401020c01081902070203030c01 73
    0x12076600b19020200d0116101c50f00b000c8001c0007105041007101c0c1d0104082881b001e09070b802c0c51080540d001d114100c0340082c803240c80d0307601c44071444282d03504001e80345500d40c81c240c00420145440012011814191402440b141c0c2c00e9650482d4144048041150a90028840801c00c4251542443d85580325950000741c0034400324401005c0d44e01c003401203004640341c0150803d20ba402400c800301000c0c0004065400158510011110880020388944600c101c180c00030040552680001c10303299a40860803411a81c0b40080146180c042c1e40e02c0b002141000e503a801003130500031600b590040c0507020007803c0c0703590381c00030656a403842003684c40041c000a04000451900c0d00c01c010140a0070310b0406102c0003584d551810206030000324040d4150740000041400d03100304004690254012130b01074403141d1f100c50004607440312201340b50142c025011001401c0d4452540c0303d1007030b50030140b111102049411340200943c403000b07090340c15000407c1140c444507000d010b2a103042600c009600c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 838473102 1250 838471852 838471897
    0xa09020f07031205060a030204020906130b1e120103030c060b0a0902281b1b0603020337020a170408120a02090604140d060f0f1d06070e1203 62
    0xf4242482180030b400e032507103402c0a00941346c0301c40d2001d8040c1c0390305440040e5074441100015030640038414403110418481c441c04643c0070341400203400c00104801c140d000072000509402c1c0c0b2801404a0020445890340042021034420702001020901403040050051001c0c8081483d1000c113030040031075107070006150b5801c0580000325036840c000080303148100955000d0020600e0604041429080c0100c03040d00c4248008002441c60003e4070700c0809038400d07583c1c4405000b80d002150000000011280c230b80c41d06500800508034015500440c800700742c60b086900000a402910500c803c02442c50080e04154103000000c0740594010840d01d5125403403940e0045060b1402407203120480d00510009407184c0b40c240984059070414000741000080f1070000c1820108019000780250382005040000804182e0048184501c490001c0c040581040701e6403d82600c0c00c44400341640c440e200113401c0794425500b00e1803281c001411100d040c3d150b010139501d160003500d00c51040e81d05448042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 838474352 1250 838473102 838473107
    0x9060e1b0102010204051c0c0e0a05101403070527010b070b0606070b0a05060607020d21021501150c050a0312060509010e0f04050c0d06093005090a09020f0703 70
    0x141401030248000d600e094203107808035080481112030404201000c11b243d0040150a001c0b400c00350802501d80c0d0400d1a024031030b00068030301074a43e080c10280701c0102151005801032290756010000d002085d06c9403800060218104000c80030442003070104c050cc00c103204445003854000c000120815481d040350781405808040050203da10510040098100207145009c51940c0911003040024080d619040030840c24840e00c1002580b00210313103406d00801c46c00c1b4103124620039030007a03515030b03454051005980d150ba2055192000700301501c010005207001081c0d00f000054a0324000902c00585daa0b401e140147e190401c84c00b0521000001d400e01855124240003854121400d859551406210a0090002502200c22a030a003c0020240001044100e4010360b018000340144040313400c0c03100040008442c111046950100d90090012901c1400600001c1e0308407403282e100c0c1001c2041d59690b1150101c280c20002901c1d00150078003aa01c090140800c3c0386d00040d60f02c00051900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 838475602 1250 838474352 838474393
    0x71805120f1e1b040f0617060a0501060e0d0614071d01030c09060807090e0109061802090a061107050402070320070e0a0209060c0303010305010221040218070309060e 73
    0x1855000300000903451404038005422501c880c603c941c82005200d03001c020401401e10709032202002402d110300040c0281c200322014902e210800c2c156403131500c0d41c60085003900d600380315080c0001c800810f50b02035480c001110040c110701c20303400000c0f4020000e400d03030b6505400f241d503500454904103115000c901c3c01d09007910300034030902e810000d10b5030f0044080c18140050056808002440c8000348170103000d0100c0c08050324650041c5081503a5544034200034192034050903018050190589507034030800d000381d8002c92802012004000e050003001c88824001404101c81881003920000d610748941c4000c25001d8003a07511150546c1901c9130708001401d003045840c559511042c0100a1400840d4200d81c2018074010056078510781c0200142d500d020786005040c5a000006c000020050154000d00910011450321201985280d201c2c2e104541e040794081c2d003040204080d120422003086402c0c1c3d10800c81d00300018240d14030b4440800b180c4414401400a50000101d10f804042110b030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 838476852 1250 838475602 838475623
    0x60305070f080408031602010f1122050a090203040c0905090307060e03070201090b0a050702120a0218130201050306210a030e03010c02030d0e0f0f0c040f090209071805120f 76
    0x800102030f0070142c0d43c41c2d40350700c00104034001c0c0c00034046102c02d00e1072003904498606c449144081c0480c45000b00500c48071340c4403102c881c2c49000b410841a03050129130f406801110001080551041e160800c040040e52005004948110500c0000300340c1400ca1720416000b10002c900441d25001545007242c11280e80d610721100c00e50043c001d0400503a40301c140442900e400240c520b8a51010000a0340c2c50f00074410002c1d88440036544c0390a1800e000268800320900844400c40f03041107019950b2086c00381901d00c0301c80140041915009540180011500408044d000b04402c00262010300064040b28040e1402a0040d1100100745a800034000c050040202e00070010b07280b6901c0065540d00c9409514240c941c0c03034030a80b52840f0f5040c40b188640801c224140c6100d403000c2004140c071040790580342c600c0785281020071000c03025940310b58070940381c2c0507100f200961680300e81540e100a07007200034601c400030b103980490305403110b542d82c4040349880b80c01858194009010542070442481 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 838478102 1250 838476852 838476857
    0x30111030105060d091e05100b060c0a3201020a0806030606101d0405011d0705040b0403031b060e0309010305060f0d080a12050c0c0c121b0613060305070f 68
    0x40c4030558411080f5200205590000035121100c0c0c81d04101048046c4a6283d205003141683d07824014085825064030541c2030040081a0030300701041118081c048210040c1d0b0310031840980014180a21009880c003c0e22485040701004280c45009032030342c941c070042a0b500400c40140031034120705d0160708031000b1006040b141c0344c40c8002c992300420b0300921800b080307940042440c5040104804490020000c0c10130300143d80c441e88101c1000415280b141046844000010270a510500a03907080d0340c29050000e1500c5c1c6140c8080321011000c520484a0041c0c0940c4280042d10522964422400141c0910385030f2540300009011200c1c014900c82c00742828207a0368959550301d41c044403180e50303c5074405844402907181220004039401c0c3c044a9107161400744100507403c0d10107080d4440b8003008861140a108051010002e0ac80952000c00e034084180da41d4403800b640704046c2c0c8041c014210905091402e18400b503610480e600003c040303503850040c008a03541c064500d094070701660 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 838479352 1250 838478102 838478107
    0x161703090312096301030203071a1206011b0606080c0409110108091501061d01050c0d080a09050102041503060e0906070807120e0f070f0b03040f02010c0803100302030111 75
    0x2d4581850704014855220860042d45509905641e40000100c3d4204019140d010040d200c061082026134403c1c003040e4401d01c2041c100281180c011600d40c01d003031400c1c1c1e9081e410f141804c04801000b443c094003040c184420300061020740324910b0100c038030041c000c1d032000c2041454400c07002d080c1001280124051420303c42c9a0010607000070341e02c4040402071908100542d200038103641044a0f200d002c10440000e04000101603901c124501206030001079400e01124030700006603510303c20000d0300e000507000260881c1e140c0d130142c08850ba01c440c2d1140049000320480d80d45608a07403180d02714003c0c4410100d20401000d40c50b1160314041d21640d07445508504044081955503500200614200440c803400900d00b0341c8a00300d03000e25404044c10034001c070090104c680b611400c0781c24400000e44214540090042142107020b800c44007400345c00c503d1601d072500c84079103c44c041032041c1d0600c051909000001703400302e4000c40c031036240c040b03803409407904601c1058255030885034802c4418030107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 838480602 1250 838479352 838479409
    0x5010906050303040e150d11010921030f051e03090616020a0f061d0c0108090c0a050d050a0c0f0906080d05030c0309070f090c0e0316170309031209 65
    0x1046609036404940b6170002c3d03a03110a1210401c038644600f042e007204100004104000000d40d90701d20703070082600c1c0c10035203036103607140c500001c00d03004000d07071094084511034004240150b03a40c204503030041c505540b40a04010040607016962041c03e25410800010040200028828035401181c2030710000d010b451440d07002075490000220252480311122680c40420003580d1284a08103902241c004a20941403141500c842c4c120340c40d5030101c1d80f0507002921018000c103001d202c2000080c09000281e05003002d00c50100900c140454039880740750228404940c1c21480c10740205206902181018108035003081500c079039900078402540f10b208142e241a03004000d895110904da40c0b400d8403035840600c20340c500300c010751003807840e40e010080c04900e00d951a00f1849007103505803580c002030f41000c81819500c0080f071601c0029100102002d0244420b0b68240c41210604101140d080103242000681000c081c100001c407000800a41c0e00c00c541000440d20141240c4401d406210501d0f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 838481852 1250 838480602 838480609
    0x70204050c030403081b090301140108010b040e0645150910091a040b07090e0c040b070c080106060203040f0b1804150806042306040f02010804030c0b13060501090605 73
    0xc040c0480070b0140c46c3e0b444501d401c04901d4165100300784010300070300c10509111a0b80250171000c0c0100c2005508004183d1014101405041c1d00b400c88403000b0846503940090300202d5810780b031a00f50f2000d52050050002c40501e158038241d203c6d905440c80d085079141201c6919041c130b40c20401d1a83c1c8005000c00103020400301d09420510141e032404168074007145080d011f4440c6e10900c90500407040c2d8144030074000548401d81c03080d403d546584c9411500c508034011000c808551441c808401004140503802511024000d160710800c0800c2d131803500d40c040142519015081040164400b04040012140d41ca880200510b04186030750700c5c040701440c00725044210780340d0541c001c45d11500c0e040e40c1c096089070128024414001a2030031400e06250003009400e180d142401190300c4a80c04010100c00818005c2c0a46d40c0b00c03550b410150704583c010f5921410081064040c4492070481d080401d12a89010303208003801251030240c102c407490b040c8110b6406030448111903241030020300060b00d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 838483102 1250 838481852 838481867
    0x7020f190c0905040c051e150f0f04060f201b031c02030403110901060f031a1011150108030a0309140d0203300c1e0f070204050c030403 60
    0x2024120500c0440d88141011002107101d82c2c4212040362a060400c8240880300a05030141d440403901906844911203895810000c240b44460f444404030152542119481c0700a1000b451207403009401c10191004403910758015501c00c3c00812408012000ca840d4091a10000c1c0b100e80814500401c2400544a03a6071480414070f0403c8911040c80e60119501004210401c0003821103404c4a024200d20081d01c079041071108a0303245003d54902e14240c03501c2002d5905841d81503444002100320450b0440107044451407940b601100303000c941000d80c83e06c6c0d6484450b00300d84d4546554141d548906e007490b10f516500d030750003c4680c080c01400800d501004488603132160346408a40e564803800d00702c10445108480c003585100304010800302d9038001c400307041d60154006003000415070740108012071a8814604100c651070813400143c50b0b009500182c840b242c945612140c0c40c00f8140912005a4460488640d54800205105c8110329143c02445d600120130255141541403030754000d80020f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 838484352 1250 838483102 838483123
    0x1107020105070501090206032e08150c07050d030603110906101d100917190303020c030909070e0406120f06240603090c080a020d06051003060905010204050907020f 72
    0x1110002d01c85051181c02d42001c460f080c0c0081601d543d0342040208034400b8140b0440810108002c500280100a840d0403010708589000002d450101300c95528440c50318002440110000810f000c9240400c1d000c000002454100b501c00051503400d6081100304854545442c502c17881e090010031040740c60380c00401d03000d809503003080b4a00b503d000c51024a055500f208960700b040c6034420b0680304030780c40418101210030202035040c09400061130075454070310341010068504e0842c030341040044c1c400c0e40240701007401c0300d0035241021062030001d4001c82c805c1d0380000000f081c0b0034052200c0d240c24031486000b030180d00c00e41540254140c0d914001c651280d00003502e038540d103400316107080c4a0910f28049001c3c0d80c2ca00218450303142d55002d801400007031030968a040c00b0f0f0102040ca400300107000c4c02129002440f0300c12443c400d41c0e58402034403000b000c0301258004280300000140c4540905a2200d118500140c1c643c2d040600384642d0301001850b0004640c00804c1c041941e030300100e102c8184 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 838485602 1250 838484352 838484357
    0x50109080c100f030e12190801080616050403050610170304030b01090e0c27010611100f0209040e03070b2a0f0f030c07030305060303040602071806030609200411070201 74
    0x15003e051805a000b4a20400303080314601404000c004a0b14a4200074002e510048004000c0c141102c8012501c001c0240140d461603880300d4007049800400c120402e00d0100545030041c42c0584076954542000c0c81070b110148602e248001c1405070f44806050811411014401942840e183d600c1740c0d071010006201e2442d14035910142c0d5034442500b44014215000080c102d40400240d0701c13550b800205c0b04946071450035021800215000c4d02c522014103000c820500200808408444100010100034a61280c540e03420054001d071038849001d1580e00303000e11740c05140caa81c00c504020031000c000034440f1841501600d00d00700304048001071025101c2d9400d46c040d4071009030307005010803407280c2c0703030a03207042d074004001c11070001514030050191038400d507001c2c02981c40301c1080c9680c0e809a030080102680010000f8030031035003644d0080d140380240c01c802048181c0e9036200c0d1001c0b91031103030041c0c038103030448218803580c00da15240c0b024024000b03807810401c5841010101205010b041d100a04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 838486852 1250 838485602 838485617
    0x60618051509090c0705150708090d09030b2e300312020403020604090b120d023c01050915060d060b190807091404020d020d0c0305010905030301050109080c10 70
    0x20103a8510a40785d0040d400700803228580021100d03d80354000440d80000000c03100000100203000c046000720001000707448000e8014250303034450305940c100030b0050104900f804c00f144800c2455402c80341c05009030541500e1840e00700301202102143d89030261180419103030801400d2160136100c040b1803034151034003030f4290034841610406841107a201030f601040101d008101036805078480d550010007241e031804a03080000f1515207a0b07031800b0002000d41c0001c0031003511824200a050b0740300501d0642800e000760300520550b40d2012070003180c02a40e5660040218442003041100b00d800e0311008080368a2a00100054111400010041019440700014000394640c44989604071881135a220641c3ea00c41d4006655521203105440b81e950421404001450070600054019a001f41c1a801d2221a075001d1040c50340c3d00c46411500d04109030070000c08110f081c030400c50001d11480c0070710741c0da501d4540010310000407504a8801500903510a14080c1c0c0c0c0e00301c41c8011110141000c58 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 838488102 1250 838486852 838486861
    0x80f01050f03101a01030f0902030c01120e120d06080f100c03061206090605011e120f08180301060f06020319030b0607080d050f011d0c0d06061805150909 68
    0x282001c2c1002c045800c3d0700e0030b11000c1c80300741100030004182c800c020307038080041e401c5101c80b02054810070700c0c01035015040100042002c2d413040780c0381d0505881c0500c0c080795481103041140e203000301c0100605540600444c03a0b80040700c40b030098a000301401402000101d02c643e18441d20b0f01c400050080c5070617910425081124088d070131080c01007401680c0c0c0c841c411080d080010103090603460454040d49048000f06e030030000c01641c0d46103100100b041000281c10010312501018401a003642e10200010400001481102c01004000c440e90b00c48100b0490000900d400d644c220341021151700c0039054240901c07580002602c0c0b000c440d100304280d8800103e403043d0b0041055981407500280002100000e01c05504010001c0032024181004142d031400c0880c0004d179820300a0200070b60404040c0021b00e1178500e401c1c0e40042c40100e0070b9140c81141e00114007155072a900132400b142009022407812404038503513070014071041d1070948010b80050252041032140202c8075204041200200c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 838489208 1106 838488102 838488109
    0x6190501060c03231b060601020109020d020d0c030b0a1e0203090345010201050702010905030a1103040329010609060e130e16060f080f01050f 63
    0x856004081d80d801300d0f280e080300c45080000140401508411400301401040d80107001d0800d65910f05049500c5030030305800914032415079140852010150322100740d9981e046504031401031040c1c801d4034201c1428a0250005040f81c1c03418820403a007421103910444284040c0546002091000500c4805034070045959803019003061100c0f0901305e03034032640401c0c90a5480b00a03284641c24180c2d481c109007554995554003845000c1d5001c003540c0a1060720303040303074007440244952196921490b50364801c102440e07040240c038806081c01090144251005585e20280007480310302c420408170072803102100803803d0080c1da02c0000610902405410044590365103c4000c40800c900c10084440b8100c0904050103071205c0c0c54062074201407120000c0d480c000034031100e92078240000100101e0f1008050310074403070035034280b140c1440359005d1907045410449448620540c8040031 = true := by decide +kernel

theorem cover : BRFrame.Cov 838309352 838489208 := by
  have h0 := BRFrame.cov_init 838309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 838309352 ≤ n) (h2 : n < 838489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
