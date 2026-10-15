-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5213
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:07:05.566842+00:00
-- url     : https://prove2.me/submissions/29b7a35a-e188-4ffc-a9e5-87e0c65807d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 937410071 ≤ n < 937589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 937411321 1250 937410071 937410083
    0x20405060103180212160e01260d080a020f030703090c23060a1b050a120801080a030c020a05030102040e04060605090105030307110f090a02030a0c110c0d0c03060e1b0105030609060d 80
    0xd5001d00346c1c0340d18903d880e42c0000030f1114038000188040a0a030480c00b102c2c48161410f20801800c0e1210981c80f100281c00d5481085062000251812015012900bd110010000079686d02d41390303e0060003002921403c6603c0c44507004001071a14400a41d10607102401400d20000e6040404000180c0e00c00302401047c811110142010ba00219002c1c000050007400542a400d0745881c0103c0d01041c50b858100070b0050460060103180c2000500200c080d925081410b480042800010303c0d1084640c80f05074150300001d808200003030512000c0340140d00c249401d001d85600d0707004200c0a1482401a1a0107900500561000c19840503601c0314560014018040c6019031201203040790804451011009030000103020071403481d0321174100e42d0302103481e00c0f111180c40900215240c407855010148907805c150841c0f4240854002c0c09802194003600812001e41c142e104151a80c0c0800104c2801d4111120800c01d41c0d40941b0480c0c2c412880141003c94550b600c200700213840c1c400c1d032029141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 937412571 1250 937411321 937411333
    0x303091e030f0d1e1b06091b06110102030402280807030303020711120705120309030f071502060105010e040203131a01090e0312180a0507060804020405060103180212 73
    0x1298a090000201858004000e080c10102000028190f404403500030b001d8a11130185401500d80d03c100384100c2c54851a05107011542c03d4100007000d0070041c0c401500600c03006002d0103041c2c80c284005822500303991940001c512155801500f00d000484010b0b420000d00324030040014503040160030051280003e90840f0f68403440c42030b250610681040700400c0c2c3c0050500f09001c030742c080a91554104507403a8142501c41c0c003034551104118422240200e01c04029040209001d00035074036070707680180499031405a00400169501e00d107201c1c55090803000c1d18130780c3c1c901c3e201048645c141e400684880c06211014400e00000303600040500c607060381c401103c40c0000785140c10b0801c0ca080c64a807407580c0755052030703403c00854076042410402503208005803960210b240100f5030740074407410b51100210740c1803008507082500281c001032040c042c618002c1a0399402180c40d0340100c5c000e680407c01643c600c00198102d40d001d01e0140e403122262070014005103401000f000035400d8810560702 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 937413821 1250 937412571 937412629
    0xf09020c190335010e100506131a0403060c020303010f060c0305090607030804060506040e0a02121609022106010e13271403090d0605061503190606020c030309 70
    0x12140c0030b0080600aa0031103681442c28500c15807841d0b40540a0000510190f041400e40e01c00090f0441c4074080c00348601044401d05e0385034040c841c40040140464010707a8040b5802b03002d0b195070ac64042110002e1400c650400080d100005903070580c0e003c0000440c0080c1800b005403102d0782c00c21412000c0007010814010191a600090010544a6100c681e820704044c6090001d6900081c01e4070b000d03600d0318079101102540040c21840442d01a14560140c01c45940c0700790416010b20180c00d40c0855001c0001100340302039000704a000b2940d4101141c0754107048050400c11400e9422034001001035400015904d00403220311600741280500007441c500c030f8004000100c0c6101e8903540b4030002440d1381400d101810101111840981d40558580600032000034031189101da00581480c0d507600008001341c0328148030b007038130740000020f6907101e02d020031880e414807400b000614861401c00800080c101d000042d004080e94005000c1c41c20019820180b03d468030003042c17002082c00c001160f40d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 937415071 1250 937413821 937413857
    0x7080c03250c020a090c0210020c150405060403030c0801060801030305210106030903020606100c082b060302210303071d0d06060524070807020d06150f09020c1903 72
    0x41c48000d8070303100c400001d565401004603011041d40f107900703d1400d2520f02602160f000c12150303071400310b5100068075641d40f00300391868a4506051200065101c0d002d0000b84030f800034016118600c01c0e40c0a003d0f100c000300c0100c2d1040e07001c0c403c00b4040360300ea0b401400080e000380054240215041681500c000710074401c80358040c0f0aa0200e40402e9450f042001450f50500c02117500a00a4400811010081400418450111b44007a10152000c01da98007441c5071900c880002400e44852403050a00380c40000001f8112840124403c4801d80d103c910300c40c2c000b00640c0103c14804002e1411550f80c580f0a855400c0c070003400d18a003805250710350089076035902c0c14814050080c03078000351a5060405001100420000020020f0300301005a481041044120b0380e600e6800000b640e01e400d098404256010a20361008200b20704103241e0003092000c4070070802c1112420401c0b044001c0d901e4910400701e06c80c0748125040e6820503160000e00502e9502d42c15000c9109240114070068140148 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 937416321 1250 937415071 937415131
    0x804060518060c0c0f070b040b0708160606050a05030105070c110411070b01031a0c16030c15050a050a020c0a0f03050903061f051f0c08090d062307080c03 68
    0x2501c81d41001049004108100300f000b10509200100200089030400f80011f03964000c6d80320320008810b0009210042040100c02c2da1080a40030500740c40c0070a0078038009020b02080c1c001e0300c2c0189002d0074000b43d00e14050103404e020b9100b54489800b0f80c86191988000307018284070007070f0002c1e111040c50000883c5a0002c4c0743c41406421050500d50440c5089070700c018403d00313071080c882500b200340000140c003602141c007060425941019004510f240994407d4038018020703041030340700c1d41d400100f1040350308150702c20b034400c14042219690790b60483e003c9000302c1200440c282e104440080026404c0f42c44140c0141c02400e1040c146640c14001914004084444101e8905600360415000544650507801381408942c051081c100c8200620704040041c00b82004024904408009001492040701d07141c500c05400c680d17410815040c90006841000075000310500482042c028072599110001e002c0ca03070302d42e0782c41c01030385854861003640c1c1c101801511103410b445000e0b240100313000e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 937417571 1250 937416321 937416331
    0x50a0603020d180b011203021c020102070c0b030114040b060c0102030c0a09060f0807050d090c060f080a0204030203031e0d051311030708030a030908120133080406051806 75
    0x400741e41c90310204141d200b41c4850f0300310350b180810250242000105043e407424151143c2082040405a050808030700c0c0150140d250742405601300b848401240e8190020901d007800b561900b01c2c0d280c1d0341c0075502c889100900c104584480c00c549241c0d440c0c0360a81007031182c3c40001300400d0409100c040c50701e0880c0c1c0b081d25900001440012103160582d0030403204c0000340039905190b2100e80f0121400383c151000180100104580014580741c4e00440b07074000b44401d50025404100140c80716005492180c0c020041c401054141c80004e009060b140200c2d0b040d2940030b40035500717194220035080841c00b41c040e01c6401a80b0144060a2103c0c050321880748500100d521500d00c0c1d03203407401c10580e0140c0d402030f003030702a401c0443c0c01e0040a80020441e80d07940107603d40054004060304207051203004004031184100c81071000050003800428030b000c1644800b000d5401012241c003051111ba1045100050100e0b111000103404103280da4011507016104912421980801d0000c0d1400c184d42120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 937418821 1250 937417571 937417577
    0x40207120305190c05070b040f0512032211040207020a03061a041406030618070b0f0910110d0516050a0b0f06010903022b05070603020c01110a0f030506030106050a06 73
    0x2005a40ca4201c1c0079001e01c2c480700380f000c00056050040040c07152180b80707400b0304400c4101011034104072507110090f940f00e81040a0b40d40b001500c281160040d0700035100d10086400c6010400704800f43d49041c0781410368440064010340400300c0500000c0c0d0032851099074440c1c1020320001c082113440c0120f440e404100c410700394503140e10008000c2165080d80407034102c41000310401ca40c584000401c55000076114507a0218101c644004c203160a0140c2c002d11200000801c1d140910743c13500700a021880d404550440d8411884402101d40c1c0c4503800000240b1340c010190101c160740280c00802c299110080b42d0440c0e03400307a4035254541108a5422640546207030200813090108250042d040b040920700810060300d075400049004d065020251069103035040b00d481403c0e5450110f00000307501c44e041e0758240ba540d03c1c02170f00035000f0741001e40055081080f40f941c040b40510841c1d0341100903481383c444044120004600a10b00107000541541d039560003c1200d40d10710309298000c0c1401d035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 937420071 1250 937418821 937418831
    0x3010906091b1b140f24040b1906051002030901030b0603060a06030b031e0a050c01031e02031e0a0c11030c0a02060f1314310b0402071203 61
    0x3a0110341155000400b0342c5800e91044528a00a680704940300540d850700d2464481e0041c2d2801c3c0030901038070071807940e0820f200e14021800014000314250303004003204008a05010504014119000012075004003101d6158000842c2800710424074404e14680520000394141c0b100086007050390b5a80412001d0f0b4000b0130f0300c1d8510740c1e16008000c942c03a41070300e40b02c0c210b0505c42c000c80c2580b1000c1c051802456100e40d200b0310551010082c0180354076103c03180c018507001220402d5110158980181d07054020850044455406801000b95502851740f80145110300342030902d0013034102900075082d520340b004000942540c1d400d001030083c4586840051540c2c102c850241660018a0360001c80d5042880f42000e8a03c001c94600e640c80e4050710410340c0e035148143c08102a10900d0844107681d880c0030008102590703001d0303444940c0c0c0c20640743c1000c40c80c01d48002c2807500d0b07a80003404600312084152071001c12107607080a030206030080c00c00740c14203115644020f00d1700c403000504000240e5603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 937421321 1250 937420071 937420079
    0xc010c030c050a12210b060f07050c0619080c030f04020d021201050a0203090d03060506070b191401090e0a0c150c050717071514130b0c06240a050d061103010906 71
    0x17200c06070040d91301480c0c3c2045200150340220760b00307008441d0860b20000b8080b40c0842401b0040c403100c0c801800041c80140d40b8020400c0408262010044160000c4c003103100152403040304004681c001d8104601d048400c0c0c1d1030346e00b040216000031004036040b4034418824030048500740202030141d0454240581c81b8940000510700d04001d40503400101070809101b0002a1280b90840e80c65070380081032410b0640c2e4178020304100c10908080d2080c580d1511560700451486203035064165030030100d0512000c0c90300800c5a40c0da004419025244550301d0380704011840703402441001c00382e22405c0000440a841d00c9407420300c03110f94080d80b5082c601a114007500001440540c1c060030422548a07040810801c00516030464103020007200c1000044034108800c0b9151004014648105800d03940c2105015440e1a03800a030f40040f5044030400c00203402e002150225031410318044c080c02e8250780b0b004100190185421005e0360416514406030781c0784101c1034000c502070491414045041454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 937422571 1250 937421321 937421357
    0x31407140a121d010c09050a0b2503081e0115111002070506090c04140f040218041203050603010e0a0b041e03050309060901150501180f061701080c010c030c050a12 72
    0xc885030042000b40324007400740340d03140300146041d0b42c603420340d272074842c1d0036850035500000054100003915030102c5404006c0551040e0a2841000f0380016000c5085196003004e030340410a01405285004040109544910405241c0c40003c0b5160071a24425481999201203a01288041d212030f00044100051100100b1694000803410384041211461040e0f0341d0000c0100a003006200a020745c0c04034056654842d0b94500c00d0603405081105801d191030520f5030100d2010308100446c0c103250001d08649418482c521246410ba009424801d01c640c2c2d804100080042c400ca8000c1020a84000000100c5081c4060103100b6110303603580b400c000c202141303000b400500d44c2440d80c0c105602652118140321007941120003e08000100d4401c0300c044c000300300c800c0e8000420100c40305000140040d4045030b102e41100500c00303c0d01550743c0310b03024a80c0711040740d144240415050842080081d21410745008031901600a60344004041d5031840300300e41c0c0504440c0e0014411603507514440803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 937423821 1250 937422571 937422581
    0x1516080603030f07030f170c03011403072706080d0c0201170402031209010320180301060b03040b060a210605070206040314030c0904020415031407140a121d01 70
    0x1c500031030418a85907030a0100d8441c484000f42008501c41003000325038007400d078510340320718402c0e2148028600041001d991b9042482840c0045001c081c0500c081e041c0440c03158152000626103010400a0000080100c106030207400442c0741e5403000000d103000d040c82003000781d842ca80d49100d1012a00d0000402c0703501c0e010600c03064142000f09001c01650001085081506c458130400d8032050f20000580c011b04190124075001c520400419040b030b02c0001c0100400c90035440742c265410103200030315080312118002c040b5004410400f24000c1408005801d5100d01e00a07e00c15881ea200e8154107045501804048016444042c40d103080282e14040c140d4444118801000d2034903164030001c11400c0c4401c0809102c000002c046068414490111091030030060410340d0385990f1b40010480307010b401c00240c00041d02d0710721542880304c0740314a6180100034959402207122150110102c0707075444a109802800091088903054010303038003813024801c0c1c0401e40c09031180c0c0b41942542c01d41e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 937425071 1250 937423821 937423831
    0x281209060603121b020108040201050d0c03060f06171801021e0a0909020708121f03050604060f020406091a040e01061e0207210c0f03050304080f01020405011e02151608 74
    0x103c4035104c3d4070400803001d080202003903024608001540c44900050740e151081890f190360050601c41da07040d0081e019080001299400c1d01011210b0740d031803c0890b00101c9400e12210b06040c12001308100d1250130061491001c844c0c0c000500e04111203440022100704245095074940d40807071210466900240b0741c00003809046029440c15010340d9070250603200b02243c040300740348a2004961860000003010100c002d183c0407100c0460749034104075580f900304071811581c13503081a0103140304041c41d00a560403205943c8940c101d0758100039810001c07d08000d51015002da0a220004204806034101c07402883c0079200c88800810f164800c01c107410100c2a16001d42d0712840d0104900c8e01039240b9640c0e054030324100118007809030324001d00005002d600080e40d00704006408800d0004c040000c0c8211000d10080326014000882d489013030b405a4443d180c0450b00b011012100c440b946480a01c608031b07180705440e0b40d0149115807000c941029a904541d2407680d6582c1003040e07400034590b913008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 937426321 1250 937425071 937425077
    0x53715051f1e050412140303090106050f0a05010906120e0102030c0702040b1e0616020406090c0906020105070e0d03110a110118030c0b0c1c0f0801050628120906060312 74
    0x4040b9050702034041d218a100d07144a8604050441c000c0c0322403030980f01c02c640034400a40350307242410049280a8213040c01814442c514511440c0118a0310481e00c004840d0180c40d0441c0c200e203001e00c1941c8284054500c4a00e984c2c450060002030340c400e2000394454040e13445495100c038080c1c01400211607002c45d10b00c2c00b40c0e5404488480300030b1410481036850030101c4440d80d58196007035405280d56a0020002c0d0000d0400030301003520b0065070400c1082d032004d9030b10b51002e2560307035804031300740c50094400348085001044103c0c403508001e41c185100314043d05007812000384040c881c2d8540310341c01c001070719141300c600071046603903900c003d1007802e10b50304a400700d4a035400c0d91600240755000b88211003115500060440110f1818004010001061038465085110003c8050592050291403c0000e4004000414503142c4242603480c10b0001500b0043c50000001000982440c080e00e90800e010400e0a40c18050a49014144100344105004144940b95140810055501d85445418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 937427571 1250 937426321 937426367
    0x3030c03110a0b0c0c010e031809100b0910170f091e06160306030516031a1501030e01060512011407090602120f13030501053715051f 59
    0x1003840041401c0d0040a41a1301640e03401141c03c010780144140c0c038034104c0d54040032807820703039801c8501c0890b825484142c9190865503905202501000c2c00b500a20314501c00c144251900350034400c54072190f0110508008074103111004078840b416800300c50718480360381c80ca800c120702c4031018403112542e9424129455100c02643c1115621098014048005d040c24581801c0c00288250815001150001d042d20345c80e0820042c1e1807101e51550100380d4410301d00e444444200480d90301d155101d0004009400401420940110040d040303204045a0f0303036482e40c0d000300b003950b40c6050a0010384410701c00010400000550810f641600820440c10300a0900b01007140c1900814241c1003d09011a55507031601010f0400ba001e0080e030f08014020508440084100b050540c00540905083c1c0b10301c0f002030180204e20200c642c002249070175450b05500d00c0c0410709200750004d40058440382684000d20b074950f0b01240c1781410310500700066099491440b407041e600401038442c0203c0911318049 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 937428821 1250 937427571 937427573
    0x6020d090201021006050d080c0109061536020c070e180c0405040c05011112072d02010e062a0d17061f030207120503160504180903140403030c03110a 66
    0x41f80b4007500900074100014890000030820351204a0007640500304001051044041541c010103034007031302d03030140c42c4c61001032010040da281c541d003082c0c203000c1c403c80a4498030300504040d420881c441c0c1e200784905400421076001d8012241d109001441410600781001ca01a074980803121406602403850304040c40045041510700704140c0b8420f0808804030400640d001d4642407401451000066000c00e88000b00305081d40c0d0600301110b110103000e1403154901ca628040c0401440c006e02040003c40b000100e8140740c4040d0904c51004400d8082c0f4803810189465072020109610800790022041c10030040c1d006414484140c00002c00e04c6005e142442c0492950a030b08901090b0070494802c1070385049100b60111501030342c7c01104080360a00282d00542075800c1550000641000800d00d800918441d1040e142140c10114103d0f81c014084541d5100030444040160100711408958003601e030302d218000c0c00114445c0c0d4503d0401e10071414010940c5010308402c0c42544c1001c51400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 937430071 1250 937428821 937428829
    0xc03100506040b0d0b040206090307030c03030c0606080d0c1401111b0d0c2411270f0114030603030f040b07020418080306040b0f030d0215060102010b151606020d09020102100605 78
    0x30f1b4019411344285650700701c0000000c0c42c00700725a2004244030303011075021081641c032011014091f4400d460034403074144c40c0d140703858480c000545c286c40090b03440d110490200b941549120307280d502c14000092980303000d50f00134015502407080141084800180040d1030103040140003421400b13490502c902c070040b84d980d10b503c0701a02800340c44020b03400c1520804980664829002d02e1410388446e60394000c94041c1c100c1c2c450100f0070030380030510f030290316600300c2c1000c012201e214038050355180c10101015030003170802c0e00060a0782c0c0d0184030a12004503001120301c028009407048a08003034590549104000c2a6104500801d40e0340030040d07840d0000078401c6003aa07420880850380031032505100c01c041001b03050b00d260f10380c0e814400da0401d5800c0640214110318840302044082c90241d44603030041e401d1714000034410741c0060032101007040e11499400a00501b0401040b00318907441c071501c500f026a0014481c05003003503a61001c13207045680401100750030140e403034014071480389010006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 937431321 1250 937430071 937430093
    0x108060703020d060e13020405070f05090d050106080604050a12031811012a0b10050a0e071103122a030105040207210201091a09030a050c0c03100506040b0d 69
    0x140c01d0540100ba01101148507400000c00360440501e031892900c2c000050707070ba039420801001c2c4c0c000da151101080700c080c0700d051600c0c0c0981c0707503440741483c064404080c000d040c0d0001c541a50300355610b50012468150510402d40540d01810052800000e0380c02c0c00d43c4d40d1b01411206205042c0303041c5003105098810209003903441d80040d90031100420780d00040e50a1140c0c000fa000f510181019140311641060300c41918250180880d02800e54400d280c03000d101e6840d0145903070001102c0c030204900d1985041c2194071541c3c074075044180e0603000a07514170f950802c1f950065828800c508002e400034002804041074030303a060060b07007001c201602c810000e10041c0112406940c00041140038480c800c084464101600d10754101400c41c10f0b44001d00074a040d40d030858040d44a008081942c10918040c503001c1e4600344040c51901c0e0021005540d0740d030051072074804502800d040290307aa0742c1841084540d5000880c00b0450345441c001700421681c0c1c60356100d06c92608000f100300420780280708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 937432571 1250 937431321 937431331
    0x3140c010207530318041815050712090201091a04031707060c050c101d03031009051608040206031f0b0c010c1704020f0402041823010806 61
    0x686001030b203010040303005400400c242800f0b10704603003041aa2803514540c3c41c4000c84100302c00100380108080d01c902c101130340f02c0040045840700700c0d11403a241c0d0241c1c0ca803101415040c48440e005070f48090303503180d20300342c15450700ea0307590108120b154000c490300a1305c1005000810060340c0983c000303080e0346401c0c0180702c00c3d101d141241090302c00401c0200e602031a0403031000980020003400c40c6a407a400b100301103460b0390906a4444125010301d065850040601d0003a000b0031901c00e00c0c440c0105001140e0b0080f62b84101d809424842e0140000c0d40140313046801c80d010241410880c6064500240c600304030340c0c7e0f0716800200382c0c903808140c00e5005a81107411507500d880e168001c5400c0010340c500d5030924142100d001881241607402041d012411000a010500e0f40c1e00d003d84417070300425105d140c0842d5039000074005144c029000742105038010001401d080c0c41e480119116140b0524071000b540d56441d6607a0904101d40c8200b9024045502d403103500c0d8145500701d070b01d480c0042d203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 937433821 1250 937432571 937432589
    0x21306081b130c210b060c1006060513030b040f02060307030b03060903030601050a0503090f0312040308010b1606091a1e010905101e0506070b061201062105071a030103140c010207 79
    0x161101c13002c082d42c101c0b0308a824020311080e100d65040540c03d0715420b51103981c0984c01d141c5040015298054820344110064400004c0300349451a1070b82100180c0c01481200d640035800d00510043c0d5404002d0b42c0a80015a000641200840d051518201c40036000b01c143d6401442000f106a034000d084508060403460959166140d92400600e0300c1c5202c00480d0a0b03000220317a40c44d016420b041f0091003280a03584854490341c2e203606030000b510400c01c4c01c1d45d405002c640f00c00081a9142c01800c44c02d0310500346055000700390540f07203095003000c3d94000854400d0301040004000458002c0c0e000d401038a8041000b0b040ca03913811046405507102c0c1c20261829a426443e0041c890350102009040241006a648000d0710303109880480443e03013036128a0b5000030801d1902014801c0d4010f440c0380051600c8140006400b140310250414400c0310700d0b110f00c000c00329070004017404215584903c1c1002d20388035415172414440d00084440400020303070081001c03c596030303400a0f4240450700b100f2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 937435071 1250 937433821 937433867
    0x40b01022e060b0309250b0a050307020316050d120e1903020a06020309030301061d01020c063001084c14010906061b021306081b130c 59
    0x20141c1006041c40390b012901c4031601000b0400b50a40102c0c0c00c18106400c44419480300103601104000110b0368000c21030008420f02031000d029004000464000ea41801103d0a00c1c8210f40c01154007000b48604480c0c1c0d42145140a240c0d540100e440310442c1c0d1103403400e0012801d6080096522014541d000400302100840b0005040c001e010001700c040c0c00540540d0399140c0403c0081d540d501c203104603800142402c82221402645032840107141c0016805070000c406520100b000d2078000a840a43c0d684102510401c03c004a15501300c40c40c803640d40461103989051103080c02c10310104102004096031100c00500c040149a210b01c00641d0071200c10030607540c0107581c90031010702c1c3c0340d049030031761610034100c05201d4603a008a04803003d01c0424070010303488400c11112140303821041c1401032554110007005192100c00d421111000403000184682c2d1003801e6407810070032400c80e24002a0001d500462404c091441d02e00d90061070005000e106202d403002042100081452500303c4819 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 937436321 1250 937435071 937435153
    0x120f030c02030d0804020306060a05030607031a040c0905091308070b09010246120e0a1e111507030806041b020c0102070f06140a030b130506040b0102 66
    0x451182203115005000c480f0406900580588089004d036000e81c0309201d8100001c0040c50020040800e450010300030300659240c40005802414400c60341c0e9035007130f100c07a0726034500340c030b5501c2004080d80403070f5524500383c3e24000500c207889070050400c0e196000d01010b10400f140e4550300f110002e50340300c0307030b10b46207560b4090707400c0d009002d1920401c036000754440f07018030003885030001100ca401c0a489000081c1c0c01c46d5041409145a00ca80301d03010500f030a0a261041e01e42e640041c4a1402420988220710303010b5507414a6422401000600c0308011040b0205111078600c15002d914016a9001c03520300b1a94000c00c0301d0300907090001e0801504400084c40c40d2604d1f0442488400c01d40308541c482d46455601039101c80b8580c8005005208032080040c405a0035081c200455441d5110b0184c40801140210001d6101d072203188240b544924603228207407110190f415150055a400003103d050042c00c101c1503400039407219045522881c1308156450905035a03c0420380c0342e0b645003000e8010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 937437571 1250 937436321 937436327
    0x5090903090916020c09072f07030b10090c02120a0e0405070f0201141e1008070608100b12010506090301090512120108070f05010309030306051c03021204120f03 71
    0x155031012078020b82901d05014200c00620801e15107031806400303484034506000240300041d00210f0382c0d900041c45200706400701484140004041c0b07401ea10a800000300c1d104006403401d2a55481144c600c0e083d84200030000380c2d1910154080d202800d8240946445840b000350340b02d002e4101490b00690001e40002182d01940312049940b001410034002c0d490205400b0301140f40703251482c80503500b44101020320550030004c41d44100684c044540e00c00e070180c9081300c410b840080602980140f10031011840080c100001d030010113990b66001090b15002080310f001c00025404121903400600588007a84409030520341514001e0fa2120b4a85049000090150548000150103400b40c1e8511594240c1500b0003044070011000342c860035640d898008660701c005c4c0d441081b0140311114000d00007507100760014103401e4041c0c980841d40d0b6031110700064040d40c0701c8012042c1d40c0c1200d01020105501403040e85c805510160070741d0f0406140028210b10a192040020241c41000d6005403c00d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 937438821 1250 937437571 937437577
    0x30c120a0906180213140a050c13121209152d020a06060e0603060f070309140a02010f0509010c020112150612050a0236060f0414061305090903 63
    0xb801502c14000b00e02d01c860f05143c0703000c2062043e400742d01103003d84034660a840c050090011041ca9410181d640d42030340c06002014064140206070b80101308a0810035518040f00300588200324260002c90460710b466640c0c03c040000e440140002e18100b00031015086000d0541003806040c10718101c0d614900d03041189040203416031402e0403c0007000302075075002610884040c85171008000301611448911408501100c506502d9401580050110700c4514060f03a0024264140401d40360700b20740c4c03403070b1190000300210300d1564450302c030b030030255a80300c400b404c80c0c0c10150800c1031a144103040000c0034046e10b0480a8144049103c21034603400081c2d11811401c00000028040c0c99201c0781e00421b003801c440d60a03503500d400c00000c550025014800c0342c000844410307000c1c445059003c12490088401d94400307140701c0c5580d21818003505c0310350091042c0da001c0700346a607480e410000000e0305040e000c1c1100e406804103100325010319034003688803002d4580031038a0b03800039170705d0032100d5103548 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 937440071 1250 937438821 937438823
    0x290405060d0308150a080c04050a090b062e0e1c02010f050705150708090f030c0a03200d0f020706020705130509120c0c04060618050f03210c0111030c120a09 69
    0x302085c00000340320003000c603984c145507a00300e0301840300c3c0d120305401e00161505020040d00084402001c200c41c0d207021070514a203c200324140841c0c6a03c0600d0080150f4070808210707001c2105140076002e01e14100701088440c1044441d421814442c80e0002001c0300071821410040c410f00180b80c0b42440030400c1001414001400002e85924001030002c120f01e405a420901e94420f1b05244481c1c0c40d00401502e0b25030050364024075a004050704d00304d031552540310308036041070102c4990014000050140c0000d40e0210b4450b05c1002c185800000d02e0144298000c5045410040003401559290b02079002090b09461010840e83c42ea00300380340c184265110800040b0f58002040101c1c040041070005202000725010000b040c2d4030841610391440c2021602180481c4250602107480e0440c43c5a0850b40040e0031201d09940c07110301d28907401c10b0b100180400b140c0100303000404020174055880344a070f40603101802d505108507900c205008604410003c41005000281c0042c0301e079004801071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 937441321 1250 937440071 937440079
    0x50a170d0504060902121f0207140303130309080f03070f0c051009060210020f0712050c0a081c0603150b0f0a090f0501051f05031504290405060d030815 67
    0x1d41094507000b4014000010100c0c011949501080306500021458140ca94a214441080741c051111900c000b5031041074102ca10448118510100f02020400b440c0b00b40091156809080304c103003009008009262b000e1400340d40b08102000c040c02c404400d40352015840066250400741c1450005485a031517000190000b040760142c007207547c1d21030034120885a00d03409880c500c200d201403980592064600c00c48543c00108400300005074171581c2d2148a441c0752502c6400e01141440d2207041030030106051700c610390045140c00815006d060a4031040d068540b042005900d10b03070700c0c0105451181c880310b110a958410700012515501604101d203c4010415070549845141420040201c400c145600a10307203000801c40b800d04103000c4207840c3c1c1100c28500c1011a0f41801c071040d500c020103c6001240e10190115180c60781d000301200f100c003c42e641003403003201200c0400c54244040c10300784182d00380001d2050a85072481401d80c403e0301450854002da60710402400031903a80c0d580c1c00c1d08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 937442571 1250 937441321 937441331
    0x903011b0305070c0b0c0a110f0307060e0303070e190b0a0302071a0402030c04090812010f0513021c0b03030919050f090f0a0b13020d091509050a170d 66
    0x3451440e51103091410440781c60070407003602c505030200c1d80c0051004006050000200201e5940c542c10801750400d403e0034074041c0041007642c40400e0614425a4940d40795600201c1c0c080100f16490082081c1200800000c600358540a84000e0482c03030b000d10100d0240c20303442115150080704e18980c1d4068035008080580d0b88140c240020f0003503000d2042a95804052003801d10030410340040180580d8004004005125041c0c0810004021a5004490b20310080015684210156244c103000b004141e04900d03000f8502014400c90803024400c19420910400c51481108400851107909546220300080c2140010000c80d10350712900c0c0c480b41c2e00c84003100e0724051882c417403000b1200f56901554560020290002489840601610261882c0780d4050001d41e080181c0e40c8411100c050081241c0358001c0301c400403a08076032220140102094035001c0301004e102000f264204505c4101c401003201d040e854807540c0c0c88902541c0020010000d404084148944900c240caa007401030400801c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 937443821 1250 937442571 937442591
    0x1020a060615090902090a030b0c090a080312010f0806011e180e1608030d09020a1e090b0a081f021c05010e0a0504021e030a06020301080f01240317090301 68
    0x1940030031015444002509443e010810301a44c0c02075441804020b005050340c24115070301e9003d070b5880203000c1d0b2041e15080c0104842c0782c0da04222903008000100c003035581d940d410300302c945018005030041d028101c4008000c00501c003000a809044070b903e11a0100080380008407038000c0d03005070380310110205001d407003845040300651003455401102d40407600080c241622a07a1003101300e10444009030401c0c0200781d4101d0301034116181540c8000c05a081c1180c540c9411059141d03101d10b558204915901d0501c0b542000e48112003880e0030032546500b440b0326151100f80c0da0807000b80384482ca0041011152401c0b04660143c991600003100e10040c460350602d406001000240b042030744040720720340840c54008092007405c0c080c46c1c000d040a02c1c1c6c218046510b00c2074041d5040c03556014810f0b5940395000c10202c1c0301460181410b007014081041030500c20500751103440003440d01d595201a0007002d0300c0c10200c00d14040343c1e441440d0000d82071000585117454000c003050030340c0650070106942 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 937445071 1250 937443821 937443839
    0xd0e030408060c0c150a1a010f020718020405040507180608280623040b0414010b0c07030506040312051b031b040b0f07020a0e10060c060e0d021e0a0c0608040201020a0606 75
    0x400c1f01031701030382185180010300450b038007480c0c2c0d9040000368110440a221603146414a40740981c000240503140c10b517144085000c4900440304c200004643d01721401c02101d00c044040c2c01882c039807924018078240b14820442c090203001c1c084650f4000c208258003c50b0054120038000c2000c0c010059001e551f01202200c41c1102e601c107035104620308008800c0c1c900d85403083c14a055160300001c00d4076824030000c800542d104100040080c0300f00c0e03400100003141081058400c81c480c0e558405542c2030860203409803400a41502240054040ba10000d400040c080d00c1d44400003140100c8e1803612000c00208621490b0803140d41010001110040b40b0340350702c02440d00c0c620940f08006403035070f9072210740d0810000346c1c1c41180c0c982a20404000462003450011303a910300411001650410310702e502850081540030300c0000d60400005954800f1410640d4904808010058000100070380e854140402031405203009200c5d41c2404207040d64820048840f07a1940440100480f0382c4980c3e601c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 937446321 1250 937445071 937445081
    0x10b030910110901181203030f1b0e060d090b090307050c0a140d1e060f0605010302091f0c05030a0809071205210c0109080d0e030408060c0c150a 64
    0x320000d100300c04840903004128442d02d0020400241c0c0d403400c01112100441d05010091a01207075000c01d000d02185400c10581c0110143c1d100303860004603468442e201309d099841280240903940030801c1c0212003903410111420051000b2521540e480008203c588002d00c00040c001e01105075074400c201380118004004c00d001809003080f1400c01020f0010410356100300c2c01040ca5100480000c00042e080003031001f03140510990303201401d801203040d80c200c0c1c6010a0310964000b91a14580d504503c410f20512014100c00c2c6015850104901c002c10310107005a21107c0008440c41e008200781481900b2241d030465120341130300d41d2202d507060001c18012055900c00043d008000000889840704543ca2540030b500c1000751118001e00d901500c8801a4480030805007041001400070700c0501b0320a8a101600c100c50316a20303040443e5040003100c0d00d46011400c590300801081c407245c840080c81c107500403105080d09540c0c076801c414003424240c0361400e02d91192100000d200540410f034002d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 937447571 1250 937446321 937446331
    0x30702030901111c051b1f2f07020a0806061806060412200603040c0e06030a2411030108030702120a0602070f050c0d11040216080a020a0b130b0f060414010b03 70
    0xc000500c0907518006c4c2e071501841924110ba442600002c1040c0e00715030b401c065048140000446910030150440d080c1c40c914603880340340c085200042c0c1508515150b180c04001d400c4140060505140840102d10340c050192640051008210300196407580c1700402c0340c0c0030301076603844030039120103510304202c607503103050b402d00380342c00e8402110341403401e00c0b800342d91045800410b80c20005140612940c803e02000c2c0c20141c150080c0100c0d0f5003c241300310b410405010b10380344880041441041d0500032551509900d809104080004219180e0000145d8005035011111074110b07280c0900405c1c58403c40b034100402950010662000748200590031034403640c00b4000b590344403603001c0200005d40c04005d00041c440b006c0d0007000c51040c1003640c0540703010102c1c1e041c80c50074100c2c83d48450300c01d0f0300300000c0e82005a101060540030000d1080f003c94011100030000e000003d51070303130350b481c00c5d5400800880c0400000c0c030000e001642d90707030030400c11200d0780034005ca91561125141d80c40b80e4802c9403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 937448821 1250 937447571 937447597
    0x7020307030602121510033306020c03070b0d0e0316110a08010b181b22080304080601090b0402090d0c05281404110409050615030702030901111c05 65
    0x6003c452118400445045c001000c01c1a010003441c019070044c134021624108010301144210140d500c0c1c60758000b40c0030b02072441000d1061500000038070340b10b60518528002e401ca44030401140c2401341c10380d26080150f07480850261200c012982c518043c5141503011020482c500106010700284c1c940c00219003500c600b0071681d154850740d030980e45812041c54211051860b04007440c614809455005540c800e80c500c00a007110718040000d800c8a14440b9200034684c4c1c04400c8101c00c07100c031400800000c00618141840d251007075850f45014441d42010070384485400f8400d58035541214840c0300d0080c504005e90240b42055406400c660098500402c040c22290319440d503240c290301d9100e500054407080d414104400f443c14104d620f03c10540094036440702c110180850009030000d082d00700c400003024901501040141190040810741420382003080c02480d5a010048405504081c203010106041c800f411314a41502c05200700e40043c42130a242c481c269004008000c0240490 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 937450071 1250 937448821 937448857
    0x5071505030c0c3a08010e1503030c030a05030a06050108010305030403120504050a0b0c060f060a0303110a050105010e0403090603050c121009020a0f090b03161d0405070f32090607020307030602 85
    0x40d13054415410030300500c0201203100d00041c0201c01034525120f00c000016043e242040c41050f13009107180c0040c141c02c000f00304080304004182c01c0c24410a4010f000910b041c074031651658403015141d20850002400d42c442501001e000180940100c0c0c00614000d081c03841040d039154488040784d0002024042203000320300109107050010b0b488540145402003c1044280c55035800761042640030860b55110301a100c1064080b50b403e11a05000300450207020071b05150074903004100e05815000542418544402e000807640180180d0310112144040c40c11a52501d001d0310700e01e4020760780f2a030b0006d400000c050f06201d5000021082040d1551107403130401d0b865684029290000700d07441400d205442e42061003a510a040c0d240c00ca08405126081411100c030101c3c090b6001101d6250100c0c1d4941107402c00f85a01c40381c1729000c085190480c03400890020741c0d8448409100b45034060f00328000c5246040d83d030b41d00741202d0115038002c04440c081560303480d010001c3c0d004800300300c045c00500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 937451321 1250 937450071 937450183
    0x1090b070c03021c02030d0915020d0501030201080c250201020a170904180f12050403210e0316172404060b0603071b150207060905071505030c0c 64
    0x6003030320300f509250f17034001e0b50800d21005c1440c0010300201906485102c20340c0f0a0b02d00181080c4020304031981e60600100303040d23066000151103404058504040c02c0303000c0100842c814840c46040031000c2c1c0d40c00603e90840e00b01d00040b442c280d43d141c00a007030f00381407040b1a18041a80710041440380000d403028050104200d2503c16004100c8002504104c0000d04660005030016a4059844d81908225003090b8881d1100790007040111100400088800d2030422030b1a0041802684903404034000c20280c61914000514243c251080c40f4000b1040d03098040b551600344070810003009440ba18034903242041192200f66002a070741aa02c03a4905001c14030a42041401c8910909981c0c0755a000a0115101c009402c0f40c8030500381c5424031140034800d054a400c0c002046054055400030038030704a14103000d0b0501300e85501a0000c5000060381105094100040d01d0307010380740c034250390303242d003580b40070700d030501d03010420303a40080100c01196001034516500d020480c00c2c201c03a0b200d0840c001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 937452571 1250 937451321 937451353
    0x3090703020301230c03100f0b0d05010b070f03030f0f0f150504060605180409080304200406050a0302220903020709051e010b0a020c0316090e031204021201090b070c0302 75
    0x300007620343e0780c01820000d0b17100190710f402150803882500c0800601a0340b200d8144110000360418070b900704000500481c206028000c041c05044032094003450b00c41ca039a03c2c00c45241c00c1c85001018507803944034031150350600c0d51004420f00012032043c03000c104240300a0000702401d0f4001e0310f100340b8000c40800d071400c261152606803415900c1c1c0c180b40c802e40d4210507685001d00d4031030b00c0c0e20036260100d030070000e402d6401640c000c510952011400090f2124060005d40c0c40c04006406989000e02c10002d43d03846990940031690160362102054401142c0c20211040c81a4100c680314140a4140c00b0160700003050f0040311080b201c104000d4a070601040419004140e150505e094103000503c03040d40c0040040403403040780c1c0111540400303000d003c6400d00216400003100700310704820400084440d801500158602200035510707010440114003043c60000c2e2010b4010485400c512140d06802d621000e0b40a0f08000c5000d12468403442c0100300c035103218021001800744807940c40100712 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 937453821 1250 937452571 937452611
    0x3091501090c0e21010207122007060513080d08040b07171506120108030901090f050604060507150906020a030b010206040b010b1804020c0715090303140d0e0303090703020301 77
    0x6496030b9030003a240309000400910302c4019201c1c4d0308401c3c22204400c401402480201580d512540b13036011122045400501300c003c1450100c0c04000481101d0310310580b0200b50303401034071f50f10304146485010304060f414044840d9000007032188680e03103034400103a4015401900c140e100d451807000550f540401112044a01781a00c104a001c807404180100f4090160300451301014010a007042c0d42d026000e2a258001c3e4054085600005181012542d1104100e80038020100225902524010205580b44254071550041140200c0d4600401c010040045149807a588040c00b29058074144000298084983c0c0d4011a15208504440354000f0414511964100001040036031070070740d0790881d5601081c0d035000000440c4000d04016502c52001c0d208510b0b50308000c0641c1170030104014054001c0100764024000110020000203a2004400075a00c2d10440e1140c0c4a001148600010f04181c070b51700c1045000c080100548000000352800071203000324001d020390409120030ba010301c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 937455071 1250 937453821 937453841
    0x2408010e0d26040201111e122a010e06070201061d012403230a050c12010312020c04020a030e1e0307110d02030a05070812270409080309150109 63
    0x71049445411070400049189500c00d0046c180070b803130360b00000d00250800c40c0342104070102c240002c0c114040800c08121807000780c060191a64a00a440310802404080540b40a0740c1288105122800c48800f90840c447c1d0140c403c04a9005007082100640603040c90f019001444245401714090052060359007412907964030910041344841051a1009040303d0780300000741910303145503001d45100f0000114030402030b1184005582401040710090303480141003080c84503000d10402041c400010110303811264425403407000c80044040507030610700d02d40c21142c0d202c0c0c400324641e03407516010b80100c144503141030240d4086070400c8012520034407002e1200c0015610502c50740300021803420b000e858166006145c8031000c001c50740041e281c00b0411104480513005044108002d880c00c00207071a4621024400505010495040c0e01c0c1c0c10420a94440c8031581000101c512902c039070b44502c0303c140d00011280d50b24603050078019034901581030460303625030042000180d0015207206102e880c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 937456321 1250 937455071 937455107
    0x2120a0b07121b03090606030818010e06040501080f0a062103120e060105010309060902060c1c0801030210120e0d030c0f0206010513051009020a03061d0f0a2408010e0d 74
    0x10610701e0401300c0041c200c44a08850540c2d0307402c40800811601c1018110f1010404210b0b038001d022203000603d02d2040c141251b0080034280814802c2e6070f0400c0c2920b81c80002d040000b82c155440001d08000b805950703100410060940c4c0c8501ca03030880800d501c80a203070280c0c4581c030044075669070440c201e9014008481c41c58210b03000500c0150700c26080082c00a00030385010400145035000104190b021010050880d401800c0030a80d80c4180b1020182031041401c02c24404e616540110301080d0031304211714204103e4819010059420b98800c40c11900d81c00d040722102411407002a000f4501d20000d007011540c6426601d07062031001840030b040e1103025115401540000990302c0281c10302800540781d280e914031000c18a901c0901c09000340f2101d41d9004101c00d46003655012078400e03d2180030b4001e120441c01c102480070480c443c40d4001c003101c400040c0501ca014610004030700c0c41018101c1c540c04090001440c3d80c0c05401c04e04401000384241d0780d039250204400d0303035841001401c0b4020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 937457571 1250 937456321 937456361
    0x6170307113606010908030a020d08130f050d08160e12010e1203040b01050d020f09040201110718060906120f021503040b090601080c061602120a0b0712 67
    0x2090030059040c81d9500c8003003040b010031800030000090085419030710341c41d402c54044100701c25581c0c05103007100140307a01c03000707186440d981c0e02000352074001c2c5a048505128001d0042880c0329604540c0d0700341c6640007c0003180b81d006510306280ca8000d01541c2c54005003030348010075040503100515801042c3c0d140c49810300d40500d4000e000d17240c2030384030b00d140d03043d503032104131905401d07052084a10001d1640b10b4190740e46094549604cc0c80f0f01078201c24044c0c0004201e000c010b8940001c026003030b00d022295942245d84501c0120b03010200140400954001c130300002441c00c05c05102c080f110440043c09210007070f259004502203501d42e104042c4604404034289e0007081c00034900d0007415001511402800c204103941c01d4090b4402d8404445805c10001001034214052043c1805414072401070952180b000c40003400d00e00074001c542418020310764a041c215541c03400e4140001d8100c0f01a106201002c5c00c00700040982102c0000125040c0900300e040d00c0580e225510400e0515840340c86 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 937458821 1250 937457571 937457603
    0x6060c03080a1506020601090f020310060e03100204060f09230108091510090e0601050901050f1309030206060a120b010e060409210f0903051207032106170307 70
    0x15040101424480c94503a9403540703c03c5001d181c10b41600500f0258006050703d526001202003294001011444070f0b61040c402c0c030101c00078081c03140c0222402d620382064110361102c0028240000003a10f90b00051000030300080c4190803882c1c81c1031403403c5807102c4041e10342c5d07107212108080c0118010494044000c000007070703035806554070a420011a400321540c04a05e1520103840c228180c0c2c091540d01c058580810815040c0d0080c5a00c901103500600362a51400012405400d01805214860001c2d05440801c50302c410418990360403025006101e8003101d41000b07501c900c03041d14040d01130078460001280045c4800031441c0032990001c00b0a0303607a841c007001d6080c2d0742005841d142d13100d81c0f100500c030045207001e981c4245005500e03d0b21000b03800007220181051510350b0340d0000b808620f00040000c01c2d404149500f05403812024240c1e183c8040c90304a40d04210f50340802080c00c00207041c801604e803a54007180588844032400b240c07a040503400ea50b40c0b4001c6010040000143c070114607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 937460071 1250 937458821 937458827
    0x705070b16050f1c17070f0212030c04050a0503070806130303060314010f0e0c0d120905220b0f0d060924050f0606120c0a05040b0a111006060c03 64
    0x503040d061140d00902141050b5aa20306109a49204512540c072943c030070811402018020262408142000481c1c901136500710a10080300034101c5040c808160490001e640c0240701e0a4400304008038015030301d2130b100006000303641040c014a40660507682020903903040006403402550305030780c02840300d580c07410070140300d008801c0b00850815895000c004001881743c0005031504040800208103900700f0103000c0200c40c40c0d141660b03202d5115415501a9842d07540b903004940d500010381c0c00710600b40d000d0a945040c0164060307500140302221401d0200762400d1510080045aa02849200b00040c204440190607030320240e40324504040040000f07111740d0003201272900c503480901d20302c0080840c0c27400c10f411006000f90440e4446c000c00c4000b4040781d0f50164440c8044550500305454500b404501880041102c8207000001840c0b261b900d00810603a0018540e006c085940c03406a010000d0000c40c040d5549812403259507a400200b45060240780c1c183c400a58400c141c2d211181c80032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 937461321 1250 937460071 937460077
    0x7021504020d02041a010815010c02010c06020909040804090e0d05040b0325020106030302150903040b0307020a060f06090f29040e0f160b040311090717012304020705070b 75
    0x120792085514101c500142c40340d02401c2e8065003040700b4417140d0080300e00050440f4030000e00400d40208040440c2c4082c4c1e80058821200715020301e002e0208608034a42130300241b0640030142c1e0301c0980d4138100420012940f00a00540740900c02c14030054140700240c1d0354403429000c14a001c500c00340001e101110816010716441007900b20f03a0010787c161400140303400d81d801c01103100140d440311403d000f45501040103000e0104407102c01c0c0540d180c4105a1512401140510803510350000041000d1038400c00a400c1626084042007165540c18a4010003c00c0603104002c004c82c200f160710000c03105240700c0d00c410704468280c8440b642074140e0103031810206523101254803955404103008050001c0081c001c0401c4002c0045c540034045184508485440e0b501c54007003401c04000500000e500a4004110880d0070380b640c20250b1602034050350841c52100901801e1a600b03000025000e409084001410701c0f00300c645450340310358009200a912070b81d800504154450602001100181001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 937462571 1250 937461321 937461323
    0x40e010504020c16182304030c0203160e040c050102030a0915020a2108180a030305060604080115140a120206090d0807080c061003020f010809030d0c0302030a060e07021504 76
    0x42c3c403903401d01c14080d0040d00703406070040d18070450883c0410407050458481c0b03206540700800050b4502001c6c0880c42c0c002c0030010001400c11411340054411901c0030000c10036100c400000012150b40c4031086c00204840440e01503414020031a0001138550010044820f042d8841c1d5030b40344100c0c1001d400b091101800c804003811846208008000b08080d1945882c620260700d8680c4080180140010a5020301412944940203491011120703180c00181481240d82d05040100e0a56200390020340b0038041d0740d100010650030000101c90182210300c080781a04c0f0724010402d0704e856050709100014046016601040801600c61000b6103419000b0b0602810b00410958030a0360507580d000d86900401c900b103414100204600f0381d49501400002d0384030203081c00b8040560319540004200402a800481c188841580031540c140030900443d1b100c41d0b016042400303514521840240207510849254048a15042002c5400884000c0c81340c00390225500408076404605d110381c010020240c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 937463821 1250 937462571 937462573
    0x806100e04020f1c0b0108160c080f07020a06051309050c07020303120a0c03110d02030a09140c18010303020304151701061d330409180512040e010504020c 68
    0x4251199403075000602d082d07958626426240c20144841c80050908816250041414038200b031003503990240c402680088001040d0512590700d01061721002407aa80c09400c0e000002103011000d0030f4030000b03005d400d209899480300e40390b0751942181d480c0070701020446000f40e98001007040440d10742210b908074240b8403402e458145544d00092455000750a6243c1d070311007441c10452894002e10a0700061061410280290314261528410520507221014113155000c004079000d40882d5101055a60f80941d00b03902e18016070800310399030400464214422005214815091100c0d0496903040301d82c103400540c00c007030501032107005502c2e185c8c42e140208944640048000d100910000c0c2c000c100341c0c0c60710b0042100e07a12188403800c211440d518002d0303070800c49514070b0221114a160380401800c18141c1070328041e41000001d4401c95010003042e50a1008400c6a0030310a14601d402c148608100c608241d40c0404103d03181c01076100b00946c041400b4010822070034290003d01a17002e40c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 937465071 1250 937463821 937463837
    0x8070b0103032d120234150905030a1d0a091b020309030309090c160b01050411073c050c0108160903080702040e15041203021c0f09150b03070f0501080610 68
    0x206c0046240c071810007106280040c041240024800a020401d2031000c1000090001d14859240c0d41d46d00d1003841410350400a031414040081000c102007001d40801c01450380c8071155a4907405405003013048540101c507040c041680d844140000304a420200c3d0240c0950304000b003420800a0115005110000c43d00042208105020206804001552080107840c4080d41844103010840d0480e254064101e4030030040200400c2c3c082c41c1d81501d16604040c2040000c92040c0c483d268500d5100246a0590b204020042002004501c0c001c5000f000e036185e0809541e41344601c070300444030348203407408203110740d030300f0300c003082240c4004c10000c0d001900104544480d03d68140c504512207960514110200081c0001c12400c0c006680056004d4581542003a2108095440f51003a26240b030a689903900c004120980c01c80d00031001050b0450318281e000d94030000024003520000310803500c640102c00300030507281d44c3c00808605803031041e518040950b66a6090041c200c1040b40d190301404000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 937466321 1250 937465071 937465117
    0x2060c030c0a0c0614030a051008160302040c0314010e0604090b070c03020705100504050d02270a0509010203070f181505040306060807061b08070b0103032d1202 71
    0x400041803a50200c0c0002c1410501c90f0030260b203200100c0d0860001c001030504040f0f1080d49080590380c1105045500182c0c0303840d2034030f5820108220345c0c040d060500605034a1a100d5030041014412240281d8050001003000310781102181e45070072501c0700b00740107000140b20300301e0580c4825901c00e030060b01c00640b14806480c1c00724400380480759000051010803c54041541c1804104014a8144e602c4104000118030103000b501403401464041d4407503601c1901991741d914011040001c00014900001c0025100000c0e0454202c40c210741c101d040c00082500c031030b014400c4a104000542c0d40b010544541030045520006001a2000c0400e410b01c01081c1401e0485400f0105c84603500c405645916500c0d00c00c055880c658403034242a040f00c14100011078120390308080c11054110f010750102c4443c60107641d44d01400c1809400d00009c240048105900900c01181e60511624003240507500d000a010500b422800d00038009080c03d01900e028109540140800482c51500c1040c121a1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 937467571 1250 937466321 937466323
    0x306050f25020309220e160501110a080a030516090501120903030f0e010b030d031b05130b0c07170c150f0d0207061a0901030803010b0d0609020c07090b0d1e02060c 72
    0x54624400981d41760b10005400c9045540301e20b142c040720341c0000e000300b030302030319000184401503120b48e42c14059001512011410140004c445860b80290015111080f0690040080204035940303a0b0503040c2c02c44840d40345004810714412144140d541c0d071a0f0454160344800600b042190880c20302d0345401201010301038a005111140c3c6d0344d480005041d601190405d854448250b5180051520f03150b6130400d500c1904003c0f00c4040c8040c200340d903940c901e105510401c6203080c3c0c0704c01c03a490b0700819100e00c103030300102e048030440700408a07500a440140780c3c01c540f03881c07003002e100d40e1100001180000b80e10405001d41507281142d00b81c00d04214842c80140160b03400450704031000c5a52341201d503542101c40d811414080da003510040706942c11580c800410f44018021101a00c0020584040e40610341d00040e011300700e8031005644424a00002130781d1440e007405541c0c40130b4103001c645078181c100203140b645203075001000d140d80f0b1480b0f00b01c5001502c0d40b00720182e030007aa08104859801304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 937468821 1250 937467571 937467589
    0x141206010b090f2101050a06140d0f02120d021c02030d091110080612010c08010e09070909080306100f09170106030c0b1b0c0108040209090109051002040306050f25020309 75
    0x483c03000142c4844c94040304c0b800c5036030091000c0b100320305e40740c8103105000b5048888228110251a02c203e40c2855081c404160310401c4e0009600200e0704807041e4503c280403510800003002a0200d8000343d42c142e000b800b128903901c41c0d00c00168000d000c101d4240e01c86800c00b084071f90040a920003181c00c1500460940180f103400c05000c80c0c2040300b13024160800f25081406501143c00800140d9100803001700801018070034001030722800408605e1b14041440f1900040540080400200d011858444810b4004462241c0305109901104111a0262410400c0c4074059524204002c0c00c01c4095602e1101500004e04190343e220740c0070002170b00c840c000c1c0d00a80052801a41c4840302c034480b203480c080620f03000c28a150002e04c58010a030341c021501ca13810580c100c5140d4a10b603201800e440c014410306901074003038400d406840100d40c0c420340c001c0040d01d002d8407060000795a00c1d24401100c0c501602e01d4a2401d00442d00074a80141c1204003401105c558415241740480311000128954 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 937470071 1250 937468821 937468849
    0x703180302192408070f050d0c0c021003090b16031d0708070807051e1c061a091006080c0408011113051e060a020f1006141206010b090f 60
    0x1c114400c18818114584200b000c243c55482e8000c0c64100003c0700105040000340c509414450780140102845020f281641c1e120f00c403503002085600d440d0f1600a01000c0305003c164090341704d04200c190058800c0c001da034489600b1030700811350b80c1c407801c6082813103106101c0b01400b00b60340d4440030008034607000c0900305d02403503a00040000c6410b1a50071402e107540e0340c0c405070142e07000c004204629141d46d0500c1c103003144c094002c516881740d05800300d4181900111000c0c0c0c14207404e0038003810031100764081000b00140c0503414454090280900c01c0040d801c2d6039098110010708000c02c0b40900c201e40c0203511030600c9034240c3c02d0a40e0360900c0c9095551030000d4001c0d003071004c00e0712040b0319040d00e0f02c08000e150403251524080c0d03d014084000c90702001450b4020074000820103a581d0003080040d601c1c00241c2d04a5000a00d0707038174006c2c000c00807030141000600400180e498145440c025240c90740305c4007005040320744d28151004100342d00000410350010010300e2120042e41d1680c440c81164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 937471321 1250 937470071 937470109
    0x112050907151106190b0d060c121a2701030f0204110406050702190b121b0702031c03090b0403110111030106050702010503130605090a11030309060703180302 70
    0x2903410207580b590214810805201089000f0754918040500064001d1304418050008101076000380d010101034a2030721040c3d600f044161102c0c400b0080c05d61300105484001d070b5901a4050780304040303d02030751810300c1100140c0e042d4616024640c03521a041d0340d030081d094500900000010b01d81c103c0c640109074030540700708001d100c0c40c5045d4105401403091420a40302d80071f15250031f028029185026402002c0e0264944a03c0501c0184007441c030f20014048180c03c40c4c2c1c65811852515010940031103e10f11491300300d01a0b04080c140003015a4046079000300941b40c49882c88003814243d0a075508507204043c2c4030792400340070030045074a05000d02d01903540c8900c1804401109070a45880030880c0300701e210108010011640d00c582901e95403903091030031030717566190400003a040301c011080103405680303094240020b5a800040000700d6900c90403000503602d20301010180c89010309201c45070810010065240002c1c401d148051000e030000b504200d5040d22600482d92a0b08085619080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 937472571 1250 937471321 937471333
    0x105010f08060c072013050c07050f0a030c0b040f060609022a101a03012c06010303080a0b04021b060a0b0a030807320303010f050409020306010e0601120509 69
    0x740310801c0c01103d9002c0342048980c0e180c0711059481c00480d68000c1d0580740107000e41c58550034035035110050458031072040901800b15003040e81c0b80c45107651041c401290107100d40041540340305004070780c142c8911b81540f555a6801200d8503814104070004008551030315036001355100096040c801c210262180070340040c0c90303944505400b01c043d80140a06400207804045e540d516803800600b07004070070303c0a5800328010070030325002000490001c0f2003d9255003402c2c0d214a01c2214030801101d5000340e10b802d10800d141808241c0d48858081c00b010700041e9918001810512307140c2c1009a01c1c1c140030b0401842d000944803c00220a960340491040303400032818000503c02c1801115020801215890030003842c43e0342c1d82c0d40e94828501c00a01c00100d0052400c154000b20000654054100c080a01c1d144000210903482e80d00c00d0090850202c00c402001c202e508180c49070f407202b0356018000701516401c113a052511440014251070401c140c50309042c0040c05c0710b001b004c0c0205a04802410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 937473821 1250 937472571 937472579
    0x5090709140613020c1b040603050111030a0606050a08161202031014271008120d140121110d0b1012031d0a032901091107060515030105010f 62
    0x7a06a042502c03e440d003030b0040c802580711103000f14568040c203203209a801c21001140c408035010742003552002e40f0395460004900e0b4005511401107100710040d10040024a071280020b84031030207030700c801074002012040000c4000c1700c40d600c4260f11045a050501c0c0d00303100307502c4e0304013640c1c011500b10b04c0342c8244120801000c03103042002c9001c10811104400c0c41e074251080340b14501001c12030844044001c10201c0c03900d010181c0500c018105100c00d4401c00084551074800991105450100c814074003d5080304040e0b00200c128181d0b00001440380300071142e5280031640c40d0490f031054031188841491400c00d9584c081d90484818400c400c1411035103014100c098101c02d80358040d00e00843c0000c4500c0c000b80d800150900c110003280000c2002c011041301180754842d1a40006129000c0c011944215000c200d490140b00c92949400391056072722162084190744402521a1520405100031030020b40a90445036102500320b500580388a59000003d094171000c0e41300480396100180144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 937475071 1250 937473821 937473829
    0xb09010912050a181d04020409020402070b090601050d0218090f010e0d020609010903050f0c0a06021b0c010905010815131503051e0606010305181c0207051e04050907091406 76
    0x50103103850400f044140c505000e0058600c50080c00780908417105001400b10356503039000160480e005802151181d466140c20200400c06444050861040c4000081ca51400c014a2103171180d005e4150040b00c08240d00e0900c03071440c007800981240c081d00c80e1828084109102d01d80240221900800c44007510345070103418007001401260091b4100706421000c81c0c0c02004a03002c0309a6030000c25900c2149d051994100704680d00c00030846030002404031002285410789400421b0306000740e50340c82010360015615941a4464140031072910070004141003040c0c0b007000c0d440000a0030070403100000341d5018003110b41003120500440c00c881e4052050100401404540c58076a02c0c030360f010244400c10309aa6070000604460408da1103200080c0781c440260000030078401c820302200d24078141e5003081c10040000d14000c41c014440c504000505290079030711300f203041c01d100c01700d0042003c00c002400b0160070004c01c0410b2501ca046400a5040c60600c106402c4c42c09850080d00c490804000308 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 937476321 1250 937475071 937475087
    0xd05070f0b1f08120405010e1801090501031707021e0f09100915030f06111c060501030b03150115050403020d05010c0f140913150b1b0109030c0b09010912050a 70
    0x80c030b10f10743c40f000c0c1c2003800c01c524a046030295102400d1016103140c01c000000c5a0300320b005c2108000054010000032481074640005040e684503405444110085041005032800307805006076002c010b8a41038034090099100e1012600341c058050100c105020010924052060f260b107074480141c401c041240d403c2602c518904803204440c4201c0b00361540d00e80710560380300300300050405662256000001d81e011400c440001d1100c4c902801390004107202c99009100611400740424240100d000c0a4a000300da44141c4482c0c100260070140d0a10107496000c60a1048217411301904000c04409a62410750007049035112b000003040301c00c9427140060024100d00d010303405020403480d031000c01158103002d41e15094001c0e94a0f809402c6010360007009019a4031500100580400d000701d400c2d42000004c00c0c10300100081d500c00d07402d1840810303080b50840e00000c0c0c0040d0300103190b5400200f0032043d20360403403011000892100801d0326407048107080300e60300d0f20108100180080d002a008014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 937477571 1250 937476321 937476329
    0x1b061d030109050a030f02010b090a0f0c080105010c1410110304030e09040b1f051306050319020d0b0403050706020d0615140301060c060207080409090201200d05070f0b1f 75
    0x1c2c05040007640d2501d58550204000134103001c00c0c42190a200d074403d5002000e8290000c0400740503081210003000107046d10130403448110704024a8020150007224030b24100c802c1a542c203511481d40f80c46921600c2600400c90145001c1d5141c000302d0038200e801840381d04201040020340e207007020b14020300039001c000c0d401405180b1407800c1002142141e030f0302c00d034000c0d04540014001d508a000d458030180e070f690003c903400411019032540e910440d074004003d5510660031280d002c10b060751140041c1440910081d481210600c0d034000240c0c0e100d20280e0001c0c401d0510b1802c10740309a0303032201a6006002e021328459a04d0780704005220110070034407070b0700c155400c0020710140081c450003d544814003416090011500100c4108043c0754101c91035075030010f01c0540c0b07072034842d04494007a000805007680010000c0412a14064010b000780c0c0740307230240f40d00402c040e080c050fa0a0319a908829025903280d01d0f04a1081c0102705101002d078800d400040e079000b40b041d001081c00c441c981085e04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 937478821 1250 937477571 937477573
    0x405060406200a02030d030c020a0c061e080411151b16050108070f0f181401090b0c0c0f0d05030307022104030f0813151107150503131b061d03 63
    0x15a0001688000c5a1450794082c1b034600400c0b80306002d00c090b0f00d045c001260081c408064814006102031f4041107041200c510800c1803400940b0b0010101d45920090f5400740000404085046581c50029080c441800c01130300030a017811400c8480c40070a1a180c2e00d01d41ca00e80054182d0f5105002e8910324001420090902c50241e00780000e00400c40410540e2010a1001c11490361200d00d002c2d41283c1120448081803002560300c412014645100c140541400b003141000c0105428003034606889140d03442c44010580341625104102d250050186070b1034010300d034220480041181807008521400342a0000c0c01031440c400341d8800d0300c42d0319080c250000a024030003070002a5400801142d15900900100d0301c0b042608006881e5080030b5201c41030003440e00072000081604091076040d44106402943d059a68503c90210940324803001c90000a03801c10014140a1941101c4c00c4540e0140c900711081c3d0701866016800300400340c00950100303050f1010111110083c0026650340c0d00b00794 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 937480071 1250 937478821 937478833
    0x9010915151d1c020f031c0908010501141e2d01090e1e0a0e03041d060604030c050112110c070e0108070b0a050f220312020f060601050708040506040620 67
    0x5464003c43d03000c0d4241c000c0c86442444004001d41e03408020443c08140c803403286490790704000201601c4014244215022542044000104040400c005005aa0010707103060119036031815120320031030110000c0c581c01490121207490510b90f620b645046400d07003102c103407556240315001401c00d401d00d51282842c0d076010b0041002c10045608010010358982c0c040354001d464074600701000d0301e250f400d603818070710001c24001001402181d0a080c20b40300c480352a036664035034405002e000e100b50b0102401c0200441402c010b80e51180d85101c1c09010342130710001d026500320038204803652120388610a5507010781320a00014a040f1003480c014891240142580da1502c0024981d90150301d07603210074480080381581c02c100062088541035901e5040110790340e580070300308a00c40b0445000541e04400c0d140c3c08817901900000d07660900b81c081c10000c000560b10140115115070050008035803100061000040ca601c40300080d08c00707000f40f91282041071061003c09000c00c15922080f40c04c1d03900078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 937481321 1250 937480071 937480099
    0xc12050715050126150c072904030e120106032103020c0615130e0a060c030c021e070305060a050403030b0a270902120c01080a0b09010915151d 63
    0x8203030451036404d569903024846000b401ea40c200400c443c02c44410440082c03c000c440c1340020003c0084034440e000b80102c000014100d880c1b00c410300c28950444000e0300313000c50042401030858510060004200070180954490002c3c01e5405545c0110b84490000002c0c5a5040070316015028041c114035045050110030b00d24542e0f143c8010b0041c1d0020101301c444013500d038442e1980c8540c00d45003c0390600c00000c00050181d9181038080040d80d0244c45c0141012602e4441d01135a0b07814041903000b0654050b145070420162120401015880c0c4104680040016000d0026900c90398410000240a01e040d04025095980c04035045100c1c28204400713001e20303610944540002980ca2525a2000505003a254002d00002c03030082e602581414180920030380000704010030300340a07642c0d00111f440700358a090584880312a5254004c0071800140184c411651002c9003403810190742c00302c41c65a1700001d20340c5904e850f0b0070000199808a200318110524039105183d1001650341038040142 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 937482571 1250 937481321 937481339
    0x606010f11101a0d030215070c050a030f021609090212060709060302070245060123070c0602160f1a0d0905072916120c120507150501 59
    0x10b800d0b044000c40759200003107580c8904962074540f5628001d421507106404500b00039543d0071860000b5407280c004080041d0240d4031503042e00612650003002002c00c00441d95054800310785402030386045203d0441528850a01010300b0b000420850800142e001c950340184001d80035844840c0c41d456001c1c006221700e403507000c08600300f01e822604d00140c441a0310720018440380c111031082e140b0600d007524900703800d1654400303071103000040b0000c0007154190b10055031311b8082c0c1101c0882c049090360100911064081a44540224902c000310340713011019501c1c29024002d82e008080140d200c1e14071040048200c0d8400d00240c002c417602d84035818a8506002c500110300420045d042c90b000c100c40400b80f802e40c0000c0c120a90110984202c280c0b10740b036009444154004421018503c0d00a00040302142011104d128106260310301082c00d40c0c1e203a034a0b40c0f4000d45020010861a14125030205034100c913000000703829543c81e15590405414108201c411345803040c00980d1070140100f10443c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 937483821 1250 937482571 937482583
    0x3030306030a0f08090607031d0409020913030908060103060203010509070903110d080d050c0a090608191146091e0909060204080105091603020418050f0606010f11 72
    0x280c010701e01d99000f80b0515020071540920700d02e96401c1100407528404058020005c820f9100f00c40c482480030821480c02c20082d9042080c001e50000105404070344600c040e0304c503d0071030318083d040c0810030360364600100303113884001da1050742e0443d800300060103145464030034030380c001140e440c08130380590a68a400d100808146040c92084103640100170800200001b6200c58044205041201c4e1501d401e50040d40d038045458080010f01002010600d14010b40045002d0804034060720181e905824010000381200f140300b40d030400040c46921805803650700f00030940e9207220344120301c803a8000d00986030440e0050381e0341031400a403c03611480340d07400300c0d901c070480728001c1e19030040303200441c5012810001d80c0c01400000381030040c82c0042c009503400a204507164900200403a41e5000251a00d40c030f803540350002c0e00a0300c10820005490141c0194804240c1c08070880c0c1d1a88030369440310310700b40c00f41e1000300c610782086c001c0004940e045800b849243c44141000c540808503c1d0449440707013 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 937485071 1250 937483821 937483823
    0x3010807090c11190201020d0f08011e05091006230a0e010e030109051507030618110d06061e09050f090901180c030b33220b01080603030306030a 64
    0x25512140d86580034441e40c0c007894821260700a444100c6010100207984c0c400160081e400f5219641031503484600ca0061341e0543c4015070b8a44d001e40c0d00300403421007526100d0000c1c10340458040342c0803a05a0380c50703600e28003c104846401110501d0090046d002a102460032090020540d00c140c4480003040100da06003039041c41d184008944810050712459162944140c0540c64402c428040080000b03460080c10041d103c0a10769a031868422000c2e02d81c03d000d080710f10b07141e40c0c4940c812441903030801221840300000301d42c20400c840044c0c0c404c646181e4890000211070003403140300926041000d2420039194541055958101404140c642610450060260a0020020b44002c0c0e080d401840b419658031000e0340048880d007080d100032170007400140c0d00030580c500422240003040c0f640442c02c0740034090140f4001810000c81030038200f85c408032500003407810340c07802440000c01803444400503242000030303190101000040050b14010946c5009a00400c140859a40d000031090412 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 937486321 1250 937485071 937485089
    0x915040f0f0b0a030b1206010b1b011503290a0207021c0201050f0f0706020307020d110f10050a021c021801260c0c010f29090114150f07051203010807 66
    0xc0240c0f5801b0555820300d401170281c2d00d0086000120311150301c0401042d0070311010341d81c030140c22102214182260030300800b0b900400c1107030702c0c20000125008204050a801c0c3d43d2900c80b0703032100d01c000400c811803c694862150f640022410110320304584494503480d4014a403a550030b145a002916510401e01030016410011869141e4089540300703d50403d030f0310400030341d00d074207000030065a152100108a00428002407203441803103800281d207002c01d4000401401c907003d406a40100502001e4180c441c4070f50208185118400d2200c80051601035542006a40362120b040702c1d00d803014042980d41c10081807001030110012050200c0e0110041d408010045e51034a0354a078180e845100b580d0503942d404c040d1104070154450f0b01400411010540c5121105003807105103524684507800d030380d0702c50071010051000f091488501c01380603401601e8280d0926000a607021140c00c92201e20f50316110001c0d803a010040240040e501c5e00340c88045043c01c42d410850340942390138581c010000c0f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 937487571 1250 937486321 937486331
    0x1061116060813050a080406092705040204020c0609150a110702040b0409021009030b100305030a0e0a0b131d04052e0905150f13170915040f0f0b0a03 66
    0x200d82c2d490306402c3c80c1550141c00c03907100030080d00d8440c1340b58001d4820f401c003040503140005031081202004100760b59100505040c00c00030300c4180742c02003601600170b0b60080d900780039060180340c0401581c2e02605081c0300038034010784100e081c0310060304010714410045044c418076a10406d2000140d0f400c0d0381d411030380440d0840c00384000c030b0001c14021201079840f070f05829003d0407141c0c1254500040e43d004808038000c0360303203a4240001e0041144001002f640c01000b05000c1c4505c11181607652800041c8902d00307060351546000080c1e04808030540d0040c00345981004004100f0344450b00304192000c02820341e1900c0d880f01030b00c0790f0584400d14101001c3c583c0680b85200443d08450000d204881c04004d0400982003044d503e40000c64540f481e003a07110045a6465510100144584100460041c00c0074150f5204140001072801c0041c0c1c84806124058042c0e80d1283d01f400c04006c41110141c852340b908000407400d0741c90b40d024508444c0c00100034402201104111004141c2509000c15 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 937488821 1250 937487571 937487581
    0x121602010e2e1b032706050a140a0b130c020706051b060114090601030b09160c02090f060a0e0c0301090e0f010e030c0111030609040209090f010504030206010611160608 74
    0x111541200982000501d869a803e0f10745444a00b0b040440301282d030104514080d14007034682c40c00691111390000c28260703000c0c0c0000746068004603484410080e021540c0c110001500f00221810349000803202d80707854034901c0303d04106013641485031024000f402500040c00d000783d1a20741070701a900c2000346c0080d0381c2d55010064044040351303036804011181e5a60750350540468807060711134101c2c8200302c0003000c01c0e81c4c1d622034000d031290031000030003000d0241c07601d800c050206180990740106011500242c100941d0302c40d4482441400d1440f0b41c5901032500c2400c01ca085100c41d040794200072000e40a101c07615210b8000d40c0d0540701c207400b00003007201c1c54000341340c640040c9d120b9510301c0d0741c01e08403802e24885000c4042c284100564000703200340c01c40e8007074840850004440d80303070f0820b01072400100949041034000d900314070030340241c503800440d07619030501307403241210141d0240e8050380041012030340c44102440c80b1400307480034000c8001ca4000104914901d07104620804c06400c0202e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 937490071 1250 937488821 937488883
    0x171b0409021c03090e182d150615040b2502130e011b1e090e0a06080705010e031510120303061a07020108011206020f121602010e 57
    0x1c0031407000561000d942c24000c0c40d00404114140c00384a1400100700c1c0403500b161403030540b003140700d280d260103402205a00d010761820205003901070107048407114020010b240d82400205240101900c01d000c05191081c14000c0060b00920303510329903982080b00b040040314400543d00d12180e015542c1340b040003a1407040304840000c02002c0c0d0b1015500c43c940100354500c0c0c3c429120142170700c0080c0701c101142c01d8240c12104541003854007284084081c0c070290b84903418040c03000046400d10004040d1600c070441914a4125048812181d894505000c1c4400400c00e15000341000d180140440c1c1581020980703480404400720003944500c2c022946030000700f8800c0c006003a1001084104040c28100140030382424480c40118803446800f5150700d070b000002b1140a550181c4800c0c000c4c3e403070040600b10b503100f40c0d1410ba9419500b8442c41c030710025103c0051203060031043c07a8400604194a44d0f9100a0103210f0303000c207680c5030400000104002082042c0406010400082078010750b40d000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 937491321 1250 937490071 937490089
    0xd030809030405090705070201020105060321070510111e27030a1506030b16140c0f01021c05180d03241712030411040207060e07030507171b040902 65
    0x36948064940304000391709038080041e01005000b40c0c0280140e40380d10050545032075000e91900045c3c40e10001054403c13400d00700a1500b40d01c241c04540440e40f1150b070f00c07011958854244042401e0000709078004495100c02c01a0700250320810614121603d4000088441020062070400680e00c0200e105594180701414400307030400308036424541450307240c0006003904d00081700c450100070003160103003440d0628000094641c0d100c0d82440f904180c0891110b4000c020040f171a84103d1a40d514014804e0010740041c54502d1400100c18102145200c10350b90000d100400340000001900c000b0400084e01c0c294000441c200003840d007201a120307540250345a4580320035041c003240002014002c48100c0007801c0800c00980c0c0181c02c040c078104000748420780340a403400305c148a01c24290320703060f402406918032541c03001034041e00b0145554189850780e40b054400340c10a50003000030b81804844071385c030708030401c0c050588a9101c016410303100c0040c4100768066582c03140b088045440b65101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 937492571 1250 937491321 937491329
    0x111010f050f01051e09311a070f0905040b010302090a0b0406020c1e010819091a0a020c030322080c0715050412381006020304050d0308090304 63
    0xc1480705240620300000c0482c0c080c0702d002d0040d02001c030f005002c0c401e40c052004100c3d0009154420a0300c40c00c0168500c1c103030040c2c007200c403031500c2c44e51a0031407203004607040c203802e00c2410b10b00b500b07418400b030303014100400030302000500010003800032603203030703c0382040c030070b0711000c54000800892810041340240210101c560308440035103004030300c0c049900c01030011074040d0f40c2101c81070740c15a0144850100d11044448504200d08400c15841d800b441440c0d41c400d80001390034002218080c50f060560701c100c513080d14a0008110b980c80c0711007036a00c150750300c00c6071440c09600d003407203101c000c5d03907248401011038080e802c400c00c0030380314a0b604440c401855900300c8030264441035001e65454882d40c044c40b501071000c00c0c01c4a001d1000d8041d106541c2100c00c4c02000f80b80100194440b41d4030a6002c6010220821503c20b440d04145000401060800101984c4004a01d03065a4803460349000f90090010f56100740020011544c4111410740e80951502d4451400e464404010745540a2600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 937493821 1250 937492571 937492601
    0x806040c03020d0e0f061b1b0a200306090706020d03050c090d0305030115031107060207020d0206030702010b010e040204030b07051e161e050c0d020a0503060c092805011101 76
    0x1820413500c030000740344030181c3c82031030660750301c0d4844207041920b450f240c40b4000180b090501c00c0e6447d90300d20340d4040003a50058816200086070555400c4c5440329240c105011468024a0310300243c00c04106550380014041d000780802c0b030030301e08081e680351080030719003003010b88450006030968504c1d401d403030a8110242407441180d5081c034025140750024041d42e42c09400313085201a01600ca0701a51030030300481c0c0c410303614108844c1c5408004c0d502c00d01d8142d8000346028070b4440142c0380d0300700a51240d002d55000140d48400e18000404100e0301c003000c1445030340180028801b141e4241102500306d04a406c000c2e658008103d5072052200c084002404640e9000c40d2850b09240c6001c4801030840c402c0769030b0300f6421a84c1c540c45001c00d41d0304001801c9030340480c03640c3c0c400342800285041c81310f00003404204003aa031400000e1a202c011290846440e601184801c82c1c1e08121140310351300ca180d041304120700004000c0441d812649403084a0402c600b036114000e10300420b610034a41a12a00d07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 937495071 1250 937493821 937493831
    0x2030315031c09150203130312020102120c0310050906060a0e030f0d12230406050601050705030301090c030c0c0b0c071a10030203070807060207030b180318031c0806040c03020d 78
    0x11401406080c2584590414031100381c0144ca0100c0c80442204c14030351490000d20385060441e00c8540d0304644c2c01c440350041d0340d420010111000e60943c4510b1041501e034030825900e00e04458004c40780f946c01c1c1d2109016000d0354041c441d0701e079911404c1d280c2d400c00750329080350001c00100010740f4022210540c102d26002d141510f440c01744e032105480980d01c0b4142e000707002003030310035554004540c13040310f007188190003074004600000d940d43c00094101c00705150644c1031458640f51941180c5c0b00780e20220640c0e68074030a14220070713054040d00129000e141060503070b0604540341c042d0200c000510040d01c085c000a41e00d4100116035980c64042c102c3c2c0003c181d403900c0c001d20314000f81d0845001c240c0c840d100e00d100000302d1140008a4000303447d22a17000d444200c1ca036941e0303401182000740c409440400410400c88000204101400504115240306005900c0f030f0402e050508148600c01d508028116202c0c11075140c000705559001101a600002c03820704040b4110000e014007485804030501344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 937496321 1250 937495071 937495123
    0x4030516060212071704030f050c150610081612090b070f09080d0203180f03030712120603020f0904031716200d110304091e0b030a02010203031503 65
    0x7039010f046002e100c45091500c1c1c0d16003001c251140d1504403031204101c00480000760020303220b040c80b440203800500b0b260f8104580004076508205900240c20303204c12030130701000560f1500d0310310004003945600b0002aa410094074900300c165104898006002028006503903559090f0b10414106030005900d0340c40341009a0b0081c404d80000c0305060005118117408074a980c80814680302c4040c29070000c1d4034014603800516601000009400e510507000521407410352400c0c0000c00d035461056502c0d49008103012800380c060045040784084e400e02d030642c14001a10340c15a190348450301110880540c2d502c928049800a8a804180c1160301510043c0700e290345002c90254840f424985800c9081109040360b0039121498100c030312091341c00451a01c900500507418003181100350803e0701d107015101d400c040709a80e076000100b0009500181040d898049522504805620480c081e042014682c0c000070350301c2c040070300300407a50412a1208100c1e40e030104000d2810650401180c40c80b2000c1e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 937497571 1250 937496321 937496333
    0xc071713090506090f070207050103240303080f010909020a031713030302060105040f05091e10050106020615030303040507050103050a060302130f180b041b0e090705030c180a020304030516 83
    0x1650001d0162501e200441c5c400c6035610300350342c0310b010154020540280b501004401800c808688046007138081c0c01600e041c40c040b01c40050146000ea1640e04082c1440e019140010348142e00150a0a1030a00300400607640c0d112070038200c94001306581c6d81c00c2448400c0d42114464100c400782e031a0101d4500100701500403401078101c54045604100c10401c0307050140a076030088a0300d2007141c02041c580308005640d41c5400560645013811140c0f240f000780e02142c00c0322000e801c910050f0f480350042246203052a410780c180f80000707801460a42c1090342c3e540380c0d581102d006003030506031100005810002113612081c01143c000b051446150000c1d2600f000400440841030702950400019001400c01103401c41c41c815442a0700d6062560b40d900e541403403045113424441c2513140000005651a0300c06c030dd0b0760040f840c180161624915201c20140b03480c6900c1c566074014503501075281003855944200030750100c04c40d5030244c0d41e43d50b02c0c070b0704a40718400c000720030091825040a44003480030b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 937498821 1250 937497571 937497581
    0x1050103020f010e0a03061a030304240c052d0a080d050f0c0403140a0b0705090415061b0611130e060105030c0a0e30060a050c07171309 60
    0x1000340d80701c500509100c2c0c01120714481d00012543c00458540301000041e0703042d8862040c1c04900ca000c40c1c0c1c0c20303a4500020b0f00755401917022820f46079201c81094000b0b103c403509410122143c0c28007846d80b030303c1e03a590036440e40d110900348c22032200c070383c4c54032030340b040350b000071081404c1c0c5134001d4420b8180f1a2500040b1504181480c0e130b200380c0343c40d00060f650801c5e000154011303038450400c9810940385d40c0c1ea003000c4501329104070710310f07003d01340141000446680303116010b14660340320140c0740d1100b0000d110444407141c0f0304103108400f0342010400e071600700d42e141c41e82c0001c5e03502c2d40d15806940d0800c00003a01650303000a0781404d000034101640c1380741038403c90640e000035024500030303141c210044400c0d01003a107600c588504200280841d29000f00e0300d4a08484025016511210030700280c009241040c08080000c42d0082d42044610342050010580c0454810300820050401000d20441c6028001b8024a64280e00e44c01800c0d0742c0342d20044d254000d150b620020f0300c2c079850f02a0b40303024207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 937500071 1250 937498821 937498823
    0x603100203010609060e040e06010b030c040308181903110d17040605130603060305030301051c0f11010e0306040b01030803190c0509270c251407050d08180f0301090501050103 77
    0xa0207501102400d45454028900240700008c010030050342403c960825940c0003030140b040c9604100000800160001e001e8420345191804009981b101300c400e2003c483e9410660f120040050303001480011070703d040c0070f0340e4400242c1e005500104c403440c2611580e9001e8080b91110340300860700203401036100004044021071440c1e400300c0543c3d590340c260300380d52450000402a40040c070060085041400710442070b40010801d2246010098985004581d10034100356801442c886003e40d84e5600032280080c100029401403100340350a407100154600d06000c000d0403410008040764544045540444500c0d0b02c01030100858446880083d150303510594102e0f01034031001c2ca160100b6008460720340b82c80410061100010f42c0c46201a490315800200300c103002d44891034410a01e10344440c9180e0100c4e100300c41c0c840b515050304070081c2c90b0101c1503000c02d104a456178181000121804e050b01c010300205203690080c0e20091002800ca40010040d5a4044d0b1074410400c2c188441500058100c0e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 937501321 1250 937500071 937500077
    0x706050112050d020321060a0b400923072303060616080408030d0905060a09030f0804020f0d20010201060501020c1504090504080712020c01090e060310020301060906 73
    0xf40c816000c1a078890203081c004207808130303450b4005981e40d0700914442e54000802440480c180d030719503070b0808494000b904055850407a0701d56040c01e4200300e2643c01b190100d01301c034500c0c15001c501e42500504840e40245034440d41c0710440c04088030514050050002e4401c0090041442c2001e001040b6014000a46a0030110024003e980b0250352088034000c042c0070708400d242100028094003820a511021500d070241000001098907060001d0080e00341c0340900402c0302c3d070442c02c10603c5c199001d0180d01030549080c19800000340c000440f030450f108541001a130b55640ca0001a6a41002e01c600c6900100d0740d10039407080000440806c00d1f640a007000c01c110056102c0012802c0742c03030768010b06015174400e615031600d83c40c080d103401c801340f5045400f01c4d1900744c07148062020303504182d8048500543c0440c0100400030314450010b034918561000f030002501480000741504540c0c0305105200050b03801013900d90700c0030700c00e040107141c2c40d40056649503520200107180306201d100341800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 937502571 1250 937501321 937501333
    0x7060c06050c030f0c03131e03180819062705100501050306070c170708040315090c090f0e1b0102010b0603010503031207020f0a050d0e0402160305030903070605011205 74
    0x280b02049003aa405030f07090301d030604015070341c019680c4600c6c0d0018014034107008001e0803500000c0c047d080800410024180c001024409520f00640001d4400600d00202c1c910405c0521008900007400051030b1070820b601072540040e03060580007021603101c007048401040039847c0c499099948100314481c8954203c0c0d119500c02184501120020b000d4190700da0401408150400c0c450700b03071407966501408040343c241071150f0301c241c0e485d8001e100403520f56401090400500156401090610310004170501c00004030742da40c101c4400290048448440d9a1500b90410050b15817204000b113150030b0403690107812180103e09200c0c00d1000f594010740c04c1c080007159600b00f030000c2c1d030b04882c0094025820400d50400d140c0c07005000802440452140d02d070814501c00c0108011201c1d9070003400581a68400c00c00014440c03244250307e507006500400c81c0702030884c06000c40e0b001d419014a0320548a40b03030ba003012821440344003c0509000d00b004004140e101101d41d01200c1c551080f03046400b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 937503821 1250 937502571 937502581
    0xf0a0f03062a09090518060411120615010c140303040f0b01050a180209150f2125030b0a090212010501080c04031205040b0309010b030c01053907060c0605 68
    0x2580c03541031030055000406943c070030420b00d100e0340c0040303801a11b0f82c0460104500c0d6041d41e07600d084070885040c0c0c1d9208008600124500b000c44030050790189110103004140b8002500e00d540ea51060041ca04200c40303044004184588500d0744103084c1184000e8aa4034141403c8c01340d0642c2c0346003000d9501e0400b29000180b0740c0340c44410f04045803500c007640b0700e100b900c075851180250090ba04207604440c0d0a06030070548600b5900900c6000341242455807036185030444501040f0a1584405031288035509020404090701040030100894001540c50030880d280210090100341000c00d4208078402400306141c0880e4000d026001c00f20081084240ea9a9004650104e400c0e11403107010f0800700020700225004000d0201a0310751402d299150030780d2030300c0d00c18403a4021103014020341d41d10041c0e039a20b0315041c024020b00c0a001d180c0315081c03010822090703c5082c0991440b01d1802c3c100442c0201c10030741c8088441044000106540c242680c41c00301424400095a00300c40851401c00021 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 937505071 1250 937503821 937503881
    0xb0408012c070b09040f0203041a06030c1c031101020406110118030813030c1a0103032303180703061d0706080103080f071103060106090602100203090c0f0a0f0306 72
    0x6010700541c1c0001c22020345070115414450744000945a0003e459110010303200c0320710700003903001e540700c0c0f940f0f40020032050f50880b140d6400506200c0c42a000250140040c0e42e4041d0041d01d07400960b42290f130413500a1078240c807900780b100341e0a0155400414000f510365040720381c0058107003000c4020711105021001810302d00061040090101d0b10380c0c408501d118007612020140e180c402e0038540503454403922512080e14541000e07800a003200d10040c03042690000c110303c0c1c00f4100c0e509460700c0400d480322244a500004020041c2600f50800419407204104512401560865410412030301003003006c00403000034110700c1d1043d01c40c080d8009000e80c4603600e154100c0ba00003290500742004900d1080c0158803002085d034040c04031400c485030b00d49d410f010b400c1c02840c1a86954400d14980100a801c1101826100f9000c80c4140f0410019200200e0344c1000c028046480c12150480c1c2e10008210701401e82140d0100a100c001c04000c00106900c0308102e94807000c0070440052071600c4503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 937506321 1250 937505071 937505141
    0x1e090803100b040b041e031703061003050708041415192910090e0906010f0614031b16031d0604140d020604050d060902120c15090303040b040801 64
    0x1c13a00c0070b00300701c00c0100181008202044031040720b8003d2003140d6036240c1078180b012500000350510800020b01c0307403d15062482403007000f031905081c070881c5425080a08031600c001c0c405000c2016180e4004850b41c0c0a008003411002e80380c0c42c40081d030400e16925a0f4000c0d10385006105507107000d8400d442c1034462600394081c000c880341c014604c0301860b400e109108502503244014410028008102c2220f0000c29600c1888170900074240d40d0f1510008041a130003980c4460300303100c00c8942c59030080d9690f2085030381c410907041102c0701803002c20100e82242e110300c000301c500300080515000b00b019440b0806042c1035586c40f42913942c0c00c0109040164510581c030400d003140290b10a464032900789880b100c051180020481c40c2810783c1c40300800d43d041008682210151747d584283c208503d018613031440540900760040c07914228a1000c030b02452003400304104541004108424155030402c00c44020341034902401c0e4035581c0d9003801d0303400303004540c80c81001041040c101c1d11303200b43e1401c80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 937507571 1250 937506321 937506329
    0xf0f010f1d071806050604120203060106093014030c06070915030c2001090501062c130206040303111c0207180e01050403021e0708101e090803100b04 66
    0x54401285060b002031104030b20150b028403c3c1d0f488410000d610764440001c1c1000b091180400025144207204242c24104160881028420040c00030f001e064049401e408400110000024090510030b580221410301c24030010580d00c84804aa0034907440070010b0407a000c03002c812a6890345036030000740c0e511161030040458000e075808048107100d21a8102030f030f0040e11800c1121500e4121061404a5903680b528007900341c0d1900e0303054080003801d04c614401415500401d00c144010a4520b801420b400a134039511604901c010a01c8814101e9440007000d030f00a02c8107503580d03070703910b00904030030b40d4050f02e582280961202d246030003800e500d04000e030134110f86c064900d0506040d03c0759101e003040e04c5034905555980c8a681e2018809124450096010b90024518030f281c51108003961301c000b142d041d0007500803020411845a0005025800440114010a4610008a15204038102d141a03801031030308010b9081d00340070031032001b18060014030810102164603200603180920445c4030b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 937508821 1250 937507571 937507573
    0x3050403051c0507060f0905061f080a02060904051b0301031203050127110d1a090606130506030705070f0308040308090d080f040f05031801023c0f0f010f1d 69
    0x4130716030000e445503002591180e1848400035081400d07480311450260100c40d9203041984050307103442c0007c1000960401058074500914410207160701007040b60081c84c2055008580718000316800d51030040480665001220025459680d24103004803907802c900c50381e101080c5402d001055000510f10340038140ca0380301205a940c0b541854000c402411145075510910701c1c28031204042c84907500403000c6c0d0546450f2054001d02c0d403202008100c80c0098401403140c40304000039000302c51036800c100111042100e84e02d0304d80d903c07110300355024884c4101c010701d0520708042e40020540c00c003030002d010318000e83d192242544c4440200b643c640071181000081001c041c002200c4409009440d940203128a1041d070000840340d552529641203003144c0d007690380b40d43d5000001940d04203c0070400d1a26140d2881d803042d611002010310300d844101d0321070412a4008014085071042051201080310001140c41c42072035124518002e10100044560003030070301c00343c080c91816840070b4603070032410030b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 937510071 1250 937508821 937508827
    0x20618060a021c030c1d130e010506030c0910060302030a0f11070510020c030d321506040f0618030222060e0603030313030c12080103141518010605090403050403051c05 74
    0x755198082020b2209950380c0209006440c54a80c40a805400c08c042c4202c1c001103020f08002007014203089100841c3e60140d803514003003210210007412580d003204e0390703401c006989071903c1c12000090030340484416451303420b1410345000c0e00c04580c01080d0310743c068001c1d00c01c15411400039505900c680d040041c03041d4014003480c4281d07011940138209851014010391441902081145a1002800345410f402d03070300e00f0200080340c05540565482808112249442d0505040701100c107008a4001c1c08200320188038500c011200300c11000015503001401c0c0382d10344401c441c5084001c0c150b0003108000f1420b00c100019000e06804d1a01c0c040c1394010061821503660051003203039254220001c1d030401008040c004042100c041407444011010b50b1018059810750030b041903071115200356020315a224000d0000107000c00601c0716004081560301c4220400d00b01c50903405811550412588092040c06000800d41c000e801401224407400c00d940b00e80e403c86940b0208680f1140f440c5002c91810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 937511321 1250 937510071 937510097
    0x115020f070b0a020312090319020607081b16050706030b0a0321051608070b0f0601090b09010201110423060a050304240c020d110d0c020618060a021c030c 68
    0x81d0003c1c03c042e920b5881100c5c10404180c81d0400090815504400b19400005100d00d0400d906000b82103100c070036000034942070034100002400303440001c00c0c3c3d1030110400e0410000030801d140444030f1040942401000b080d1032410300c1900d801d45032003104040b17032414003600002d00300700d039003041240e4118120b6840c068075240c0301f08420b61000000c00400c07200b0445514203140303440c02c1d00d000601500809464100034500a850258042c0202c082e2000c080300300030300c980c1d1111400c0151504070311341c01c2e19515041d0044c0e01500406481002140000c41c020445182081d00000182e14841d0706003301803100c0144203091046c289540c1c0050003c00000380850700385102c080300031522015607840c01e01018032210031200312540f13420061700041c6460450942c407000030b0341140c10160141007144c502c5007001d808070310000c000034025200491201665510342400700c06002c0d014151580d03c0400c484c0003500d170203094240100070180340c0b010050041c800d10a45140c856907480340c050460300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 937512571 1250 937511321 937511339
    0x1020d0c0206100b0f16080706060602010506181305280209010902210903040b0301030b070e15090d050106050a15020106080601140120070906030605220209131a0115020f07 76
    0x3c02d00410f9400031b4002c01c9a4005121040240302d010700510780014040c3c1821402420f680010303007090311070980b40808108041d01503080503000310425524502840543c942542820341c202d29580c86002840040c4181541c3d02044040c0310740708448800f41c580c1c075200c0f01422401030740807800302c0c17400150b80d9203030304803c0140e05a0801c03c01070440303080c16650005000746503c01d0f0811a103040c040c0701407180250300680c03107443c80303101200e0054000c1020b110310a028080c90140b1480b91504442d00020b00070290310079070180502400c0d1050751500e03000340b080f150b554502c2d0900150f1820000051190000c188981656030705003007a01c404078a8801160003000c132100068900304401c880e060340d1901000307454000c4c20344c0d401c04181c82d89036042000803030b48002c00b84103100351000720051490a40b503541101103641110035203581d0301c48003068a0712200703100004104c6030000303070110100c0031800c00e0700c3e0407160101c680070340124000c0000c0740c9660070304101e5143c5a011170010300121300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 937513821 1250 937512571 937512577
    0x11b0803040f0309320d050303150d0f06050106111506060a050d0c1d0603090d0c08040305032106180c1804110703091d0105040f090501020d0c0206100b0f 68
    0xc028500480380d1030f1502d0104000c0750003503085000e0b005e071400d03800c00e000d01d90070b12201e40707113600700c401041540c0c5944805460780700060440c514541440a00c09203035070f40441c0d40400a801401031040c3d80c95610b030441c010002030081c04041043c00b00c2d4850500400580c0c581201c1d10108220602d40300d0320117001440c0c205600072001d114041c0020080c0c0041c2d803140980048069441c1c0141c2260201540651035181510b240540c0007002008405240045c50028003070851800891346051410410000e02440d040103281d400f000a00300100e080601000d00f00c1240c02c440044203407264810003542c0480c840301c03081140e100700300142a043d144c10161510804011004007068003e10004040303c010f0906c0c01c00070789000c00c0c090145035000c2081c8001d0203404c03500ca8207800201c021208441414498544903c3e100c18520f1402140c507000582c0041c1e204000355100c0c0d03102044d41c2c01420050903c0c600501c140780002d4415050302d080c600403501d035030071003520b000501080f0300c99541c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 937515071 1250 937513821 937513823
    0x8240c0d0203040303110a0306140102011a0607031107180b0a0623091908010f021303080f1608030411011e0302070f0203030c030c071401140c0a0b090705011b0803040f 74
    0x11b6461a4404d83c3d41811070007410900450369000a1312802c0c4803924100216520340241160300d4143c0c00084225028070312802100c044503540d407134510314541212408541d400514460154210000f00b030986405841d04500c0d01c0030003402400b4902d4103101459034188117400001c0c5142c1010084035011003160000a40c82c018400c0c035005018010542040d481e000d20100c8101d1604c1c02c0002d0503081c0309900110100600540c07501401c8403101d1001c1c0810301001e4814000020b0001d80c0401e807100b150016035103041d030981e1040761070418207056002141c05895049403105448207070341c8110006404c20030b82c0c1244031048a055241100250080f500071110b04290280200140e0b4042000e0450701c03080e00000c541c1d1354a01002c003400e1040b030350300130010050020881c3c4d20503078122000346a0f500744104802c0d10f50160300c0031549429040007000e08040708000600005000100742c07401600c8003a202e680131028440c0304228228518000600000c1e000d202050000f2042c80b1903109107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 937516321 1250 937515071 937515077
    0xb130b040f0c020a06050f1006080c070c090614040c050f1b060103060b010219050a1218060905040b0603100e040309150f080c12012d08240c0d02030403 67
    0x540e000a03444102e50706082c600c0c002d6072040c2d030000c081010501529500210700702650300b850400141c083d012081d2400f401040c460210300080c8116002820750b424a074101d003131040c0c443da607141100300914042c02100e6030401c88104001c0e240c1414051300c101e92020340c0d04d00f841d100009100003003580002c0514100041d03210040c0120b0101044181e001e1805081c0c000ba14070740c410000391801d041c215070140c040102e030304a0000306102040e0900c0f190703000340704802035818980741282d07410305000407184140900d900100d00c2560040c1c44406a40c0d003500e040012481e002d04000c4a8042120305000b80c60030300d002803180548001c1441c0c0c100c2e1280c10300500c0c4c030303407503c480e17040e4519070200020010761100d800020043d0311012542d0060315055096150400c810107035542d0410501078080e00c003c138181c01101c80310004c200503001141e001e840d044002e484002c0e060703c0c1c49110812400200843c07040b074903c120032183c0603018484400007149441e40d4003421b5006904000c00a4040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 937517571 1250 937516321 937516331
    0x106081b0904020c03221706060108181e0106060216150c020d030c0515151908030f030f0c16060b0d0f080310060203191d040e100b0102010b130b04 65
    0x5070403042024006c0840c80005010b4a001c82050040700b40604d44e00c1914500c0c2c08001030001c000012491a0300481e080c40c1000300e5030303214142c40c04d454800707400da00305a104003010000780242d29600700f01060080c0300280081076a40d80c040385d03103848c03a0507500003c940d020001c0104000d0410f540000d40200d0402c02d1515006400148091810140c08c0d40420b40981040e02003010a01001a084070403d004040c10b0800e01824041d400149040030700030708504402c00c50f9100c40103201c500804c10b250031203640d101162580a00d80d041540d03103801c1c035450b09001c20580c07540b000980386604007041144100702d0b02510340c100034080005220343c201400425030700116101d105900b06084c000c5141c6c80d56400c000c29890812019a80300e81c00719002406074040c90340b0000b000c1e4140900c1071030716448a20180c0225401c3c5581c0401c069805031500e02030081c219404500300191208000b4100210203400005a0a9a20f100328a5900c5525440181d00100c5198080341034480c020b003000036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 937518821 1250 937517571 937517587
    0x110921011104140f1f1110020703090915032f0a0305060c031008060a020a0f08070912050312070917030a02030706050a1b020c0f0d020906060318070e06090106081b090402 75
    0xc03000402010140020300d00072001d00091004c100c5d8507500c007e80c1808618102164038001d00600c3c07540500c40c4601e80b01e00e29150050a03000c0440e0140d500804002c51a080712107100d81103400301000c052058294443d011114540401068226500100605107030795600894121070790005003440e044001501000c03880a00811403039204120402c001661044241800f030310038100403081e6010400c90804200c40c243e80300000c40f0032141c040b4060f41c00144145003090442c040d00e080341020401038800c00c8604c551005810040b2404429940940c0c861a003890340c4030303c10b003550040036a004010303420001e2802e504c065801a0190000126a41c0a014500d805608031951800582c00702e4000a080c6c03500c0d101644819000b00d440203c1000b007980454903030040201030510820f000b0002602445425404841c0010070000352501e0740c1d207810308011040e80c241d68071400b40801100100c1d0301401640b1280c080c044048044520048042008045512017000140c2007502400520 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 937520071 1250 937518821 937518859
    0x2070203031e0a1101020c0d031112100f081b09180d09030b0c041212090e0406090c05010c0203030304200a0e06030c011b0303110921011104140f 64
    0x41d040900072030b400c1c0c0c1d104550079000300380c10021507900c0940d9104010710b101e070040010b510355080140d82404142501c0884044401c0c1c003808a02c200014a803000304058a18601e81d4013003075420123803031001c406440b420841c3c2d4900c210381c42c0c585800100801f40060380b03049071300329900424089525081000c454007560501551920100129182c18820b0042043c42040142e0010000c0d45480c1003a140800844804000c0c400150648a4104580d80414071a44070306010740103820145001c2d00b03044c601100148102c02054400e0482c0d0034010499611801c450b00640348c000f0002d600b55151520355018046404080500d48000108080714940b0380008080040c90b14892401c0c0504c0c1c02000e040c1080c1c460407070b65042188034211404020540d021a015098040c500040d0441da4025916142e01c1418501a0301c02888010718060070b10540d031304006546002c000380802109612011068000c03070081504014000e9030b209081d08120104803500c1c3c01c01040d0100c4c24482413011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 937521321 1250 937520071 937520107
    0x20409060203160e0a0614120108150c03040b04021e03011b02011103060108010e0a020d0627090c0605070305070204060f0e010f0608060409020d02031c030e06010510030207020303 79
    0x110303015500801080105040c080d0210021016410942e081000803000940c0b152060700448090003001c040210b001034090007030f212041c08145480c3d405584a480c46030b0344503030840c00400708202c0309000985880840302500c0c0a10340c00070104000d80c0340ca90030015500f21200c15a0074540743c8241d2a0b03c16502401010408000e6659154099508400090039a1005020302a04810400600219990046001381100e0340555643d1542d00e424450340701070b20a1071000880603040601c0070516858802800100c440c2400f002d0b00c8448003040b40d01309441d035100340035015800d0940c0820410340110001d0000724480c0c90b00601d07040300c69000030103e541e0794018080140c3e0010040c010700301d4000485000d0016020401c0b101e074508a401007075080001c2089000b60384880c854021500c1d00140b03c1c3d2180e5005040e281403c0d040300d400c90982d02e03039100c0780c0006401e100341c00300e04810209005050310000b424524000d251711300203802961282000700d030544010030170700d05d00c2003040e950 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 937522571 1250 937521321 937521323
    0x201b04020a2c040e0a0b0c0c15100f080c1e01031d0a020a0803030f04030f0c02030615010201050c0705190816080703080a0227221d070320030a020409 66
    0x74021070a21005002c11101180c0c809801c540c8040703011720204140d4820a5484040485440e542d001c03604a046e00b0b0540000d904001101e9903001e00080c1244c1110701c5c41665003003250460740d981e840b80e0b02a6200d52182d0700d2500b01d521481e284501e048003d82800f59a081810b01140a405a91031902d140204000144d03240c0c00400d404011494090324000080007203400450960a0404052840010242c801000e0203001c0c90311606042c003549400840701c2e0000e0540701a403500c0700440f041c45c5d00284682e401540303014001226050400c06031410300303400c080142840740442c52030ba410070342c24030016500080d041c010400c0490304034103a00c1301c2e00e1060f074850f511004036142c064407085001d40350722051401071004201e4509090910030f81e03042c45c0d02c070311001d00e0030035804224601a24500c10180000e50750254858003240d40241c0c20603410020204000042820826142d42160200500ca5144200314070040110b1240b078825808006003586e40d27210301503000500b101c6010030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 937523821 1250 937522571 937522637
    0x11b0507081209190b16060b041415060c301306020d080c030a09030c020402030106020a03110d020607082215051602030a12060312201b04020a 63
    0x20340d40c0d070301d0905503004000c0e404600441141c0314140300745e05100380100088400040020600701d014000d0b02e810916500314064810444804034000460014104031400740f041011052440c05030b003480011a40f8240c01c1c0e0007d00108942d140c0342c04050200480c101c0e214036000156204180b001e90000c200748180d014200100c5403270248007900b00918102e200c000c1c0300920b001c12210883c00c2007140d6004000c11000038a242e0b1034603003945c034402540c00103504903202100215140d80c0004650300007601a0b151200b094034035584043e6241c4450640100503080138000c11204e034040c2850940080068441d01c0d41a4003c142c04681c08005903c140e400580c0c50829125101d1140320721a00f04081d656a100d6403100c903c4041e40e244112045101000000c4140403484909980250043d5900c01d000d0000d40340c603000001c00f0400c000503d014203641500451440c0d140c0080c00301c110f081c0f07010031144000e80c0202004001c1d0880d241c00340500048914421000104c05040d50011320500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 937525071 1250 937523821 937523827
    0x1812100507120b010f1116030507050310051905100801020d020d0606020a020a1401170c030a0e0d0e090709032f04060b040b130f0b0304110f011b05070812 68
    0x64014600b9406512400305203281416859103039a2103030340c000400e8801d003000c1c0c20843d0290200b40c86c24020981c0c55000005001c0084100f100c049200000ca4000700c08540098240f054803c0c1110001d40e29003205035400320710030f41108926042540d10032010310805001c20f5607540b440b4266030020100c3e1040d0760340081d12000c840c0c0e1520a41029045a01c000e1041e076006a000c200782c1c4500c0c1c024880a002001c2c1da04019a125060441e01c1c84d90002c14030500e41414200024113800a940302d004090500c0460110094001080e002a40e415524042011581c4061290003100680b80368208100307034002202043d41c61020301c0740010b81c1c01c0c6800440e418140c0c14825150021031140c400c1e41004410014a1984002d40c2c040d1460020825074508072480345500c82643c513071001881d5a008000012540c001c0360241d88224000d8905d00007103801d00e020007400b401c04e070010a000c210340d03049a0025078540010700d85004c0c840c00803512140d0701c401109281c2000d0104c5000680703000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 937526321 1250 937525071 937525081
    0xf040b0402160602030a141611010e010606091a03090615040b091f0b040609210c080703031701031707030c021f02010f021911031c09060b030a03020318121005 70
    0x18451000c7c009582070300280c0718200100d40148081c100141301d02004036401c4d030203048038429407010100000c24402000140d80c0c0b00000703061100544149404101c144130303881202440071089a00c20400000070b401e855480001c24034854490003180354209545003420081601c034200303200c1c01040320694200b880086212801100c2902e500400003251081c003003005043d82108a0700c00b40c40c003d002082c00300b0500200b400380401c040d400507001030545400040c0010b0041501003d40e402a510540e6420310340408502054080c40002c044003901c0c10100c10800400024003480d130301c2864440581c1c3c400e600011f1645000408072041c205034500400c2807a50244185403041442c0d04d415400c2c0003a40400c6000f4402d441310311030a20640102690342450240304441c00c402d180002c9800d40455100c6260052500381702c220f404618103900c0c0c42c5145400284e0302d40d001d50550041d440e089a110201d2107010400c02c54680043d0342c2802c0a04403242802100500702070404001018946 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 937527571 1250 937526321 937526341
    0x60f0c062414030a11040c11030f13080c090a020a111e0f060f07141b0c0f011e050c0f0708010f060e16030c1709010b01020c03010b0f040b040216060203 67
    0xa09035050340309520182c015400505600c01203200003008486c000354103038404405032140c2c1c42d0380030001040d0000003207020b6030b40f01c1407001c1c1800e101d03441c40340902c071901d80d85000c0d44c60600e00180c0341d004d1113400005415116079001040c1007910380c600714403922040211307185050380006c1507121070456060010010b480c200403100903800184010140360521031500307001c405010b04450208408898868031a41d4413404031011800790001d420b54943c8046400d0b6110301d64180503e2103092603c00300015580300b1041340c07952425602074a03c980d030010905850382c0d400030303240901c68028650302011403e01400348030014060303003001051103041c840034482103c40300d400642185a4a00a1060446080c2d40d20741f010001400d00103940001d20b00203480065030031249002e0100c1c0700342040301b940307419000344a0603c02a021102017980841c109402d9904204c0c0070354020400d00f020b0121403a09030030074801c03000040c10041c0740c0440318102da202003208030380035169250000203000803003030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 937528821 1250 937527571 937527599
    0xf02160b09060c13090c03020f0406020a0203070f140405100f030503040306150308120601030207021f17061c11030303040b0f0c0f03042019170601060f0c0624 70
    0x6640e024a441e0070388990340c4005404e05401a040c140740d0356200200424043d03030440e180c40054046c0d05488991743c4000a41d80e10140004900a000b10800003032113244201c080b200307841d403002ca030400e242d04500900c4000c02009000b02c8000103182e00c0004c200b40030702900300180d4000d00c05503540c1d0341917080c134400351900c1c842000e01200001030304101007461401075500c0100705410040280c0c4580d00100d029018109029600110320740d01030089c078200c004500403603040750300c030784ea4800c10703403002d9092500c81295800d40080e00742e8028141542d074800000c818500c1450301e00c54074480980840d1654104442c2155000e440c041404040554040041e0384a00c41c80700d480c0c42d00200c502100300602000d0002414040310140d034440310703486415414182d650241440071444885000100244081d104200000c02050201c44102001007580c5050b1200d030b441c1d640701e00b00d145800b05c03000c1840b2002074401907036170001060340d11020410b9492090360324101014541c200080e211801c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 937530071 1250 937528821 937528831
    0xf0e0d080a0f030e0c01020c060a030902090a050105100807020c0d080c0f0c18060a050d2f0f04090b04120909060b0406080f1003060e2125050604060f02160b0906 71
    0x58441c0c51015600c6c6c0c0e0014403005003141c25120591201e00025040d4090003a0b10710003580f004a610400c21841d00e1075000b0360480302c003215080c1d104904401d05440505064401c0001a003290391604100c0c1080100864928884c0c610189040c1c0141307042070401c0100440b0214503000f10075080030f1480c00300101000420805030000d058201607001a826400510a1500901c80c0c084441c0030b11030040800281550f4480e422030410f5402055840549207404000384121602e00c0c0d0200746041070304c00c00d488264014034043c6aa101c0307445100d181c0031a80c12282c1003101c001e0010403105420301415000f080d00d03000342501c55003006405440b6110050034002d4907407811003040145150320b0600b1049981082000514171641d81e030b140c0c100784203951901116000201400700c032074501d8004007540f000703003002c404403270f00d00b1001d5003c0122a40009825640100c0c0071070081507160b403181110303400c0e0800042c40c0807480b0414081401c1020f2081d1154140103007080b0004609000d49a441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 937531321 1250 937530071 937530073
    0x51006110601060c0303060302030322090902010806060c031b060a0f021204020121020406052a0a11041805060a0c1803030c0510060807091406010f0e0d080a0f030e 72
    0x80a048003070381d4210511407402086501400c035018940282e0100021395009400c2d40e43e07420390f141145a250700e1416600703181e41d000b40e0f8009a84240d512403409543c5d4142c0d690300e055142c040030441590010708807040c0501081002110054078100d4107401140503034090405850035001d80c900f1150b4400b410183c0c14010005801d010f00844000f641c01303035090a002450290418000214447c81c032540d400340c901c00078021489a400c172010304408009103120910783c000c190902200c0e00c0b0400c01e00115544003d039128009122610401c0041401070700c0000d4000c410004e5405070820724100351400d41103403080c05030b180458020304990b03140509014000c3d0104220404500c01140f2010f0200501e8240c44410810280401d901e8408070010500c045500c62440c961144940d00c01c01d01c9003071030b00000c9034503030701070315041407180302c1c16110303810142e0b960031066030a59035001a96610100c18407a0b00d000504020191030700c140b856641e50f9014114400c040c0484c0e4aa10035000e117 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 937532571 1250 937531321 937531337
    0x80901020703090501080a110301080106050f121e161d060f0105040b0715050703230105060708070203030904090c0f0e271f090309050409020f21060406051006 70
    0x403c0c1c00030706800c00c4640070300c0d054039299162400c220040c04260148254030100100000e09024150403480550300229890007c182da44010424000c44200c0f0301c2c241174101034140c40c0d07104022203040d001d482488003aa0340111031000318500c0600550401500c40031440d407440e0a440004540c0d540c040d200395881900381881c0b40000e4294059442000b4480100240b01001c11440700d4a840180c8544c080512481c100904042c0c0038001c032103800644101411880005070398503000e080d040314005010240b0301101c80c2c88035000c0c0d51006509030303010f2000b0042d0301d090362074510071108000d024a40c041c40440c1002009290b481c040d0340444410481c5005000c40c200000e6503140d820340e16412045810742a44810a00303019200316510340c2c5104015000075116015004200aa8030075038072104803030380710001c00080328002c1c50065007000b110040c0410f80d003006062000b099174160a030780c8034010036444540c640303c41101d08070b50090b162000c3c85030941c4d58903070710301c00f07862907040201d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 937533821 1250 937532571 937532573
    0x1218102d140a050a061706010303020607020303071407020f100e0306010b04180506220e330403050f180a08030304031b02060f0f0a080a020f09010804080c0105040c060809010207 78
    0x2a0080c1c010300b041040d2641d400200b40e404d1410382c4050001c100d440143e20203c0c3c45d02e40b800742c56030801d10042e405400f40f00d00081c495032021007100d200741c9d02500e950660550240034511241c00c03d00c0101d070811381080c45001079a071210540e40910b8120b80d10050301c2c2200b0010700d401c002c03042e03002d034031070f2401403005122080d03c00c00b050480d00b0b00c066001600b6541d0f02d0001e0046600d141c10f14004490803520500455241c0d0001c00b0024980f60442e80c50700012954070320840c103005100c11100d261104410030450404180303507046406450040d080000d80c00c2d14210503171240440c1c0d602d010210349014914140790216074000d100f014065400d524042d140078050000c0b440941081c464050301010441d601e10040c0c0d941951490704450b141c2c1c003c42104200c55201e000840003081e8a540000c0741c80c0d2941c021540c06030464058a420240b42070b005450881c030140048030521010b11159807100300c2440341d548954041c04903032020030300e0120003078100040a42942070690040264030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 937535071 1250 937533821 937533851
    0x6060305060f0f0406031a07090510050f0a0908030c07030b060a0530060406091a0103020a090b0f060f0403031704080711040e0618070602031218102d 66
    0x20601da40c02e46101010f0007014002500610300c90300006c04d00b550714041e18401600c0c8103400e6100703802603203810100c03585403c100043d1240790003180001503c100444481104001d029010303004443c01c2c0f0f03840c826105c0156a00f10742100e032071340c00c4a902250040080c0001142010340181050310894086428480411401603441005210702081e81c8220405075001003007000d0541801b400b40e4146017070a00d48180540040d10065035448a1590300114503644442440d040b254010b00e2041454644125080078003076650301a030b84400d0940141c1e920f6101c0e81c00400200094404072035940d8214038010381000c401006202e2111280303020000007440078402c548002d60046422840c2e4540c05002401406050f10640344034007810041c490744a8074803443c6803140c0821020389001cbe503212441280c0d0382c061103d0b0407248002840204601e01346621020705000f150070706035030344510201440015070300e00380a007070081501c00390881040303000d490352400300b07490141c024468a00070440d56 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 937536321 1250 937535071 937535089
    0x30b06031e030405040b0a09050a1a180403030b15040905011a0406050708030c07081902060a090206090d08090a240509030a03031a0a03151104030c121b17010606030506 74
    0x25030049954441c40d1b90240e4070b008100e0001c00341c0c514180004d00d04104a10b01802034907500c103696030344e2400107a0b81854042d29400e445204a454038003541e8454400f10003812055a916402100200c0c20610720503010300244068031460703030f000c0382d95450481e41d50900116a40100c0f101c000500c0140505684082100e41a98202c1c00d0141c60351506510f401c050710824100a0420f4400510300d81c840a110a003d001c1c45615001d80b004c541d81e020341c1c1400c3c0d4491b035070001d500004c00c001c1003490b8a4501a0b01c9821406480d9103410f140142c030108001d513030182c2002c10071140c0034070038058007411000030280f500160f00d01a42080405008203136500640c01d4020189a2205500c00802e100845000c0355500003d01e40f12015030740781400e00140c04401148500103040005201e06c0c050540d003200d0440394009030040c501450705100c04103c511070f1074110340c04041000100340e19180f141a06c405001902080c001920039070303450501b140c0b815407160080c14180001c01c8a550386c2c5800c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 937537571 1250 937536321 937536329
    0xc0e0a091107120516050d0215010f170a3f080c0912070605041d01030503070210050d090303050708090a031209060f0504081225050c0313030b06031e0304 68
    0x40e0030f00100d01403805549500030f0319142c50030075408207909405e11000185003200018543c00740c40f600c9407204004030070f0400034001d10750032a504d00020840740c4190481880e211003244266840c1170043c0e654603043d0221210318014032014012007016800c00f031101c00420510034913007080e01d110380740800360200d80001d186800030740b000b04074411161101c044240ca012108003d83e051151198006080307900f0500450003103070810088403040d54420300246044e00d070020021414090540e00700002180389001c0b40702041030501c48140058428001e90035412720a440c040380c9403420010041c04003200524401c90b6500446042000c0b0350801e0f64003600e40000030380850b240b035113414680083c200c0502d80d00e19003480c010400c014400368501030840e42020f15015415902c032110200c00d0301c2c081380741c0003860820301440c80704841d0180b0006c190050801d410340c1c0c10320390300009103a0900400c0d03006031200c2840c4000c01c500c40c64240220911984900541c007140301003910580d5407030141d402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 937538821 1250 937537571 937537583
    0xe1e13050115080603010e0a0308090c03010e03040519120b1504020703091a13030507060201060f031109041109040506010501140408490905040b010215190c0e0a091107 74
    0x320781345803029003100040058000803941d181049180c020b01e546c4040f9800134003400384142600c030b5860180285d06c2030040c428010350030329040008022103071b005103080818142e0b10b280300041801c04001ca07401ca0b240a048640045c0ca00740c0d140510411801494910480c410080c1d02c00080d0480c0e0404152201204044034a520b82ca141d98544d00c00c1c055030f0100404180d01c000304101d0f00086103001c2ea2100d074001d1007003950740c042c45c800340401c1e400010b082400903080d1050500300820710950143c0680324800d03445c84480b008c80c43c1c1c00780075602601c20360030030801030041d96001002ccc2c00c0c4c0b00f030360f08003541c1ca002e19080000d5103485c0742e08bd5040c6501806000000c10003200360803040e580c10076808030307032003030801e40380103d0700e200000b0944001c0354250000081515040c42806104001a00540441040005030341480c0c00c009000d103019000d280c0211141b40d20b80c0c460302c1e00065054542000503803005040100c9100c00c0d60140300d02900309820744010100c43c4055804c550780c046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 937540071 1250 937538821 937538837
    0x130b070f0b0c09060f03100e0f0f09070513090605060a230f060301060f140f0d18083114060a02070e0c0306090f0601050313030e1e13050115 62
    0xc0310780c1d16205103183c1d03541c007550210b0340d40d07130500400f40111f024102140d03482d405c143d6130303102c28000c1343c0044405801400403400020107418140924560128010303085d1128030b03880d80005041d9124040c103500300e1542e502d0540e4104aa40d100721a0044800c548a1884600c0c0c1500c810001c0315181c950b59000a881c3e415094540710302400c41403501c00201000c2c2c403980c5590300103000341107180411000841d81002c0b030301c00350909003c84100355810070038113103440115000e141c054850100e15000e10b0080380300c1d400124107480c0151100002c0703801181c0603082424032095101904404400390701c2042182007107030b131403e9410011364490a03981c1d0354480c01c02503000d0b4204440740c2c0c00900020043c0b01000180b10342980150711030002164403000f1901c40c540646100c0c03070102e54003400700750300b0408100300f06050100c2100742846403410b00540d031403550228804208082d04401d02000590b08551b05240ca03030b0a580c81e840003c1c0c1c0c00c0015615101c02c00d855401c0d000982401d01441c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 937541321 1250 937540071 937540081
    0xd0516021f0e0703170c0d0c022d090106051b010e0303041209080d120c0507020102121620042702010c0c1d16020a02011709010b0312130b070f0b 64
    0x510440e001950026521480070b194001c00b09110f600841b2505d08038014100c039030703110034020a481c00d20150050318800811030090f0400c2e100c1c141310244012002007a1412030102ea5481c2c0e101806480c86540356911681e13070f600d00c3c2c0c0c1c08071000c03450b14209904046404903811000000d50f980160030003000440700c0040ea00507103003d003182e08209460700900800540c0150032183cdc8450b05d2011840400116041104c21501401015402401a00b02e04103541746c40450303c0c060f182e20001c9840c800011540ea80c1c1e07100385580c00b100c468503c090401d144c800a0b00d060b104041d4109000c0420001c03001c021007008030414203054000307040c0f10f02100405c05000b003844078100034045440981480d803001203014081e90000311407140d00d08a10300e030300d90384103403000c11411135056042e1555030704c9111003003c6201501e070003010441559a510074646665404009220101c0003800b046551000a00d01c041d040030320540040b6038440e27040180800003001002105419034000c01c209641e5195 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 937542571 1250 937541321 937541323
    0x311130c0903020f0114180d0203030d0c080f0c07030f110304080a050d171308070f050309040b030d02070905181203070801060305010b191413090f0e1903140d0516021f0e 75
    0xa00c0c1d00203502b41c880810fa030038440450341d002c0c4a22681503110310600765130385054640e421400300c4841d172203030109000c4040000e001d1502e41a081070141407100660300340b2901e5604d1900280e105018903440540c07410700380300080c000d00a10030300d01d1421a58248c48454041500680034180c1600780b20b2900001e418000c00c0b00070b5441d1b8513400034221101000c94101280d03240c0041500c548aa40b8110403400745160000d10780c2c000d45120b07006001c0c2180382c0700c00c90008000091080c0d6042c000d00388140040f0b0400d00c0142000c5020342d10098803410100001803084e80160401400e2514000040c01034041c4a4180c038440c1d00c80d44140d40100328461011603568500070360394044014081443d2690718010300f035071003d07521101e0b010007620303038840444000d80b080c001c100344c0241c005030481d410344a1448201908940203040080703107a444180035050782e0340282c0081e4013140e80c85040c042d44c1403100381d0000710194184001d00c290700c08898114840c8030b01e48a80050240da400700408a180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 937543821 1250 937542571 937542589
    0x30a090c0803210c1306031a03010b0f040c030b0406030503030106080708070e090c070b09010b1302340b070c2f09100b071406090607090311130c0903020f011418 71
    0x740490240c02d4082e42c1c2d40000d0050a2181c0c4a0001c419080c02380d0302d91401d05208075004c04000422216020b000c200c18440141200061103081507283c1200b1081c0352220b01588004520500056a072585054402001c80f038020300360b8010400c00c40e090100e103692109128414030000c50b810407140c0c40e0111950783c11702c2410070080120200307100304000c04e0019032201c08076a40948424043c82c0d01544400104e04c60061040c12003000914260f12402140c4d4550400c61845041c400000140d0745400580c0c0100b01c884200154081481c0401c2112450050300510010201c62100c503a540d2442c58840784101d20341401803250308001514805034140080c0184000703036040396201070904110b1003481d0042a84002c0348940c07000b0500c070301c80c0081d0142c03003640700703a1312121803e055980e401c201000d091600d560013203580119401c104510f01c503000c5802c00c03680307481450500d1881400106075007040121305200e6a1008810b42030005411940600800c0304518450040c0c1000a41207030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 937545071 1250 937543821 937543837
    0x50c031921060806010803040b1909170601050a0e0c0703030b040f0c230c03160303090b1e070f020c04050a0603051e0c040b150a0212030a090c0803210c 67
    0x140506196010001e03169002d0b8081c2c826030003c2d40e00303e0b83c030b0300c07001c5a072442180b140c0c01c03914404200f101100d0304090707417038192101c051500054107a511112500c100c41454101070580e00307d03800402803483c10074010001001d03115145001071528140c1c0e43c189004101018061640b40c4003003210a6039107034451402a04c510310104a58508040300601143d02c1e040010201d6604200e409210010b11040d9a07010140500851501c007094000420400d03a0700000c805040d210322000c400034a08805072b81c440c540c10740403441c40d111800404800b111002c0c110380d00740700300005c549048641c0440c00c1d0030607040913a0003003459105c260000d8000c10080e0300c050680d00406210028240e0b2a520048010300423604030b0b00c7e2961103070b0030030003190b00032004550b210160b9440c1c0c135945d180c100f010301200b92660046d920300c881168000021507008403080d100c01e580e0b030f902546c10030580072080c030080c10085008500b011307030a4801c00360300ca00c106165060080000000366030950754500f104c40368 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 937546321 1250 937545071 937545107
    0x503070e180109140f10032301110c010c08011401180512010c020d0e03030306092203050405150418020705031603170705030f0712060902040f0302010f050c0319 71
    0x540e500d40140e0f000340035102c0400c101c01080390100303400c0602c0c1ea485902803000e2107860b00070b451455442c0300c0c80d00700780140e040801030101d40050341200207200360050300e81400485540c80021003026421984100d0500c5c00f4409507800502080d0b07104c00c0002000c800c01c0c20680105100400d0584c4041100d500282d0301004980080d0b807042d030190041c4941010076000c030340e14088421003d680c42407808280e6030705a03105000040c920302c0d28054050700076080e12913141c040d031031858500024010214096011600c001010000340c02e1800b0f0240b10354241c0111503081070700340016817144c0d0b60340715692501940c000c80d10300f003400014000c4900d055140e4200b0259841c903443c000e0302610402c1d0040380310120340c80000c3d503030b45e01a0f0100c0c0e200c2e41080301c5e600555520b1f058151100710a9442c1960442d503038036404100c88510344003c0c00985a402802454a0314501c0014002000801d504041050a10500a02c0c00c00081524003d4100069000c41c080100900701c1e03608800801c90031007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 937547571 1250 937546321 937546369
    0x2a1809070201021812030c070b0a03051810020f070b0f0f01140607110118090614100215100f06020609011b0f0c020409060609020702100315060e120105010f060f020d0503070e 77
    0x240027000000c000858040c0c0742803145a55141941100000302c2030790010076003200030188a02c40e666070080c04004141e200450a01c199625242100ca4049480b64072400300700d400d010800401300c8ca014010a50a05e603410900a0240450303243c0c00740420040c81001d92003d003000aa0168802c0e0000d9400c884000780790b643ea80a03c04058045131007011200b500001e4686a030342046500c00d490040b00380c00a040010440c90031840da0360004040254419a5440110340005145016802421580d0041882d0b0501071405401c4800d4075051784036000e80c241c5003503074454105900c40d8107441242001d001001c80b0340041070241c40c1c80140180070700d00d44034000c619412070340d000c8c101c42ea000780c0c4e00b0482c0000f0b04c18160116000c9c844d10f136641c201c41c4102005898030814600e0f840080141042d8a280e2581030500c2c01d6a2089c0c2001c0001c114514080c00102c0d407110301c0903d02c0c8081c0c8000c01e000082c1c903e000e48075200c050070034800c1042c4600200005d454402000341030802e07200c4c00c610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 937548821 1250 937547571 937547579
    0x20c1504091404030f080c071e0203030307050c060a052701110316020d0e0a050409030309021002010b190e01030605090102070c15140708032a1809070201021812030c07 74
    0x10000d0116003c41c08550300ba0b44120165101b107035041e21946410b04810b141c0402a218004201d42c50302d01c14a85480300310004006072014000745008102c2074a99030b8a94082c04005810300a009060300002440c2404006050415492442c030f1010f50714090581d8030480060140034008400104a8500001041c020305031607902054004aa9503400d0386c01c8168065000c88451031240b00e140d902801c05c03917007440b440c40c0960026440174805e0030005a0103001d940454000703a0914113100241c1d54541c130400300b13402e0110010501d6084901000d61141c00c1810380640d0440601015049030398820000302114400d6044805150308500b00c000c0c410354400b05c111500016810000002d008214020140e0004405940b94076500003141800c56071201040700003842c20702da120020964603e00c1082c5086c109009220000f149010700b5891024003083c0410b03d440a010f1200310380c410004c003401045480c0e10310001e00c03401c03900280764031403e03403d15146004040c2140220f01175108002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 937550071 1250 937548821 937548851
    0x5070606060e181006110c0411070209131509061d06010602100e15060d080403060c0311090d0609020118060806040f0e0607081909030c1103030a020c150409 69
    0x40e04100d411103980a8055100c0c3c014a000c1105940710381080c8299641403000a0007020444540c18a070070440c2d411104001c0040d09561414400003842180021240c00751306003180c02d40d50201424000c0d102d014165a900c4038107442c1e91141c0034800b55209803c0301006507541002ea500102c06011403107034020b2207601a1141020321904000d48258800e200c000c1000c3d00407400c5010000010303101242d85001081403c040050809074095010309000000981d02001341025500611000601c181c12100c040d08540c841204c7c800b240c50140085003243c0d03101101514030950004000c103804c0410310040e2955400c200c0140e501c0b6500810109102da40400e1151103084102c40900c088112640c2e14002c460380314030780c103040340c2195000518450040300c00c250014400740074044400d04145081c400c450720194100c0003c1c1841c00b11200b40300160411035140841107000e140741c1001d0b603001075503c00079012000c0c0102602c201c02401c150101c1c0940d0005c1c28900c03401c1c8036080c0326440c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 937551321 1250 937550071 937550087
    0xb030a0515092221050a03180b060607020409020907260f1b0c0a0804080105180d0e060909010609081911010e0301090f0c1703090d030f0507060606 65
    0x11180440c28140e0350300c075629207425190b0298500783c04801d00809000d040d03410118041c0c1040e00d200304440300f240200d03d804003a01e2030142190352103c1e104c0558201c0102621055601390403c900070135030f0a00417561885005801200890701d450352079480d480800c004c2c0004440203035012102e0400c01606640004401c211f140c898482c034001c28200410300b0300d05000030703103140c0c18054083c2d000603146401c3c2c1e025007099900d01803440c0d05104032120503d1074050b02800840b5800c5000c1010000c00009000d102c0e0040b0320070618148005107083c1855581005c3c12101003000300622605130300c1d0301e0741412200310005c0a0b10000941d038403200d000d0b00030006846410000d12410b0f8985d003107000112024046c0e6980240760560303611000c07004441c1d2125860700790760305540c0e03030340c01d000000c03040e84401c1b01d05845012541c0aa42c5001d0070001405074002c241c150f10780003080a1811a40d0f102c00f8140c0c2c5940c1070400390340e8a040800101d0701c5004440780140400d1034440d000c14070319004046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 937552571 1250 937551321 937551331
    0x408030603070b1806070c080a05010c11031e130e0112050c060f0405040c050f22080c0d02091005060a020a021009050d300c0c09050f0106030203100b030a05 69
    0x1220300040d550943d004081c40303a100c1203008503ca0520a0b0b80510b40300000b485414000c0303034420441c94442c0308040c24141d490740100d41c0e80e951000d00100550f0046101c02e4010104000703142170515100300f07404e480080c800c14514655000030500e844159800c5030601030314050110032003e42c5c6504201c002e04030342240690b414856045445480d2406104039003482500258035401c10303140105100146c041c101c10b900500c9801c0c81444c4070b04d2003a81c06003441c3d200043c01550383e0542190801c804000302c0c3c10115594200c04910a01a11504111340405a05403016030342992240645a061542500400d5016200080380e0502c26400940011014022240404602040a81918070202074841e144d00400d402e0b245001140c845100401790140311842c1070b148910480e0320440b070f030503600104004125440c50b038600344900c03140c2600140031541c4081002c0c0c05d060403060410f2030148110030800d5000800900e8071404019198000e0400d8401240c0720b080c44404003003c1d21044078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 937553821 1250 937552571 937552573
    0xb0306060d020a03080a09170a0b221407050a030302160e060a05010e0102011b180f0e1611031c15061407031106180708060f070c0312050408030603 65
    0x41005440e16070610075a90790b00501048085103141e8940c4500d40001706828180001c008001070000c0503050700d6100492103501501040d4401c0c0b9200d454040c0c0542141c2410810003421390034603c03402c664480480d0000340300740711030219215561401c02980c000c541c125407000d100104040d00003600c1c10351300c2c00294400d0038081e1541d81c030b80c5c9200b86c101c03141035000000400410265000703002400d08560f040c8000305d802c0c4021070f403100c8840441c01c03000300000c1582c0c41e0095040c0014108502030039558010f44d00079031130a051070b0140d0300040e003042040080c2c3c04a0381d41035801840c08141480c85101034a8841440e9240c0e500c4d002c0307070901c104801c1c1c4e051940781032560800c1c40e084010741d40251200859405440d681c69080e8001c154120300713028864940104c88141004038903c202041045080b480410050480c00c26076160300c031044079404201840340003500301d80b050b07030310100303e02d440510224141021281c880b210944084a185400c0610052141c140c0045101d15010b034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 937555071 1250 937553821 937553833
    0xa180c02060a0b010e0904030302121602010e010e1e150405010b0f10020d12020909090f012f07021f09031101090303080604090c0e01170c15090d051f0b03 68
    0x2c266002c0d0b895590140d800035444500101182c5010309180340c0080c006c1c42c005003013000803104c1c03030300b0f401d0291103011142c01150260010755034240038007401100b06400a1000e00c0c0c0034289280d4070300d000e581050805085510046040c04200700c03e031a40f00c1e80303001d9982075003014200740b402003509004041c000c00030080d50600f07608100c90b001e610742d43d07031b0742c01002c0321042541d04490031071b284511540f8442d000c10545c2d480e940c480e260940151b04400c0034200d90204880d001c3d08503045912126400c0c0c143c009001081c4422018107890103210201061752645a440000d0010901d0144850051100358106102e42d0340309032403c0c16a4030610341c26085401400041d105800c4070301c4010001800d02d4001180c034101070700f11591080c0700c0c0340380c0c0d0615501d494400503400400d2308501045441007401c0404200c0803c0000c5030000b0666541d10900b40d0919040038502c6645856401034103070840030401c0240070010380103801070080e05514800c842d90b1030031010f410400860384c07081c4204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 937556321 1250 937555071 937555081
    0xb1306081b130c0216082a210a0b1303090602010509030f0717030108030a090b09010c0b04021f0f120e0303130602040305070b1908240a180c0206 64
    0x204a5010501402482c150021081c11072502c041c2503202d0384582180034501c24841c0e10402da14000025051580c0030700340d8100880d41c00c980e4030401d0302c0000038401c000040d982403911010518850300400d001c0c2c2141103600c80542c81c4c40c4c1020104000e000f040000108155501d81d050351528452295650b0010315564030f100f00c2c00c1c3c4605030781200d0141c0040001104e03100c48200240b401c00d100308000200007074035080030344039a00309074400040f0741c0000440700d041c00c0c0d21040032000b07401003402240c00c0888410000b8034040c0c90701001001105080040703400c0d59105512950303881180c415014071001110402040d001070400d103603002c900290a2525090085e001d8000d110390190020344c01d50307450b0201c4205d202c50003d810b460319a400c00000c07002c114103101031805810358180c140c0d078a440c40c415804a11001c8100013003008110020710072800382005045030100387c180c0e0038403458a0307120300184050b00543d100c681d5840300e460070301000864a400000e8450015001e560241e070791 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 937557571 1250 937556321 937556353
    0x3070b0f041e110f030a0c0b03010602070f061d04090b04060e0d0305130b0c0d0606030614040203040f0215040801021b15100b0a141812010b0a030f02040b130608 71
    0x156030014601c0400c1e4001d0f510310f0429016100900b0702c024212003010105449006200449400030104c0381c00010050150980400480740284114000244114942003004010311a140340c00052032003500485c034190741e5640c010440050708070403a103000b030030145066030040c41762043c01200d034040d00e54a10040741c0a841000c0c0720300c00d45078006070700b44040c0e912890041c0300101405980030f018400d25100e1201445101c000d000240c03400580d150414003c0025048000c40340391042d40108208400035882d440104060b0b070b415100300c401800c4549203219140259000144558804660f000c54803a0200c06500384a6606041c3c590200180b400d0050383d41048a11518242d03441000f0002d2402d9100200903021442c0b4050342d50700f9925001740080c1d8000d00e0381059680d00c00348085254a084188842e1050710f078802003200076002070206130b00000c41d10014004138540280c00d401d549490b0030203403143c1c40052540c03e02059107451440104480e000c7c003103861240440030019020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 937558821 1250 937557571 937557623
    0x2030c22090c300e070303020a1509080d0b0f1e120304050627040e0f011406010210020d230117030a0c0b040c0515040905060901210503070b0f04 64
    0x401e0340560569008058118581003201442003c002daa24501c0201e291010300004c00030710300ca40d000d000d42c000e507400c084220b810000311840c0715502d403001181c0014024411034080c00081440400c0800503400000d415060200103582c1202006000003490b4202c0300800d0005601202e00420340c2e400707401072a5481c000d5001e02500544208a0010f00d02c01940c205a000f20303400e4462046562610041400e0715166002118194098106070b03450600a01448624510205200c42c0d0303450480c0c0001e5441040b1250340f01119030000d0b00c1c040d40000354102d00c2c2409401121008101240411040055000d1290000d01c40f15580ca00c0700140f80031040780c021642e59540d817000043c06455078030706480e0140045500210198002410361680c100c100107180c902481180c90300d00c0d01c1703060340036610011f00ea60b1243c0c81f0040140170a1080c1c60000200c40d003181c0c00c1440f68026403500700c2c0b030740c0308100c000f07440d01126504000c00015440801032056100d48070485032400041c1c03030152501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 937560071 1250 937558821 937558847
    0x1111203010e04080f0403080910030c0906050c01060b0412020a090203090d20011103060a0905100909230115050f0d150603080d0c0e030a050604030302030c22090c 72
    0x1020810040012400075407100b900b0070301908400d0701c1c02645100d1030310b0f0350f4010380c42254503003404610800c40381b800c61a40e44400c0480d08083c0030f220010b86001b0003d0806000340c105004022503e107000b0134003540b2900260118516999849440b4041d06d8041324080e80c00302e00c100c4c200740f00402d81e4007680c0280c80c025484040140001d4070280ca0035200e113840800e140c07080344400c0045643e14242400b40020355084105010350341d0a0010a010000026401c00301c2400d042030f090011881040791010110340040c2c0300007500c18074615002c003081c2101010309407100b080003260828054194842d4143c0031207079080d900520750310024480703410500340515030300c11a000c1410f000700c2d100c0451201007a00220000400303507120359950a07a5041a160b0a280c580c4d10203000d5405034101040d402c0310a401c4000b042c100c961541c036103070b540b003000748001d00701030b000b03c0422003903515a0181c0d811ba4440b00384402125416002c80180c0504521422660906100c0c903800c2c014050311a010b82d030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 937561321 1250 937560071 937560103
    0x2a04082b0f03050402270a18020a0308131707090515030c0f060c010609020702030c010309080a03200403140d0318020609180c12070203090109170c090c090111 70
    0x1030010a5020b40c01464000c2050b80c008030705048503420f0441000600d1160a00c0c0c044180d003a00b4100c0000040703400110b074010351100c07402080c1015a8600140c00704a96004800c295980300c2205120b10741e000952152002010440c1540e2044d540410160217841100303400b004070350303039101610b0200c50000381116016000200c01c0c5055013000481402c1500d0040e100c0c81c900010101842d01312212603100f0012146d02182c10411850f0910404105e01400d00e014040300d6403039200d40519104086200061583d00c01c070084080492035018518000300b841420703111a9681081020070341c0d040c03c0c9003803d010b121103030600d01d4003e210700040241c2c2415503c80600043e400e000280e803280c20701c83d5000c0a040e0360341d0f0354041102e50b554402c1520005003629200744e00103961441034090100c0c42550410f100402069130300c1615801160038825948140c00940304c091810243c003825a1500300000d0000c014025000100a080701042030340c1d10700c0c02d014543c0280340c5031030681d5143c200d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 937562571 1250 937561321 937561337
    0x90c090103121b0b07090501180503250510032304080307050703140d451401090501020c0d1e0e12030c060703232a04082b 54
    0x400b62062000300c0311400164403d0303003d01c0898455040380281199508000790480c4028020795900c103098203042c402000c2a501c0050402c0c001135101c05085004403100c201c0c00c004103c010300001750b044010407004d841103403400448075008000e040810011910400017545250310f04003685103040c4910303000380100f41562034190040710994003100041d003c100750515040503072284c80d40100402d101e109400074190b16403906102c4240751310070b03001c0350a07941400b641070b001606880103c02840003601110a1002a14040b40d4954400403402d0a540c43e10b100c80d000c1001c15401041c0300c2c03900204170b03000d050a481045036a1100f055043c5501d021488100b001b0502858406254400044c01017030081100081140f0716000ad0038540d54031b90144013032205683c7c0611031240031405031140840000640304100c445001c003d0822645185001030004011116505420303150040c990841d554541e9000e000d80d6410010f101032056540401e546401130084414441e00c1c00f48035203662b070b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 937563821 1250 937562571 937562603
    0x1080c01080402060c0a2909030f070609020414070c170901050f07140d1e0302030405151f1404060501021c1b02090c13050303040815150d0b090c090103 67
    0x1513035000321010040620030302030384000180030150741c07010342c0e44e054410b804040078500480b071541c9005002c0a002d0741041003e1031504145170201d41c40309400c068040380301d042c0740c4040740c01007035020000148603007020140140d459000140500786402010070340d1489140c44100f0990340f240303060050200300704018603502c803400100a040f4a41c00340c62001e60340c103040c0044500300302c80d140b0004002003090080c03221074106046080000a15464110b0039468030751744031031f505c0030206550482c0e0154036000030311186417a10260404440028500c1d0155921842c80310080c0e0f452500c03c0c030a908214000c00c4035440003c0690045000086500200307088200a0382c2c1140e00c1c901c001020000c00c2d502c213002d038958492031409180650703540703903684004100e621400c1c0c0355500001d109410401c001c0000c10000a03040c1101c1c01c50100d400b0311030f252043c501f00051200718100390072028550801041c0080c0042451042141e281540d003000100401c1042000d001d01008010010040e941340c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 937565071 1250 937563821 937563829
    0x40b041107032304030f0507080106030803070c0c150314090102030f010b0d020405210613020102120f0d060308190c12031a0a140a0e010b04151202070305030105010801080c01080402 80
    0x105464611452608481d00f1010840b510359005400907907070302070500da59108103e0100015030040c082a0001c0209034150342d6401c03900e10000c0c0c4003101304104014501d0500c86172044000090000c0e0f0050130b00c000c440395028000e040c00e802c3c08909402180000780100406000326445003a6406003d00f4036820010400c0c2503402c48141600311035801d020101d515241c1803101183d0011004100403d06e0412017100c1c50840c0c02005c1200e0415600d040c0c0c00180d170001070300e01c031441c0c03580d14032502c40c000026550814001d070207484043c24241003002040c004003c0040000d104401448840c0c103407100000c0d2280b580c51f06000307040b50fa840c0c172450411842684510700099071562170319852100880080c103458459007200e0260144068484410300e0804004001802c02c0c4050794419031418050300c000c1d009501c00c642c0c0800a00003100e26241c03007151544242c890180702103440354803505004043e90001d00075036001c00c1c403000001c1410400000c01c0059000169184080390703540c1d074244 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 937566321 1250 937565071 937565087
    0x70e01030609051f020301090501080a0b160e150a0e1c060b01090521010c0c051c050f03070905130603110f0f0d03030e0c011107140102120d020702040b04110703 71
    0x140d5940c002e2041640500c2813890b8001075000507101d0150700c80d4100b402010440f101070b400074502d5400507c40303000146c04040b04a90103660040201100c00b483c40c011b0300e800384c0e01d010302540540b80c05040c0c1001d00480c0041c0240316440e986031900b580d05003090103002518180f001e1340304144407440d00b00140090f000a8481c0c0ca041c0341c5002d0681e92100401c0c1a50504040380e42071403500c903040d00040200340310f403441c1c034583e602d00310201c803507103813603550700c5124261801c48001e2010024400041c0520200da0000040c0503400d690307450000002860342c12a4001d02c0d00c245200d070b04820700300d003075402004180d0340c0100c40c0d09444180001040b1441d90b03950407143d0817140304195110141d95584002e00c8150294074041003101c01c0001c014180720550b000e0605128520315180301000c40041d508040e00d10860642c140300d418000182e25241100390702c80700050f07001541e001c00b80c515401501c2114070075501402030407101d508110503141120040180c0314028098180031a00c1003040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 937567571 1250 937566321 937566323
    0x507020c06071203111e070c03050d17010503030301050a141201020412031205011d0403050706060303110c031b060d060810150806011208181020070e01030609 70
    0x440d1a12141100440e1540d044110b00f0f070749007580c0c04038100c4200d030140155110381210600031864900005072070203a24803080540411001c0101d00c4004011405041002640d0000b08585c440c1c010b08a0040210315041c100e20a0f0044070301c0005000e05002080e43d05031b5100404188406d03041280840b44161803552496000b50050800d218100d020b100800240603100003010751030b0003504001d0048040200f00e000018a0080100083c0b010440b5082002c07071115102d050b1034031541012501c0740540d00300a03002d036250034000401c043d0410340c041d822031001000e440c50402c18004044d11088076030056801e0401c05011010107242c208000c026940c00010002140c60300d81c1182c5182c021407100c0c650140e6a210940c01e48546809401c40041000c08028000d42d81444441406c0014444004200d00ca004c90020350105c103240703501581e00c9000e02108500b102c8410003c0024850900b4103006111400c06550901e02c0410008280c2d108042c01108592941e991400209105a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 937568821 1250 937567571 937567573
    0x3030206040f0515040302100e19020105090a09140703060b03090c010f021009231216020409060f0f0b06090906090a0908040905190b0906010c060615021005160c06050702 75
    0x1070b100e01010304c0300748150300450003540148019500104010119032001c151880750b40e00903031a10070070303003100c0d204110903590a203000c540320406070303000c1244e0107001c2d0448140a13041a691421503d00f50040d01e00c541400d5600b071140319078442100240748020703102d51289070001c242101c010350080d100160580104e10464140100170b000d4841242c00580017114006080301e11000410700342501c111403a007501000c0d0070080d808851107141c901c101600070421341d0b5508814015555207a0007a1441600900d050291401c030401c50b90050a840303800b520b0f81490601100d05504029060b0b0b0050352026103a02202e4031a00200185418003c0c0200d032101d8580b00d1110000e40301c02c1c00342000f4060010049802e05102000a145900325071b0710301031083c500043c9004540d200c075180d80e0425020b082c00d86c480301d0b003410705c113002d08642d41018070385d114000700320480240e001a5414959610040801c6580c030748482c100c500900310243c9078006090461080042001e0b980007603003008041c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 937570071 1250 937568821 937568833
    0xc071e0309150302130b0903070611070902121009231308130e07080705031302012007090501050402030402220e0115050909010b0109090c11060c03100b0403030206040f05 75
    0x861a910002c0c0c108400020b500451352800c002c80c2d010307070040505034a00c2d1150811300c0c0100440da855942d485038004100a900203044903560a2060700c2c003420700c5001c290351729100d07082c1c02c0903003403416901d4050600c140c0c00c000482100900c56a119040c204040e10401e09120f07405403040340002e00744404c42c140b520200400151008002c100e1050801e034444490b0b0b240020704003044400404140c14004218101314031164080c04a9510011000d00d4001701c04442c0012104403020f01c0e00c619200c050080c8142170020001444400c03246205410b01517a84c0f01c030103000503800700b43c40007504101e03103484104001030f010520b222031300024240000e41501c0c01c500a402e42c3c1c0c60b04003c50540c040c6800038805400c046010303e51060303003013000340201464080001c003109000d11994404036902c6048004652040c5d4080080e00c031040c08841d400d041c030101002e0b89500580e0704a04d0115050303400a04103212006440440307801d9009084150344036200c20609046005044440d40508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 937571321 1250 937570071 937570079
    0x30f0b0603010306150b1c0e150c0c01061a0924030c1b0105150613030b100f2412020910020609010c0c020306060d0302010204050a0810050c071e0309 66
    0x1450085001c4c40e804160500404664107038084d090300540c4410604208000e000d9400190440c0850407941c0c00240d01481c1c0c038040741c01c1489400320103500044038070a00400d1241c41000c0e02c5078805a500030002669242080701a00b40b01c030f4802c8803681802d207c40c07222031520410041000d4000395031540b06484032a040c02c080e0b8402c403941c0e90f5407000810411040724004000c40c3d8100001d500810460402c908041070b5026103840c1c092140c04005008142185109810b02c015a844000084907007410703552288031048a0146001d125055078001030408468010045980c1d802c0c525031003070815403002121860200c2480d28201d54003003061011545a004075540e80e004294050300080c109800481c0c20340b030b180032504080000400c5140c01581d0b020441a8020301c0445580c1010800c61070140c0c06401142d010035400071400e10000b80005010415104584080b4001c118a03030362040500b019005843c000f90425004000a0300b80004082000300351600a05007011002d580d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 937572571 1250 937571321 937571329
    0x603030801051002071401110d0c06230a0b1903050c03100908160c050d15060e0705090105090d17040312020303070c02010302070f06020f2502010530010303080114030703050d030f0b 80
    0xd4030300410000342c07003000b14600f401458491061b84a02c000030004400e0800f5504cc0d2200b10042d0024401550310a0b5020f901c0c0d503801002203030070300f6080343d600103660b40b070910301d031140d0b55280203500900030304024124480c0305c1e20805440941c03281c00380c0c0c14046025811115400d03144421070301d42d900c000c400701d46503841e050400f80d4144501e03924101001c01c42015010307a44550700c080075080a0205110342d10382c100080e01c121800030b10702a0749811010780000d07203400380030a0142c603030117100802c440d05510707410043c4103803030245018900000400340120396a200c00c40c0c0000006880580304c10040d03129400801c002c5000301282d009259160700d91802300d03845610048480c103c00504180e6030342e00032800d030303c1154102c1c2c540c2c1a50941034002815900c00c03200701502010488803400c0040984122105d94440040d85c900c1280da168500940002c07028055894004005079560f05103180c0003c004094a07400301c0a80322100200c01e040c0d0103014420030350300c101a12400742c240b454a0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 937573821 1250 937572571 937572583
    0x5010b0a23070b1b03190c09050306150109030c150212090a050d0302031c020a031401030b0103020904140109110f040b010f08180609010c0e03030f1911030d060303080105100207140111 81
    0x1040d1b4501c807030708205502d2507108841c04454a0024005440c4c2c00300700d5994003088240d4000000f94082c500180d0b000c0c0125215002900b0003080e503030882d180803504600007280c1c0e6803220f0440d000c80d0a0395900e411464194021a407020358480d480c010140240d082100100103000e201e030040b0b038140f400001c03030306001a47c001416040d0b42c2c3c0c04509220625894001e06980810328102241154115100d03006000c2050002900a00d010008601040075401210100d8a55a0300800141c2e03901d20780315441040268500303104050081c046507080c80e1902c29051560816160400485280a020b90b031000c40100030b9107443e549002100e8407007005000791803013650300b4000000c503506400006040f500382560914001e0b40705001e05400c81100da421141000e9203070b4500c0350002c20040341150344400841e0b44100602011611b440c0e10381040d001902501d100c0e0301c4603000f60b030700d840500202702c0c03100300c2403401a40300503400c12000d1085049110014018546418001c84092110745015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 937575071 1250 937573821 937573831
    0xc08030a0e121c2c01081303050f0703050403080a0206010e10260705040c2c030a1506051305160f0c080304020d0206040605041502031305041e05010b0a23070b1b03 72
    0x1911300008205070740c0d000c0010b6620442d07403104a1664001030718010440e0003151420014131000040000a01d03006006030b070000c66000c09803a544d4a40814001c2d100c80003031040c100303200c200c080456100c2600040344000d40d07040140140c0b900c0e1641a545480c40740c45c0f0500b0820303004000010a40b0340302c0b80240c00d005051515502d1244c0708404124882c4101550320074000c00384425106607541d40032030344c404580c0d00300302810781c040103440b018401000c15520066100c2692034103a00038480d250040c070b10512a903604660035401410058400710080600030000171400c10020000520342b001640d0002e0010f424848501403941c00300308203a111380c210001160300442d00b04442020f1452111080100b84040c1d0f040c0b140890080e8171103e4139004440c440c540747d4445051007120310500340a2014041004d0005503519150075140364001e42d09072001816a0300c4915040004402e100503007000250b040b03140c10030503100d0315102c14000d000c044121801e030504280050384180550701803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 937576321 1250 937575071 937575137
    0x50708090a210b0a06050f0d0c0806151903120c0510050a152301030504050c030d050a0f030203010e0f07050d09080405040c260903070c08030a0e121c 66
    0x80342c03107061006001100a0031341044a0616006000c591514464130200500560319000b07016907a29010104584c150481c40c100e202d040c08011111608041212500c3e2055460610603140c01800b248416240d020140243c4400c0301041b502d07d114001d0400c4c250b019000707607460ba1100e48000750a4031001e48840d5101501c0b45100003089510071062001800040c0b14049540c5000c0a001d01e0004440400350525a0307030000070302480000d104081c00018014261110f21740300742000f42068010040d008000b5012081a040c124042c4c03080303905a81100250b540d0655460146807402c0d040108400200b003424080b400b520302d042c0c065001c03801e00c90340220340c070b0302e007820b05020450f0640100e00f410020f4030560000300600c031f04c41070b821006c84210701299580d60300b10200c0c698810440020f11107106940b00080468012020303004d142419a075081100c04000100540d507104600002c0007a001400055410f0416200e0b1548480c2d00d400c0c0a54991001d07200440400c160110340810 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 937577571 1250 937576321 937576379
    0x14040c3e060708060627040f1407030606021504080c15010605222411100203150904081903110d09060c0305091005040809190e0106050901050708090a 66
    0x81ca070700070b1960f607404202643c02a0400809110300079907002411a0031045285600d03c100064031160401d0b070440b8140001884441c842d1280007840e50741c11184240080d00d429800300300c00e071011134001e00002d20052841c203261942c0d211107070580d1000424200d244101c243c1f5074500d40380da440103030081846858031a243d198400700600002c4005c01070302c921501c00c89040c41510758030711102c603540c11218880c050b12120303507806031048014141e1450b29072041504240200e0010780083d8030680482689060702024003090007030001303081d5001004014144440300743c0c00300361180400c200b80e6074500032401e540755440308580c640c003003500d09010640303c1302004140502d0340a01c885c1c05e1a640303010882464203000304ea0b110707000c2b02c0b0800c04464803040403d003170082c000306903414010014228407904411140307004e101d40c0188505c820062581000090341d9000300c0c1030764155501a101c151510700d0641c1c600540d81e100740025503200030182c102080c007a00c10601d030000d0061074541d00e18 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 937578821 1250 937577571 937577581
    0x50c04060e040903050a08060307032f03060103080a140904060611060708060a0504090303021b06340e01021603050c010e041a1c06020a0914040c3e06 66
    0x8a1000d49070542c0124202007440c1d0010380d124088505500c800e1400402640300c1000003030a2402d00e034005030028812842c03000300502c3c1004208000b00f0309900b4680b05411403003d15445100c241b10241c2400000c1c8203206a05016141c4211b8500729940450718200e405030001e002c8414640000e40010b0051072221075400c010051990064843d052030f1803030b4900040043ca4001a500900b8011a1039019007000c16010f40c06840200c400c0030009500b155a00e40c02030350324202200d10644511031051601e1b008880044544035440c3c080c0e444108805c408041070f10303640700d620402c1c1e046110b8001510009011802104081c601c548050f200302e0040c0070005001030002c4a4851040d444d004040e609440b80440450b41d901c0141c5015610080180080c54101a40c80b03000d800d950002078011121035001006078140c1e4112011070108078000e030144000c8484103d01e01c80400c00e1818050b102403926040361407150400f400712412038a10740c16040c3c9440340301e07040e4482c0c3d6001e882400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 937580071 1250 937578821 937578827
    0x6050c1509100e03120703020f1e0306030618151806090a1b0609090e150a0209040f09030c0f08040f08070801050106021207110619050304050f06060d02120a06050c0406 74
    0x24058143d1040107600780714422407100c0c41c915001e050300c0103141e400074699031000188403e072084d4a41a03110035020940c8000321510560080300c0503446405003d000411000040075010485e041880040c4045079000d0f0100078800380152a101422803400064444400700300b102c0d500c01c030288000b4103501d0142d441c00c124113803412101241d81c0740c0440e00c14084c1c103602c4141034080720039008004c5042014541414100303603296544072521b0a040041000350042d42c0c00070300440c5815241040f440c0118801801115500c8400400052040841c0b03800716119000c2a4a01e50007106c060785426914a100f2441c6c0880d94410021500021002c100c01c040070f2080e20300404407400a44050480740c501d840300c521651500400940504041c204207403036001c103131082c40d50044001c80c4030443c000400341c580c1c3c0040324100d55500c039004140d50030f6140030500328003809010f0589a10244644d08009402d075411000c3c1044d44100d084410220b000c50140901440010380c0c03943e07481d03003070480c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 937581321 1250 937580071 937580081
    0xa03061d0105011404050408040e0705040f080102071707140f1b0d0201211116060b010309120c0206070209160807110c130209040f151403060106050c150910 69
    0x3100340e03450312004100b400407407000000d1402c4111400641a9a10710308411070b800780782c0050000e000f01d20300f00300038940c00500400955010306070200707556542d620513500380d10452078002d06181040c080d008602e8280006042c01038410884190030448143d000351400c081075001030003a40c400c110446891810200501604500380c071184d401c01040c0c1c0020700292403000c919996002410f9081c200141c9683c004000c01c0c00421000d0f40d41c1c1d441070705082c00410140c50a8856610b0819284000d6000c0e12410b260117501102d00e1504a0f040c0c0e1068508401c52036003603030403090401c20940140d45408010748a00e03d050f00c045441a08010001c1125800803c0c200500814140c041d018800c0010301e030300d241c0800c44801d40031445039600c1c00003174001c001c0000e40150409007103072011a100c0e046402d004082c41c2d0714110050340d404441c402c0500906c3c0701e541542000700140483c1d8819401460f50005d00c034101c50320000c4d40f1a1301030045004503840059a00041080f001100c0c6902807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 937582571 1250 937581321 937581371
    0x40b030708031209071e030b180706081306050c03180604050c09101503060513020a0804060506010908061510031b0e030f07081c02060702030403061a0a0306 69
    0x40c2825401e00d008160740e8880d0f141d010701c2e00104a0f0000d125210f081003000050a180b0001100d10140f0082000446005000860f00c00d41800001400700710144c0b10620103040240080007820f2030040103030f1300400c0c054081919100c1c02c43c3d000001c1507060103440e010300c01c11300d005640d92800c1148094030f40c0011105165580004c42072101180300004c0851103890300303d07080c0744180c0303c40300c0302e50140c0c129602081c0482440c448001da2139406621200886034141c401c0100e540d8054402001c82c403ca0a140d004a019500891b021450f00e50003d6071040703042c10802c208070788507070a26180410440304000c05c481d910341c08219034100145a20607030303410f6040c2403055000400030445041110400401086441c0303121958076a001c22a11021294850546081c103486130034264454102d8000100c01e41d8602d203000d07981d2480003500c1d0f44035014650156080c03078290b0341c3e803901601c040c4a41881c40c54550303103101144d50300c4c4000760b8003c602c5964001001110310710302c00101a40144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 937583821 1250 937582571 937582573
    0x1207110f04020406090b0d14041208010e0705040e1306020708070c06210905120c0c0306060909060609040609020a06050306011209020123071406010806010801020a02070b0f1204030e040b03 83
    0x4004c2020700c2e04540c4080503144020981615200340309042401020079190f6060325000704000c0c0424031040380c000d01c2d440c0da00e40e60307598496038954200c0c1103416010382e400d00010310104400c005d50004c40b0701898004d8103040c85c0f51403880282e01c61805a0304440c03001e41d42081c0000e4494100a03002c0c1c035100040100b42005030f20317014402c0300069829100d0385003d030507a0b02d882e45201040014080c140b151680c0c0c1c0c8001c0d403140b081c41a143d40d1042605203440c02441348078040ba0441c07800011084c03080401900400b0a0398130281031041c800005802161442c0e11106d04c1c1d07005aa541c07440c500030b0800c81da1015164074000000408922210350b1005034589016608d00240c1d130302c0441006800c42020388101c555811241c000d07172a114506015240301c0c0f10719501080c80c500450f00314101ca0b0a081160b60b16603d8100c50781c00c03845006128009070744618010843d20b90680003602076940e002c5401828080c50000400400808450480000345040b80002c66841c05102d0080c100b40c00760 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 937585071 1250 937583821 937583827
    0xd02030717130b0c070b04140106082b020f0303070e1c022b020a0806040201260105010e0a03050610081014010504090f050f030c0c090f0a0e1207110f0402 68
    0x2d0248444840350540161104101c18002142070b01d191086420350750b809040b0364a0380c64641083d0906e64420580781e1019401c0803400503001100054644440740342100074254540e45610410b006110103040d0000c1d4040e651182e545d41d242031010f580b1a1509459100a0003e4441081190080f420300c00f00781042c100840005615403224500492840d41000d040c005055240700b4030041c4c039408025030040004c080415007035004149240074900c01e80315013080d02d100c800704015070b00c12501c40c0302200885400410103136205c0e01c0c101045030341c041e000c403034425201d440305400c0c004212184113800c07144d040c040103801b10410507040a8a0003050401c5100b24502410b401c1039018407582307100301d460741c0000061056003480030800c20f034450100c491240310036003000d4494104180398440c0740507091040b400d81c01e201c3c08040c800c4801c65140c3d80e1382c0c0e4500004400500b00140d0f6041203103e000e150031120be203440010120b450044481429079224070381000390f161503800c2c01a01982c018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 937586321 1250 937585071 937585081
    0x30b0405070516060c1806111b060d2c0c0118060f080604060b0a082a071202160b040e0c09150a0c060f020c0f0f1914030d02030717 58
    0x3000d400c050180d80003030003017002d81203603d0889460714417a0246007106c01060f0000350345500502d02000b00700206080c0c0742400c42a0880d20100316180a1642c0c1210040041240e0b8070420761003101121000c001404910560125142400c41d424a2405465001c41011842036070444040e2000d00c45110008005906182009088850b083c6408052203010f0300450707107a544680045015120300d0864079101da40b441e0004006400650350420b001d1440c82042034041e2070f107802c5940c001c80ca407028074500142640c404680c625000607541c04c50144011008580c1c40a28440005004030743c40c0c646c495060048c1c45100200240c0300480021041024469503210403c030540d8070b858000055487d0405060143c1e00c141c01c04400a0495180c507080c0d5004101382e602409103415010120f403001030808032402e99500032020070f120940c0c40b01d0000707100e0705c06000403600d5080c0700384400c01071100c040b03c4051650300040c985000003500802008070290341b140b0070017103482c02c01848801c54141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 937587571 1250 937586321 937586347
    0x162003011505100c05010e01061703090105040b0a1707080601020f0105060a0b030c0c010f05010f050103180206090f120c030d0c0b13030e10030905060a0b220b060a030b04050705 78
    0x614858580070f0b4006000c1c2000f81801610070480040c1c0045c002d11000404900e0326000740490301482c030000107040201d0102d5107001040d55210345044c3c4400345040d0034502001e080c1d400c9200403800f0464101600d00b0440390100c03800f401042c07203481f02d43c0725007081c00000e401c0600e00030000c0b030168901020048265500740c0324804592141000958a4641d56031142161061605110080d8285807041e40055519442a8101e40341c2c04949540a502c42c4011015503100007140114400385a41541c09454a80018010283c0040c00042e250504001140560440d07a040c1006a00145484261414144454205080540b50004031b0740c15035580c1410341382c0c0c090300032a060801d99681c1001c050040e8810001004014014030303440481282c01805030500f0101200c0324041c0f040071a10700420f034025880c00003001042440c042210344130a1030307180c20504500503050b4459a4000c6d5603104c480c01030241581e10340d00072810341280000e01c8155480500700e1001c20004110000050807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 937588821 1250 937587571 937587611
    0x110405100318050a051002031e22050a06110702031507170405060601090b04050f0f03031219050c040b09040c0903080a200d09051516200301 62
    0x50100c500050a0000860440007803401030a4104407100c1400b8003000d1060010349080340600c03990403521840d08400c0440142d00003504c0400d9000c032900d034815883c0a0600003da8441c0c8c203400b41c1c81d10085407460901000031759003020303034541e0002c0640d6400c1c041580101d2205550a03281c0d00d1900109502103a0350b040a2040302c01c03d0072104c1d0200704640c0c440c0111540343c42601c0002c03600c5043c14100b007030302e8510955003240410b201441c0029000c5000303040e201160f800528a4120040c46401c4c407002c009140c40b400c0d8503010421040e0f07881c00900152030b000d15000350b02c0c64802d088040d04c0c602128005044849a1308050100f00000c02c0600d0490707104881c1540c011a00788500101a80d008045800003001c0d00404940e0040881d40000d1014120f40003502d0101590402c01119403201250f0b000c9500060460b90280f240f03040520900101492001c4072924000c1100d51146110451140803240e150740300c1440c254171003d1191290403984c1c121700070001508080b00c4640600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 937589928 1107 937588821 937588829
    0x8030601030b040501140105091809010912030902090130030e010306060c0f0b0c0d11041d07080f060105070812011505040b040e0c0c01021305030106091104 69
    0x620f007501038030b4101c1c0c100031000c00f0b076920345500450300c5a0184d410107811038803540200c643c01001c8004144284403800002603402d10601e032800c200540140c505040600f01450749015039179034103001e4110b0f21441c0d202801d8541001044400064850200c41c001c52020025400e05400c1614000c048000340c0e4108010b035200d0030107560090011001038910304000c6013200020f80c00c071a415401802d140d052a0a04861080c0e6070140c0307100c01040c82580c00c000c50100064004d142070810400301a1801e101a071178801c90003800301000811f007105102c200004901140d00680031600c8064120440d665a04112503580001c1a028452600220511410700c10b21034450010744042c2c0b800c0b04d0300a03151925250608440300f034090301c40c01841c001041a610000c2003480106a1451702c40c810580300c07071420041500b144c000da444218142d0810302103a110704441d0046a050b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 937410071 937589928 := by
  have h0 := BRFrame.cov_init 937410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 937410071 ≤ n) (h2 : n < 937589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
