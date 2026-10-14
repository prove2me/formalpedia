-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0839
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:05:18.522986+00:00
-- url     : https://prove2.me/submissions/d3c06046-d57b-4811-a326-8a2c3d6e1a66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 150719424 ≤ n < 150899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 150720674 1250 150719424 150719431
    0x101e0c06060e010605031f03050d0f020c090f01053a0c2c071b08090f0a03050d1b080a0e04021c090c050409081801020c120c0a05060901080a05 63
    0x1030381c03000702140d00300420140c00d00801d20b5586441d213034241490000b42d05800c0084029410401240c00c100283c00492984030f40b10042c1015100ca0301c1c15242a4104080b01d48a198007005410800215070100c402445c140c0ea01034800c01c09140d0544045920005200d01d82030300030780750682c60400c2e07601650310304140c0340c4101c108900e996a1202c2d1103c582c0c01c2145214041030300b10046c541204042c20305598490f40b280340054121605800c003d1100764401d4001e07104d800c00150080761521840b0b030f000417004000e00381009181d600c0c2400b41e200c1c1030b01d0240100244410150306105001e00a15440c010380140b0b03541c0c40c001c02d60a0650f1440c450341180c5401030340078000310b4908100030308101c00c082e01b254008602241d407071604c0c0c4051215500002e2080d45411607000104403514243c502156000b00858840744104005034a80140b0b10310855001030021200c00c0c1501d1301043d0045c01000035506c240809442d5010081d5600520050600048401c0d000401c08a080c0e00312641 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 150721924 1250 150720674 150720683
    0xa1d0106140315132306060f1c0b040503040b0c0f0106090e060c070501110a030b0f0a0612021602030109080408150106050a051303020a060c020319080306060705120414101e0c 77
    0x80660030342c40061107501c0036115410440c6c00440c10810701c1d060800882d00b0b800c00440b0400001e20451080991080c46c4200180252401100007001c2040c10001c65010706428031030242c4804558010564610800c1e00342c0d9002c1d4281030000802030054040c090710106003030054285030380c662030140c4080e0000c2d10240c0311503490b02d910070a6484188020306a1040c55078012582c5080d0505000900d0b070000000d0f401440c118500f0072110b0b41c8a00e14000e450400440580e4440316043c00410140710018082e505502c0c1407503540c10400000700038411504804141d4180800004004111f91001d22070076000c140c04001c0c8010340c40c0b080300140350101d002c02d51240c61030703181d07000b0440450440d00544041004100410706600c2e0401a072001d408000d0300711080104103a0325548030780000340c80c00780031300c40c082080070400800740881d4014168901070292074540d01d025490703c003800c0228060184104541c080c0b2010301c40d02c00000550560340c00300400040c4150100d0b60710743c2400082d02c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 150723174 1250 150721924 150721943
    0x2090a061d1905040c09050f01270b041a16021c17030114030303090714060403060e06010e0f07020a030806130e0f330a1d010614031513 60
    0x507115941c020204040c0d05a100c207044299041806100440f40008078031014840c007a03c0030809569800e400080c11202885c0c082d02406503115001c102d81c01c1403501d168412031482c8040f40d04081300016100329025108801800001c0441e070030458414075030300b91900d540200280c80541408028008801004480c451010f405030316565007649800c1145203603004008010001039000c0c8000805440085000d1851410a610b40c603581c1c91580c800c2e420998440e48016103c1d41d50403068400441d00200184501e0001c86d100544808003405994590048140850084c0c030303507801801d10510b0250000c0292126584060320b1003d801040158000c80c0c0e9034a5a044030001e004110061340760708000c1020700c404c1c2500c00d00b072100080c3c0200051101132a0544407810310820340d030610880c091015000e4540240250141a9604e448c074180e62aa5400024464056001d04101e51844041c2c104008501d020035440d5800e040c0e075480c6000785000403401c0d4040884110031954450202c0340d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 150724424 1250 150723174 150723227
    0x20a0302030f06060109080705030309121c0f030c03050c09040f0204051908060619061110020403051b0105191d180f010803030f0703090f020a09020a110102090a06 72
    0xd00c2d04400360390000d0303030b90403000c103110b100c0d40c204280c0307006400440c020305442410312004ca951b07400707041c1200f4829030070701c641c14080728014440c0c0503171090311440000c006d00a0340c102030302c8141c0c0c3d49800ca000910b0030410b422450f1003489039a028581514059233403603d1002000040e020f03100911004680c00c0200084c150390f4010208c1804600440c0422294506a4098106000144440d0041a08020f02d0562a0642103090199022030030b0552811100900741440c0020350f4440d110598070004011041c00740000c2d1542c1c00d0f01c0540102c1032505d044000440709406201e0420001464009802ca0031034000c1e9000c08054064410481d10602c9002c0080d028844806441d24183d54180c140300710040307009000e41c0500649001189542082c407200c40b44003038001c18500c1019034501c0094100881c600541841d030b40c0003020100c110f512845904002e501c41341e045004585041400800008103000b52144602c0040001089900d4001c0c00e03100840c40000410743c400c00350a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 150725674 1250 150724424 150724429
    0xc0c01060b040f1805130b1005101106070914040c140706050106020708010c35043e040b01091e090f1a1003020d0501080a0c0b030f04060504020a0302 66
    0x140c0000d0403c03e000b4000a13140c0341030013003249401d400803450075013004c1c100042410451110094103030701c181c0348003840e641c0b2682d40e5044242c0c0d030801a8808103212462800d564803290014000e010181902c03803903125140147c4800b10584101003421214001c8010702d07160070790000d408480e10b030500c849200517908004130355900c1008201c1d0000d0340c1d14014499031760b04100d00300240c10030341300802000c2c0724140c0141200d400a020704200020060300b4007004500a449402d01201c5003c100e0203a0400d45030021002c03901c1009541c2040c2440c00c01910515050b8402416512030220404104400403c0c0000b8043c00003040d0b040c80203030240052100025003403402000001c2c59114003081c01d201c0c030501520a650071440038942081d42041400c8076210411030445411141070407002081c5000340c0c080d0180303440d414840c81c9417400000d41e60030080743c183c4a09118061032150980c40d03003d900c2f05800180c03154841080d00d04006000907041d58080f41d0081e000421007052141d69500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 150726924 1250 150725674 150725677
    0x2061605040e18010507020304060903020d031101180506280e010b031618051509040302011e060e18100504020a180c030b060901170a0603020409050d020d0f080c0c01060b 75
    0x10103c48240c40c000101c2c840d54400e00c649500042248003841c90f00d07142c410014001105800003a20900c014004202014041c110000071200301c0340013804548903041109070040301101d0143c40900075000010441c034502c919002140b00340190310082c10b00c4202d40c900040c52030480701800b9643c1e5525544407544c0401031091030500d509000ca19039400c0c030900182883c50020104481402c1c0410702c207080795500000010500700391510707031a540c1d03241022400340c48401810580c6005035204500c11035a503802880640b03250150100454413402211100744810742c55244050308002c0704440c0481c03250300419002400104580c00907502e451089803403c044010022165070b903050341c20540b03a014044c00326070b00300c21030b0524101210880080c01036200b503680c0d206214000400141075004a60020700a5900500200314a000c0f510300b16961f1000c0900b0070340907224203018180310910642178540c2d0301c41c2039903912002e902c5450000f18280c05c80030605a0f10754a90030f02182c401c070500c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 150728174 1250 150726924 150726931
    0xf110a020a080616020a030e0904050a0206180f06070203030723030a09060201050a11031302061c1e2309033702070b03340c030801050108040302061605040e 69
    0xb00685010b0038415016494201025403050540d00044d004038046604103e80c100750100607603c0c00242e503201d14103c0e0409441c4040250301200120b090a0f10b0441140003204119042d2000400005004200090341c019000c009515910810090300003d801c03079842c0000c0e000107582d80b000720321a540c03111b003190880058000004c219050030082c441e4240076158202244840400007040501c0b09060303a8440140802c4240800c0c0310301c1c004548400088440340c000e4641402c1c0510951618140500000700d519000c0300b407040c00084098046200300ca00d00300702e134015544d42c400200d40c070070400c0e00c00410440d0540028801400e20840d01d8004a01c9420f00004900440c000282c10030741e41800395403d40219400404203020051a2404898105030a08038694180c680c5403403041c840b0003410750041d0390034602504d41340919040002c10010724440e031980a5180e880d1001103d00460858020700140d0084c130114a0308140400c0d515071503212480e000d031034151224070550881e0300c2030b07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 150729424 1250 150728174 150728189
    0xf030307140327030d110f070b07020f09010e010e13020301050f19060308040911040506070b0709090207080703120e1b100207050109090f0f050a09110604060f110a020a 74
    0x201c800e0326200c8094500141040546540071401c44140801d41c5c940c813201c1e46a052202011000021140801c07a0940046a07034080b01e00050311010407000c0d903002140205e0080000b000300c00380b60b25020350844d050b00c05a100c00c408503882c05014031200a0003a000c42031301c1051941c4a03000d610207004007403080c0d45010f5143c40f5400c10110800200701c000c01d0b90076100340341c20382c01d1001844903001c840807510507140116526800f0070303031003005108a03840a82d000300c002803000f0401118109051060000d40c030799088180c0d035582c2c0e02041e8801c0034001008001c04021042c00070f40900e1100178443d030000000241d0001c81c2c0b42d01480d1210007210030643d400c4500e1700b407400e8600004600705180491024182d4030341740c5400030b0445880e42c0114044140c482030f0301034000300b05501000b03040440070300500c11824602d42c094010184104113840d40e01da0754a42d0000b609182c801c550844d0903598843d80c0404260300110b4002010101c42c0ca49801004111409607407007604c04800307400704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 150730674 1250 150729424 150729427
    0xc062304020906030105071709070801020726090a2c01080703110f010e01050a0201020f04060f0e04050f1302040f09060b0901121104020a02030d15051201090804050f0303071403 78
    0xd40100410000001c01c032034441c1c2c0c188002c10481503840001816105070002d9042e44607196100b8207410840c464008822541c40410090140807544014082c15180340d8401100c0504240400c850362259011031a0800390281d81041005501c000070301c414240b049100740c04141801014803081c2c2c081e80300a041c2e610000d000d20034040140e0401d5038482d0100e41704200c10900c1c20010b454464600b507014140000800c103500c9480c000c0d01150b04601c40188410b903165107038540501080000c604800004180c03802c0041c0d00d0415210b100e01804982070045060703900d006482c58600741440040360400c1d210401011601c05500039891607620454011961400080030b10012005c140e1014208411001030100450400f0341c525000c2c400603a00543d64100c0c814050b45903224a8513107480c16440c01d0948426058000815010788004946075042d0818400c40c2031b084c1d9200090140c400d400c10042044a40307401441a0071014000c0c05480c00d041c100d403908a00f0079400c1ca5111101d810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 150731924 1250 150730674 150730681
    0x90f0308090d03020304020f01031e02071a010501020d0215070201020717071b030b040204021305120709241e080d05032d04030305060102010612050708010506040203160c0623 77
    0xa040c04000b550358000d1808509515003a00004c803603032082c0e51035506160350f07080c0d90000c642e140c40000c01e83c0d40c1890303404e6507140c000746071016468240034032901c64010803a002244c03644c80811201304031501ca034020f0010b00c4059501c42c1070624090544000d540d402c21070300f0002804100700030300e811403151401b5180c88031800e04180b84440462400c05100070b01d00d00740700084200500942007078044d1030041c0c4516140380300d40090380c0e00d40c1109502c582c40001ca1142441d00240c0070041e600600c105210521401c19902d895540c2c500540e840700b60448400c0c003c402c0031490b031803000761b0020182080540d503840018240380f402294000001e40c004200007420800c0c0303040300c0d030f00d6600081c200b00e4600f2300c3c030004141041c00382c0011700300368035880480c0544e8400d401c80c4000c0c0018159110403005145060782e41c8182c117102e2051254203040010701c01780f40502c241c0c0c1c4180c8020745030b0020b0003071405044801120743c0504880c0150b4a005800d059030380308040f09034403151409900428103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 150733174 1250 150731924 150731941
    0x80f15120109080322081206061209010506012007030201050c07090203090a140d0c020d06060306050c120115080103030f090e0c0a030f1a06090406080604050a02090106022e090f0308 80
    0x24914001700040e185c000600700001150202198521015008022004e84502000915500c0703910030043c2c03401d030001c060220f00b400641c07115000d90001d88541c642e446140710b60008440b02c0c18a5a8281c1d000210200f000d54058001000720384401d400350781107030b9118034a81081741c106540060143d40200000410003040c01411b54000107500c2c0100710119540c0b200800355044020002d000b81041444c950822242d500904080c1d50701c00d00501080c5440c07071226100da0843c102620341090040000a80049440c405e00e403190110b036114501a03003140c5096031600c0c400d2041d8003c0000141000078841101b41180b8000c0b101040c2d03d6542e44d00044005060711000300005101a24003c4d56601015201c1c02ea00c1a0325401e0390181d444505c200c0016000309040c1d80014903901030001040100840030901c45001842101c3c5200307541d80710349089070754000c049020707007000c0682581c00005100c05020445221a103078800f02d40c10105594045000755401c00c00c502040d1034005218040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 150734424 1250 150733174 150733201
    0x1020c0703050d08010b0f07020303090d150b060906030c030c16080a03060e16110705090c0c070b03040b0a18050d0807080c13050d02010201020403020d080406030507080f151201090803 81
    0x3d031452602180d25410181c580702c0921071841d165141d01310001eaa0030441d1410b0041d15080a07000301011180304550504041103030070604c0e01000c15241140022292070801d0650307050340d0b40a030100e0708540d43c0340c4001c03c00d54400b0742400d043c0e09060000a201460442d8032060b40c1344501c04464807000002400340030f0b10515001600320cd5555810405404080310a03064911010724012400009011a250a00515400a44d0056445010040001602c000401468052400312a0f000c0c0d610078442080e40416103004064200700e07000308a03294103e401501840f010800c0d040d2600c00d09d699041c1c0f405014a06160104035014100011942c22024030341d4025041101b00e40f80c441c01441d02841c6030f80600031380b40318600b2201d040c0c0541e4400d40c1510b014680c00f03440340070000070790304002449070040d10171400020300301000a075245100e03200d1680690042e5405c40c04540343c0307800140c1c0030341d83c40c140943c001708141074540c4500da00340642d0440b40d007e4000e4076070303a0810303a40f5540301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 150735674 1250 150734424 150734443
    0x902090f06030702190303021b0a1101050304080a032a0215010e090307030305090f01051009050610300f020403030e06033601110903060703050c0a0e040e01020c070305 74
    0x15101c2401080700d0540c0214080301c13044191444141c0d00441031600307500038003c000c0e002401800e150400e0b9801e036400901e040384103001e10180c9644c288603900444403071004440041841308148400148540a500720003404103000c01c0402c0014005204000b4010034022803c00580c006000d080540d02650140f82c098401809180c10700c0c0f510810080d030364881c1c3c4100504140d560800142d08880078040400c545401000911075403c0c09010703020744500602640040034580408140e4920340035401070b03070f150401e40717407021110400390702002004058641207070084100c00d0340f841800c107684566982e80c05c9004006031144d003103007001030070a2010410980120301c20814015a445020310103592140c0060311500e600c4030003a1401c0400e0321802a01326107600f0100a6441101078030054819420150b0840b819035a400d90210150340090340c0300d0b10f00360340802005802d1031140d0f0702082c1030100503001146400c0884c680c5422a40401c0c4070612603000303202c0510801c803060140410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 150736924 1250 150735674 150735679
    0x503041e060b1c0c05010f02100e03030601080a0507090b070f1b0f09060317031e04060621020f0f06160501020304060b0d1e020a0905041b06021203012d0902090f 71
    0x202d140c00d594402103008960f0180c1750500c503100107944400e0307208101070112015010001d0000303812081909603aa041511814040780d8402c002560720951441024425041584c5804241c0d1803c00b111400d580a4035043d50781084452103200415114400d204884194a40004c1a94508069001c0075840c50304441a5541410000c00c0030070f18954880424401c03640719103a498955510420007001c0c40d1240c1d0391404040c0017008140080d40c0e20000864020341c0a1702c0300020014480e14514849600080d44204115454242c50515410080c0c0307804c0302800852510780110702e6292030015100d0100c906a4002003008108091802140b941c8032054545c450703411400d5984800c00c20b40c02400310b080750455a0705400359950911100d006113078200c01040542014180340c440303110038911800f201b400c0e8000025180f480000c4044a4024031003045007540d00b400884c494010144c1944100b00c061040c00550585144860310000c150101005036507481c080c082c002840c81e0013144a2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 150738174 1250 150736924 150736969
    0x1020a0c05060c01141302040c030506010f0f141b01241505040306090f0204050705040810020906090402041701060f0302090103060506010201090507120201020f0a03050a0503041e060b 81
    0x35000c95251015520704035038040c2c59000c610100343c0100f42001054500950603c140100d4004280c240c0144171f00070b55003440f010a0754681501540e1003592001d000846e2204110788503407155021405a919a03e81642036030000c8a0740b181580109145055480d00300c601c00d002d01c0024400d29083d44020b0220007500707c000c00c9000260310242c456040c07009410704e00303071203428460011030300a140e00c820200140c03d00d41c2044d9800d00c210f00c40c2240a1b82ca8080400e1800340190144d80403035071184000e014418582031030101940002090729004042444010740b0b40e900d42c009003000d443c0c0074920320051202c013031896094980c568800c05140c04800024009030312a040e0041c19660814804107003500c44100403401001c0054029150b402990800b00c0c40d144501f410940d004c0c001d80c211091044002201d64854000c010007c1c0484c00412801d8a090302400c050340d80715020314051250140b030521f852542c005481000c41d03809540d0703021540c0d1783ca00315108111207034014681c1c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 150739424 1250 150738174 150738193
    0x90f05010207030201110a0206031503010b0301050606030a0c031401080f1b0112050c1b030c0c01050c0a020d02130221070e030c040209060c070807030b090303070219060615020703060b0102 83
    0x203502d80b0654000a0704101c085100c65042c2e20081000b0303d0070b15400f4010700e9480c40e02c0c034103c4803421200851240b007942031000f031071403510741401118004d0400801c460320315201c5141000041c08040590020300d42ca45102808000380d140700d080c02811454050010704050301d0a40e402c0210301160b00410b04070403d40403e03140d03404403c60140b810070302400940c540710141e00003041e00504d14512240248502c200405a80c00300252075081c46001c104d800c002404e000540b254040c000561980340d0000c98544007600e003000c800071600b4000f4118915141c1403d03101001d0b079100c1d121881501c170184514105001c450492140c0c000810321b44001080148000243c884824040d540e20658010580c01e00594a250032104612091012036040315560040251a040d031407005036660f4015600081c044140401203a216228030f9001d880d920303401070b00c140d0510f0000318060f10501d65480c00410308580b1200c00303064010543c0c0041035000d140d4540b40080d545036030301a504540005850 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 150740674 1250 150739424 150739427
    0x1020d030e0f070801050603010b1509060d0b0409050a0c090624090e040b06150702210c0a030b060a060507020604030303180f05011401051005041202060c010c17012102011d0405010b0901090f0501 86
    0x1d41e2074cc030000b04d4030b003940d070f55999007071070090009484c115500c1407030042c806007007040c00030700108828071504ea450f41559071406e00c20201c40310784c41102808104468640682c00e5142c4420260005500380a640c040c2c5131926210102000c86084440d5a0081d00b17018803441d0000010103d01c4407110200d151504581c01b00c1c880c1700548182524400440303000906210301440031300e003011009010f604000e5540d0500900c2c15509440c0c04d8002c03901c014000c100c8510890449203480e40140c036403441d00e403550780c00302c000300701401328a14840c015246200004002004050b100e601a0001262070070130580040f60204040e40110310502c3d1898019809581190545003111109000141c1141c45800032481e83d2040444a40750741d4a40150051001e400101c50f003040c442c0000b104003642e0300c8400000c0c142881220420741d19002000071001076200751501d0000026401040c0c110307824120120302683c00a0300800e424850208030050304e035a01c20110746c006d090143e490291549000300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 150741924 1250 150740674 150740677
    0xb09060a08060d021309170310050907030212010f08010c08071b05030702100f021009020f0409030507020d150c0921020a15050d11070201020d030e0f070801050603010b15 75
    0x60440600c50200c0018146903103c0440092881d005003124031100c0704512100010620000e01329004c59094682855403036000f4103892040c2a004001d00000d820709040201c403000c000c10354000c0507004c1280000d000000b0149e41e0090040d0004845050b04040c0c8050035110380c5ca505908010402c3e0410a007650300103242500d4240310540c0b0015500e00d400d10508603c07465001079003043c10080303040401c99100424088900a5500f41ca00742d803a00404a41070321084200a54001504031020b0b5440c0f50542c00a20128440d04000c0d2503d000342e800314603181060704096400c0140d02c5612041c0744100d00855220180714501585c602e400c0c200d40c426485003040d210500b62217003401287c11501c420480030080d1510355181d004054210200a100342c2c07014110a194078108602400603801c0f00c0180d5950540c144c01900807540c0b01e2804a005140c0402c1a01040c82035014110f05000c0038806880600307104000031074a4a0410149820360341c070783c0d104501541400030b080480445410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 150743174 1250 150741924 150741937
    0x8040f06261008030c1615210603060c1809090c030803040f0c030f020a0b0a02031909090608071a03060d030e06070222050c0f04061b05061305070b0906 67
    0x215100c03102e407200344402400400300d401c4141d041c07100248a0b80f00ca5000185000c0100306149408403081d1100507000520041f110f00001040d410307445a07a1aa41c041d80c41a40904900e1001070755070703580e44905064a000240e01c00114651451488a000b041c1241402401c140002401a480c240d50381d600804021311000c3c100240102c081401c11580300203014070950411212a0900d0722420001d103042201c034030491160210000002c0c0591000c010303250300c520503801940c1803480c041d1500708d1030310030b81c0f9107201041094200400c50b040c0e02c0c81034001410741d00c1d006142060503c149603c0d0500801500c0c03508040c20f00400075140d85128800a43c943c1c1031811400203178040c40803843c00c0c0039080e0003c0d40040b8803c61103500304218142680103946855092001c1d131a1110303040f406108155131304281f40c0040000707201e000c5c081c926281c2d00000402107192074160302c0d12581d05107001a5131544900340120703401800d00c58204800c001070141f00002c5850800c400300040c000b0721440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 150744424 1250 150743174 150743237
    0xa120b01060f0f051606020304080a09120b01051c0203010e030904050a021303120e040912080604050403320a11160f0e0603100c0f09090509060f1008070308040f06 72
    0x5030391500c03c0b0100d900c14000d69071146c03056440342440e25042216811400840c400034103280e40000d0410547c0c00711501c6180c0040c0d403803025900301024040e1004059a82170180079050904a0060b2000d21400c5003110104020310345480c404410401500d4004c1c28103041d00e03005021110480100004400c1103a0f071080480e00790464003901554000c3d003101d0002e6000d450300030380101b88000700c1c54103070650080380c0d00e414141d541c07141044104c07501a140500020048400f1079155424034441e0b07401c950707034600c040001c071035180381020450b0700029440000030307030780c20b0f103020442c4041111000c04035011910401e52820018400100300803885071810b410080300100390f00e524140304c10300140d002028140001364101901900b0704010143c4240040d44d1103d001801040d684582401003851002030042520380c6801070703400001c054107001c181003d14800083c5000100001c42c0118801c16080391214a403c884c0b2450888980c480424041c3c00e8000940c0c0400c440d283c484003a042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 150745674 1250 150744424 150744427
    0x506120703021b030a05040614071104050c0c10060609081b0f010c080310030c0b0a09121103070303020703020315060f041d0102040b0403061b020d05090f0a120b01060f0f05 76
    0x103040c1105000f50f02d901140566000000e540d00c0301c13581c02001441907400540f150581050101c0c482045840b40c0c0c0f8025001c3c2d43d4100b03541203a1b25198010f0340d00442d0740c4401c03900f0180905905400c026000d040c0340445070340e522040002a420040d010010600030f0090141300101035001c2090621620f1355522400c02d48410b46800da00a403920710905070000030240e12840c01900302d55107070140b400700342c8281401010001d102500701003110100306150356032064461038500e01141101710644101c0e41009290368468050310208010402540070758014129146540185400d24a1070800c01c003003035180c00c08109441c2c4411800480c20784040d075000403100401010800b00c8080c50070042c60a50001800184019524001e8002e883c01180204883c0941200b14409981c11503400340168100c20f050019050080014042444000d0520310001e002da00000b90382e80003a401608207000d0a8910105102c07a80c049240900014117141c08022100280600070303119001a00042010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 150746924 1250 150745674 150745687
    0xe030d0e0a0b010603020903060c040f03081303020d0305341b031e060b06040503060112060605150304052e090c05090106050406170c03060609010309050f0d0306050612070302 77
    0xa04200700051241c001c14101e110b5612954020041d51050342054404d124074400b1501c038504200c116805c0b00c500c0c45031940e03114610340c1d072031b01e80e034100841d00700d11041242e90010150301c0b40103846420b01e20aa030f0320341c0d0310201051340c000910211a4002c00007150340340400040c0c81043c043c049469000000c44120441200c440c1001a205c0d800090111403895408640520180320315071040d4410802840f06e5140031082c840c1c40d0045105084d81035110f40c004001800480850402c0c2500911000c21955201c00c0890041c140c40f42041e0f4484400000300703c18090b0a000740d203c01c2122501010030f8030710705090f000140708020700c900403c03030360b924250b001c202111101c5070003840c02038240d00607580c0d240b00180494110384101c501041c40181c298071140602d5849900c10b880d000007180c2152108800e0120b0381d003091041505156443d061040854010005c0316081c841150040819203008400102035030300035800039010300b1007408000030100085025940c40b90303084c40d00580b5080d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 150748174 1250 150746924 150746951
    0x807050610080c040e0c130b0102070509041e1406010b04050f0d03080604020306060c161508070206040618050604060b0f010201020a020a080c01060f09020406080105060405031c12020c0604150e030d 87
    0x507140c03025036407050b5951081d010107d05e94000f00d00c1507002340c09a414a5030346409108941c9002c4800800c07158401080c1400c409005868444141c014400ca950104800708180d1400c6402c2c5c00c0105120404a0204020702e40b034808503c841005455101c02000305a40c0640411070107411244900d40100c00920350361944000e455015074a0021182034400c03400940824821500420840d000740784061551580140d103150300a100641c014101ea0b0b44545400004064020a407108100b18122400108030304002950203580a4000090840703015020800440c004038011415a401030082c4182c481d0081450140c0c560485191640c2c3c01d1040d55590060465410001d0104144103010030b0100b0303140d015209880039078440d010140d80320030400806000e03a01c01c45178560701c1502c20084da189014001c0d11010103506040784040700300100c0701c060b600300c0c045505140d48820208000c0c0143c402003a91200d040c0352701042a0211681e425842c0e2180489107030f011900d6840d4240c008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 150749424 1250 150748174 150748183
    0xf0f0d09180c110a1a060102030405030a0f08070605070f110619050603030c01020c030703020601090b06040501180803032a0343030902210706110a020d0807050610080c040e 76
    0x82e061182680c810303012071710340040b0708103203034860319409500240040c4140d400002200c080e58401401440401030540d510301908450510480d1000c0040c04010002681030051600900c4075445642c540000104014070028423200221450340c00401449011422a00b02103458005540046165503405005c68a1885484208401e0b51310004483c02449800f20241215910030390903220241d0b40c0e102040c06442c031076121194405003c210401480d0f00913054000d825a001c65401c0c0996230341d00e0801d056400440e0ba442041100310400400158180c41c004e036850385002d052400c5007040f03010031404030350f043c42603120f25410103ca14000c900301c407468031500301d058807040c1c00040e1046000300940031f8008200c0c000e40303050400d54a640c4482c0341c0c1c10300200c01c200080198510f800d00840300c003a10603440c2012402801184070258503074603e861180e0b405841c03460350b542200c0c54840e2400344018515501038200345424000208045810b8001c3c4504480109030342d040c010145092 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 150750674 1250 150749424 150749447
    0x1060f1e030f0b06120d09090203061201060303020718020c060a02160c030623070806010f090f0905160815090712150602100c0905040c020f0f0f0d09180c 68
    0xc1860040004100089040c45920501c01642c80f1001800082405540e504140da102c06c08520440800d000d0350204c3e0707000d1343d4440002842102003155103450720382101c94580040c1c0050304403107402d020001c01c034000c50100c201c0c0c00404524040c0a80034143d19a40090b18504240da0005001c0d0009440c0341f02e003413030164019401c0010300f5581d24202006015101ca5805024171880381800700c18107800c941d40c03241c111621485a1592905c1c01140c500c03410f1000d88040c03040f1400049a0b48600c40366140290010001c0007940d8180048424072140080b00418100092071041000c045402035488a2201d419201d40603680c0703818030190380b01d50b6910f10140d00305d4601002045003010096840084502d9a000da40710640748000443c00c0d01d030920968008a40400c038204542c0c1415442545c18182c03901c180c607110015020b0641c10300c4044900f080003644000d00540041d541071115062400480c20321203043ca107003d40c0f6500840211155031100ca41d20000780c8036035030203181d4501e01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 150751924 1250 150750674 150750683
    0x20d020114120403020d111005060406150e04181a0c091c0308160c0f0501060b0f030406060803130b031305011506030b1c08030a111b0f01060f1e03 65
    0x2111982c410024000000c01c035400e80052094141e1608440d0140036081e400c480c111018003d011220101070b03000c3d00002d4400341e0030550342c10000500840d01240c0500048007913807181a0001ca20f010030044e26201044a10391000c50f40e241c200040d50030030140c448403134648003004150345030030454041d40110705003203401040404495070080b500030400d070401803080d280da401d00d4542d0748003294031071044443c44000c150143c2803040030444107601d22000d984110000f041150f202c0c4002da01e950040000807100c840080180010407185028060140400500843c140050036a840016141c14407510f0f285c04000004149013660407c00d1221880c0c01500034000f03001d200581000c91101c43c821540000e1a104c407080c5185052204a51612507100544843d40071a840d5810550b002518082c800780d51000f03101e40c9101c0e03120141c40c4403c41c4140c801d8490310110001070511400682001c0d41c0e0349840418004503207151403403004d842400d015210805900b258001400b030403508080c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 150753174 1250 150751924 150751927
    0x80a060503120306041401050924041a1201090206030a0c020f1507021002070c0302152107081e040b07050403060204090e0c0102070f060305040c15020109020f0f0d020d020114 77
    0x303070981600011405010182c1d01006000c1b0a03030410b400d4000d0a0040c0381d444180d00001c6090036040d02c4113000c00303a1140d2050020305c0d03803000000d4100c84400d085c04070354190300c04562105180030810005040f00d0f8034000d1041c0c800315800100188801081c41420036a07072403910080c90310801001c4c0012464a00301c0c0c800b4a5031006080008501b1201000103204400340140d2b100705d68000d0301c0e440ea9100c1d1040c21160300350350800c103280b160034128484451051025118056107484c08141d81d0700700d000110703001d00b01039100900004000704068201c0e2540b40c09400c107a0941008154055040350001c0340903103660b030003216244160b41c000741040f030000c0b40c040741b0628603500c50781c8421034031402c558550700750100582c2c640ca024410642d256080080402203140a9008035501520030082d40c80d80307907210b0424a220303007a604078100040c2e640784070203021824125221200c180e0708480023407038000102d00161031048201c800901404e900c3c20010f04590152440210b45903a070301d09075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 150754424 1250 150753174 150753193
    0x3130b031018051603060506030604021e0304030f020c01090e061509190f0f0b030a0b0102100c0807020607030209030304120f050102030103120e060307090b07150f0b130c0e01080a060503 82
    0x40c0c2c05071800b910545454080f200c03600402c14000c2c41440110781340a4401b50860340c0360810040250030a24004e40e0340711020b0b1140d4604002c81c0c0056100754425103c1d04050400c03024004d1034121542401d506005160009202e0326000784080d0342c1c000070840b4000da2a006011086c41c0c1c0c0d0280c590001c0e0058404100780003010f464402c030006980c0c645000721003043c0c0e41c00c0c1200ca5500240b180202c1b0313400400110310141c1d51908501c55442040c0102c2e8000f4400540300c100700c0d14990300d504001800f90042c4002c180e07050004c560091028602903040035401c500190701c85c403d074480c1c03071414864520304034108046060f2042c41185c21038000c54403581d4904000745d030804c03c18074003800182401c608100e070f803034071605a0340107540301d0f034903941c0079410070f01c0c8035406500102d000d8403682500e1002c5400e09900e80100070309911002000b142e03038003030241170000b10118072400034442400c09803000039466001422910b005024603040640f42c8a03150200000d101940105030580540c1900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 150755674 1250 150754424 150754469
    0x702040b06030709091a010e120a1b030b06010e03120c070b030f010f170a020d080c12040501110736180b0c07050d05090a1e05040c0203130b0310 64
    0xd010407607144040a0040c8284600e0605145600ca40010b02260b01030480200c4d908027101c4480040640b1801c860b4000660745841400b00e8200c130061401e019910030902c100136003059446d802c1442800e00c544d000da4030000080d00e03171a9003a131060110401082410b0040c1080110310024005140c10607680e003007080000001a409000c0d411100c00d180800045070000c884ca91801400150301905040d0b1140d404c002c81c46403040030980e0400000d000003034180909100301b008860b100065107030354900d4500050700e40c03121020315500c1a08038041c00c11018425404d405541c00704503001c01c45514242d01803014141d488210301450301c3ca0b01d1040c840042910006081c1e030ba0040c1c50001840d951003103012114070170810010100c2e004594004100c0d0b0040c2e000d0403040d04010400100c40b07464a6020a0454414404100d4200c40f864200102d00b40740c1314200d216481e40c07003d1890696611000800f049040c445c072806a1000030010340003092000b101b8005d040741283e811100380c000c804 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 150756924 1250 150755674 150755687
    0x509041203150e0c0f041502070e0627130807050303010617010302060a0f0521040b070c121103071202010b09010503030412020f040e060c0406091e0b0702040b060307 73
    0xc00c880400d01d006101511420140c1405088070001081d5880a54981181a90075007007004415010507041c0000300700003a4440d20700e0781003011540240303690b0740f41c03040100c800d2001402250060f4032400b0303466400c446049840140d50380c610700204050b11940543e136460002c5040203089540c021803c0e804000c2e0100045040700c0041d6507146405611504250a00d0030a110003981b161040100d51070003401401d2505d020452403c0607401c1c0f0980581c0c501c4075000c100d1304580b004000a08020412130450340a13070300709a481c6001990380c5065030700d80250380780c0c5000d83c006100d09401d9083e40b0000400445d45c02c84d601a1514400e60000080a07018104a8245500c10f0008070000b040c2418004156403c460f010380c080c528844460b024044210300c0c01014030341040d16501c0b02645c8034820030206004a41089020717940c3d81c0f41680050103828581c10900300c5602c81489000318074290548482540d032641c0481d0381e28551440010000d200102c68142c00150100401410a41151 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 150758174 1250 150756924 150756953
    0x50706110105090303153c13180318120308160c050309010309080f0a170c0306010806060a02010f060b0408070b09090c03060a030b0a0c110109150510050904 69
    0x10001e100b551118445543c4900085821b4050040c480c9603003d06440e10100c00500b61000c890b800381820b02c440c8120516800c4543c040c807200c61421500610b5060006a003401c10603210400c00031502c200c0152810404411030140c00c201405401c19441d0107403511880c0100194103013600b1104180c90098041102110a000740420a8040b80c040d14001c001900c0c0c4164004090b40c64040000010f400501c1c0342c40017030720480c02c1071103c203c00340040c000900c44100740b500d901d02c075011681c01070302003a20002d0002d50f00a000303009108990360032800040e0000c05c00c0300c1e00c9071580c0c003c0c1c134201d0040c052204400515424041c0000e42000c00758014402c1d914000709440300542c17960707402d07030040c4200d24841d500310080d5400502c00f07107a07040166030002c074005c0860700707841c0d030b04d40301c081c0000b409035a290314031941c0b00100c0241c1600300580b4482500410b009100004250311840f0001140c2d05184041a45800019500040c0400e240c2d003d410003c0c0044001c2c00c003400c2c9002112000b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 150759424 1250 150758174 150758207
    0x201060302041103060a06180803040306050609010b1312020f0303030f06031e0c060903011107050c0418050a0f080c07180f0209150a030605060406171803070303020c0a050706 77
    0x1e1a0118030500f003048078490b00c0040c2c4107800c0c5500d0710000321891000032018088001c0b010001041006003170005000450140d1008201410701c1800c00c24200f2060b44681c1c10b0381c0701008040007005c00e80070804100c40071096400e580d6015400803074411190000c48542c540400800c0250005851008900607042607080b2000b04101524880984201030070494555100b0440d100c0b061a02200822000c2d201900101d03080701184044003241d000403400700e6068024450b10350980c1002c0c401d03224450700c001108890200c0d5900e072030f919049010340140c072650072840c0820600002000701c901101ca114129011503955180840307406a20301c15010540b420300205d581c200c030450083c2c0f0300c003080c010b04105000e294100310442543c084a40001450303100c0c0d02c0020141e6411703010b440184140e0301e48948900d8681345d12082d00d4001803100d06a03076061170251800500c00030130345a849505d402d0040e078645844400138a4208000b00c0145284a00800031540540c851000030b52281d0300c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 150760674 1250 150759424 150759431
    0x1020a0f030c05070b041401060308030a0c05040501080703020a1103040f080105162f07091a0d08030114030307020a08010207140c090621010f02090a0603020301180902060d050403020106030204 85
    0x5181141a1401200b1410001d00203000300004501c0e40c0d5415030b0443d00c2003150301041c4121142d003c3c2500e0310f0740c0c825180c040000c801c120f200101406a0b45203a00e00d440c1c502d1400342804006455408041c0045e400c00d42d000c1202d0182a0258800700c5408290004407911180e80d0490b4005490003801006015420600401c041d902000c0120f40040a04e40754808003408030500c03201d0400b02042030340340001110010701c00010051141e800076000e0698003190f030840b81c0400c0145020305208090140561840c18408210948180da042d1078803013038089400e004402c0040d1450190301030186d8440700d40300c000511064154010010315110722051040c16114503035007070302d90740401e1225812030103400020b0708070300d000c044008510034800e40311002c400b2505115401c64030079002090340c3c1540000c0760152840d220320118028401490250b141d0b605011190751a032801c40024280d56031202440c004568400342a40c0610145840c10000c0c1d2a0600b0700034068a8141302c00e030302462a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 150761924 1250 150760674 150760697
    0x41506020c090108030904050403260f0606130603050603150c07060e071805070348020a0f0215030c0301050f09010303050a0c020a050d0501060f0b0306010f05090f0603010801020a 79
    0x10622001070481303200d480518144100101400040c0070028021003c110399a4030341c02c0300c00f10600318000042210403a16540c1e20780384224001908024149920402e800d0041c88000e580f24a403681c1658000d00d400f003060b40b0b034003010a280400b0b40c8118003c010303014003009600340a41c0040d080e01806941c0600c083d509000d07816450381c69030300036420229003e0558000700c098a41065070418030314a00040d201000c603104480100c50000f00300704040d02c200d0b00c046221007968045289030098402050b9541c90302c00081d5503214000c00c010700780e02040001005654a03100540d208001c00c442450741c030700c1d010300c00c0e020756802405002d2041e404800c20542a050520515050720350580f2000c0c40c10101c21401c1d110624121002c070b9020b40165408500d03030301c40400401d0342c00d1042c00049102c0707042044074002000d00b034101002516040c000c102c996a0301c50080301c2920302c103051850f640d030000d0012508004e900c4001780d400410010000800c443c0c15802000c494185580b81c0109a6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 150763174 1250 150761924 150761929
    0x60a050d05070c2d020405070e040c0207050d15140f0414011104030b09010b0a1e080109170c0115032010091703120703020a090e01050108160c02041506020c 69
    0x19000750031490044940c4d003030b080020910705a030030340300121150445003581c0040d00f81c40313003281c40c640020284403248079942014010100c0c0c004050010305041420440420b00e91155038a01824545181c96641308861440c0d000b2494180c1d100c5086140d480d060b0b5030b05c00c00791b0741910300700e8400554400c28000c009d070620800351803005c04c6079018642480c64030740c0c4084807000340c41e80e46195681c1d4003c05543d031312240c80340300030104a0301c200da184040301d6202c50511000c1d400715003e42d05000c00840081c0c144190b1180c070360b4807851450388a90a0b820709500600c01d03190a40c40e46428881c0120901080180440700c0202503c0c01807403900303454007405400440c0c005540c0c08180320036010301240407440c0400000b00c44040403a410400c000c1d0806840000691303503030340801e0b40001c8400e212584040103e02518151704640d00c55450070300003d110250003011040b0f034524207038902585a10a44500031007540007070080c08440c248081850000d451441080c1c050b115500e044501030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 150764424 1250 150763174 150763187
    0x30607020109050705010f030b130b0118050f1018080c04060801020a0806060c0307060908030f071b0605060f0d12030e0705030a0f03140c10050105011d040903020c060a050d0507 78
    0x450703114015011300b03864680192819840c031320704102450b84032000500d00e500c41c42490303900c5a42010001c5080418400007400c440030460061b0101c054011052205440301107548045030825100e1143c581c3c5442e01c212940c0204038003107030990740380c03400018408000050301201907800703e904210031942c0d4807401d03080384501c04401c00070801107800111180b034610058820300c100300090300d1904006503501c90032181407079411244c9150100034000903060311103200394800554201b0010b0f44c903000f42c0b1400700c4900818000d090f1921240041d220703456040514160140290104030350040500d4100498401d5070301e032200003407400c2a824400c2d1000220301e02142c00c0a0003411a6940c1a01e903422500140003060b418004c2e40241142c2441001d001095140f800c01d000d840ca4840c450b8041080e40c1042c2e214074104904c20005140040c8201800c2207814003c4400048404484c50143d007404242441d00d07510400104041805641140041034400a40f06040150750341d0320b1001da640 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 150765674 1250 150764424 150764441
    0x201081003030c23011107050c100219080d0f0e010b1c17091f0206010801090b010b1309020a0309031808030f0c070909061a010305061c080d05070e0306070201 70
    0x6103d0005280814944100c0c0aa001e03240b1102036140c810703451560703007900d01e0043d04584480000410400b0300000780084106c48404407032a805c2e01070807100084d502c1001446401c0c03018091581c0e542042601c404807280102c00801c103001020074120030f00000c1140b10b03010911035003480090100c1d854200101103d02d603c03002004600c800d00d071104055015041411a00850108440034070f0b80d80e20b001a007061a088042c10202c000b204100900341001a80006603070780c102846140002d01140500781500c034407013000d540391100c0d01d088001c0c00205910404480d4400240d010131725506400441906000341c9940c21800409035409601d190b00c0c0c816005150424003035410b030107000d2802844100e000d20304a40400780c840c80c80034100d4807041400c5441a40c1d6054071640b42c0040c40c420103501409090811003450523001003065400f00c0b01307002510074104400c4408000301c410944800030300d201401c02c450700d02041c01502c004280b000b200d100f88545000600041d1050084101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 150766924 1250 150765674 150765677
    0x60a021c0c1b0203012901090801060f1403030d060605041703040803070813240f05070c0509060414130b06030f03071106040b030a06050a0503070e04020607021f050403020108100303 80
    0x804800c020b4100400041d941000c0341e043d500c40b602a85070417801d450344104846c41210703505000404400140812016501c4144035034100541000410302c50103041088072941c03000d000c90880c01c02c0009003148503001c100c03680701c2d28280c0b0110f0302544c84405003064800038245408101c0c4882c003825a03e01440c03091000c00c0c0d004110329400942484040e00500180c1c2100410140e110351f01d104511071103186403001001c10314a64040a40d00414101820311103040c040e01c3c28401da15244100354880c0502c038041d00d0f01c1c0c4c0c08101c0741e480d5036005034a40c050141e401c901e1760a110502d2480314141403800c0c1e0380d880000001c00c0342841c3c00300c0c41501800320080254903042d5aa1b4800d50f120f0140015240e0100703040c080041c40710300401c01184540c404140015031039040c8002c1102c0b8506541045010b07034000307542806980000001203030429012114207856807168400145603007480c3d40d80e40b020b80c900410007602c1580110103481528400d880340c0d0415039070b00758840300501c102d10001c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 150768174 1250 150766924 150766937
    0x2030d05040e0a0b030705090403050309010c030605062704020703021509061003061a06030c070302070806191805030c0304180203190504030c0c1d0615040b0c0c03060a021c0c 77
    0x803c00461070744000c007900e0014007503130351403a5101c0010b80540b0013260141c000c10400000c1107001c0e1004c0c8100142004a81801c0119030300f03140c086800d46c0100721103181754400d0b0300c1d84d10f40075001041015085490081095503500080e141c0252183d4032100ea4041e885128000b09115020100b12284120401064000e001e843c0d900c841d00a40b080f00da1480b180f20b1a10b460b00300c10340318034008601c180c9605080981e1101c00d80350080ca01a1540d1100c0e480b9040002800624280b80086083c0e0007540c3c4004a007006290f5050305800c0c034a0203000b0b1041c07000044280c0c00c4a004400f0f40708807440c000c0c103040c180c0d2841d0101c000341d01c8111981c1c0711103c85400d00b11a0024181c2c80183c20600030b1400300040b8199680b80d04000f00a40c0049241d11300003130743d00c8141d83d070500d444c1d580900250f91098841c090030321001c0c6240140e00174401d0840002c2207403520044200000303440c82400404031001e5060a0741418029440741e003040f5200c2c4408840f02c840301c080741c0140c00140c0030310341d00c3c80f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 150769424 1250 150768174 150768181
    0x706020619020d0603231b1306120b01080d03060602070909050c0a0e1b0702030607210501090b090601030c0206061003060f03080c2a060708070602030a0902030d05040e 74
    0x80790304061688400019401d1007800c0c0181000d1080c1c0740074601c154120090081c004403003d11045030204100a240d00044c0000c2008010904c601e815200940c2c1c03951207000c440444401034001034000b81d2424580c00b030300d078090003030150481d0b04988580080d0b4180c0d4560307000407000c4c2c52160140002591119400704001c0030b941d448121040d001c0c500360780b8844464000600391450550103100a4a204001e0140d5074502c01240d101040ca0001424074065450f404651200e100412010a000040072004501c50708000344d5681004800410061503031079900740001000c018281c40d026041c404006030706035000384038120502c80282c00070041d9a031030390304001c01048118082c030201038485100158485110852a01441c42240717401e0b11120800c41d101e240c12140044000d40300108800042c106031a42e0261203185400d9035520340d25146414400214440c00da80108040e20000400c070640081e50b00c2416111710841c2961410b04c0004022180b40c0a240181510035040e400030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 150770674 1250 150769424 150769441
    0x30403030f0e060c010e0f031c050c07020d030f0f0e031c181d06190303030b0301020f0703020105060a08010507050a050304020d121d04020301120206090111011e0e07060206 76
    0x441d001090a440d100220380c584502140d215000340e0700340d074510303911525011390504c17040c031a0001c3e907810b420003141410641c40e1101c10050300411002c0a150307551000c10008000f113000c48000e290090010b000c42e40e090300c0c0c014035a40001c0394600010312401034843d509031042400b1407140c080140289420441f040c0304081c011a064100300030312800e00d900302a03098040c020100140031000e203c134012078007061304c41040340c0000c000c2d42c0314402d02840100d0441325480c03900151303501441e0009a00e540403020031300a03c00c94607441c00714000480c2810401d5130540009120348000d0320a1803a65689890042c260f86042d2404000b050707003403107081061840382e009035074428001440820080c81684514608580e4034005000060a01c0070b00c01520b41c114164444460381501e086182d917142026094981e458000000d1003a00000740c0c0450f140c1c4107041201d15000401d0081040c004d1804510250700140360340818898101100e03114010b0006c035001c011250990041c01c0c46583c0c041b007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 150771924 1250 150770674 150770687
    0x504030c030f0c1e1e03020316060902041a03010c0201051510170a0222180504060221090c06030103050c061e03090c12010507120b040b06070506060108010608040503040303 76
    0x14100304000c0a4004021583c9003080d120090400118001c401c041030a00111036174100801d1202c3d10441102e0350f00203640081114804000c510400e504c032262460004058a842d1030b01a62142c1401c04400d80a020410103009480b8120000c011441e00b05006a007610402c07201200d900d032200b081c208841c182100b903404103444070300d030900040da404000c100e48582d09440812159901113103d0401e51404041008200380f60040c0c04181c600d400c030950201d1042d105400041a260408501000b0301c40c2c06590071080100a511006e905003141440d901d0300c00c4440c072182d031094401450ba40e0501004032410b9980180c05010f050260720240803480c0d0000f150307001070040854050700e11746000e10146008080c110041c0c51000d1a5404025034210078249010882e4540300a10066641213488251003002c1c7c4a408250580b06900080042c00d00c00402d9800c00d10024000080250103c1c0e00c0344030309008d0305c4442c4544d8840070105d03038112080700e0043c040da00810003403002c83d00550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 150773174 1250 150771924 150771947
    0x9030602030a020906030f0f09150c0a050d1a091b031302120f061009020a022505040f020301050414040203030a0c1b0305030702030616020705011b1a090706030504030c03 75
    0x280054a40902240170480035481282e03018000c14001c1c0900880e40311048007a90050100c20080100d01d040c440044404100034000024400380054180c0706103001c1e00a588840c4c2008408220000304c4400c0022420324552486101d07624040000b030b41443c070180403405900e9a0541541565107410350180d00c00f40c01003040e0380c800e524498915464070300b00b01e44401d020f00d40010b44100c0c106000c0c4100690099080060024010b00c10380c0034035603000500a6080d2400c2c0c1240e40d0f402c9038a140722000d400d0340d03000b140c1c01c9424441450041182d42d00214101ea5055504104008001c2d010a4969100303070ba00a5054004200060b081886007114086032030284040e045206003511109100802c194000c0790160000f02d040801e41c5000c6c132000350310035075641940080d4401818000d40340d840c103000e00f5050014003030000c040c840100500c008001d6011350503c05240301e603480c3d42c19100c01201c0c0306046100791b030004a0220f200c0e0203010300903035058030390780d0910340280e806403140720380349 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 150774424 1250 150773174 150773191
    0x3120a05160c121703040209060d02012312010f060807080403050408030703030518010501050a05060c101104050a1a0f030c070c0e0907080a02030a1b08030703090e0106020c010903060203 82
    0x1a140e401c0402c8441d0304500040000301c8641c41c0ba9642898406007a040e10001104028130610810016071902c096080c1e1024003100c5101c0042e00300d10041c1e40c0303405007081c140180b080d800700040245110f030b0000c0445100d0070303148036003030b07a82d5441a0b204039155004100005207204040341c0d581d4002d91010790040e1003814070901301901c13400d0796031460b00300c0c031010350000c0d40300c4082c07041466000c0b1b00080c448a0801c001d00240d81040d001c41c01c0d00c0454400c40c0d0203160300041c3d000401c1c009100a075240800f01d00280305104400310031102540041c0036035449019401800245a820190075a8031182c41800c0c60b03040030035180c40710042d0340004047c0e41d0220810485600060704447d041c030080c10810344011b88900309240c00c9450454650800c41095108088134400360345d0018211003802d502c80a6002030403c0c00b11190300f2040540d00c40d070254400811268109034119600d4810b6644a0b075030342c4000d83e41d030b00f0100c4e9a0810b20325414041a842c480901c04104942c0055500c160302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 150775674 1250 150774424 150774457
    0xf08100e070b0a0c150b09072001020c0a020f060403031704030e060703090f120206090609030a0b0c1c050f0415021e040314060c0313111206090c03120a05 68
    0x790b56014405921100e80c01000034194140d2004101035407011440c903540e000d0007084490031250109406500241696090000b65600b803130042200711800043c60510800954980c0060200e00e651010100300880c031a0340e20b07040448945c1882001d441c02c803605035030741520407003903510070707550102000d84290100303d1642c8541070151217110040c00c065109940e035084880c80c2050101002c9095007044005401c9101101c0160f81c07402c05481d441c0d041114403564403c20070002914220603284024800c9031011b04100314031011801400c6081424110b04072500342e42c0c0d1566017201c40032140d4a0010400c60041000f20b8070302d003c2084c6411172103070018642100e102069500d44080740f0b540e00141c400040510400454440c5d805da80a20440100700b2030804101d0541d603400001c010b04400c0d4030b008201820301c95840c248aa9a500141c0501d00b030407001e18403291a894215010307074aa1003088081031141c02c0009800070300c60940400c460030700d207880307500b141c5070340c850900003000303520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 150776924 1250 150775674 150775679
    0x1104030b1e040b0604060911071506090606090306050705131809060510050411040e0c0313060204030605040303181707050c040e0f0d0305070c0209041a0a150f08100e07 74
    0x3a180a0709000301d0061400140301e1801d0000c20090704c440f501f003080f4043c02c022508000380c00780e01c103951050b90b22081d0404c1902840b0041c9004200c62b9000d40140740c14007000041840e005501941502e002e02003d203e00c3d92510002c1c1c81c2031041500104040c010301c4010040d081203a9030801c1e82c8007211801040c104503648a2605072807042c2e8615a1744890ba1008000c2403420348107000f000c16841e00202d08092a107807414103951401000d022455400100040c101c180c001c00c402d03104c0303600c07110840d156600c030301f04003004210441d01200428980300b0002484034814400060140e0f004445803901648010205002e411940044506205404508200d41d0f9a030164449407000c1070010010080071400280c80c00d85022918000c1c18a01814424a15800744502c1d10954040c0d981c82d4198036a40780503440c00e01c8440040342c0789030810b01808450072650b0841d041e428109980380a00c1c94481c2686c0382120b58500c601c1040b580071480038031100303425800c28011b83e5101002e9400480c3d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 150778174 1250 150776924 150776971
    0x3171e0705010b190602071d070507050a0501020f041805090706050901020106030b0c2a0d0336020f04060506070f020307120302010f0f02092409060d0b0307091104030b 74
    0x100044e6130302c0102c0c0650506000032a41000204000e0441d0004c0950361b440030301c6240c3c1c0d141c001400e03110812100003000e0042c00000c201d104807555011000319552500a607005000360050b005000c175140d20415040007000940c0103a44c05501c140d0f000c0d12095182c440c00340e6107075100c001d0341819035483d940c001000c07920409095100c0e44c07045c0001a5140180040070780e0b14404042c0c41c0301400201200d4644025000450454070001803c0000309011101c10300c441100004000c00b20109240c6031000b0f4242e07188a2000105200b610640004142c200c108002e07240c240c007516030040c005015800114031f2300000200802d00103015a0282501c07002882d4207a20520300a0340581e4490740b6100304800c0c01c6c4905080c40d040030008504040306a800101d491201c11030058028019111007541c40584000700c9015000043c1099074030b0003400d9000b0060602600c00381c1c400d010301c103000079046041c1e0042c2d110078240c01d02060f01c0c0501b9a507a40c403200102805440708044501960b44546 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 150779424 1250 150778174 150778189
    0x30d0f150f031203060e010e070917030702030f190f06021e031005040504030507060e010617010c02010608030703140318010c05071e03140d0207020a0f03171e0705010b 74
    0x505151004445450640c02c207010f4080010050350101481c0560801014040402160540320500200400c68841c403004a61110305500001c403040707103841c0e076044025000001080e88038400e0302a07510300e441c00c040e83c1c0c4d207980c00c0080b480241c0c40c40c81c4801001600662820840c01d20610005050007101b0003905603011901c2030fa1409004004144440071400102c000e008050844046c000b03840c0566005040380140ca8000709203a446680016500c142908202e01030068604211035048401d1101c07030280c14a0a6980050b52030501c020070f84550100881310600c2c0c0503202c400c00c98940d514540055803004080e051082514501030326504820300441074070100d241d50f02c82c1c940d481824003d52010f2100391104103446148039210010f600300c54103c0105030125a4240c4400030310303c0e144042c0c410940000d60000b4247e074081031009040603400142d80c050b00d0000000b4410465510003803181d682c0c0502c4180344400c200e50015404402031902e503204038008a1b03216544804901c09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 150780674 1250 150779424 150779429
    0xf050c0601060207050a081603170d0c1214160509181003061a01020c09060f09091011041d070311070c032f090c0c07090b090604020c030d0f15 63
    0x50b04440005c05c6540340072081c4502034010070740a010204100400000c40c0100361100070140780c04083e800c10002054015203500b481c0c01403081c4010311900318010b10080340c0d4403190448610302900240408140340e104d80c403c800141c01c0e048000c0c0d012a0582e00c80e04164182c6920551400000501c09003140107a406402c054200c0100c4504604d011403d5030444041d50401250110444003e80ea001400d000700d01400c0e01e42c03031450344500d804218601c2081607040c3d000f44440f003e2028400000070b0b456601c0001c48001c00505001c002c030910749128520640344901080545114100342c0d20500a80040680c24001490340d030440248100d03410012064401b8a100e4000300140802000d80007406103140900c41401c506d014900120030030710701d0000b40910008000202042e100c40304903800b03210b800c0200c0311307880c3e5510b180001500d10303110211f003e075000c0d0303021882d2070a05009880040c2510b0f0007445c1012600e100901c004d05201203007080c076640b540c03105290031b5000f2012801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 150781924 1250 150780674 150780677
    0x2190b0306040f11030f040c090c0503100501080f0a0c121e0f06051c1104140901060602070f03060506040603170909060d020306040b040807060f0b012d0f050c060106 73
    0xc0341d242039000c01049420902c42440203c1c240780404920044503400c0340e502c24032a2444502c00d46176414426200b07401a089011064a0000111402500640034501c0b404000400d120565103c200440c2c184c80150345561401c40140302046950525403c42800e550103071802280010003403401a0680b008040103a050f00645000103880b40414001e66121b1800301600b84580b03032410340400c00100070305031003402c8540c00c1000030342041107406464020803002401408040e02c8101079000402c1d0680f0701012544c81c20000050380c078001325180c0c00701c40303e85180c4000c242c519200d50001d0030008090070780c031035552080803000070201c11114201500e1803400c40e8485c0300b03400502c210004080c020710700c1780e00311002802c0140d40000d0f800d54440c0d8080c1003001c0d6034440c0e02e0a074140e402507100040419081881c840f03243c118580c01841070002c00d81ea1201010600155147c20954210041031103404524482011078010905104042801e1404510b8090070449681c00c8c42c10a810050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 150783174 1250 150781924 150781927
    0x1605120c031608010e01120501091515080f0a02010f031d03030129040611070306020706020306090106030506030715090503030408011410060207030213090506091e070503061302190b 80
    0x9501403011540b21a00d14508016101e94106001469582c42c14400e900c0e600b91003100b40c40402600390400c00480e86d0010104c203a141c405160000a045006c03154030075000f0340000040d01e007900003001c040f0506140050314561145400440b60900050716050500d9201c1112007850328080f60b1644081102c3c3c00550745a5043c032110903038007a80001c00e11040024400d40303804401002c01110b044840c5820284a000c907114101420015690b20280003d4030110b804d1081c00010380045118410407960075a240e0380700c1d1010350489806079001034060348542024000100d8150f03c02c41181c84030f00f003003204642d64a00203407640e4040d420128070340e5150528481008100140c05800c400ca8135121038165080103002991390b5181c2c1b101910880200602000780c404603401845400d80140556200d8134189140b555a03841d00d50061801c1e103803044000b90101e80108095007134600013800b902d00c5071141801c001003d5000b90341642e04c051303410281d10651134100001e100810030b410245 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 150784424 1250 150783174 150783181
    0x8030a1e02150a09170301080709060b0703080a05180a08130503030307230d0903020d180f0515090402210a14071b02040e01022508031605120c03 64
    0x9003125000c4003103040d5030001500310b20840d280210603500c00c4000d900080c4102150070040e0985034001800440a903001001142e200404681c10081d10850342c01845800e5503841c9503810341c803070048041c0000e1040c901003016437030190000ca03009000040001d12052a440e021400d04801c23700032140a0400100030815807806d429280c0200001c03006141546003080010340001e03170f10910070613580340e11120000540c40810a581c071528410340104000c40c000d240103076032400120810408200404440340c03180c0c80000c00441610004044030a05514000521583d5504180105a60b0705d00788010155030716144054071666068403510000c8031800541d50f6003500c0c01408a52075903090150390102d01c1664407295400807a00d203404d038602c2c11420700086041d10001d10080d84503091070840e00002905401914182601000050390b100140401145802c1c0380800100700302e4041c03001a11003451a003803c00700110605000307180660f1803d100410001c02c84800c07500e40008801e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 150785674 1250 150784424 150784457
    0xd2604240201060834050607021003061a1c09080904020a120e0303070f020105070206070804050309030a06060504060b0903060103121112040e0a02070c03110a090e010603030f0203030c07031808030a 87
    0x882c1c2c0e02c819040c80c2607002908010200f20322344554400030f8011002d002104081c24441c0e40a54001e0010300c040b2910030100b009926200e03070007a0401020744210403456603450103140308221166610421140c0f80607108802c7c08003030342110194205100a0607245100b00d2480e019403091004141302031581c0b03103801e10f40a03000209210400b4110781c54502004001d507000501290407240b0b606003008256120b15003503207588100c043d880c2c1c2500545801e142000380b141c019001b505e0381298140800c03a110b020100391402140d050301d074183c0c0806c00400102d23402506c42100e4500500d80b0050406034400600e24208030030700b040315801c40c0050108801411180b4654000c0b0f10301e40250f2074038030700fa22440c4a6010b41e01001d4410750f1031030040c01c0e0a503640c010701d000a1040300360038000100c4000d0340fa0f00900310ba11065012410701d0142160071407010003160b1090800340041800c018440e2000c0741d0149a8881210b00280144004590000e04202800002a0700d43d01c0000f85101c007181d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 150786924 1250 150785674 150785743
    0x6040b0406080108060403080a053102040b1203031801020f0c100b04021630080105031509070b0c0c0409080d14010501020a140c0d26042402010608 65
    0x13160055800440034400000d82c40044150000c280c0c038000319450711440165903c0b90303035800c29015034840514051480c1012030469008650084400300100d581100c24401c081000d0010100590000c00c00140c46c80f0070510b4100c0c4200408000609040d28860141240d50004110f400d480c2d000c00d415400e624494003c140c410041590158100000180340342040c02206800400e92050078081c14403000d40c2000451124806c910b10740d040e072700c4031100582121000e02800d402400fa80d4442030302d40c508120b50740d014072032440c01030054500c0c0080000180d00a4850f03081c00b401a40c1424006030b840d80200040035010b071258641d90341c4540400f004403480c11307041c4550100f8602c01046030343e0b00800e68002158000c41200c070500e01c069811403c0a108501c15035000660f05000800c0c0b00c1c0041c818030390b2a045168182520440590164060185101d285d400310003031000d82840c000002c00041c641c1c030070360002050b515140c2803540e081009006540d12070440c07801c09000c0f410410715 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 150788174 1250 150786924 150786929
    0xf05060c03040b060d080a050307020c090c070c0803030606220f0311010e01020f0607180305060a06061d030a020f040e060109020a030c0e0913080c0304060203031815011703040506040b04060801 85
    0x54145d00010100e80c0c4a4405000d030499460500101000103080c0c54000c4c49911604840208920700d10b1074405840700243d00803402c2603549403490440410010f00000c1181c1c0960740081010b03040c4071038104a40101c188812140745214210719000440800e00d001e14000f551207030080f42c100500310b800040800c0d0840300000d04552004030711216408001c030b03032181c1141d41c0c1d18000d20348910300b480e0041c4201d4036030b00040c114400c6078204100c003000d6030701a40a489080d56410001000443c4c552142901d440e280341d419040309003040d006141082000000000c041c1000c01c820000740101814031b00c0992180c082c89800203000501d143d4544180442d813015400d0031881da98001c00814020000100f0101040323043d4001d42051200c4071007580c0d800e00c0304c44100e0741d8494881070300a48070782040d03c0498080240201d914151280481c5c0d028035a0080111915160f00c0d0100d0356039044800e4070401c161340400c21020401b615000e0060000c0c05002c403036281e55030301c0e148004000f4641603 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 150789424 1250 150788174 150788179
    0x509070e130c0e1b0d20031005060306010318030306060912030503010b071a0907030b010b0306030a1203020423100509010c081c050a1d0102041206090f05060c03040b06 74
    0x4524040000d07802800b1400b9103016000d1980302e5603600c07106242c2080c60b0301d40508018404590b0a42103112078000300e107140b000c68954103860111b0280541c2501050f1800c040380200c141c001e0215092000241d0307071204052401068881981c42030405a480c86041580000c0d00c8090501016801c48071400c01041d50f650444010003040d2801004e41c04103000e501101440000d5003018000e0441c13520406036180c541e44803107401c044282d03075581c0d034641c44201e9a0318508400080e01552840c1a2032003504040d0240900d0a010f40d503142d01c0c04030746003040041c140c0c02d20000c6216232420f21025541d2000007040707401003e400742041840e1008101c52802c10404001e05880790343d000c0010004194040844d50f00d6014192050804140304103003440e25078a824204210200c00d504800c0c440b40308000c42d4a590031203084042d003130780300703a00900b9034101c0701c0c101440000b100e075840309440e20300a010042d203030171060351450300780b0005844520750604080248000e000e46070381c410b40c204204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 150790674 1250 150789424 150789451
    0x320010f110307090302090402130e030309010c0f0f031d0615010e1905010c050a17071b1a0f070506070804020111010606090b0d0e0a05100b0a03080301030602090102030c010509070e 80
    0x20f00b500500052103804020700400080c2c001c2000c6450b80c240900700d403691a44240a20700c0c402c806d07656250070480302d441c200d40c24407245141c0e075401a2107180202c0d4a83c0e841000310040c0000030f0b0b000d08a007041880301d159001041d4a52994244242406680303040a1100780b0502c13a4001070001c00c540f80000d1280211419000005110745000c0040354820309150714800d501c0d0402038144184590301901d154a00a018046400103100a20641e441038900b5002d9043c00161090384031611301440e03c80e40b264104d07030480c0c010120040c0c190142034811a61410b16170741e444c00c2c1003000c1036602102041001007404210341e04001c0005401c400c80000b004034600c1c2c580000d202d8060b43c070a00d1500440011240080c80c1c0c1c41d040b48920b00c0000040302c4030b0f10580d00d0b110b40d8854441e413403100d60619104000580d8a48411444222078101104c282544d0854136001c00a501c4000c60ba415884208071001d1200002e01a0b41d03c00c2c09a040a070034014500109103401560040018440c1c210 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 150791924 1250 150790674 150790681
    0x5060603040b0601051207030b0111030c060a180c0b040f1d01060813020916030c020c01020c1005040807030311060601080c0a03090201020c15040914160c0320010f1103 74
    0x154082925403040e0003070701140c07954980c140165031502c54980300214003800082009050398050308460b204400a0381c1c0c7e550440741c1c0013038450703c2e8011080c1030455501300b80003140030780d116508000c4c0c00f2900c1c020344881c4100c0d265075401c298816030780084800d520103d010403003030140d00495030003005030042e0318050401d001844445032405001e4181402040e00214245c0100c0302a001c2c0103940c054016829400c2680307250611000b40030242c1d0000707042002140d041c2e07101107041300070310707030103800134200c29405504100c0f0b200300036100c541c20001c041c80001001d80041128900440c02074590b030000c5008440120300b001c00080065040c00012000e0001842139601110410100c40c64001002049440103d05001c003100c43c00e80d00002001904d040100b8400040080b5a04070348200300c1170803030041c0d11703048410844558041e89004501c1d2100707a40030b0044040450702c00e2600222034108001312840402d242c211405c41e50390b4441603c00711901e10320a584022588211241c00c514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 150793174 1250 150791924 150791929
    0x40b091608060f0a14011a070807080309010c050c15090a060c0c0c1406091915031508010504030f180504020313020117010e061207030519030906110d03020f0c12130501030506 77
    0x5c06114054001c1100c0a07006c44100c0614155500107a01000490313640320b0b903044c80c014540060780c100c1c0155103005038082600d40510100c075800380d504005404608400411000c8151005144c40803030b0240024000c0000c41510440b1085492500d030007002c440d00e420600144001600443c0001c0301d0400889403507520076040d00d0035200200c070f114076010601244428046c0c0c055001001014414a0400e100b90700360304550b411920080111415554600c2403900341c42e015140503000c900c85c141c41c045924490104501c0084c1d1014000c0036150303070f03000800c0403a8001c54010140c07942000300b00301103603400480c030514911402a10600c55040440481042a001e0941d42c072900c41c3e0040c1102d47c0c1c4082c445500216004401c1e21184076500b014044204402034040b00090350600003c031780c80340110460811500340000800c401c200880040e0001d40c0001c84146d080242402a611f4202040104006180c4400d0700300d03864554100c40c51079143c0ca00e0f08441d05050600d020040d40382c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 150794424 1250 150793174 150793211
    0x21c020304030c05100c02090406050601030e12040e061c030503070306150905060c0709060b090f1f0305040c0e091f02040b0f220f06080f0708040b091608060f0a 71
    0x44500700c0d0805c1301c44030084800d0301c1c00c40d04844000c0d004441502000140100c40d4092446504203890a0004606039145d1035100d42c05103550356030580052006000300355a90208035880039001d03141c0b052441180c20781680701e20203590210005407000040040080c1c1c940240001094030420001181c106000043c24000349070244502840021070003c10f400d008100000041c15122020446035440f10303131800c2141d01c45d07100c01c0d00a1040c2d101c50a0a42000d00b0540440b8421250380400010f038400c0c00c5000d0000a0001d035000700c14468081400411401d646002e61085d000601c445280c0d40c1c01003d0304514280c42100903441171004002c01d0201d0421600c0e000c00b00c0b90101e80c0c0d26048074418080346041d20b00010016450030011500411180d950400e03280d00380c0703030414590764080c80510100000c50300d001c0012040701c041400200c204c0136a5400c50030b40b07020307160844410400c0d942c0521040d840000b882e4001d1060218100c50308602941003100d031310b0203000c49410030303403071030280d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 150795674 1250 150794424 150794429
    0x5010807120609020c07080f070b03040b090a081204020112060807050103020d110301081006140a140301060b030a0b040617120a0203071a01090507090807060e060d0c021c020304030c 80
    0x1070190103070958281484a80c4044082c00d00080119201c121800032190354580340d001e00c54807807150100701180104006002411144501c1300180395035201d0780d81d8065200050400b040320f11510307040d0000903141d50b001d07080e50350040c2800c00b0645410300005002501060011088900d000018001c03140d01044c2a010fa44081c04c0c0540e507103c00c010580700034001c0062000d20004044008240800c002c5070110000481e604117200064984a0709042c01a80d8034039513610080b140d00030003803000081900c1c54100001000090107a035102d02000807540b0072a140900d807507039204541e859140500c5040040c104000340364443c240c0a80e80c007551180d84103250141d034007001c00c2c0146142d20800031030f10003079440b4508a455269a4003c0c8814007028000c11031503500b0a80000c0d0014800c131803a80480788583c0003810180d00d8000d050303418009011040c1e0b0002000c100c050313a45c00040c010160705c010384d5030040c810805181030082c441200b60381902d08541042000b0004203481400410a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 150796924 1250 150795674 150795677
    0xe030d0b0a09090f0b0f010503070909050c030a0602030105100503040f02010e0a030c09020a0809010207032a0b01080304050a120507050114090904140f030702060f0a0917070302010e040605010807 86
    0x500c039811000280c0741000a03844016100d00f800380340700800c1308060096540911902c404c03280da48640e4001103d415007405080d42543c80054200514106900201140740c020010b440300140c0c2e58012078145500000c0c10b9070510340000040201d42420b00341c00350481041d10b449415410190f60780300c02a1031004000e0304100100803000525510030440600442d40020f410084a554180400c06500030f803400401240204000032030111040c003c6448440d4595503047ea5003800c03184809240001814071a100313040004482c0c0040c8218072118040c000c81c0c030045445a01e4075080088804098010040072482c000c540300c002080090302005440382420044c0700070700f1658601d5004d00035440c2c80c40e80284050107210911190349076000888580005032018502d03e209182e6492140301c5009400060411903000462b80807405064401100d00e486280d29559440009841c00008070201041d0001a0100f0031507070080400c4006d420107031000d00003940352500203012031000404110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 150798174 1250 150796924 150796931
    0x2040303090902090f03101401050d020904140c0406080307020f0406050a030f020301090807080702030c0907090614070606080f1b0d02040e1204090e0c04090b07140c01021801120e030d 81
    0x90b540d44c50082c0c5617a204409003c6030301c5480c2040303041c005031010781103003140c2110308000401d80b42000c40703001c0e0503244c01611400c159211079441c0e410003010704c40c9192540c041c4038203600c3c5a80d15805a4002080c54000440e01c039561801045a0000d00d58101c42c4141e00e0b0100c200701503140d40c12080c0031039400000d811100c81d418000310340035200303840d401071004030002171800411803001c0140c0002d030b00940441d988441820305204420380160b0703022000c212a00000c12049110b4441c41500c03409000090f070405603113903034942c20346505821440042d0480480d20014080410505a9007044d00000a08103800c500c040f40c94103c0180780079010f00d03140c000303080b150001042048013613aa00700059681341d40e54a80300e0018210015011400d01034518030082d58542802a0103040da0041c0d070a201c2c43d12000d9081e5001d4011168110b02940c041c072001905c20f03400e102824220790151030403289011110001081000d03d100d0340000549421101e0310001400030a5402c05419600c001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 150799424 1250 150798174 150798187
    0xc0d0302030702191701060e130f0c08030406120603080406030507051c060501090e04051c020a0b041b050301020a09060e010329040b370b03131101020102040303090902 74
    0x101e0862150820107500034480d5450724101035a00400001201c20b483d802d03201da410092006030981d000c47c4500d40106040d4008070b01802e8844030301400c0541700301100c4201d07011590b261282144ca503805070861b80c2011034104245500130a24440513070030100708114041c2140c2d5442c22a0040b4000c460800d40d42c0c0000601c001d0290040740d502d60038100b2602c03040b40c035400082c00640031a0207040e002a591400010f0b0440014400038012580300000d044202d680002d24030f05100c294125004611407005810041469090850300aa00416080d1b80e402c94001c442510100b2a91115000760310403c2800d01d040c1c1e1050000341521800e2414040f020082001280a41669400c2c01300d02030a81107804003901c0c601c030310f2807400e48003038605003d00340908080100c58154804170640081c218081030350043c4012030601c050b0408070320342d909044c0e00c80c02031011035001241e18400d080300080c05441880a81100300c40104000d1000f5446c00d4155a00180000d5140c45130411480c4c011404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 150800674 1250 150799424 150799427
    0xa0b0705130819020a0504270609080307030f1407020604030807020c030106090501180b06030c030402040906090506070915050d09080903121b010501210c08060106090816080c0d03 79
    0x500000c0040400f01d5040d1002c20301480182500755000301d2007078400303401c0003070981014042c503408114601c0c901d0003c60740d001c9550b0761004502904403242c43c2d0f40c903041000602214041c601600300c540e800190201b40e400e10800300c50305141614907103a41e500070024881d90008515a115906282103401c030b8441a000340c0c07030418210141a45542443e80100340411503a00441c120340940c840b03004050f05024941080752110404242c00c00301c1040010008800d50009542092000d030000035585010340f6020202c03540c80204441c540c1050007800040c5500060000292028462a050003403036910050654400c81420920254482c81035505210002042e10000040901600e4030440906091001c07a40040c02d12500c6829090310320414000511607241031340c2140710b080d00c0701028a078841403000c40b0441b048030b003c9514103003c0f404000a0110380e0003800c250311011242c0782864446801c0c10400c074a01c0144c1d515a280400c80c60704c0010f020b50143c44240ea80c0e10a81400342030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 150801924 1250 150800674 150800707
    0xe0c090415051c0c170a26070b07020d08090d0f0c05030f04050109140d080306040f0c02010b042306060a0210050c0403110405131b050d080d0b030a0b0705 68
    0x107a0f202c980e80c04607a41c56520340c1c44809800d0701c07a0b00280d001030b449804200c64a4480710100d0050341c40082c050b0002001040d21400044050540b15110b48200d08240d116030f00110040750004900320920803070360b40400c080d10000050b800d142c040c80c40c1403210107644001c4029901c0c2080758420f11f0320000ba000e16a000002c90f0480c4c1602e030380b220b50400000c0c0590240c0b24950000e18000360015461040315480b1841000041c0310034500081c903220040e9075000501002e500540d070340038540207014607124207402100c154001084400c0d0410421040710520b10044403594800c001006203503240305645903000404444a985400c0a078034103d1500d444031a00c500898608800e0008903810b94000d48200d0b0311503086d0801d464503603000c2c00240d0300241c3d5441d0092000c54071060004895055104c00010807511002d92907030b0780c03c000344030803202140c2919524400580c1c50b815902038090f10000d54400d60040c14407122680d580c10420400070031070010808041000c0200c2480c904 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 150803174 1250 150801924 150801929
    0x3071a0c070f0c030308100308071b051210150305060a020f09090f040c0504020f1605010b041a09060901030203070608060319030e01120b0a0902070606080706080108070e0c090415 79
    0x82080c190300ca60303d00b90000c520356000135804500c88100082070310000c44483c0e401c3d41e5110002600708000c69940e110103441180c6203280d2010f00c01800700d072644600d0751a01c0b108140704010030172500403807914003c507040e050069641ca450784c6002c0c0081140010820307000801c2000042c0d48090301c0110070301c140569030712a64080082c00c280314003044132070032003070055002e18020310110b0341d12400c020481c03103210103800b00c803503080c0401c000c2d01c09000705255403240036000101e40d480756000013504503071081d00c1c102c07184030082d84040141d080c8000181d9001c8400d4840300d410b035045400080d40c032981c910030441000b66039030002d50f03141c6080c0180300000756610074a60040305c5170b02e800381c17400020f08040c5001400c007000c010003101e8207004800c0e4552010703042e03541d02410586000041d500001d0240d695030344034840010768160800c20740d001000300303650b11115541001c19090601c4416071020345001d85031010b001502c048001224074406c01241c0020700d030078a40f50101c00d15034007035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 150804424 1250 150803174 150803183
    0x3040b090f06030906090105090a02010c020405090f1606020601120503090907110604110319230f15010f0603050402060306010c061805100609140105101803030c020f0303071a0c07 79
    0x310600c62072500000e03041c0c1c080c2006c40020b015654503400b07119500e44000c1c40103400603011f800140c2c0541015800075400ca407c8009541c01c0107444000d19280c4000d031409181c038610309220030092a81c4c184400c501500f00c4920b2413561304810340701c29a03603000d050000c40c0709121074804103107807a000b18800304403a002841134418516080c1080304c010032290100b01c1c0240144d500c05030120f141c002a01c110650311195400340c2c49403205440c11004402401801c0a1040f0001d84c3c0098004201450b0682441148040190305054140041800c80da00403400d03d400c0030b0500005a80f24419280c2c820000c1c079000d00214481d0401c0c0300076005403044002c00c89648082c030000e01c1401f00f906405408040c0e81842840d5503004041300f10b840c1c00120604202e00040184403034540b0050409c40324407903151960710002c1000403030640320a55072040300803584800b0503e0031400c100e25101500d0b041140550305221180c4c540101c01c0c2d10080780c41c6160b203501030005440344848015101c516401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 150805674 1250 150804424 150804427
    0x705060733050103030305180601090b1503040b1e010614030402041b0806040501050303040303020705060d0902180f0a02030601120b030304091503020301060e07020a1103070e09030a030b090903040b090f06 90
    0x141d90303080184800e002c1900020b06140000341d09138901501c1400e013010400040c03500d603180c11300314001030400d44441030b405203501c00308071000711400380614083d600807400001241424484249042900003d03c1c400c0b0141d0001000303116003244410007541c0700b01c00c015589541e01c0c40000c0051005003518030301021800804a00d031607211035003c1c800c10054070b08104598980003010b5070b82c040d40c4001001a0321030103042c4081e0900c00040c1c00c0d0250400400303d0290040d0740024000c50001c500c111600e91403108003c4243d11058545070031501218085186042040000f0880c41d684460f52040f1034842501c071180782c034200201c0340109000c0b40308200078540318880d41901c42e1131344030980c840c0d0708003200070070818201d0001c98001c00f0326400902c151042980e84031803108508107110750500a2250010744c9148038407000340325800b41c4000d5551400c0003440901243c416040d402d00a40c1c2040c10003900701c00020465081e115641384083d15035900d0000114490070740d40340303070303821040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 150806924 1250 150805674 150805763
    0x5041104050703021b0c061c0609020c03070506100e041416090f0e010501060504210204050a090b090c06091201020c030a0c0c060509150304050309030604210207050607 74
    0x2810350103840ca4941c40c2d4140d1100480c441c6016960350034001d034041d0300c080d00f0008a29080203070035203e032309082d4403440420031980c4c4000100403604055440240ca0f00009290005c22106101c000e5022041c40000c0528a0a00c503641a050200800c000c1a2a0000c1c0703580d0000003003003290780f140070807114114000c0c50301c48040902611214549400090801144010820707045c000d19068441c5aa10b2034100b0303181c0302400c0001007180180d00c042462591b59200562100d004203807058214460114004150b413030b04038045100100a6085a00314805030400d656522084641c10038003120741000f51a065480e080c024860752035444140d2000040102e41203420001c4426404d0041a9100a03036940f10001d80d55407041149075980084aa03031000d002c4200744c00030719001070240046904045501000c20f103404c5060341c081c0d4000700c0d106c0c0700c01380365141ca16004664541600c003402c5030300c0c645004102e550040c124024802100740094580d00700c000c102c0101ca00420507100717441c448 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 150808174 1250 150806924 150806927
    0x1801021501080c010e0a030b0c03060a09050906250801031209080105010f050a08120418020c010c0309060b010314130609020a151d0303090904030e12060603060108010e060406050411040507 83
    0x9001031502c5003c2941140c55120911b403005080089a0f00f00203003903100d03612a490041d4652005200c154800b00d568000302c1c00c08070074860240700720000d000078501c5061103c002030515080307441680164806100754050325a00010060440303a20004080c440a080b0078117a80725982a040107400358030b07104c0002003000c070740d1881e6800c550083d13403c17101e03a07920b4040305600c41210840350390f4060010402080101d0a150742c0b4550880040001030400c20390030782041c05c3d2408500d00b9000240c0320040cbc1c0080c4144c52242d012074400c00d09040054440e05286001501d4005140031017141201c6c08070301c00d00006820140450b070340100040b0301d4070785071051190541e08502c0303104001200714004800c50b815403100c0c42c0d01118000c00035814600480100088124010700c11410403500e20500301c2a1303181d1800030b40c0e82d054150084c2c021803400c00285481c5c510168814183d03030381025031019041c200030070160f070416000782002c903455031941000506c842da1700d4002908a450131040040e8503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 150809424 1250 150808174 150808183
    0xa05030910081b0a09030c140f0f01020a02061303061d06010501020607090306050709080f0106211e031707030501080c1503070f030b030a14160803180102150108 71
    0x240c208948a0303154455800d4122180202282c40e601c0740c40030400600e0b82c12450901503d0002a140703480d102007516a9115551420380380e210010201010b000540704c2c4c94580d580302d411402c29208141e504041c07500003507a8109140c0080e0180d9800921465a0005100c040026640000e014400c42d00201146080c52030189401c0545005039400030660390310215625000d078a565489030011811070f2a0703034004020143c818814000d0b10200091009001c0c48001210f00c644400041d05510b07007400100034500341031020036003000d0311982c1400206548103201c802e0103c0a000c220030541c41c9003cbc1c4034020700b401840f0144800b981004105c40e4950003440c140d0382801c040d168006d482c1801d0020100061014000040090000685c3d9620840f54035440c11114034000c5407600d0044040703030800d03070481019540f8014000d40300c0300b01c52042104816034445440c08035040385c9002d4050b620390180c080811030307500036541c9258190b8820804203441c0d0115581e010842c0d40e650f5812503a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 150810674 1250 150809424 150809437
    0x907020a02150c03030408180405010605041706250212040f180c08070807090b03010b030a05060a0803041203092103110c0d06050919060606021002390a0503 69
    0x1511000420301014401001641d0303c50100724011404c5442d1680c80700c0c01d41d080120200c401100003508040140d6507402141c2c024215502e4480d5101c1c18144c12071030003040d010741c42c40030350b0242040c00003400b003441090408803c9440318152000000c2c1c0100d0500c030140c001c408540c1400305010840c5040781000404881c9035041214440394059002400e845116000001054040c80040d13030301c0f4011820315501000c149402c002c040d40314240002280c00a8114003009000030040140c030190b07520410746c004600f02c030005a424a050300c0a40e60348620b0044094035407001c0d0341181054003d05251000d4014856030700c0c0c0e020100c0003507110168900001b680085c505400c0d848080e0004128030225400280242c10551095210400503010207050f50342640705851039600305021031540c90440a2003680c010403d545000c034000e00e000703504103111103d640f041120400c0c480e08510842e81c60039600c080210764914060310f0384009100142e062040d80034904116042140200c000c121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 150811924 1250 150810674 150810679
    0x30c06030e0c040c0c021e03010608010e0d080105030a06020705070b030702031207050a0c061e091208011d220206211b0702011103090a0f08060708090c061303020907020a02 76
    0x86607040c481c00c0105032584c2d10f5640c000b05843ca1210000340c00c00f40b802d020760345070941c00d000c0103402c9100428211b4800b07501c0041a40d54410070074855000c04e11040c01584030750318114029505104c00a9101c45000c50010000d43d8001032500030440c05200c0c175070080c5105815103889113840d42004c0c0d200e0388007070080d402e502ca402000034100c03800b4070155255418680d1b202c489046181d610f400003401481c1121050f445c1d44070100c110b0020b03501604041c544929901c4800d01c2040d0000ba040b080c041c1c11800c0c61418041007501140d025102c1d1a40c030845000d0511601c2e503000214030b400200403600030f504035000040d00d4080c920b00e840300d103861001c860f202036a65956003e100291070440800c5120181c0d0812003000036601c00c540040345440071000f80c03403130004400b0004040c1c0c622a4000b00200086010400c8044014420035510414900f8544941d1800c50381d0310b6180c0100d0107095104803400b09280d030a100c501c02110000e0b40c0e0107082c01e00241000f8101a6655064000480c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 150813174 1250 150811924 150811933
    0xc12100c09061205010e0118060306060306091406010b0f07020f09042409050c060a050f0310030c08010546050a050c0c0a06050622090204053706030c06030e 69
    0x45503c4407600ca650704880c11040400c00340d90a0a0a0009001d0180c1001b0406500c070803010000c04d09611518009600c20100000d409175149011801404441100d0000da00100d00402c5212030601c100d50705803c40700d9805640d140be80c030005030940d60349015980c002c011141000704014003104050b4100680704000704046051266540a5442002d801000d0760440064822507007040c1020306a040784074200742c5e040c080d003900c00b079045c1e0b001183c220b90b80e502c90881c100300303002c20400003030050034180740240003e2810300d412540b48044180c8018980740207480300e0300800030b2541710f40c40402c80c600440c42c83e00c280c2c04120001e00380583c0e105680741e00e40408075954022280480e034259003207a020700030044076500c50800a04000b40b009421000701d6401c0c88800011a103044016076056800103902e00060041c481250b82c010040c8920480100c20f4003e000c00300c8540b10409084000c52740405e040c1100c0e5080540b1a40e44000c2c107c445d95a80440d074140c140d08204548040001201e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 150814424 1250 150813174 150813197
    0x11120904020d1d2a210f010b1906080609150301090302060114060702151621030b010503090a0609020d060524010504061e02010e2a090106020c12100c0906 68
    0x820f804c01040c4c10340034403c42c180000c0e5910b0030483c84e04e41003441c01c10114501c4070343c14502c60341080149100c882d910395580020701c03074914080024546604d000c182d04501c0a0400c3c001408850010300741d144641313103081c0003902c014055000429680c50190003489100c40c1031502030f544000030b00500c0030302c5036880460041030130800107543c55142c00070700c030f4220344e440c000003809903605c1900420404000c142c000d0001c14640340300300c0780170035041d07140036480454032000408892036420303084c2c1040410014003d45a80011305603070304607080200000c1d01062440040d1400d0300010004100c01e003440c08104030b0303600c0524091265061042c00216a02e80b480046070b4030310a40c0602000314a02108502d074000c0c0c06044c4590a200c1400000f82d00d0003000d407028504280c0c0c1d50031094508030400c0c42d0b003070101ca19061101c41c030b5041e116218103505003113005c1d403501c0e80102d465000c0d82090004180d062800c01101c4102080e1000400004195078801004981d6602824005c0390004022 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 150815674 1250 150814424 150814453
    0x61413021908100b04030c150206070207140f0411030403081506030406091a0f0106020111130b0f0d0204080606120f06040305090105040e01080f0d11120904020d1d 72
    0x8641d24011032200e040c0200500c000d080d10503240103401c801d0703841a200710100f041225000101302841c06096607440e418078244e100070f2040f1400b0071510441d0445000e020f0407940014080c000d071000031150401c410038110205242440b8181c0b40381c0d10609141569034034030300c07110080d401180a56144040c1d40d0b00d89102500c501d041101c01d540101c0c00b00001804500c490b444099800c0c41100d14164019980c090007003003c00c152020300f8103110050040049940912031405440d10b545400e44c2004244010f03074401f244981304002403003e0009056800992002c1103074072802c000d64045480d80d40b500c003050703903990003140c41d240203140719403685041000000d8191025100c0c20020a0341d581c4655040300d2a403c00c1010078148030083c0700c081030744094001c0650103130840100925451030a000128034002441511b0014031451a6012603c1080860641c500950501e40311380c2d55030241020400038442d031001d08400524106c45a0208070f41ea5094040f204428421a4260985102c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 150816924 1250 150815674 150815677
    0x608010c09061b0c030803071205060a080709110915070506010603110319022106130219051602060f03040201030501050a0f0501080603010b0306010305030c0708060601120e0a050106141302 83
    0x42c0340c0209044415800004041c1c0d803090541620907500f9441c541c0d034990f1004101c1d001500c8500c080703403180d05c007101c0314030042c4078684d4040d90489a100c2c8042c07622407681d44400d01d40c000d055039251238030b10b000d01009581003182c3c900c400103007051104004000000c001c5401c80e402c201d0f500c0c0924400003441500c41d008100d41030440a121610b180c441c03c0d040c4203e0403114100803003081c0c083c00300070b000000c504a0702c0c0e402c0d800708501c2040d918043d420002000205100110543e00c188040c01a01703035000810281d40b081c0e401c0c216944c2000001d03511008502c5540254420720010340302021301003070340c0a180214400c0e2028400c41c1d80300e10812065050f14060041450141d0004201c0c5611504a281d00060054000208110028042810318a00b40c200341c580d58030000c1d81080f00c1c44d082101c2d5004206041c050043c0303042490000304203142c000f801c1481d0a84420021828580c1882201422a07100008001050341d401314880c0040407507506d20700c5000e0700200d150b851080b030700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 150818174 1250 150816924 150816929
    0x108060108210a031517010c1704050c1e0a0902090f011d060d090503070506010510050a090b28020610050103050c220b07050c040608010b03060a0e011104090608010c09 74
    0x4016410f012007018110000c028a80900020035001c0d03500260040425001c07009903564480045010308418001074102c01d4100b5101503d640094108004035001040101c19182c040310501104400d1641010801550050f0141d02c410091400a08088540d000b001c070150300ba1007446064155400540b40841d8090000540034003880c0c8030295884d03d00004c12032107100641c00642e6101d507450340f90ce1038006803800c541603481b660040c40140381c9002c3e51031007009503181052405c440e141d0700605000d81d6104a41c0080b0b03001c10743c405112240d0442c4505410381000098456241d008002d540c2c01090b502861140c042100110325540319001d16407060715006001450881214140340b0704041014041002840004000c40c02880e020000c2c02400e00944c01070201c44040c2c420841100c0040d4822103031a8581102540952000300391544c2c0550b406000080c0c1c02c9c072028006014280352078200b560450002004189140300d40c0c441802e843d6090b0003000302c242c0b01d4006039803440301ca0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 150819424 1250 150818174 150818233
    0x21e1501030b0903070804080307110a030c051309120305100602010204081b060702030f010f15062709060303080f010b040e011e0f060804021306050d021207030b0108060108 76
    0x108018004101c0404034281c20560040459103031142d141c03a40d54068220381c00c031081035000005e102050011007944004030040c12940701e40818515950851154900c1c0300d0140122010780089401d0f1180c1d070b1040052940203070381c0d084d01d0022010010010441190f245904940604000c00c20a10510a56080c0e5074004003c140800507007860300c1d4a4000010003580c007003010003d0f000180c400340f00c60305d030300046000041500703594404060240d5240c038041d0b00390200c042c1000c1002c0c3e40d1018071000040900700c81d0242c000c40c010510030480c02242c000d16041410700c1000020507601450040c400c2000c0e4041d11541d03601c1300e0712010030307100d684500e85000314014018003060aa40d001c8030300c040c00300304800d0080c80d5250191842450340da80018003140360f403010072007541030002e580038448411500030018181080001252203009003c06401034600e0b46605000076810080311002d5504201501c08940e03444107510741c1d412007405450441e00801480d405842c0c2c54500c04881d84441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 150820674 1250 150819424 150819463
    0xc0606010908120d0e030d06061206050102190b250f031103010503150705120c0c0f010b0102060705070519061506020a020f010807051c1d0a0f0f02150a021e 69
    0xa14080304003812a4000617822800108065002c80e0443d00c1000010b01440d102c526034a40e6125082c0c04503002c4d640480d05641120350410700c443c3d2800d45c42080301344c0c40581c2d0005a16404030961b54860507052144165007620751100380c26800441001d024690355800b8010742011301500c40141c0000e204542d0580e000104000e40c007a015482154080b400389085e03403c1c00e0107032007040c014003020794000400f03000001765410144000c0c4441840c166170740009202e80c40703103580000d503180e00040400c01003200109007402004800e1141005810003416035051059007418200010499164040b001e0104118001045800800c010201c0341d001441c1c42159004e0030010344400b02c0c010081010007200300142060300071901000c0810b805100030024034210102e403e4003a8403803402d03c4501c40d82c415000100018545500c1c8030301c0e5607115500c50b082000d01d20104955030a01c07411000c49100c00704201340c09590000320401400c802030502400e10f149404220340f9508442c04070b0310348486 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 150821924 1250 150820674 150820687
    0x6060f1e050a06050f0c07030c1508070e0108072102041e0e04121101090506060108070201180204150825060e0120070b0a080405070501050a0203220b0c060601090812 73
    0x4001400c44000900c00303179031410f900780340c400e41020f040e90000c460100e03841d40f05012030b01074182c48001c584554107107c00c25083c500b0f400b4050101035005281007200950000da017940c4070b92507d244000030012005445406c04202070044e41090041068031440d02c100810000c00b0b80103a04200d5400700200d1185e40c64945030010301c40d42a00540703091283d4016074001c015030034441e50f000240210040c141509003040010288030002e002142107a040c4205940c1c4070032001c0d021680598100e50004003580000081210b0f14026032142c51640035034135801f0450b801c440c409103c5100d1030b05220f1405078440390141d4008030b00000d944e00140d07201e2013540100c0e8440300b041010940120445284a40e10000c42003030758030110105000408640c01d02042100401007103003e88800d0070304030b08100b10071200035560b004050b0000041c3c481e0058038054441c203075808601404100b00e00582d521103c410301c95032235000340c90f49800102141000a054400802c400580d42146d200da50714001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 150823174 1250 150821924 150821927
    0x30617030702101416120e0307051e040f05090a030314041104050402190b0a021c0804081c06090603140a240b0405040b010302120c03060a0e0a06060f1e050a06 70
    0xe500016140900100300401ca10400c00500e41005c42807251000034114540e0300c4008119070030080c00300d40245d000d50b8007405039035107c2030140c0c0ea1841d81040da0000c000214001000313400c4c40040301003424035040a2142c0b108020440040276030294405000e00310401030006039905c02210f001d002034070006054041454075801c019049030009050341e41d00402c3c05040c0c240300b10203610002014400081031300402c3d4044c043c000c1200c4400500d20040341e05010060016403000b04003e203400000600500c0c4690303490f0a01d4442c45050310100900da80312058a001000d082c001610b06030001c5001980c04c050000700c1c580c82c69800070368411022610200e155080241e100c1200741e03913860b00503101c010780781d5109003441180129800544fc0d45980107002e02c03850b00b64844203032504000c11482c92030b00c3c001100343e0048921400004d002241301c04071030815411031002021603081200008503084043c0900094504907082c03059034002000011240d9045881540d410030324003d41000b065 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 150824424 1250 150823174 150823187
    0x80c0306090601050c012c12070602160b010b03010e0c0c1b04060302030109060213120b060105071a0412090819060e013206041e09050f01020a03061703070210 70
    0xb0018104203081c610940c0725039080d29155108010109041190700b0240c8201300300b40b410745803080d005010724154104008015100c0c08070302612040e0002116581c5d04032020b2951041c47d006031035007409503101d010b5080740350f00a00c11008ac088402e8042420040300c1403c846207040300030000d116082c1c5c1e400c400341a0384001d80400f40d20030380c0c9000020250f2400c0c003512003154481c0c440160750b03009440c0c040c0c800708800d410250520305a201c1d5038001400612000d07820040900700151119003c1c6407d00c0c1c114038080c0b4100f03c0a044000744070030002030f01c0075201010300949660b4065616800e80075a100c01c040c3d00300030700c1c1008a00040101c1c103158041b03040304921400200310800e040c01c40c5110301d007162070820816a600201c0048040400300800d4000c00304a0b030070300443e4020640c2d86a9021100c6001302c1c1c06627525040010028100844048215024004e64944442e00c0001d0010030840c41182c81b072aa4211403815110004004c0b1120941c0c02005240c0c08808d4580c11280f8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 150825674 1250 150824424 150824431
    0x2010f020709020c0715030902030d050304050a0804030b1e060303090d05070b0a05040f0902040e0606090102101a09010b07020117070c06020d020301030203010f1104060507030e0d0c060f080c030609 87
    0x19030051078000704048030140020020804e080000741161460203604807007000800d03607180101841c4c01d20440c0182d6001c038445d03a602e60945001038498840782015410071a89003001004040b0024000003000034070071160344100415010900200000c191810340b0410403603105a154204022581d0f0500d01402100b0206026074100c0d00d01d551204840c460560200c6c50316008104c02040030083e481064000d440a0015021306504061410f945032180500103095548034900c04507040515034420487e0240c00144e409051100c40006404500d504510202140c0640069000030403c80807000443d003055a06030b50750a40c0101e650905080e00c0c0c005404802044201c0b050807010480314009001080048480107030b69516610405085400c910540c0d503c660404601d00340e622004016901140c8582c20400c1c1c2e01c00c40e91404480c100394401229910a1440c3c54039000d0140c442048010f03100141c684503950200404140d541500840380c802b8020381c2000010824101220210340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 150826924 1250 150825674 150825677
    0xe010e0c01031d060705040f080c030c04020901021c1227030e010215040b0a060909020f090703020d1d0105090f030304031b062f070309030b040804170c040b01090e0402010f 76
    0x10f00040e1010003401d15034162916000210081382c24025039685a8012005202120040050b29000c0c000701ea101c0f810a61500c0c440c50340030500c0510f0340d000303005421000e80c2d0303103000c00e010b2050765502804110034502d44038201480d00407030350ba2045800e11300c48809019416281801080c95900b110752400031401941180a0001d440720681d030b00308450b6004510030305980a481c54600c80d0002100d20703a5000044682c02c1031451009606c0324005d00d017144005a6194000307603038180040c1c000e48940035102229514000d101c6100e0b10700252020007054501c80244030548801068540d00d02805107400240d0b003040003c100024040e0803046458103040240040204982d02c94500308c034040c2c2d2441c0143c035207491080701d50308103120703020106060b802c00082c14110980c4004207182c0281c04010000401540403c046c41201026a0018103004600442d00340407442c1d001d0703c500388442124015070078a5000401d560107156400141d0301104c0345c4610340d6640c0d03001100c1c200840702d5a0310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 150828174 1250 150826924 150826961
    0x30b0f12032a0607360f03050c04140601090b09030705060a0201050f180a0303110906070f0b010506121303170a0b01090e0907061206080316060e010e0c0103 69
    0x10030508119044420140200ca030014151114034002810000300804510800c0302d0800c041d041c4804000144040703440303501191502401c41c4180c0b000400454010940210001b080001000400200c18421002c10b95080c4900c03c4100c20620340b43d0410381d0300c2c42c0400d019040c1440220120030250418050007011079441c15a103401107107055110a43d0000140d4540c0100b00355403d22400f00364100c1030000c003030402c138051034412949070403604000800f01910b070442d4500311001c500c103643d600e00000340b40781d50368961441c1480c0c40301c40854046922002000c0002000c0c50f08009407041c600310440c40069940d00c0c52b410802241c5030307030000c17824400e000300707442c100100c1d42c80401c1c441d80714244001030960100d000981248110b60200810040b0507003041840750300407404500321410382c1050038008407400f013440f02906082c0c0110a907440045142406074a4020f0700700d0205008407410440b130140d0402030b40c282c0d2141c106d0410554080ca006000039480b0f03611080903445c1d010703280c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 150829424 1250 150828174 150828187
    0x180906020301030305030402091503032a150f010f06020a0201030e010906060b03090114040f0b0601020a080703090f080307052518050702061317030a09060f0615030b0f1203 76
    0x42049070000e0b0030135000104081300704811070030001e0009402c000d50b25a4003282c0c000c0a00000d40d280b2510f00440202c56080002581c030000c10350f0109568415041950446500e41c1218042900102c4031034140311544000000e09003030300c050480c1a101c0701e5000d000d061040c1d40041d006070000c001103464940d038403010740c0e0100d1850320800010307006c20760700b00f5501e04140391143e094501c0c44004100c00c4800d0b80c01c0c800021440d4070b1003d0101d034042e00b9101d0540d00c81d001070b41003825030b401c051702c2a40700240100c101540100900b0946902000d100c540c0c80e1510070096803402040b0004205500603198040d040300c070520034800c10801e01c400490700c0ca80300d1602d203103641c00349103811849a448009000e10384d901440750b03642c401c9803c69246036004440d00c4040c841d0b403002004092188000011608201107138000e51400c2d500000c051229090f900d039104024038492107045011a400d404c002d1903144a400b0303828015070000d10001c4080c07126020446000d0990700c01400900c81003201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 150830674 1250 150829424 150829433
    0x18091911130e0d140301030b060102010212070507051b031b030f07030c08010b0f0d03050a0302070204020318210a0e061306050d0609020307050403060207020d0212030403021302131809 81
    0x1c0c60321084030240085101d5101010040c40c2c085800e60110500c000000a44c10052032507064a045030f40210501072a9220100140c2c0240b18001070307503c415101170100500c0c66081001440903a20940840f80300c8004600c0000b900c0b00d00540003581a081410040d1000003200c1103800003920050a80b80140c0b52140c1380303443c0c403100c3d502c200e030094500801085451001e2040302c4091800396202c407600d078400030020343c600e140900002c041c00340100c0e2450480784203605070b43c003956000d0300465607402c0c00c0e03caa00b03c042c0c070145e00d4088d42c03103204400500a4200c1200f90111078560340501e0401141c0328042e690515650700351500210217001c9049490000350f40c850003030840d0f85803a95901d4898113031100f9543c0540110000c24010400c0c803c01e66403002c121800c07203410a0f00140c5880c0c2c584005203000c2400640130b5440843e00b022250480000300040048a00c02c950086500320600002400d901680180c0002810480c0f0100520181c08044244414098100049080c00c1c1d80d103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 150831924 1250 150830674 150830689
    0x17030402041d0a060e121608040f03110f030d021902060702060403061b030b0604060c030c0b0106031e052703041809060c05070c050f150c0a0218091911 67
    0xe0302a156011884010a2041c5445601440f08004020307100071424001300002622680f104281c490000c902d1f02001d01601c1c2c810782e0090310802d0f41e0003180c2d0b0354906040d46101e034000300840c0304102041207600c01d4540001d6100b030140041d0007803c00150a1014041d11008030041079030850f40402070b01c00140d50310720081001d14816440007e1034400744072135020484551035031206052038010566103d6481e102901c08542981c5480168404946002c446c0742ca501c100040c94603407010300200c1e030250542c1001ba00d5403501000d007042c1e404036401e143c00390740c0c05607072000000c80e404800182c01c2c0000808642860320140c2101d2a10b81d0724401041c1c00b010490b6460013142c4c0c0d40c0744450800c001c45c01480480c1185107404c500741342d0721b034036560140451485128030580925244841c29150127249003d41c50885982d41e80300c0c2039000c0183d49441d0798a03400c070710072522054800316240d040013450780a03101c5240100b0034603481c1c00b5a80b10032f2040c00300a490009000107021f06a649010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 150833174 1250 150831924 150831971
    0x702030c16090506010207180b040902180402091e180a0b0a0e0601050901060f030e0f0d1206050d0b070503040f060c020c01023d0b04020301030b1005030304031703040204 75
    0x38070365105940341800d0b4030700711107001d001241150420401008015002c050f94410001e04201c0001c1410440001038014090210001e4100e030319429080c1d440c0e1500c1c2406841203000341c40c5044503031b035105a80074204040c8540c6000900e00c060105500c010355000d500509a0341804880c2240000e07103032007080c840121901800c054036038019040d03000d0b0a000c142d004000c1070b2451034507075040010252a21030701c80d5200d0101950354a081c05042c408210650003c003108066518030f2030b011400034011800f010108001c0350074480000b80ea41080021109900d420070040295500c070010200c5841e44094805c1e5880e004010411022030000c3c898a02120429001401400000310000e4109050841d02e00c810b10510005405050080000c0395048110601021444541c40d1480d40082c04a03141c02d54000c2d2003c000841080910003031940503600071040b20601d10b50310410507944e03100d640001002031803c1136043d141503541e000519045031001f440400d6052070704581c04003218081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 150834424 1250 150833174 150833203
    0x602070503071101030c1e020c0916021c090506072414090d090b0c15070201020301030203120a020d110a060c0206070e19030206031b0f12011e0e0702030c 68
    0x1800b1810030107105158158940282010b2280d940c100b000a8051105000c81d00c600c05600040411410702c01d008000e90400014440080c90801c1c0e43c402c00e0048220003c0070140c820400d1412101c404102c140301a5105c5540b582007103410300c8140130040e00524001c8804019991101c0413500c10014440d214000c0c0101c00a6151010b007070168401d24041d00007401a00302084070b030780707141e400200602564035240b080c035519426032010516182c041240640e1411041043c0a041c5606400540c102c2c5d0088003211b501041004020310b46101e500600070243c0d01040180c03000c107000307882c50140c2040d01002c0c5ea00d5022207407202019510b0f20246100160490001c00c48081d41240c0000d8800200b6107861307070300750b02d116803446041c501400068850803000c4000303007aa001d210f88038440e62440c065120345030282028013880b950450b04c40084071060486c00070400d00310150760300c580100c03003048120240d483c0001c41400e4480c084e01c050700311701080050602c10b88003007040a0308540d20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 150835674 1250 150834424 150834427
    0xd140a1208040c090506151608040909140d05090d0f0f030807091d0609090717070501031103090303152b23030a031a0d05100b062a0106030602070503 66
    0x52a1907200d1055135042440b8861801040c80700d00d40b214800b040005039490000d603a04e4144c003200d40601072007038500a000b00340008001c1244140d6802541050788918610210082c0000d04c0c0358a031040440803030000340301401a010a440c1c0f0100e2819242e00468604030020015112101d00524050056006c18211000c4c8804070303600414036001080c0c40340c12003041c3d40f81c038115038540d80b40207409944502d80c080d020602d00c0000344038200040c512503504d00c0c004010350031002c0d1605041d10440340480c0c0b50044035540c60301040c085a20882d0701001851450303441c520400310145492041c3e40d0814502010810001954200c14201910000e881d051a0401e483c103c40c40440c100c40380060a46200e1140303407400f4ac00010388001941a05020940c464451034001c503040520281650000e1003840c42c0080c01400b103991301c107100075228140034003500c50741030158a1050440e901d408404030f0000d85a0301d1140c3d46e081e1058000100003040b8550742e030b120003003617070003001041d11070380c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 150836924 1250 150835674 150835681
    0x203060108100b0a0e1216060e03011a060c070b0f04090b03010e030301180219030509061308160804080102072409030e040b010c0b04080a0f0507020d140a1208 70
    0xc10180c0564008070408060100d281040490f403074900a81c2040b00a21400304003040f0b45517651000145607040a400319520f010015a1680c2c0c9000248258000b083c61242c14401600741805407404040c01c0c203140d075460098600500600b5840f044419103540500400454140020401032183d010750301a00f64403075040ca21000c6c21070740032102448c481c0e8544072161030714040110541c0d0455070b1041c1110002001e29400e10041d100303c9001107020325050100c5c005540d016440b690042031038804075401507079104d004003004078080c0e401400840781840000e051306000741d0301a01032446040c405080a98601d13402d8207a8000c00c0b400c41e485000a8038801344a91558201c0c030358110903e00600c9031010380c0d1006040501031010503409680c4032642c95902d81d004100803029168040e4503240c140c83e140c1015003036034000700b40000018680001030041c0318440c0c001e071002e00b9002407001c15580c480e07940b01801500200e050f107485006940d090000314040c4000c0440495031615a05020314 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 150838174 1250 150836924 150836927
    0x20309030a1101110a1e02010210050c1b06190b280501030c0807080408091f0c0203010623060a020114070f020613031d031006090b090618071404051302030601 70
    0x38002d04400c040703500800819010a001c00002406042d451ba4000b00c480480d00040341031401080349003203558140700c1030044100d05000141811440c00507d480c0c83d42e110010b591322403500317680c00b50501c07204103039002c00070300030768403840e127000d030081c145104494816041503074550118601d05204e120b2900c10032507035816000c1d42c2c98030107461034603900c580b500890143c000703040544003915140d0003040c002119103c130012005072030b0040c07460840c01010074400030300520045008074040d500f814000101461203c41c8400c211000400758485604244103008603034005003082811907403100072440349441c010840a001d00065a5161000c84203d00302074980080a82100705081402075804080b03584070804240000e11440f101200b070a100000078584070714100c80450140c034008000800394400d45c0102d01030070b81598940802d0340c4100420500300c3e00340b00841c0d800d1032000b0002d14900c0c03040e0320b081900c00ca1101e80398102074503000030401c0014025000030040b07900005024807907 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 150839424 1250 150838174 150838187
    0x30a1d0a08010b150a1b260306130e03041809140f15011503022d04030203010501140105031810090809041b1d01031d0a150b1f020309030a1101 63
    0x41c210800721038a40703080d03400c0c014004484401c1b24035050040c0c84410003000094500c01800c00200030002965200c200e03401c54040e4419241544601c011361001752002105002d038040300b203410400703103040a00d007044c41c20402030740540c40d1010a5946845c6400200303103503440025200d074480142104041c40b400b00785840c00c40e4084500c0500500010401c80e150b9101910104110385005600c501e0350410004000850800803010171084150000340c1840040140003228001c600034000c03039903a9800c5482016a41e10141c0c00600c0400010f10703503a14440c0d2181c0c80440040071583d980248400000443d000f03008112840240003589806501d000d014007080e0031344019a40344908480c200190054004900c0d501c4e022500181c1660b2503800380d80009003034689440c6023402c1d1580c45074495210324000200326500031400c004020800103a102d040d05491002d00b000b000041c80c284290014064041c5440840c4410041416140c401b07000c0e0f506964482c46164422405190001d0040d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 150840674 1250 150839424 150839449
    0x8040b090303041e060f0627020c0c0103150e0a05250e040506180405071e080c131811030607020c06120705070c0602060610050a02030a1d0a08010b 65
    0x1e600900901021074182070032030480514007410800604007a24117000038009078002c60030014505000003d00e01c640c0240401206880c8207100000d101580d000000ca004851090707031b080d8440f0030705042e1540a58400030480722601241c003001a074a40084840d8141240c22100003900d5805020140014502c00343c01004d02c50328600a00ca802e080c01403a804030100068132440e10346002c640c0a03114114023403a0f070f0b411512000c0303980c6860701704035954241d40d12601010303550002107441445401c0c8a10403c1e0740d154006803008040c0e240400c060b50805032100050355544200c14922071078060b54222495100d46c2548031409003040426080a03801050345055400010300c0c014540e60302c0c01141c00d054441d40c040380d4680c9490404946900403510000c000b0306c10a000841e1450b0000788440c4950307001c55043c0048030440604a4444c0070760300e40c01015070300500c00038105c180210481d14032821f03000c1c090fa02030740c1c1002c00510003400742d901075030141e59183d40071102420020b03501c050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 150841924 1250 150840674 150840691
    0x60305061f0b030c1206041b1d19092307120609020a050409020d0e0a031e020c010804060b12070b040801060b09030712030e0603010e150306010602061503150708040b 73
    0xc5144c0b200d01640c00e03100d012010301c2140c04000001b9850303500d5602007104821064003c3e629603220200162007440801c502d050784081d0030100100c40d1500d5901d0040541c19081ea01401501e00002c5801802d485e0440f0b0001800c040609140806100355542c0300d00c61030b6a80e15a083d04019100b4210780440e084076010b2801009000301c000d0304401120b00302c1d0350310040182c0d40c114a241950041a003849140c1c80c0d4000d00c40020305040c1d100403000c141049034440e624101111010680c2d440840c541e600e4040f0b05801e00050101d007242d03110030311088018084005d2501070806090901506400c8904400008142031003254003d21684002e0a41e00c07100751b1421480f880001c1d40ca4041d032007401ca1003561511000101031080b100030b400200b01400c0603840f96160000d00113840e4080750150306440342524203910703603d4000b034014106c0341540c014105036100c02000d070020803500849076405102d010422010312070724401e190301c607a90399a00c68040c0e09003171a1074034043c800504101e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 150843174 1250 150841924 150841927
    0x1b060513020916141803060a14090c030d0c020d0b01090e010c0809030d0b010512011214011505090c040f08030d05060a140108070309050a0606090b1c02060d060305061f0b 75
    0x3d401541021030001c0300c032a410181c0b81c0765401420700024804008440a8144c000c1a050002004158000640c10401025840010b50311036040da5690620100070355410744c054080540858000c45d1031010b058009040d10130410800e4079543da49020a07032020301c580769100300b00d072610842071180b004bd2b1040e40c9841591400e20058040d031302d0141c2c039030b4010031642d0340312503010a0b1300900131180d00b250300203030000f050340c0c1d82c0500c0c2413074002c3d004080d20307088400c40341d00c2c3e03040e10184035001c12054100c40c107590060409050141214000309181701d884007c1001040c2400101e81c880014860078001b566130b81070b4032030800c05450016005c03034001c0e181028240000010032071241c2c2010404e18203240540c0c0c81d8042100541928800500503003c0d06034044148007098102900340c80e92079105109500d00d9000f403140001043c007090a1150344030610310018903141cce0003010440107082e03000c505541c03a522100c1c1800010385110758242d5100c0c0d80d0401c091015007081000341100c003641c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 150844424 1250 150843174 150843211
    0x10207050f0315070e03060921090d1101030204180203040c15020d03111306030b03010506150406050702040f05160801061806081015020102120f0106020d1b0605130209 74
    0xb561540120243c102810f61100040c540502c500315809003103200804440050130690b412640303803000d1503140d0803215114000785860350030410807581c08481c094884240781d00d1544840420281a04489041507000c00c03000480d0341090740d003403070041032202d40144c1d02e0406103045200e0444540c45200d100d0303481d04a203031100303801088541f100c1006c3d0401140410004d0500d04092040b80b406d010002d001c900007281c440d5040c0d000d5424200c05800070400e40d00e078a000c010942c40894052008003074100818041284940082c019003880500003182d02042d001145003035800c1101d5034250f03968454003a00c8800d522000c5540180f100781000300c6441e640711042d040c0000c15015060910010101103003198544506c4640103103010001003841d00c1c16528000d01030740c032812a020083c41c042c0c004c11040d240f02041c40c2d040f50941e800402404002650985503e03182000c100da2800c1030240c008040340c2280a05403003418800d844032100c4643c0d00c10802881d1001d800200d4600d403d2040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 150845674 1250 150844424 150844429
    0x1803100b1e0907110c031203010303020d09051c0302100e030c0709050c0909040f060608011506031e050402010c0b0a0b040e01020306010207030b1306061203030605030d050729090a02010207050f 85
    0x82c42e41200340c5160811100c904014041d18118400011540520a40300d040890920794405507058074480c1e4291000441e040c041103901841c10301910b6445030150900c007441001c88410400c1d0b13180b0034019108078070969599241110414a1202d91503040060b41080340c0f0300602c03424002c0c0c000040200543d0401c5841d51446d4060b095800e40603103204000b0130180220b40e0807000134070f03a00a60501c401c075203c03e103075030103803e0201c8192910885810003190540c064010005106000380302c21400354421003000015000181041e81844100c50000020035024068280705003803111001c2501031b2120f00b80b10444460b40d07607150050b441403043c007503183c0e804641c0408898110a00b803102d0780340e161041b8403c0104030340090541c0c0c500f4100060280311a4030b10001140241c07420000655500d040c162500100380e4902c0020b8010045100027643d90105541e030017201000941400d200000300340c40641054030400016840b10b1030620456904010200c0901419150700100f503428502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 150846924 1250 150845674 150845689
    0x806010503070b0d0b0109030203190606060e1e0a0510020619140f0603010b0a09050402090f010627031509061514090a0e060106080406050106080105060703051803100b1e 75
    0x1a0918080d403620b4250b01d11b0380c42044081c01458000b403c0d25042d461035180307001ca90040304404c4410300c1c180307600050b00303074091881003803404405498600b00c8101c001018030070300f00c0d40e07450359880174402d800451035440f5a80140c60282407500200b0f240e051450340705001846107013000072a5810421111800400d4160094003d2510b031241c139900e8179102d000074098041c007030480f900300c242c4000000d0000c0e001d8000c1c80c0200d0003a0b0b006a61303900c45c209500305542090007410003043c40340d01c21444004c81602d0480700c200880056084240c0c481c0d98042e40495010b112410142e1501e00c42414800300e4402d0303601c0d001900e40c21101052a003822000300203501c020580c841c4c11514005250500390343c1101c141030440400b46d9030325684601c1c0c0544444010344041c1c1c0c906150500100da41e50003140210706a48000b0026801d12400355012109036100c48800b2114015030304070250191020000f2034074460b0b150102040c14184041070000c0422000021032490402c03c164030301c0d42e16803c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 150848174 1250 150846924 150846937
    0x30504030f060b130606090503150f180706030218030a03140a0302040902070303061a030405060103081c0e0d18050a03030e0d080711040b04200c011103040503040806010503070b 78
    0x101c00d5019500682042c0008040503030f00079400140344a440d525209403a031004c020f071034041d10392245442d110818590340700d150322010350300c5e000e0010225a24440991409521202041c45140050090980c5600f0826181c3c04000840e8000c216214108841c103150301840301d05030002c000181c00d07610002e11402000c2e80c84141d040000420865933032003a011075014168060040d96031305240d10b0001d004240038030401081200c9015100d004880703080c100c038002d17504140207003401c0c1d00b1602c03507007a540c0c02741042038090480e07918070000094042c091502e2150248029000310040503602030103610707410120290341c0c42800810f10941e0382c4e100c01001626014605081003c11020125000340d00740000980f2179040440c28404002046411000a6034192070510070555050180b00a494039116540c01c05000d04980c0e1032011043e802074415100d04a0011411441d41c00400090350310550301947c90350130000d810700480320300b003000900515007500100b10251820000710124015103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 150849424 1250 150848174 150848183
    0x90403030e0316050307020405011a07080904020c010c0807020705030a0302251208031902030408161b0305070e1506030403030e1c11060f070c060b0411160c1203050403 74
    0xd5850304418007040068802862042000d040200d0b62420540d589400100d0704901c02c0d41440d0022070241d94a64510f1242c00d0a002218201000340c0c1d558401a0482c05903960895070a1041e0818584240200340184269446902031410f2244000303043c00d0480c0c110a00035440110b941000a40c00500803d400f04051034014181072400380d2110350032044d502000c40c2d00d03d150890400c3c01a034000443c0200c1060449a8040801500860980c001140c01929102d024004200d0034050807085030810f40c0b042c4002d1020b002c40031a403490b2540300750030941e00781d0300c00907040c030501444242d13039900305604008500101e03007000001070051000601c001c0805444035810643c0354000c100d022440703122080d80d11a00a090300000b0f01400c406a0a18214401c01e0089074400400385002401070f070b203954824007101501d8480300c3c09400201003240d00181d03910b1200e100b41d146100540841040a60054902d513140c4c207241d60055401d400480300d40005a51620000c1d03000002c540c00c0b00d030700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 150850674 1250 150849424 150849431
    0x605131419062712020c0301060308190e06030106030f050a02180112110307031b0c020105090d020f0301090f0507080d0e0d03030f0515041103060604090914010e0601030c0501050909040303 83
    0x10f05140400300c074000542904008964079401040320410090f0042103843e42120b070400108003c25085c0d0f8803134440036012810802448a001c1503c002d940d00c02c504074108038490600e0b04c8045003071903009a0040e00069500da0b280c42d0018894003a068100c1c682243c19810860841c051491000d0b005001905000229443c10200e0b00e0540102881c0007503000701503181d1502c160040e01411111071108901240d00403411410f50140e0511078a83e601070791554102044042031010b44a052070040ea4001e4022480070103659090280781540c0f4810300610034480050b283c03180c0b6200240c1c000e0340340354002c901040c40d00c5a02082c0c66200660488800c00d40c200141419030050210840000d02c5900b0714040141c00d20b00d1501608400c14150b404101f1b80e42c4e00c040391000341c08184e03841c50784100100810058180c40e50401e4410030b01488400b4100700c441d5a8603800c4601410810030290429801007046c00074040c2600014982030030f101c0c5c5400300c06000141045401000141416603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 150851924 1250 150850674 150850691
    0x30106030507120c0305060109060816051b0613020f09090c090402040f050405070e011e091a03150103060501050603010b030f0702160909050d090315090f060513141906 74
    0x810410030a2103d0401c0c0d0421031014008401400b802003103c1807400f045000c1d5000034043c0c0704402c0103200702d0f80c0c96410030306041c030074108950039806600d10310f641120fa05a69600e0107814808503014520000410152400a1050107c011203040040303208110550420428200c042010007069504a5030b10009a65903c0010001c110403102802c002e8646010002003080020b1140e0076505178140584050b03a84030902404840160b15020b800c40841c2d800708800c841c00c0d00003810300da058180616182501e840442d2601501c200c028507007a81c203800400c217110540c4202d5001d403405a5100b031656060070328000c628071024081588014200700041c00d80c074030901403285410b1040d42c5055006980b601d202000d804464019a664003642c5040803006001c2c11015046990004480d86040c0d0b030644180002c080511094400100314143d05000400f5441164800c0e0070602014080c081d9600b002c00850010416881183c1d1140f800382d60b81c00f00605410001992040001c10f4124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 150853174 1250 150851924 150851927
    0x60c0703091205060901140115051c1e060605030402100e0d0506070201140604050708270a0303021b01090206090409030302070501020c1c05031003030e120a050f070902070206030106030507 83
    0x3680d12281c40b14601164020402c07002140640c003407540100240981c11800301020205e01003072241d09084050802d459540e640500d01400320045c4011034850f8402800400e0000e030761580704c40c11a4404c041e200b42d8103441c054891040500520f00d04a0304524040d0301041503070a1091600c011f000a0000040c0180d641c03c01034540d6551001c00d481c0341d810f0183d030280c00b90000c03001c115042c0d03401400042090a00b07105007880703075509555004075900c8044290b44a03580007240c05102000d1107480290417072040154441d140d100384d0380181d03035140e0314030010401e02107143c0542e40740c0d0509580f8405650341406542480030b0071200043d4002d203500d0190000c1c413401c64001c0a030350010541c03e9588401141d15215132160226505c0003090302281104d15100c211030000c0102d400100c00c1c004a0710845500001da07001400641c401c1e95228500f52a04ca41e068007203c030342d400702c04c200001d0001882840000c002010003542005030702e60010b580303400140210410180da03000089d5445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 150854424 1250 150853174 150853187
    0x80a020408121612020c041a0a0603020c19051515010822050114010906050907050d05040c050619021e0c0607170706020d0b0d050c0f0112020a05031005010e03060c0703 74
    0x6580c02203c4c02840d451a420103526960541d181074404c4d460040c030711000126200c0541c5031100001c3c080c9107224180300c011307002500298032131407140c800e000e106603009155072210110580038000401c0000050710300861080c00c028200ca407034050f041810701d10f030b982240d06203030003440107142c030407200104000c40c1a020032103c070090306541c2880a83d80352009a1190365050314172501041c0045501c9009002d06103409490000020b20100090742981c0c82e60b9204035001440340344042c50295503100010348a4202c0110000801c07000a050a92a5010400408048a40c072803440c07440001c001065242d82856640c140100c10008442c2d0410401d80c00034503460b9410142161a56005e0404a0082d004041501c401c94505000d01d443c914024020021460b0f0240c01003000360203800c10301c01104081000780d0f0500211b44040c0104480c2d030700180105081540d2095200e10303160030b000042400e41d903c07181c10b00c18080310a011940703001c00d038150b0003218692500c2d9240401d11302129035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 150855674 1250 150854424 150854467
    0x70203160e161e08090d020309010c0b0c040902030a021c0e03070b0a0b04050705121014061605031c1505180c040305030f0d05060108010e060f0f090106030606080a02040812 76
    0x80d00c5103c515403c0d1070b0708100c041d03005030b160740202e821900e01e00074142e940c4d204910b1154041520418240000350080540c560301c0700d5045400c0742007a68800290040c0c1e081503030403242098000c05c0c0910b0f000004903400b0310000020000340000319551240c262a80f00d44000a09170345031110003d102c2d032116030460a45d142e4060720400c56072500307a500800f1500031080328010295984081081000005101402c1d0307507e040e440c01d210900d2100f04004caa2241100d9201c07540c02c6450040801c0040c00034101e0000040307151807010140300f4032901102c5011000034521030002500380075a4403080c1e0314583e64111510746400588030f290500602d80103a81c4014039074400002e85035540800d080c06814950044e040030302503500d4141c0192070743c41090141010080780303040084e8083c03078045070324a142200030388800302108103800032030b500913000d801c0304010903100c4504110311a0b00900d20740e071100010740114146802e060f9040d403141445d03001c1d45030f00000402d120f4581e040d0404403041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 150856924 1250 150855674 150855707
    0xf04090c090c03060f030c03030f030203100b210403080105040b060301150c031709010c090510020a020609040b0405160f080705030a090312021801080108010e0606060f040f0308070203160e16 84
    0xc17030758901e42940600710364002180050740d000d0f10070415501074000d40c0d00460074a41105c69140c203145080c1d29641000003511403020307d105000e21303488005162a8082c901a0782d030407469604002c02d11040d100e40c131405600030032082004112014208001500c0c4554924007180200b095043c1150319400c020440503140380d8610502074090015801181d010702907486281d030b410b136601c0822461124103d501c60168111100341c0005140c994010103104000600000f4042c0840d0041401c40d00301f200e802c40c2d0441c10040c2c3c900100e400c00030910708034000303251502c01c500d000d0000924500018141e9500700d500c0302030340c600301405101507001d0040c8940c421074a0f41b40c04803207480f55a00d000c420b43d000c1410000041416034060241082d5070000170700515980c1c49520900045038092000c28800400501c408600d19455220b04001140141220391303d5080c5070040500b00011092045070258048404004024001c480541d104000386104107804843c5102540d0b1114803116404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 150858174 1250 150856924 150856949
    0x70302060325030903020d080103020d02040f1506020f06060303040b1206011403040b040c0e0c0a1805040c020714011b0f020d051c0210020a02070b070f02030111090f04090c090c0306 80
    0x82d600c69050384014a01402035007141c5405002e1401139400b40301c280000703034012180001c0c0b100982041c0e000701003510048480080c0c0c50844010b508440c0c0b035940c0050300160082c81c0c601404e001c04001103508900100c0146152a1814007904000c0c40754407202101d07400620300249050707010b0098400510300f01019660b9070724180c600606c00106c00c84040700c0755144a02c1c0452107501d220f42091003405e80031240f506d40380d2480e00540e0b121001180f680c0030800e002c00c0119407038407103014800b8200d0013a0001c00000d410304801560201000e180b0b20304111030300c0d41029510f210142d100340a03c1d00881075000c00050340c004100e2403541e11001920511603c9500308a066180344c10b0f000b0882c0690030307504410864110801648540701c401e000581c049541030111803120310042c0625031050407c80052200f9a0101f825138002c180d002245840c04580754150b400e0022032582c0c52030341128108001c44041d43c4ae06454184c60140c5410640e850400b2821b45009500103c0509010451b80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 150859424 1250 150858174 150858241
    0x9210111030c04052103030a0b190603060e0106030902010f050a230a020111030405030901081008010c0201020d0b030a050d030c0c1b03141506090c040b0c0106030606170703020603 79
    0x121420781c8141306250040d074041c2828091500c00d180200d0700d0207880c401443c41d5446040c2d41c14060032001d03100c1940a01181d031000340100c410045d4100508040d10040760321460301801161000050b44000141820141c181006030b0b40403925442c581a039050264580c0c40e44101100c00c3c40d1103102480000c0030190750700c1c5010000d00050b21409121354000e0100c050303003600500641c00143d6005040340d0080c03100f84032a6014100196020051043e00b060040d500e818143c20740301006000c0c00035075400500c800e021000e07070140c101101000c4d4010090100543d44980e90740c0e10320000401090b6840000c1d19620788036404101030070382c00c041c04658955003503110209042592004603002d03400c004c08001460701c0440c181410019202c65000659a80c4c803e000070000000c10540c4095000c200c0480e01d0000b0b10084d100d095040000040c5040c01c1d850318808550042d041000030010300c0ca055091b106000455000b41c0c1da050b2045c1d5103903200c0c02d050344102c2c04103400382c049013450104030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 150860674 1250 150859424 150859441
    0xf010b040e01060f0b070809090c03060103140402060d15053f100b0d080d05060f15040501050c1e0604030e1005090d0312051e0c0921011103 62
    0x482005811a8100301003040e602007142210310307501c039030303007030248030715020482400c58401400c26680250f081c10b2034411700030000307000c581007201c500800e007030701005200351540c8c58441c42c1e484030000002c1d50120305150700010000d019034000c0e20240e03903c0341020250300034810f414100501000d4481c0c24041a031303481c20800c0944002010b40c101c00c20200d41c4004040440c0d0000314202d03403074080c000004440400502030702d00b02d2042c0750402c0c80541c2d07200000b000318000f0800221041c00000d41c078240001080458410329000d82e02c40d1381d0004050705541c01c00011107040300e000f400d2613651804c0d591036135405d1003080ba07079891030524080031007410320b480422400d2142d071203903031844c1d801c100040c00c0240d0304101800c00000617405101d460901d09010303034100007050290070401c405203402d0101c00140c81e011a02042c044405123049039540d620640c1058100f40d4140355142000e00380008201094000c40c8041030460991102c1c468007003082d40301d80c07404c1280841090380da2420801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 150861924 1250 150860674 150860681
    0x90f1017070608090a110603150901030b1915051903060c03022503090b030a09050d1d030604020f0609011101020a08010510050319020f0c07090518060c07081b0f01 72
    0x19002c007052002c000140300e1540800c00d0100c0a80c000e507241107500303008003800705030f80004094948281c182130580f4800e5840c4000c09000754071410090f203080c0743c25510b0103846440d9400360110380d4104038645104408524844050310015101084810360078080d40985000d00d81c4041c004618102402040690540050a80700700c3c1d020b1400c0f00407414401c50107000380c803001c041e001458088060000810420085030800c84003900401c400400b43c17100f07420481d07250744000c0810b05001603640300300c2000700d1058042d40c085001d002d1a14180c4c010a04103800d261226120b00d0000803009c282c2d0f0b01030290f0009a4000f00d00864035030f40d804001400ca207030207000780b0348104201402410b00a100300304032403080b03246d03079425002d038151280c9050180d0003820303401190050a20142e10560010840e040c000c001038000401c0f64109180c030582580e520b0b12000c18290050420841c600305241c00f00c030580e41d0310001d800d0743da0080700100302c0c50081c1c036100141035010f80c51405a03074400540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 150863174 1250 150861924 150861929
    0x1008150f0d050c0a0e090d05032809110105090603040b040303020f0408010603030e0d051506040b0402070c05150309150703060e07120606020c030a11120106170f06010302090f101707 80
    0xba10038200e0345d11031400104404007140d4145680e403102e42840f290718440c0025580011092000400808118000e0401005035043d21036a480e075800510701800411900580204000e080542c80c001c640c0c0082240d510005001401145085011508051007503048520401a8003d49910740c1e48502045018040502c0b0a5000654907145c08815240025421001c5039204004100200b0301c8000100c407080020005540325940381ca0740c00450301c9030b000511001e44940308484029040204200c1c01005c0500903050161051040180c060f1001031356035513040550100b07000c159140502100070f8081d0f504000042c02ca48001d10041e16000803d02e90070409540e41489400d490b804200ea481400c1c40c80c840d41a40300501140218180c0c1c0709031030796401d010b890b1025030040c0c01015401d5030307840d03403050500c40300140c2075000700c1c170092207400002c2d41440c000d064503501d10780004524002c054103c82654014102260701d1000c64620340e80105100183c44a16030010441d25440b01c14a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 150864424 1250 150863174 150863179
    0x1051309060305030d0f1b080601090b040b0a030e01061217090d0c06020d1701050d050106030c12120206010311060f07020315100602190305070c1802181008150f0d050c 74
    0x1103c9010802103806200200807d00c1590713100d80c0c8503030100f03c51404001d00700038140b010004000c240740010000070300c0608622141365a6686141d040182120001c410302c061603450a07005010100c1001210300402d50045010a41601001070104a600c550382580d03610500300740b07100c410440c0341901001260059001d5526100038210309540a440040c0d20411081500700148558036203802c035017109074055000000d03c1900d81d039036025418003d0300036480090a01c4102c0017003090b4400500d00004071032000e060f50b54955651299100c00d6182110f10030400802e4041e0100d40707400aa450003034000f000c5038590078094110200b485000d0301c2078850040f2105001c0703102d500014011030318600c0e5020011005050b502d040f2140c2d04414030803a28440d4138940003c0c4010210201c0f6050402890010ba8951841c0603400e00343c2116443c944c000d11500d0700d5244050341100c1d04aa01c102c1640b0b01105c0d41101c500001d40c00013054442d40c0e40308501c840b4800512400003002c0c43c1c003ca05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 150865674 1250 150864424 150864431
    0x2031309051905060907050c0109060e06100b1207050306060c16091802010206040611070c0605030106080114010804111504030f050d09031509030903230c0604050f01051309060305030d 81
    0x10841c104003640c00803651285c000c05000080340045104000622805414000014078100c1c00d42d5004242c40039992161116848a000c1c004024000f614400081404001c0c207441c00e0094000d140a0301002010700d42444004000107003251100c0040340c04800c05081031740e81e282c444050f56803001417280120082989008040072810524403061781d08240c051f0001c0c40e42d641c8603941c400203020000148408400b0602c540c0001a411002406c090606038880c1e984940c10030f8402004203505a00c8042c402c60200038075403050360400106a003058028145c2d1240102e034401042d12401580e81070310300d40c20000b4000040c030071001c07021a030345803040c02510000c8204103421502c030001c0380070240001c8850800103414001661000d201c0510904095510a44e80e0726004080c500b00c2c5501c00c51190a05440484004207100405903200103c800f01d00780340c240408120f0081008440505000c0006400c1c120500c09034030f400010705120030b05100e0640c5a1810540340d400c100854810702c0d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 150866924 1250 150865674 150865711
    0x50f090316020d0804150908010e0105011508070201060b0c07050f030f030f031302060406030504061811060c0309030105040c031401020f1c0b090f090c031504060c0203130905 77
    0x40100407140d11240710101050060030903000c010180700d9000f01201d00000030000040e646480b10340394603070052103460b81500c180c0b80648031402c0d142000c00e044426490080140070011101800b0b24450032245080308482d55007032010b80c0141001d400c038460b801d0000c00c840302007100000f5184c0554009640000204000e5002c2c90798800d100e009159140e0030912040c001c1114031800345170b2092690309100440da546130042030090303006420110009071510b0411040c02058041c20181d072500351071180d040011b03a00d5003140000303160301c5c0511401000a80100340a010401e580040400400800035401c0c280f4014071200051700c000c4400d0f00922a51440c03074030044c42070321604400d1000803854811005481c2d0b07103080582000e04c04450341c5211018280c0c403001e500704d1050a05181480950400514441c544142e0380d103130038403a50280203160b40d5018551030701504554409800703da07a21403a1800d81c03c5006c7c40004400c004a606400100c2c15a0703a003205008070940e021107aa03220707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 150868174 1250 150866924 150866941
    0x7111b031509031b100f0605011d0306010e071214071103120610120504030c1709011b0c0302060a050a080703020702030d0e0102160e1506031012050a08030a050f 71
    0x25402c40b1048210f420921042d0549406032507000c0079040702401740c03a2451031000b00e0104880502c100c444600d503850006001b6540c01031000320f200c032a500202800300e0a010b000a03130300e03441401000515610107020800090180c501c1c40f04445d1064024000c0c07640507200d003044100304a480d01c00080c40020300740003094010040350300400e40f10350010300c0d41c0c0d01d40e02408100c50517840351a04100c621403440f26201103034483c0c14001d41c42076444400001c80b03420300102007004010b8007002440100310407440303a80c010141088401c40c2d1201c40000e00d1483c1000003851043c0d50001c1e41100c00012400c035915800390050011031095100c0100c551a0503400305d040703000e1030340c000750958809500d50043d5409058040d042c414144101c2d80a00c1c440302001c03846498960003550080c0c0e50b4000e11082c0c08044414480f241c4003559164214076200048540d07035045407003100009210740c8008024004180045400503800043d165030b6401c14034280d5008020072901d0304020340d20180450140c0703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 150869424 1250 150868174 150868213
    0x6040c0e011b0305120106020d110c0f1507020a1d0a09171b100e060f06010503010e040c051017090a020109060f11010c02060907170304030b07111b03 66
    0x440603520b021061400101010b0490b0320444240d06018050050b415004142c11a030f60180000d40d003d40f0b4015031041000e440160070805000e0305400110300b0340c4046e251000c0500c2042c1046503094402c1c99050000c00251080700340c081c0d004000a0804101d1000d00072400d4103040006001c1481a034134621602c0448a00303140091400c4514840412145144c03006021600c191039071000c48000c0b28001c0c1450481105004845107840305401200c4400901c0f505900c0f0490a450400b00d00d44500020300e01e01c0140500c2e4410598075001c034090100604107000a02006003030b0a0001112103009001c1c1504058109840d000d00000224002d0010440301481581a1a09035a5030f040803000d40c0d09416000b500780c00c0164440c0c910b5450242401000209035458002e440d003420400003e6050010f90b0300600280c40c208080248040d000004840840f604403402c15400d8490140844241c12900185031083c03140da0319009500710f502c100c2c0200030104604458070b0705040580314092 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 150870674 1250 150869424 150869447
    0x703081e040303020c030d06081609140105100909020307050306090601030b030a0201030209121e060601050c0a06020703090e040c0f051203030615040b03040305091504080a0f03140f0306040c 84
    0x180403000101d40000e000c0c1d000b07400c6110303080301a00d04140346486004102c032038503441010250710000041c00d00c2c80354042c1e000040c10b98040144003610038180c0c9100070b920188a0540201da0014882050602c52b6941c84060040e02109554a062800b0005d146820965000344113041c1803000c40c1e01580a0b110707444805101030080c007c0e0085030780041d4000e4002e07107046074126540041880740d040c018462408040000800e0b19a0400d03248141b600d0000014152810b02904201c02c030740407140094092501544080096603480c0d1900e42240d42402c1e50388004964880d01c400d21040004500081060302c1e81c3e07039081c002d09581c4e00100610010340d41d401511640040012031100c0c00c02a5448035101500038440d41f41a664001c560420385c02141e0580c0081d0000c41c4910181c40d0150480182c40d603246040d904190601c0c2205858480303165004002d44244032240c0c0404d0300400c1c08030b801040130906107403180c02901c68610343d80d004444081c4924504040400180d0007580703039520 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 150871924 1250 150870674 150870721
    0x3090909021309140d0302070b010608060a032004020f0901080f072007030803162714010c050115060e12030f0c01090506010f0503100e0c041104090e03070308 70
    0x102c003184402e071001020045401e60b048602aa01544100010000351a8800e910b90f00181c1c0c544aa003010300500e403040c0c0040080060040c02d0000c1d43e07580c11910401d0720b030448000c03400c180900d11803450f0b000140e01e9694000b80042152031502840c1c4000e001010001c2c0c036240120780d682510710000c46c1088400c0702c003281203810300c0740601103141d0401016034007850032600480e8403a1a0708805400840e00c10150100540c0450f41c00c603071000c1e0b0405000c0840c40d81c0940c5656500c0052201001da000d5980314240300c00480d07900d40c0c41011003010300d40d080780003000096001c846104016483e0b004020215010300103540c81400c100500d600c01ca01108051401c0c80311004c070300766040d8089002d50549640b03442c501b001090b020300441d40280882ca0708040c15600d40070a050400d00c1401c0c801540c0343c035041109458100205500019100071500007540c0c00e80014142d03040c0c0510b402c056203c034500015540315800001c010501c00c0e001740c445105035642d0030307102806c0e010645c0101c003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 150873174 1250 150871924 150871939
    0xf090a0b0403050304060c230a091e0f0f06020c0103230a06080c060403120c0f1b030b18071e080a06020904050c1c1a0d0b010303080c0c1f1103010b03040309090902 72
    0x223803007101080501040c0c0414070304511815075500280c1c5c0f44001100034800101154882000700020b4111550700034815800040c0700e00f482c1520103510350b0340d402c01050500d6111003103a1186400c003e4040094100680041c0c80340c01d010554070300611043c02100100d10441c140d00066140c00130581d400c480c1c1c0a88205031b08900c01900300c4041030065021207041104c0203210303000075150311844908180c0750340f030041e0451440c2003800c0f9869000d401c0401c8442c4107685004c822001048480940c4d8080001c0c1d484d480d000d00540310003030740c15440720244c1d00884c002241044069001840d558404075000c0c40b0355250864003501c50301c03e541444020080c002001404404c0580054222030101860104410006000315011580b00203084400d544e66038010700400d030300051055000840108510b0610b25240c500b6580d41a20f661000e10303074441c40342484c03407050094000b4005220380c0f032406030712940c0d230346855003043c0c0040e101100441e030f9102021565080c41e102d04200380741c00a0042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 150874424 1250 150873174 150873227
    0x618010905031c060503030315091003021f05210f09060c0403061109060a0f0f110a080c030903250b0f0409051b030907050405010b03040503030f090a0b0403050304060c 74
    0x10711900901d11080f4404640b145800035440c2d600344081c6200c2c00e400712212400007280001c0060519004154078001303445d052060000d6280c80c540d194854039241c050f80e544442040f41038491b40503a0804000d00d0b407069801e21141840b0100703045c0076400001c01c01134203885052041c1e4540300c084032200c107542400c1c0000c1002c1240d0340c0005440042d02a10300c1e02c0c00550101113082e96004a5001c00890020070a040c1c01c4c40d8095041401e0b45100e240c4109085a120040d64841880c01c42c007500118020a920040d03800a108581e03d210780201200c40044500300d4a2200250714500c519100407070b010002625214201107405505400c02c0040ca0030742403216900003440701400000d15502003d101c488416001c0740254010fa0103a0024201c1c20320b000208001d85005030800d1003015004d2040c400000c00000c2641c0d00408281c0454510340ea0304148107150600688019141c02c03020401d2109058100c0e0055004030b009203024002282003460644480b032031300a80d942801e0f800c2112 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 150875674 1250 150874424 150874447
    0xc0302180d030c021c08041d07180501140d0203042607080909150409031806050c0a02010f2a021309051f0f05010f14030607020607050f07020909061801090503 70
    0x3901030b0002c200b09103002d4116034803a00b0647d085a00624401c500344c240d40000c3e030003906c2c0c100e40c2c0f1108518000e003c0c191007900c2e1030b200d00d00710b21481341030081e00115520000860b605540f032180ca5401301715280e260504010365030f90319032908081e495a0b0b042d84a500340e055001242c0c144e0b07030800549840c14040d08284000c1620040c14401d0f5109903102040d00c0c0e0303656005e00c800f154000e5403014280d08110402400009140d44401c091040400c4210748800b8041880f4000d6074090a2041034004c04000986010300020000303c0d917048180c20441002c0120003c200c40306000b0303030303c00e00804050700170301017100d180c01c1000e4090742c07052826170721101405502407000f0342c0300c0102141110107000100305541007a004401000100c6070700b80414544600d145000400440c01000d107410030000c042d490710380241c600410031800042c140180c40240781107919080c0d014140c10154542400c0302500d800c010f40b00070f071210b800a4903070b9440d1041409410840e5420801a51501801e07070705 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 150876924 1250 150875674 150875689
    0x160b03071b0215030f0402030d020d1409010207080f0a0303150819050f0109030c150203070512060d020a0b030a060f06020c060313061803030c09180218040c0302180d030c02 76
    0x1c101c1c1e000500800c2031056103165009940105580103015000341480c2c17040504180b070a105a40441d840680508466603018451704c100380203001e410f8cd5200c070400c004038185061500032951911402800d065a2400054482c0400b070103035034104000013050405481c1e5100038030400d10036134000707080041d8a039070510440e0400e9114908680d078041e1500601c6088da40038a07000d074081082d000c140350901664a8041152a2040d04218170714904884054503c2c00f0702c00c0c82c808580480e20003d0860345540c1031107901c81b0780040065092a544104801c140c4d44100e460b00c036490304100000800180441d44071058581d039401829010342404140401600000c142900c038000030080c001c00b04005100d03c805c64000d9244420a80700c25090140a80c1d001000c0c4408111410b4400c0200b18844c240381ea84c2020101d0700981d5402c096036000004880b1880102e900615141c460030340700c0d42513070042480e42907008040003010175980c1044684404100044c0101e80c02c0e00c04140140303490303071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 150878174 1250 150876924 150876977
    0x6091806031a070e040e0d02010b090c070321050f18150a090201030b0604080604032c0909010905011104060315050d08031b0a05090a080c030a150617160b0307 70
    0x29140c82d42507444c10000b02982c5154810041a402a590a000141e4203019030f550b200b10075607114a08d41000030020109208940c0080c1c00c01c440546640b51034040702e0120340c0d00001101080c4110300700f10f031600d9031a00301a9500004101c1044051000796400303c1c4154540741f031108018802e6450f4000d200103480101012810140c0d100f81003c050790300c40001d0005401140002c000c0ca14040c68042c0083d081070302c13056841040003454000710b00031005100b40c03014055550070080d80760341d44928050049904010301c2e5500f4040a001c0b12004400030300100c418a5074180840759100d020740c401d40350a40105a0030824081ca64800b08183c07800031a0000100c1407505510540b281c2a4907a9030011304e10000010b41c0090040c48928100c0d8240c1c02503c903100c043c001401340080080c3e0b4a890300c181c01003410b50b001c01d4004507003070194841d40c004c1595106000446207040907041d1140651004a04594044507012516400500559100d088252901c03580e1500b88520700c00c0c00700841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 150879424 1250 150878174 150878177
    0xf1409060409020d0204051009030b160c06020703020114100803030c07050f060411090c04051008150424060206090d0e04061503090210020d0c11040e030406091806031a07 75
    0x4010005507401030740f000703021038980c4120042c2c42d00d050a003041346441500c0d24120030841420000c1c00441d2030743c801550440b507800783c540e04001d00004295081c100301e01000c1e040e1480805c10009064041d0001010800301d0300c0c9400e9036550350080c1050742246030060344103d600610000d40c1003001700d4020061140500210303031448803100b9405190450444040711020450b00f074121060901102150b003140d4060042424141000041a01203941d40043e20412a0103408140003060600070740c1c1406901030014040e070122441c070210944400042e61100740396a80000910034404902c42d402101e0050180410b8800c1030700c202d611700440781d40c50358031607030302d54000506004001c007100c0d00304c500b505e01240c01000e42c010824280b00c110441c02c11f41d00400741d001d0075580d007c4490341045500c55194a8005030000c042801008c4a6800c501c56100008011a000b50440030003421541c160b46c1c0420640500004801902c115120040801d07801d9600382000e180703240f619581c8010340e07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 150880674 1250 150879424 150879427
    0x40605121e0f1606020f010c0503060f0f06040f050108090d0e090721050610020c0a050d1103060901021b0705061b0102090d080c1204180203060a0e0406020301150f140906 75
    0x144141c050408041c81900001c45514500403c80c040d0184403800c80c0014403c000c0000076123014000d44107108c0103041a02c1008400c0b400603117550344515082d045034016001c680c5031900d40c40c0311164076026002d4a8040340d03005000070311904001400d401481059691082003006601c140004400301400301020310400c90680048000500c42c51040c6807011800031a25003030000502c8541003003000b07260110340100709191150307100e00d048170046901c00d03031340740b042001b150422800313003105c1d2544c803035240c0107030403e218a91005401400382400f410000b022000d0a60009540d1204203104141e0400d105100c0410060300e848090340c9420741c014009498924200e0018a514613010001c0b0782001c0081490210608104004075507801e52050f030510745828020643c001400390071071424040d03000000110b06468440c0040c00800c05000302003005d08103403500d0f2010f50824040d502c410a00c3d04150b43d070f014460801c480050490b51501224a28030802440c00d0340c3c040d42d15607070031020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 150881924 1250 150880674 150880693
    0xa020907050d0c180b0a170a0902060414210c040903030b09090d030f060b04030f0501240e0f1510110a05070e0c0301080712020102010f0f0209040605121e 68
    0x502c0c1c05000c84007416655130704e8152001c068545155005500715000400040c0940b660a6030040454002d80c10411254102d903500c8a4481001e4070300444002d40200d40402d00103100a42d00746142d090500c01c6800188000c03954500000d544800e003400c1e910b650205c950701c61a41080e911818150303000e4503003c104021901b02152000c1d0042d10511190350140c80b409461561611508011002207a8180722040c50300d850a5140c0c040e600000c5c0c0210344880d12442040025480110485580381138140700c2840b10b50003050489183c401c650101400c4400140341c0c1d080c800701d0754492001c8017160184015280c3c2403026144401d10baa03001d00540c9103031108040010011802070602c0340380180840ca090800844400902074420300072808280014031201340d001c140c0105440100c0b1003107101004030300040b800341c4441c40384c1c40c0f55103103801c807200000c0b0070b41d40080600703600c01e440a1051a52320400d000c081045821756810b980c1045d150b208030031004000202000c41c40c14200c412644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 150883174 1250 150881924 150881947
    0x3030b18090307060c08090d2708030310050d08031807090612150b0603040201080a020412080405090f010b0313080702031e0607020303060604171f0c0e0603090a02090705 75
    0xe032510400780e440400c02c04104140b038061031251943c207161a4289042149440d540c403c604201030060099800d04091505008600034154150b0440f40607541e503901c000c000d1700c0e6407007520312411a24090601003940c0c188014501c54959008800c240f541ea00c500350504c2d940c554518000d014016420000b42d03072031440c0107082c003400601d140f0820715000f03460b0182c45140d82803081c0c101682000e103800301550f0b03010241d80e4001d07028280b241c03580e031382c1003da04000d2080d6001036211440d101c10140600c40d043c0c3c080c0085c0ca00c00e98580b25180c54440300c40c681d04e5070034820344050ba0b0342080024178024400009400641c1b04004450078100194002410030816107442500b80e080d0b442801d0102c801008180d0700008580051407441c24001c001c20290b01c0355000d00000d5500d0750031001d803e00701c1081040201c0110800302ea8000340103000711405000c0c0082800001503909107051140c0c507101c02141d000351030701ca00a1011101550a125407450000c04490a0080600940c0c0400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 150884424 1250 150883174 150883219
    0x9110406051c09051006090b03060c0708070c0e1803120403031a030601030f02030c011e05281106060f0d06050406240602070e070c030e0f030d0e0f03030c030703030b 73
    0x213210700080d01c0d2114580a030f41c011501c09611403400d0906041c8045069100452081e4000c045420126910101810200e48a1240c06801050802c950400003041c011202c002e6015607000c5511090440100b0481c583c0d9009a0381001c09004a4402050011f8083e500014142800e05c550103c0ca503150030010341401c80c268001d6905e80f090200080440c6018070002890103004d0a1000b4407108040b001c01b03104107482c2042041c0200041c40780302c1d0a8103514100da0144090f940706024070380818004000151050a09205101e6003010130306c1490043c070b20311160040504045058001c5450b00c001800c005007081d00d041e50303907500c0f12502541c202c1802c2c64400807512103044c1c0500c3c0c01c1c0001e140446a50002c004142808140045541d02c00422841140c0528052030013002d03030000502036241035054554548a0b907100f801c0c1243d040030183e241c002c8220354045401d500d02c414151030b841220800840d54204000e030800081c00f0354404180c2c0c1d1805000c1050071580030303582c2e0360341 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 150885674 1250 150884424 150884441
    0xe010c1401021b010b04050c03010308090a0306050c070203011506052a0a050d080108010b010c060203040201030e101a09040c03171c06090c090302030601060e030a0803071809110406051c 82
    0x40364440c0340d43d0201040c2402500c0950300241d60401252411803070404580c08103000c01028000c00141c100510303a00c020002010b10340000d010003072070510321481f12242c3d1040508900075400c04181041400302140c8030002c40d2170a4403218a041b41c07011011529000707034060751500401d00e0038680004e040400c909021030b8402c80c002c10351818083c90182070104140d00c003400980c18125846016640050303a5095558410000b584075101c0b44010390140c502001d14000f80d100d1208041c00070001d41d0401800c035030001844000381d444400c107001c0d8540d802c07140a002428010800c100141c04030342d5801500c40040b035010f0901460b010070040984c48005102030b60b64940c0700030f0150011510448104014a0900050052440d0301003600c4402c140328060600c022044000b4250b103043c094840070b268020850b50341c03482e0071640607020081d4143d0104004400f5a00843c1c020110700c01c081c01110030075840f40c10a80b604104540c507511001c2d80041204282c044010081c4250050662 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 150886924 1250 150885674 150885697
    0xc0a050309011403090307080702030a0210030501090c0206011a13030804080105040b01150f0e04140f150111070509130807050106081b010c0b040807020307060512070c030e010c140102 81
    0x5031035920303200052402c8841e030840c0000700f10400c14486848800403c48980541c05010503454941c5030001a0402e02d41d61400b940000000004e490340b280e241e0b2245041c0c0d050800f00300400030b01d80c0d42c100c3c0e4600090188101014180c0080200e021781c1d40098400002c0d2804910f012945075542c0303107001d0304558031020300c0d80c0d141d0081c8070402101c0032000c0d015014116140307078940c08516004000c8100311000c001400f11840f9007010710303281c40d00183c80c0c08070442c03002d802c0d03818501c142c49c0032450200c40c0b194020403842c001074015032088a421114a21090042071800d0800d010800b43c6100035104008840304008804001f51140c000341402c02d0082c000083c00c149041121800c008600d215000c0d9516104262001c50780c01001004090350001e400d03074a25660f40c50900002d03c25007201175030600c00c822001404071ba000005084981c14501c40940039281c03803005482c00e5010050090206050f0359401c1165407068550285150041da444c1d80040940b642e22400c82c1d00c2200083d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 150888174 1250 150886924 150886927
    0xc0303130c0308160506010608040b06040504150e0307060b062817070206040302010e06100b03090102090a240801030c230907020d090503030c0c150f19110d0503070302070303020c0a0503 82
    0x103100c5d0600c0745038010a82c42c184042207207003558a07200740d031200800303407807003648d840300400c050001100040c420103040d01000c100c04030300b001c1740d69940d4000711400c560442c01c0800380b01c1d80d428040306031494007007081d42801020710300206a4450801c40b248840c02c10641040b414004010001007074040c10700d82d00500160b0900303050007429900c490302141c11651006051120512580c80032100300d59100d00b40545a0b1115101c40307019200340c0c00c45a038082040080840c44005603000c441c207650700c00382c0c48d0a1410624000b40d42c0c84400f40700150251880000c00c1010130a80c850316011b24000310403a03609805d02c070303001a42c000c0c400d540c1440141d02c0007106040b9103030481200780c06440c048000794180305200c91002d0340d0b080c01074070280c0140d9440c0d0600400c250403000752000203c803048003039100d1542070342c8910600d010080450004114050b00701e00c0800108440440e200702e40c0c0e45a166a64155054010f5440301e4011010550708012011070441c00f4803c00101728400c2d009507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 150889424 1250 150888174 150888217
    0xb100905030114150d1703070216060f171f08010c020706080402090a091a0114100c02100818030408030301031a01150c03260a0c02030c0303130c0308 66
    0x1800c507804001c5103c0800c08001c14010400c1e8401045200604116400c40c803610841c68a05410701142400c102120404424030070201e030007140740012040900350075480540c2e00c41c0100d8800017958201d40103c0c014000000051008240c0c060307020b6441401801e131410200620040c1c00c4066202d44602e95581009032079140d418409034008002c946403120f524109500005e6084078045c2600c80c0c040c1c1c2e280034920400c034401c1c8000e61020b082040c142001e60b55810306540c458555003c1511803940222014003440c002c0d88580000f90700034000b01a644000041514800300c081c29044280500d0910120041020001000035146000103961207514526200780c850f806880303505900d840750f80050200807140b0040c90020406494001040009820309542a0600e030300c82c0010180751a050403a0031284c04440e41c0100341d145000c10007c0340c2d11400300d0f2a40158240b000040c5c00400c0815607608400750784c500e1503800780680c510381c255a0303034030f00346a9400f042000c8801031004801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 150890674 1250 150889424 150889429
    0x70317180603070f180b09040f09120e0301050105010923030304080106030305040905060603130303020d0b0d030f0e030d0905040203060406150f081509070c21230c0706120b100905 79
    0x1a00d05c041d03034956060a104e410206143d0300c500900100d81e00466075014144501c1d80590013070580e00f074106100a040043c07c2d0349c000e00300c0000a0b00700f4004d41c00c220000820f9481801c0040440e83c0b5070340c80c00d9a0318019845110b500300510031041d8148014407000c10707092000c0c401c0800561190b250341c3d90300d40c68501e80000b5164010802441240700344108900300609603031000d50903900d803800599800402c00b0900c020414140c4968004084181c541c08150700310322801881049074980303142d5000c070300d01010341d01c2527071409060001da80c030f600030030050405401460b0440402400495500d45a03407038850210321407850403002404401c154a00c2030707007000480f0b07009840402c5125010007841c02003040340740090302400030030140001c4c81e424030190709690005c1401d04912000d40c5100240007c100103101e0044480e40600800140c03201114a0211200008060b020780021854500c05407515200d05007040d486ca03031a03c1540c8481d42c0c0d21074001d032a0940c01c1c1c855041c401c3c149004d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 150891924 1250 150890674 150890687
    0x109020a03150303050418140f040201030b030c1c02060d020a0f1d010221070506010906060212032208070605010608070314130602032d0612070317180603070f 70
    0xb0b1144003110031600c1440440d612004950030b070790480009540120710005108000d2861203841c40d400e03001c0c003040c01000c1c2c0c0c1150440e4003860007642c060000c41814805c06450350f000819550b400780360f044083d140d05a16030804201d060004140504250512401034283c0e03004c8200c1000023091a10115030583c4c1102c1c1c281424075240d400703281d210b008807001035540c0c0c0300c1200d070380c260071003004ca0000500c1d0814102e8404540c400c0c285d81455a413042000007400040c01540c0160081d4480e884064400c01e05880c46901501015560f41d0f0326074005846400124105803070100c000c0000390080b60440c000c0b180204915613072121249401c0c18010215000480203400c0409400d003444202e1049446041145800c04801030742c0f9102d91030303082c400b550300404000669504000c101c0030103d0003410349205d08402d0b26076440103414640c0300f0b5120070680c0001407001980d14030805251400c40068000d0b021841a20400f240e035140000b441900201c4908001809410f080540243d0010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 150893174 1250 150891924 150891941
    0x611090301060f060c0602031005040e010605152701020109050a0f0201090645140420040b0a02030d140612011b03021e0301030b0f0709050d020402090102070503060109020a03 77
    0x1500303105a2810050005c25800d0700e4a00901825004004910460b10b03c85610008050042040107031240d1294107a010b0110340c40b07418030480c10000d0f4504031021040c07c6440250f00c00031000d00c9650602901140b030001e15200504640da03031515100003c0c8204502c1c05010300500014024088a100040041c480d03500007c04000c0592003170f04405004058508400f981c042c203c2400500301c44a010f030600016003d0902ca0401440006406d0020310180721469002d480c140320504e801111b0803080e0400c5140500110810003040003c000030740e0142910b4102803055078500140382c0d02420584620030034062800070800c4c140000c40c038050301900c101e08070220007440741e140c000010038083c00200c10807405042d000202c0c658612082e200d0005c803508140c5541ea01c0f56100e007082143c4d80c008540140240d800385001c1400140036000000440b8001400400c0744000d1740e0a00010350000d01d109410b511801d03002050656042c418180030b0004e0160041e12980120380007426034142d030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 150894424 1250 150893174 150893189
    0xc0a0806090f0d09060e0f030102030a0614030a020f01121b0806190e060607030c14061b0403050a030c0206070f03032c060105061b160303121a1c061109030106 70
    0x400014900760300401341004907800c41c109083c9030b1a803000414031781c040290032240e25520010030010001c1c9a58800c10a032000e03064800075415410f004c0c10f90700c0d003184001a40c41148004424030343e6208207624044403c0d007040c045181c14500494050700050700383c00d5000701d00240d040060a0400002490700c0c0071018140900303040ca46200409092805000b16004079800a4204203050160755801c65071030b4400129807812102800840d01c1c1c0e003040e54103400d0310204134020450102c40e081954250b0760040f0103800e401d8036a0b9070560b10400c089030b040340c002005018031004196801c030740040041c080c1e02c0104e9545030341056003510620000300c0c0024450910008070103601d00049140c1034071070549456a070748590f0b482000c44000c40c0500320a40388079240594803440204003003503007100d1198861000c90540c2000320016100b16541400000c2c00d6520f50029503c0c040e10701030308107031428440101c101d546e500c524090390151101c0300c00300d040001b07508070f1900b400d109800081001c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 150895674 1250 150894424 150894433
    0x3040f0e040b07030213060f02010209090a0e12120a230403090905010b0c0601050904050109050f03091003020f0a0c06020f040906031514040b0417031906080106060e0904050c0a0806090f 82
    0x140f02c546c4041d8442d90003010100b00300c0e1031a401601e03000b54110f404100c0024410082d52800401c0e4001070040d403141601c3c0c6000c1c840c80b50740c102203400700743e030444000b5448940361581c4050b030020081802101c1803c5101030205501d89401c000d40c02c6500903802035460001c8582051100300039540180c0c040c00310441d04101c2084030000100c1c7c0141994011640204c0d03684860906074090507588c44044c1a5005400424091000000c002c003102c0384241c52007105072101000c00c1d001c90240740d85c10100c8903c1006507041c081d200d800d068411034498000181040004e070703d19840c5402c1500101d110303d541c3c000500a02101c12a0920105034424051184030209175207528681805400100011000c901003810040c00310700d80c002080200e6503d40c0c07070b4640301350600700810408118480300c0389040001b250510040c02084142c2e069911240ea00301c140c1410700c076503284000e106440d03d0091002c1c40155590b141201030080801100401072402d0203c03005061211030455110107500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 150896924 1250 150895674 150895687
    0x4090213081603020105031302181e01030c0b090d0804090204061202040605040b0c0c0d06020d051e0105060a0908060901020c190209010e0a0b0d141618020c03040f0e040b070302 78
    0x142c0c0c41c1d1040c10307a41d080c80c0041c0c0b00e07140d480c0188072003904100025400343c000c00d402e46400004404991007150040402c0104401c00302050b00c010400b0700001e05240c813041d0040c016004040010002c480020341454030480094807071801c250081e0b00021405500000c0c200003956118412401c2d189040380b085213002e1808a0162031841203101e200c41010700425542000d410602282095600182c0b0400001e4054030303210000b540030180b51410a4502800b05014000700000240c001c0c00ca6072000c0d200da42020100420380d0440d000480411400703c2001c03486000034442103000e100800005601c4207001e0355031030300b80380b00b02c90110101203d0500c10f5000d83c0e14040068111031503040d5807a003e0b2281c002c510060300740c401d40135400c20041e0b203410003000020f041809c1e03003001040946190b40003c0c070072552070b2000782c40780b4003604440c4a601c0c0c1407031105500070003001c00c9800c01c407032401b9641c654088a0f15503d81c050301c03e15040500b00801d1080030b080a50380b00540740f170118034110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 150898174 1250 150896924 150896953
    0x1b050303160c0b150a05040614040b030f0a05010903140c07090e030702030f0f0622170c0307030e040c02030f0708160b0a05010e0708061e15070f12050f07110d06020409021308 77
    0x40300d0027202e88215110300151040741c400b84100383c204400b000545a0040d190b0070400d0180c80206030450014000440c605940c01030003054540d682400d9028118252030302c208480a09118402441c003030008010401c01a6400c00c50325808104007030142118420402c081410520f0013007003220481c0702520a1708555a08200c00d5411a60190a0000072010320010254600940848480900c0b00168010034590000b0300e110710344400b11010702103144810422a182e029501c407a80c1100b02c00d104600c00500250040d1034420035104182041c181583c803410782c00348003136038036403150359440f801444694643c0070901d601c103105040048540c1408004540303212500b403c001400780085405070040c3d82d40c1400e81d0b190034030501903d9110402810700400318001290216003504246004250701400364081c1c40c4400243c000035403c142c40768444400000c050400542e008032040c000301d0000e0403520140000d030109140050b1140f92031801c2421000c138603004080d250307120700c070013891a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 150899280 1106 150898174 150898199
    0x6010501360b1c0b0a03030e040f0501180507030606080117011409070503010608060f010b07060e0d11010b01080f1b1312031b050303160c0b150a050406 67
    0x50440d401e000b0f040324803803100a50031107524502040403d02a0a042c41c90440190010540080341c4824208036a403d0300080c00402c84101c000300111403074402c807940404581020000642860800b40400701c0510403401a4039001040504503402074111181900c400340c100b10403400e0800c0c10949444d400e004060081d860300000290200001800310f0040720b03403103d5022540d00305100d88150350300a201c1520005e44130b5100c01032150f010400d80c0240c044c50b07503c0410042448540c0703030075150140b0385a81003101d010180301e401c103002070030282c00c442d0301100136140348684607513262a070203028007408002c21a0700c0c0004102e0020300605011906c26a210307026140c900c00041004100288040d00d5540300b8000600002000314403e001440035061480310082140e03600e6041d8003040300c0c507064980401e400280c042c245241420040d10301107030140000c9080c40c00d070103441d = true := by decide +kernel

theorem cover : BRFrame.Cov 150719424 150899280 := by
  have h0 := BRFrame.cov_init 150719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 150719424 ≤ n) (h2 : n < 150899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
