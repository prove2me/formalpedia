-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0780
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:44:32.586831+00:00
-- url     : https://prove2.me/submissions/93e89ab1-34f2-4fff-a415-f5d6c4c1085c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 140107913 ≤ n < 140287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 140109163 1250 140107913 140107943
    0x910060b0f161a01030b0a020a0806010309020111060117010510060c0312060506030103030809010b0420131505040312030510090b010314010b090f0103050415090503040305070608070327 82
    0x70b82a41c401003a6032042d2055103140300c5800f80348481500b80803d48803e0748540100b02ea8010354422510310180503114010184e0301c031401503004005403d4140e05101d0b8400c0744010004e02405014041c00c140260f0180390205413a40303500b1220010321390001c0414000f4188000794002c0c5ca952651a41880d060810840362002e010161516030300c600c0e00a600030001008040e0007000030341c8900c030584020404055800100001d6843c0385c0c40101c0700711301202c0354080303500940e00204640c24180c0d00040301c041e0343c0e0307080c1510002d07000d05041c000794020405208000450280c0c1c081d02220345000d20503401c009100c0074240201d8071900f480d442e51800d503489964065000036001310b100e400202c01540c5d540d140300039194031070341303089100c4c0c40c03070184400d80e42d80244100b9000300e822074800001614001d0307420005005447e001e8450b84030130702001002500030403450300030300b441d55145100c03401c100e41c000c1c054a5200c8030f18141c52200d0941c41a0f04003580d8206054960801d0703504006201c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 140110413 1250 140109163 140109187
    0x301030f1e050d031b020105040b0601030b060f07050d110d050f0711060a110d0201020f03010e250e180103020d06110f0706050f0106111902040b060403030201050910060b0f 76
    0x244070050107400340150540006405501100144001203080000311901c20022400ca0b0811500141803008140c045031065101c0d920200d031000700a40868174200c4525180051504503d408440303070b1303001ca0480700010b6840386140b80c1440c1c250000708100c07a401100a005809804914100e0000100b52a018001c07d0403c0724425400549041e50f140d00303042d03004042001418134208030344111200c0415152051007100c501c45c9102c09003900716400c1c5000000b9a1002524500c5074000b42d40c0029864181c00348800c5403800d0715201e81c1019003504c004e116646404030102c00010407811300420258840c1882100c01961024002914510100c4124818003a20007521881c030f502182c100200501984890301540d610320100741c090b81e0790b00080300d1500c00003015002d41e40003d500d6551110041a032181014402040494080c3c29035000c280c0c00d0b04168810740040c1c1d1941e050200e408401d00208a18410034201480041e04000750f03801d00344a410300c4441400c2c1c00041921800c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 140111663 1250 140110413 140110463
    0x6180102030d0501060206091501080307030e0a15180b12190e0706020115090c0f051606051e1302010f0e0303090a0e0601180e01091109150c0d050301030f 68
    0x307001c00d0410003c65840d220f00940d9010211402115031042c003030120700e07030691010f1460407100500f00441c41c00905a800f01e680c3d5280d0501f054000d0111040030403000c11840408007080700b1540c2d441f050022210400c01101c02d554030a090120040080c102c0d01d00120f501d055008400207100b0b0100e002c6150194003e0540c01022042402441801b18074141e0642103840b407020226600c521443d100c900394804c4030300f010001c40100d2900500d0541c45402a03010381074040303032400001200001074031848150b07030044030402a500032061100b03810140c20b41034690044070400741440500359544c0080c0c906800b010500d4248642c0d4440040d00781d804104445600780040c00c1d8040c50b81d0b5404a01c01c908000f81e030064003140e103540002000c21508103071360045600d1142040c2269180502050041545030710007291844204501c031f0700b6840e60f14100070001c030b04a100ea65200c0402c9481030924400e18003010420008200420204a620300e00e0b004480c0c000ca560820b5a902c21080e81c0c0300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 140112913 1250 140111663 140111677
    0x108090319080915100e07090b0703030209101d19080a0507050103140c07060b151207030b060403050a080a030207050a05010e1c0f08041b0e0103020f040b0618010203 73
    0x100640e180c00c01e05664014042030003400014211107101d4400c40000a51080c01c464101d00c89030b4000341045000300d0750034911341100e628209644000d840e5008140d8a90180c84c0941c0800d0b00060391210900344290717014207a050a1a0462250001c1c1c4040c0d03018243c1c000c202031003044445415180d0101e003102e0403000f4000d402c2110ba6407880c614055481d50301c103118050210b8502841564800318008243e880f6002e0b41c00079616001040da1054010201902403680003014011203c1d481c451000c020030914002d10814041c0e0314092070001e094902c10a1028007455041c00100700042c400075542c08076070340c0b161145446041e4903030214000d004050000e0a9032082034114402c2c440c041d4004030800d06411f00340c4d610b030b040908404501d00d43d0280d4407000205c0031212210304511401c04a50840e01c81e10801c0c0c0250303601c080c1c420808410781c0024091500100040045140c881c40244d00b00728182c505000701107074000020201d000e0030305414009644400702510320b0707109004450130 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 140114163 1250 140112913 140112937
    0x1206041d160306060e060102060a1a0d0b0901050c0c0316110901150f0f080f06150a1808010c090b030c040902030a0f0506030105010f05060c01060905090105072601030201080903 78
    0x300780c48140140140301c000e10041d200c184c9410743c04103404510184183c401c2c0d1060300100155142c220000c0c009140c0814051002c83d03140c0c0c141c4c00d050341c9600c0c0b103034039443c06250342100c035041c510f034800c0c21a10702510600c47c3c000f0401c2a503805040100c10b0b1801c07100302c20000c208004803810b0111543c6011866242d010f072000f00082006e00c45400170300c0301d07a031250f620032440004041c02511200d00d03102c1c07400c02240a0000251900c0da00300032899102c000603085180c0003d03840301e800c960390404900d07203001c141c90021000c1e4829002e447c080c001d015850080c40b8010038400007420181150141800c2118000000f440203100c3c64100c500410a122045507245000c1c1c1c18140180007400d4261002410300c004500d0301e140c140a003074160b811000c14241100c1c90300040220550020b00d07400c03441c0d501c8800000d0041c03290710a0601c6601a0000407460385843c0000412a000706801040c403c03200580720181d01d550300300c403181942c3e82030030813242544480c0307822480c41c00343c00d0808803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 140115413 1250 140114163 140114173
    0x5040606021606030c0503010b03130204090b060420040b0306030f15151e041d01050916080a08190908010510060e06040e0c0306060705121903021206041d 68
    0x29640e034001149600a02c107000c0480c121511507200f103003652441e41704240001c200344014017003a0b00800056412010041d00c0e03223001c41c220f074040340541e845240c00781e0f0002d50344004c10100c3d0400b8042d40c900344151911603444418207112014060142d40202c4462200c0030000603c1d81e14104401c1d20101034000c2240d074a04540c4002c180c0460044440c441c20810311030f500350081c105020440410403851102406254041007801300a000e11400202540044581d4086081080c81518096807810024001c0d000705100281036041860b03100d000c07103a00c0211140302140b16070069940180500d510104024000401216034580b2604003441c65440c1000713100209024018081c2110000d8507107100b003400d00303c1045010f000f2031140c18410148280002d608030101d100445d8080700040040c1d090404545400c1d1602c401980802d4141200040c0e051218843d1008000c00e003440345019460319010101c8042104000b9240034003441e2901c0c24107034982c07242001d46140c000c485044907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 140116663 1250 140115413 140115419
    0xa031b1e0b0717130209040302010f020705150c0f0714071502420c0d060602061b04050d030c020d2001090b09060f0c0a15021c0b01091707050406 64
    0x2041d5000306640030004114000b5a0500341c04916990b03e00c01d62960740c074100340003030341d8007408000c5c6401031044045540e40d680240c600d006c140b000d050306500400040039a181400ca01921100c409000362040b00c0301885040168a40b001c00c075400343e980b0084030300d00c1d15411500245000360f140c005408290514616258003540021440d5202c0a80c44907540382c0692407855143d9880d280d202400340030046403181c1418640a5021030308441000d000926180e60380c685401181c20580040006030000701c144207031030314540e15130a03102403a425000d1400c0d00d400b002440481c4030010003014801c04000c1201555951110300c0140c9030000c81c2c4001c0046403591147c010001d419600d400f044020f9404070b8005040816a140c0703040140c4810b1800360b0b400c8407180c0b25040200c81140754800e103085c07540040e00403100d41d52280c01d0101c0150310350001c00500504031140600e00d0071194544901420710345e9000d8045400c540060821201003a40b42d0b03026428601c207500300b650410b0500e4000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 140117913 1250 140116663 140116673
    0x20d06020304020907080606041505091f020d14090409110d0b070f020624031002040b070b09060921070b01030b0103020102011112040204020a0e03010c090807080a031b1e 75
    0x1e612580c0b003204c11101c1561080000c1e55003c4056401c81d81082e4140424402c080814419085113001c1e070a0550800b0b00c40000200074043c0c0d58018a9260324402803400015010854415150b6050030480d0440d030070b080d10041c0b01d01850300001d104a48800f601d07002d102a0083c070100e1980c000d003500c00400e02c2406c0c81003040000b1346003500001d00403030450300414404100340e4016004180c8100c18154100e810300c0203034443c2544154175001e5003403456248481031000700300a00346025466282e60740350901500310030000345180016045070040004142e00031070511054110404d0302031031070500700604407060282070700c000d040703813058030012040c821124003580c1264800d9000b4000d50b41c034422a81224004c10394401c0c0c202d45e05201103801894240c006d441d003012035280002c0c13032445030000282540d40300ca06010202d2520101030004680a1100c4c40103040600c00820742ca0500e6580185011a156404496810a03d08a000b081a0f070000120046e05862407500c2500c090f041c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 140119163 1250 140117913 140117917
    0x1b1201060f0c0b0f0c0903060a06050405010504090510110405030f0606030d180e06040f020d0209010906020705060405040908070f080c07121e1401050c0a030f1a100309020d0602 78
    0x11540410100511241d00c2441007640080d0340b54044801820b81d181c80002c26214500a0440051180c1c01c1c00340c0c2e5201e4500700b1031540725485401c00483d4071b85c6482c0134001100c1c01a04090701860800c1c0404011410001d2050541e10908100140f080b40041d2005a01c1c095600484d0b40760241e41300d104102180010711034020f0800701d09440c042c01c400c1c0d809485018400f5421009800100020803152072000041680800080c1010510602d441c41d2442282d0100c003031054615400f19446c1002c0d640f2581001c081c01041c0002e240d05801d101c00076420340a5840346604c0765854502607020005050b0641e4034032035100d0b5942c40782c440b03e850315000702c0c4c0060034282c207507108000c0c3c0003d1f5400b402c000040043e130040c100d030b001c040344802580030613a1100c00c2500d042040030026210010240b01c0c4134030941c0880f4080e626021542c60007001c4c3d40c5405001425503042a50440c0c5400003a24040c440300002c03150aaa07140c0340100c10f4000e001d1b00d00020b98408040280c03a4140482500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 140120413 1250 140119163 140119169
    0x180f020d09020307051f050309100507170708010e061509030a0b180102030106080c0c01150311120f031803150429040f02010e031612050d0f171b1201 66
    0x554801c5a100e00c03c6c080c0541d42d845822416030340b20f0800d11103e90140f001560070030034a038140c5840c1001c40d80240c05542c001c0d190080040d030f01240140260060301d1905070440d19520b4102055490500c0840ba5020f0152101c2d21503440d90f0b00e1844141c40110407030300e515101070180e070000010760520108045085500000c2c040100854840c0d0034818400c0301d050300c2e4140c4540c140c40d1030300d6803e0002c80d081007803500001d65885954440c83d1203580d003518025880b038203001400d050000f081c40000d42801c0e10400d21a40b00c20341d8100312650200540e226441c10081d003480c00704860700000c1c42e20324030100624040320341006100038002c0340780080e82c0c030403c2c00d091030000740c042d11802940c902c002c56020749000c10601e86180150300c0740160198000700202218441229082560801607465005e20307120310f080b403048010003109100000091401e81000007480648a40143c096900c1d44c000054201c1e110001410b180b84040040c2c0c0c654800042180d1256401c40c241e100241080c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 140121663 1250 140120413 140120419
    0x806070207060c05030703050a030f0f050411060a1d0415060c061404120806041b02010b1903020d0602131502030c0708120f092e0906080709180f020d0902 68
    0x4900800e0043c0200b16150019920500035403030100c0e07a86013200c51f82c0249010310308142d260a40502c103400980144012011080000074541c1410b1070201c1203055007104444c000d6905010b401c101e01e030009802c80c000e101400c0808105607000700040c00518100e005032507401c034080c40109100303038000956141c0f184182001c0010348101d032440b415203c41100c00504003c180d480b80104940300d120680c0e0042c00242c008540d00f07101840121079080601d1100005039540c0e030f4844170300d1800c50305a045045080d407081e001c031411500403a075540501880a0489900052040c21035000380354144002d00c5c50740c0554144d200c039100025125442210048880d1003100404501001d000c151070081100d01d480b881c2c5884100c06841206800c080000e0b58020b080f000040c580b00c0c0d80340d041c00308804098020301f900136007410000c0c00310b100b6030304280b0402c0120820007240c5a0011b10400540c1d42d40c03203900425401c080f4a00300030380388242c030080d19180040350010489000360440032003a8401c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 140122913 1250 140121663 140121673
    0x70e010503031201051c06060803070b0a06050a03030507030210091a07030b010f2001050c04081005040302030a0c1103120d0c03020705070504200c0604020f09151203090301050108060702 82
    0x2501015583e000d110b020600354010742004103d80c3c5002e40d92801d08a181c2841015501c1e41620741e041102c0c1c882d8400003080d040081d01e0010003111650484e84410350610400c034540c01c00e0b000c6010310810f070100405101c00081c54a09041c001c01c10360540e101400800e00141c1d0023403520340c408c1841100c00382c0c3e81158903400300cad410f14000e0195100303079a410b03550b004004010040468502030f10191032141803000550309810a1402e00a89100702c507030190f070365942d600c0c000e03082e407800c40d9000e8102c0c032031803030a014000040d3b400f00071580d01c4000346c5450800c410385c60911100c0d22a01e410000e0740362250407030070a0a050504083c00345203081060800c00742e0300111054003a8420b840c001421a00050024803091034654440003250024a0b10941801e03455a49400c440d03101280d100000c0c2e00190821046141c50f140d0380d91422001e84490529050042c051030380700b060090240c0c41800360105520440b4001c1050b58038001c80203009000c03a503960051140c5600060764080014060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 140124163 1250 140122913 140122919
    0xe040201110f0c010f08060d1101111c0f08010609050105030a0b09070c0309050d03140a02120c03041e030209040222090803090613030203040905061c03050a0221090f03010914070e01 80
    0x340c1e44544952005400d0109500c0312799107151501c072088075003905000c140e41031000d208a04204032032000f132081e5001080d068100c00c1c00b40c04102622001d00070404420014004a80d202c2080e0045070420f0030401d40301d03158030ba0034801910107019016081130489040100361903102e421300b0b048a01036110100d4094452060001d0300007211005008030700160071250740400c25500806c209074080c81980c02c4002c0401c0f0f000311507400708400612039807010800780700c81460110480302645400b208800210300c0d50f400704200c2c0d100104040d1103001c403040314003901c4500540088400c20445030401034000b6916104100350025921450785224030400110b414034103038012207103190150002c5080c00d1422070000098003008101c01e410040720810410300105030b07039059491922070b8076042d44030f80098000a02d040455094411625884009c415040010743c080f0380444c0400c0c0c41c8031000360300740b10209000d000784850080440d0070341c41403003459980121b410001c0e9044000c00c1001666 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 140125413 1250 140124163 140124167
    0x60504060602070501110c09100906092a03060b030109091b05030316170d020d0c021c0309020102010207020d060501061101020c0c10170a1a190e040201110f0c010f 72
    0x4103074010340015070f100e01c0c41442190300603221440410a400110b402d611458408542c01c0281900ca9905011b684030052005070510701407440030f00720300301040101d0300303010540c4100110402c01901009401204e0000c00c0e40c400c0c0c00000c00307800c0c000740096495a41e600c2000013003085041c00d880748207400301c0741000031241c40700100c1144c100400860401168401891542140c0001164600f9194401d00944270841d8040c200c0c0244d040c900580b5107a03071500364000c1e11800d0301c600045401040d03805929010250044400022901d40015100d51620050b4024815604042c0d0f00c00380300e070280c0d000c0110301d411042c10b0710160b940300503042d034200c001d46081c0d000710443e017802a001000744d9119810041103869541e060b602e00f013055009901e003031160b04542541c03400c1c10151184010f8201d540c43c3c8600c031400c400180c0d40700700b14043c03400e0b0a801c800d0040c05802e0104041c00d021030700307580c401c00400f002400050161500f0009910140b640c5503405901240801c14400b00320f03040d18 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 140126663 1250 140125413 140125421
    0x606010e030601151b0c0306090201110f070e190f23010b0403020f06070b0906010e06100504092a05040e1b030402101412060f0409051c0c1e020103060504 68
    0x18018440007108240030079000c0d1104c4841d49400c01017090710200c0c1e0404a1910301080c8000c40c09040e001078081043d00004011198232418405594030651001c4100040004c80000312405001034007419191405075000c0a080711009803038980c100503401128200b154804c055400302c5841818130701d071621034041c40c982030901c84d41c040740c4014030080000d8101500b1000725003030028406480c2c200c1a507200441c01e0030507901340007668011001802880a80b080300c0350400710846846c0a2002501d50090242c400da0040888032070b102c22603c100040ea54400c4c802e045000d0080310b200b102404c000030125041441050113450120b0041000e03603200f01c121490030808028003618556494003400b00a010346070844080000c0305404020121410018003100c2440c02d03020a20b80c1482001c01529000020100344150300e41101c60300000c030006255140300700725800084c40d001070340c1d1007038411458204001e4840c1002c1020a6a401c014084061466100362806c005540c0c46109001c212 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 140127913 1250 140126663 140126669
    0x5091008240a030807150f050c1602030708030f0a1d100c020102100f060807050f0a0509070c0506042a150e04090203030c0604050d03020c070b0f1b0606010e030601 72
    0x1500c0340724071041c01440310318401024040a071007418255034999070603c0641c404c0a040c1c1c0c0700b1100801404100c43c49000d40d14038803110032020322840c20303c1040500b15124000075914840d45105204c0c045413002d2010b1070040c001503050b03a8903110000011501c551107507501d800011522005268030200d102110f141c142000b81101e8502490000c007601c80c002010426415031184824140c10049075004001c504d00c0314080200d10103141c0702110b8a04482d0350031041c483c1c04642d4160300780340c8410710104c1c00c0355030880388480c1c61744901d076040d100c8514102c0040c02c40d001c0c0c001000700344401003c45540d003030940382d1101001601030918440b011064005c3c0805284c4444141094a2203040c0e48520f4060081000401010382d6001034a0f680c0008403001c00b0b60010002c21051290030712000c01c0b4000036003030541c60008a0f594581d25440c2e1802040c030007080c0030890034540c5071a80192066040c40030f80500104072441d1800d03035155404c6a009001480794204c404007418080364190403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 140129163 1250 140127913 140127931
    0x313020406050405131e081c0b0a0f050f0d1a070c06020a0206040b0c0a020604121b0b0103030e0108092a10030504051e030315030a0506040807020108010b07051902041b05091008 78
    0x4241c8d00401c40b111014844071581d021076220102103c02d943c031040110005e040320505aa070040c41c0605200c082d0b41d42098141c8940e0900303003010042140309010025804202c0048102c583c0e4101301640d50860703600020308030314404584803110f103070002034081c002c5010b25000e000b140c0e902d01c2100c3c0c15105c0e14094000680204c408100020130912200f100d411701400c01020701c03c5060641e802241d4092000d40d4900002401003050582104840899800a19281d841403400c2c8000a949402d014a00801d00400c092200070040600303d1108140000400380c1403007214031600140a07040950381555940100191145010b0800d01011b105600c030364059030955443c5d42d50980721a40354020250580108544840026018000b49200e2031207202c2031520b032680c1c1e0000600f11801600000d6101504120100c02700e030001501c0c801d0300740480055480741c0c03028804903000c0c0582c090303220340e00390801046001c2d540e004005807009503010348100c0302041402004841c040d03002e8440c184 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 140130413 1250 140129163 140129167
    0x70509041a180d0c110604050102150c090a030501020315011809150b03041407060212030a1a190315061202060f0f0a0908010f110313020406050405131e08 68
    0x4a0003054280307095000309806000714440b031408142034104405601c2e5140010168a121001c00c10046171342c103007203401901c2c030f03034109403c0100203992a00801c9038141b180f80d0717480010f180320381030320704840034400040c14440401366a403500324040c1d00161a0030042c4120b50703014907943d510584051089080100804441c5860300701b80750010050304103a00c507000341c4c0d0400401c642000300000c5004900c00e01c0b14004071103402e0412800c00c4c001e50000000c54100c006402140640403080d80d03080450860000789050754450940c0c0b080b081d0650140e00800c0d6000001100c03030414840000701c078001c403800180300388038042d02c008941040c0070f44440419a03203440700240c00e00d003018080624200c0451440c14501406502058110b50720050000e0080e11050000171030030b000300c20a0300b001843c203000b42907000c3c800046070302000304007050411000d00c504040d590f40c0d41200004182c0507004204604184610310201010300006640e854503040074901c000d020f210f040304500b82c10001641c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 140131663 1250 140130413 140130443
    0x2010f0b09130510020304030f080114030303040809010216090c140319050c0d02040f03170c0d03020306150d0c0e0d030207060503060409060c0e010207080102130b0c0f0a030305040507050904 84
    0x412262140c9819078144c4030f5030400403030b44205440207500540c0a9100c400002c0032106005000a07016042452102020090142d06890000c10369800c503500c0070007075440d006444c1c0100c0ca0320621a41026500110361800030302000035078403444c81c0ba51b80e6a591301842407802c880d40c410748004c1d240220450710441240c0c0b8013200941c8800d800814081f015440c1a04002c02142660042e8101c4c401428100c681002044401d84100440889440d125414030f8545490192034040000c040c07024990008000b604503038803244c00d8001c280740c5006d1552600e42c10782c8400010012042c0400110b034201041c62490b02d0203180d103000855050740280b40f12410302d0021100750304060411504603445590b458001a028001e4007800040d540d500d8000505603000240340101075440b00c29564810800700c0802218619050281d0f075149410960700e0f0880040325180403150f800003d054041e004607801016415001710b40a5070152040f80d00e01600d480070030040140a032001040d0b880b0340010300d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 140132913 1250 140131663 140131681
    0xc03090507031104060506030901050f071403060904030e040204080c0f040608070603090f1a15060301061b020d171803072d030507080f010609051012050309100f02010f0b09 76
    0x600d0141d00042c0001c0b0381c1719074a502145d10350304196001102651154200a540e10036100c0180e48188103150132000d0307410382042c10510703200c060152030041c111440050141801640c48040e507020291045540300e9a500100d62a2591910254032030f00740d040302c0001514050242000b0303030f01003c0c05880700601d03001040c0e0041c0710b032000484216250b40620300100b80031202540d2440c0c0341c0200c0740e605192002c0c0c0c4104840310702c910a84148010710051040c2640003130170501e4040c40c00002d0001440b40c1c00000c1c0c0808080600901e03046d1001241ca10852140000e00380c00d410882800541c5190042019203070415401607a40000000160031410071826556440e20712030310b1050000c15440761903190a011076034001102c140d0041c0301031a8100000d1081400800700010300704502d0034a14100c105903030341d91140c0303101e00041c58040b8084c06001c0c030446010590041c5414582d031020340c0d015200a0850035060050b51034900c40b491980414080c6100a11000b0081c0542d582c032a182 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 140134163 1250 140132913 140132933
    0x90d03180b1602011107080712081b07050312091c08040b060103020d0b0907081f0302030303040201180f0815010e07021f0b0d0b010305120a0e04020d0e10050108010c0309050703 78
    0x1142d000c543d01c990302c802ca40741c9500006c08049008800d819603c2d100c2e0f0034007000d1100800c4000d82003020500402607180040100030044400c08003149541e1441c500780603181d03005880d0030314100f542e40810b0182601d400035102e41c4080000c5815030340f044828000344d8040781e049402414410100002911940c4254001d1800540341c40000882c100c00b0000701d60900004c540040c0424040014416019001c0004041c08280c0d04008900ca41c11540869124080070740000d040c000421550707802c4184207044000602042d100034080b2a0b42c41c88032607640c95503c21071840100c5840000f180d08400c484440c3d00c40c100c0780d0020503400581c601c040146850942151802950320f000c1c040047d541c41070070101d02c40c0030b00e66900180d41035044c00c504189c05001f0128511108100c07841c1d18a0f00a01c0c000c0305020704490058540380540030031805440c1003142d9400502482050b40d90381d501d00d500039070503034002100030000070101c100c0c01d404517104100c000d00b250b440290100005111100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 140135413 1250 140134163 140134201
    0x304060c02150a02010f0e0c030709020904090203030a02010b090a020301081906020c070e010f0510090608090106120305030a05070f0e150f030129030106080613090b090d03180b 78
    0x40300082c420249034294241d000b80c009080140d4543c16110700e00340d040d001e280700945003840505042001c903000a942d820b840e200b5060040c5d00400e4030142603807158000004213130083d0603a41e8510061000078002c04103001424403c0a03030602084010145100350fa0681c0c200c0c400401010429542c103091303d042540c0102c3c0c9058003008881010340e42400901c00610304d00d801d400540d418465000c80300c06690700320601401d03000c43d0291103150301c0250032044901504004070700b5142c02500f6409030171103400060f005442c02c03103441c040551120096218003114403041049880380b0b4030848240b89030780590300002e0741308802c0c0141440c0030b030618601900045d1481d840d02548001c4055242c2003603004040b0071421095010340000100c103402c0508641c0307002c0c146190704085001c3c00e46900030301503c0c020195494050403444045e4007825010750060801307102c41c9006140e0681da06448001d1000103410507001c166901040c12240843c02c0d4002142d003030680d610140c145484808003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 140136663 1250 140135413 140135419
    0x9030215090d05031824031609030515060103050f070203040b0a05070605040b06100908190f050a1b080f060c162901050d02032e0213080606030f0304060c02 69
    0x2c640d02e0000c0c50070001490511080110002c00001510403c0341d0400306540d81c0c3d42000f803500c4018040380f0010101c0390b00041034015181c110103003200403505400350344c00c010a07070f1090a9203414031410100c14680b04070803d076002c4c4107035510300c07020404040099460801691041c4018001a82c0802c042d00c1041e10920b02642042d80680710031050740c406641c01c2e41e46c45080710034000c89003040d10807081204c609041c03e1112501d4824440d03516500040445200c00b40701c030a09042040703400d6030290036034000d001c4450084c0c0da824911500100b000b103010041c02454070001e089000803a000340d901c00100c1c06440c240d07a518490504650012294060324032040700c0b0800040c8401080102000c0007410700b0745810304051481c030100d1010781090b80301c2d1500b90540001a54001862114600c400f05280c80b1408a581c111a601d01106050070f44c46002044062903403252505000c00c031420001140c1302340c0c460a040c0340d22200080001c03403c58008100500c01d4900403021070b14018806 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 140137913 1250 140136663 140136679
    0x20a0504020d11030f0405010b06041a0f0c030a03050106110a05190206040e010b03060301150305030a1d0423060406180b060409050708090c0f0d03081009020406050d05070903021509 80
    0x1514901c800e41c42140c0064170785641e8000e1005101091140040b2148141c030603d1419080c121501d02010030040e5566103080300152074404500504150303002036203544122604d5200160700940a04024000c05001403203801c4030804c0c8030380010700f4200f5076820901610300c0003220b0840c4452100e0004042e42c001c0020400041c680c903a860341c4a00030510040010340b02d00345402058296111905814030030640380a05101049011080300c0103072201d4101040030b103001c490111620b40240700b110754800c0c600f80c02e07180034945000b1030051481003a03200751840d0ba070b100e00b0001141e1250061501e0010101c104288901c016400380401100041c80d04e41400d68891200d0281e0b10304a540400103134882e000d200e1441c05c1002080000c11040342c100100c19402800306100740c0000c18043c04015100c404644601c80503c89200540100081550b841381c45841c0500301e1390008007103540c2d40b8074000000303202c1449082c0039401e42c2d82c024101c0b20200701070015980181c0088031050307846036034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 140139163 1250 140137913 140137931
    0x90c3a0c0305030a08040c0902042403090212030408011118060705010902030a031215061e170405070312180909021c1101020c040207020a090e120301030825020a0504020d 75
    0x4202402551040c0d61743d64449141514102d0b40300009036000302019401400144601d20f044103090643d100e04801220185000c01c004a020b040305440180d0015200403030a00d44510200080083d00c20f001e00a00244588100941d01d0f8800c140e16280c0c03450752003500014525001000700901c5002e0000454548a1600000d0070f00d40300304022408944203a646825500450140455002102d6204400240f17045000b400000300210461950300e05111413581a42c00750704150840e9100142c404464902481c0c95569a2800d0005036010858805440c030114415003094800400e18482403140e14a800d40d650098014580126805104403400300d14000104141c0e141490041c200c00a0a4015400190500c800c0c514514083d5004000003405600c54003000c10803580103410001c0c4800d8101c560030f090100c8081101c40da00000000001403001c14030150545100c000d545140e10500503841105216210074002d4002003801000c00440c07a29a01802004000c2e0001040d9410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 140140413 1250 140139163 140139173
    0x1203041a090303040227010e0c0d06030b0601021504030c0f0606121a101202060306040b090a050a2a031a030706080f0a0b1509030c09090c3a0c03 64
    0x40031103000340c0550010041009502c0c11107074011180c0f5003100c42e01d521206e2010400320340c0307405005994101e5030b08800300352400420303c11207620f03c3d1504000c001c0e040c1c980c50991150801502e81c11300511441c0080d40348083c40d00d000c06e0095038151150b141c0c1a240707907078151282000410540da1580e0398540003d03038011000705600c10070301c80e030500b40c800080030108504032680074001211003a0b41200a00c80d000c015450340340c4258040b214162295500d00009000d410300ca10800e402c22038800c244191070001c1e4000900034500701009000030000c0d4150010000e00c081d0201c0c0414012100024406000f40e1125210700031003103000e1203030004540072920b030a2542e80003e0019480a04000f4640c861500c101d4100320322440034405114500005848119041d591035803002d00000c180c4019a01002426804d0001506020680c43c0143d2901c3d01e415400709200e01442c2a40d920b19071400c1d81c0392040c070940a1384170303020b40b2165441010341240c544c1000220340f41082c079000880829 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 140141663 1250 140140413 140140463
    0xb0415260c091e0f0607110607080c070806040b181e030c0c0907020c011d0a0312030b040c0207270504050724090303030b18010b030106020d02070503120304 69
    0x4035480c646544880072010b02c8044240a1203940ca0310415401e0014980e40c0c0300c503031000b1307400c2c202c1d01300780c80e24403078202551859050509681c0c0b003a00010580308002e454005001c91340005c5c01a61a11982c890009407501e0007100e0013072818018030000742420100364001d010039840c880494041080b44403840c508000c0e4940954001e500105220300510010085240400015901c44840d0f00308404082d64607511850468103015402d242c0c0c164064102082420124000b0a6400500d5403410200c4000e9140551800041c0c20721048100504250040c2180000e07207a000f01001840e0040e4007043d03840301200701883d003c011311101401702030350048600a9000380d0107881d4040c070786194103604078503d0714201d2413000b148045011186c0c115131702d0b02c01c480d05400c3c0400e80314400400a1030b6110140f594410903c040800880c80140c05000380d4181c0360184c00f1140da41c400c100c01071ba44d4203501d02c2055496480800c9000c15035021001031500140305007540e02e510508074080510030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 140142913 1250 140141663 140141671
    0x10504060209040c0306030203071a1c0f0b09060906091308070605091e0d08060f030115060327060b030102070f030804020f0d0317070912030305100b041526 69
    0x854001c19030b00031614041c0701e0401d14181c2800d042040524590110340c0711211031140d4a080c0007038951100c00040c28100703ca41600103409911400031021512070000c201c0000c96042081c501402040c80b41004003160307000e50030080c050070f03591380c0380d40801001010080039040d0000f41002030000203000b220207003510320b2241e9030120302407814120262502d0f41c8042090150111081d511000700e10200c1c0c1c14640008030710703002440b03541e0342020601408440421942540c604144000048007542c841d40075075809640521200c0b00c000000c0085028000e842d1020310b410703414902c0091481d9104020a644c003400150400241d519002c1c1c10040c142c9081c4c000c907058408200852034001e05004901c40708981d8051160344580380140700e000451041c0e0006442e4101040c2030b40c0c000d00c021f02c02844200c0c0c20000301145844c004000d05819a06940290001400410110004000d990503039459a01e200c030301048640c000c0b20306c0a40e210324048103000000d0703881c2c52180000581d03841 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 140144163 1250 140142913 140142923
    0x3040801060e0910180803060d080d02130509070207090e0703020901030b07080702031603230a020313121e0c080d0504060f03050601020712060f050f060a09020910030e0a05010504 79
    0x10614003803c1c8030b030401c141c198600c3e01c0145041c4001a04140c50b0540c091000d40240725651a55076070b0001c0f4001d8107101b45c015000e40c0020502d0350000f110740d0010060a0f108040804006641c1c1007032000001e0140c07002c1007da0031581d01442400041e43c80f484040c1c10035011034041a64079004151410400c0e001511120190020000d00d20741260656802c4501031006604e032001c1f41100c000c04c082040c400408202c0b51340302c00c0c1d494040c200d03007460b1003a07019844113946e120b08510195980d40b0110720141c0700c0d96124000203000070a1003245141d180c01403504002004035458040a000900c5c0d4121140350b0703a04404903904104028070304003100d00ea1034084d9146d0902101800e10001d02099404040c200800c0221130703607010442c40704540b103207a07091030401010f04c1c240002c0d02c40e9203210401141b40c04100150b548110070183c2c003c1500742c401d5640561030340307800c0d4180d04c1807443c0e65400100d080f003400d201d50311a0b44641202c1c41c10000340c6002501660324142074800070b48003a10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 140145413 1250 140144163 140144189
    0x1503060c08090d09150e10050d060608010312031107080c0d03050606070c03061802030a0501150b030f06010507020a080a05010b0f0f010e040b0a030b0c03041502040501081501020304080106 83
    0x524a50801d0203150800710030802041c808400d02d01c0184280d100d0302506854a0030180e00070700035802040c2d41108070000510070351206058600080864000c41110300d80c3c0c03410480d002030040d0045123002d0581383c01004844c446000d01e40141c0113020301d80c007080d010b12001c010001c0460740d07404c0500008400c03400544003880a600004095030f00c0501103034880d2008101d144c0006c0c8070070341e507281140d07404400891b41043c1807058031024035000c03c01941502a40c0f1400007004010b5020911402c1034200b01c0d8400d6484070303d01006070104603922000c002440e80410845c1d0b0246001d420384910090401c001c0c2512900d640d410001080022185a034640740440ca2600e001c0c14001101d5000383e070900c1c0381c081044002854000b100d90001c0c040d0b5600d400889450712040445806180c00000d96040d0b0f08100462a400d5441200c0036200c04c000720300500680300e000e0084400300c403c141e464004c3c40c2c0700c4600c651108403e1412450540c4000c00000800030420700400d0020500441d0110b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 140146663 1250 140145413 140145431
    0xd030c0501060605191409040204080c1e0607031b06020a050c06070e0d170c01140703050915010b0a1707090504060e0c0a0c050c13050405150402060a12150306 70
    0x50075102c05801120520900b880740410300b10b680443d144510045207080042c51243c5d140346041c0c0e12a0182464200e40000780c04110441c0002c0e030a414044155401e6940c0c0c040b4040e401c411903044031000303130f12401c20009540400d02c904441c0780022054900605c060480b80d039800102e80c4403c060f03902280c0d000c50a2180b410b400e0111641c080550304295040384c2c4250005191094021401403071894281e158181400c1c0c000e0036141c481e01040001c00120049004060395a01d0440348600040d0400b0002540b081010800303180312940c40081403a03503400d080e107241403600310b00c0e030810030800c510500f210010502d444141c01200704c1d40741c1c410400e0a050510060343c2a0750071242c110301440b018010350200c40700c1202e13102c1000c1c3c44c0c204039144003460003c0c204040c0001440c1d100840e105080b0395485142e02041c0a188074004407062104400c1740246100380844000e0350000c8140710319080c2a000b49481541990703924000100025014440080110340b5041aa54a2740d02c400130 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 140147913 1250 140146663 140146673
    0x6031807050637020d050f0705070f08070f0b030705031f0f0503070e100504020703050d02130504050901050f04031803060501030b04020405010609080303040602070303020403060212091c05030619050d030c 90
    0x1071001036080c808280300f104081006581c032501180080b041060004450414003074040944007603a90040944a941f65120400d4040d01078030701038580f040c05880d90000d11428102ca140d01141d010030003141c00d664603141c0554141c3c000905861118443d0b01883e8160307004052644050140d54506048450428084c9481c141003904000a22400102807040400e03015030b00380c0c2241e000f1580541d41e40c040d454121501e010f6001c0510b00c80c2d002107150081285401030b260301781e030025982044250364a442c090309a9170140c95611101440c0000f090200344141054080c61841100036481d069580e52828101c0340d003640195880d5021b0402d0200b146014051036004007480d2819a4000c4e0600030055120320002e00000d100c668000b880004260180e01510005c54200342c0464030b0b510548520820f0302400c80f401c00301c500412002a40d6680b0308001c240201210383d8031181165a0136080c48008507001a1402c04d9800700140022590748942c1155001842540d90185d500601c0c40c01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 140149163 1250 140147913 140147977
    0x71a0a0e010c0e011e0c0b0a050609060a060c021504080d0c0501050f04051209220b1f050a0302070501180807030206071d101205090327060318070506 66
    0x90411000e0356800120b42c1e03100c5d00150030700c030b24185821000460058285d89204181e00010301d2200180104040220203510452181009840c8190280c2e120000c100c0218441d00400e404034000c0c0c403240c005070400350307090060310001c2c180a40c90300d52180221407500003248442800036850002e44400c20000b07000d41c58111040c2c0d501e404450500d65146616443c50901c0e10090303840102d4004440e41c0d179010040b40003d081803800071f140c840b2040d9072010340001801d4a000705c1c0301c0d0540c800750b405180801e40c400181c03940c501c4e00349200c86d6800c8020f541300d090300396403541d220240c0820750080c1c808010801071040d201e00f80d03034401d60702d4040e062a4005089900b0b000f85100100c19032207610b406429440412151000c0b0840080c80c140d07030400e00d40103105015450f02080019152000009000b10715030180c03420003100395103000050201d40c100c0215044401803022521034a100c1200c4185000e8901c15580141d80350b801040f0036404c031080f524180a11108404014099106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 140150413 1250 140149163 140149181
    0x120f020915030402030d110a020901030309050913050303070e03030705030d02071703100b07050307050708071e050a060f05040b0d020306040506042003070903080f040807080f0a08071a0a0e01 84
    0x78207400c62509800003920b41c800340f8058410700165248014102c4002c0c0302d266400307507000300a08a196102d00f0300034144102c034010340d4054410280030580c600200650039800d03e41c0b00d4000e43c510380c0c50f01d1040303c40c11411840c482d0141b1050080d2070018509001502600d85001401078413a0f0041c181600c0022101c00c200d00c10604c00c1081c048929203071004d000568003051480c0e555020185031051851081200c00b410720300a48002080c0b50502240d55400c07981030342c00d00d2008403012160f4243c81c03030952060507400900254204106406840010b044004a04005061594924100c80a40c0c0841c0e07558035450390000030062030349054801c898000500350303400c01418001842a1528084104150b8023942010002440c01c500c00e030440d0000d10b9003d01050f0b1030306030312044505580c010f07020754803c80c040c101010498000000b03800c4c4403804004005c00510b0036585550b14103030701045054034600f084c5501c64902c0700070101440e028212003100015480b040ea201a400c6810703400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 140151663 1250 140150413 140150449
    0x90f0f05070906050a03023006010206060f030c1512010902040503070603050f0a050c0f0f0304150903020304150e0909030d11091e12010507020607030b010e0d0b0601120f0209 77
    0x72400d03c076055000c0c0c00d440c0410b010b03082c01030351624080c2d401c1019090786408480c029514800301044207031b0355039106000d075600781c080300c0d603036260f0344100500c80c0c1d402130b40c5540607842080003292510f803110001003072403011400703503103040208840c0382e0f03d0740b400360028840250006000c000500303041201c0d100030502c500d010071190074920300c13001400901500078081c054488001c26280d040c05002c58000341c4002800640d0340ca003071147c21a19810844041d90384949039224140c0e0040302d409104e1405d80c0c15406503140c14100040b005500c114581420104910040820320603141c15201600400006009546801072090004142c0322240e102001002060100c1e4416858044c04003880000c2c0040c05120620f8a001065080c3c1d004403c2d03081640c21b210030b000c911900414054002c101d19a4140094a030400c01074405180348115150001900c00b090804204100f500a0b00071005140640141042e0070b00b0700213a45007400380007034481c4e00103031060591a140d403010007550210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 140152913 1250 140151663 140151677
    0x30806010810060f020c100903030905060703050702011206080601032a050a090b01020f03070c030b10050d020f03010e071806140f04090c1d1603020c0a02010f09090f0f0507 76
    0x85150082004150310030501070040b095130120b1441e00038050140d042e031019144101e14030300032030b00a008100c2032106078081a680400421036083c040e04542c54141c05450700740c60700983e44e004484200301d840040d04107a9440304049100003092020380d00850164403808400c41200c00031044200070f28100780c4900c4810002003203a602c03810516405c5483c01c0c48005141051000142e08000d05d003003c030600741c00700080803810031840709400780079640903401142107a42c500841c0341f010324060013030395840365946200d40c0040c6803c03404001c244402a00224216189200241c542005504403070030034440b0042d0800a92580e105030801443d008001034107041c1c00901003010903c0c01ea0380c66000b1502d40f03202c0c4040c804103d820b6030043c00d103020a1074445c40100400303a0301001c00d882e42c000c004d0101002290b85072182c02030310036040c80d1001400c0a13507031550064440041203010142400765510002901d50300511681900400003103012404940f890240000c0b1100140b81c48244148 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 140154163 1250 140152913 140152921
    0xf0305040201170601050c161d0c0d02070c05060a020c01020c01020a08090409050f070f21030e040f0609020d02071407030b1f15050702040506060306100305060f03010c09030308060108 81
    0x48280300c1124000003c40620250700c031000103c4e11031183e205020f40790301c100b10b15071681d1fa9464140401300e450340903a00c107a48140e4410b0f481c02c00c0058482100611081c00a0f444e40a216401000028820f4200712441d80e6500c2c00318641d80c0254628001582001080d44865601409481404c0700c091010b04041071642d0b0f19007419000d04150103010340e41d65420241008000c00c2140d1940c500f070b0b400c6410301c17079580c00204174150071400703111040c0c00240c02e542c41410004403151100e90345501c8940c0040b03080c0f01480002c041600c0c2d17030b403000c54503501c0000b100d90140c0b0050225003030aa5002d03a0b1344055040c402001002d070b003818070442c3e01500c000c0003c610710480c05038201815802c0003058000f05807028002400075005403a210b03c4030101c06141c1e507001070050081074400c0d141440703a80e0b6140100a180c1c00121443d80c4c102111040094845100343d00059002100406028001e01c240010070700311518601d0301c50108010701014414981c12205840d0311074824a460000d07450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 140155413 1250 140154163 140154167
    0x405010e0702101d06090a060f1401090209040b040f060305070f03030804020108070212040b0417070305120c2107051216060c110a0803010510030204030f02010810090c020d0f0305040201 82
    0xc0340c1080d07480401d13038a0301c9031503096005a00440d07112100b40f04a60481c282960006d442c2e040c2075800326042460b000009014603030a0045100074110302401d65001d030328040c07011019600000d4815400b6940700c1140da50341c1c0e2503125007d0f508528540010303085007076181042c5000141d804c4400321510300300c010400254090f0b10668006d5080c43d011019449410050f0b2510f081014441000038002c1404541d287e00135015200721220050b801e4003450020481c2c50300c4102500014101d07400c40285081c00c09405001003052008903422120341c0350000031050951418cc3c016801060400240d078801d0141c1000b002821070b58200c03541c0e140107405041d2140103402c00c100100300540b20302c0b0407840240a000f40d010603019900c00d55240c412a0300e0580410350090290500c2071103c44001c1e501144203100342d9094a43c4000e110603015815001510302c050002e00704a0321114980d004181007002d4001c809622000c0d400030032503288901800f81840401803012020549000100000f507a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 140156663 1250 140155413 140155423
    0x40506030c070c03060507050a120c080c03072714060a08040615090207031e2f0c0d0302010506090f0f040b0702101a0a05030601181e06080c0405010e0702 68
    0x5800c6aa0b200018a003408620115a1002e02010715240805c070070181c004005040001c0b1581d47e18601d00310400c082e00489010baa002d20000d041000000c0c802c0e0110b80003943c01119a00f010b9500d40204c0c0c40b02c2004400c41c0b10b12020908030807408203c080404034450b4130002044070722508060051000030a41c000081c00684800c1d1541c60050141203c003240801a0025940c1555582c07050304000e803594100030400c2030310040664074090050300c200c41180110200c40500d40d841039800000d0305550b41240d508161a0044000110103541d440c2d05009499110f90000b02e5035180480403c440d1100c01402d4070303022045001081030804041ca00e113030f032181d8420352401440d1541182249040c0401c03001310b846030700c0c002c122085824070890000b030400044032406911600c50081c5520b5840038803a8235420094418603002c1d541c081e8011030154207001c49a0034600d41a03001d682c05071015644036620755000624103006d17a003801d00030a40980001030500e5040d007404d01e4025518 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 140157913 1250 140156663 140156671
    0x503030f0d060f06030b090703020c15060f06030f040309080a111215011403010605040c0203120714030a021b010b0618040f0507090602190506012105120309010605010504050603 78
    0x46400980d0700900304041e07002c1c8010b8403d580c0d581840a0b11102c0244c010010811650b100f95241030000344400c0c400d0088a030b4007a1540050585040c540740c8004015002824142d84812691403d040603260301018602c5000b00b00000449404c00d818003402114054000c0b01d07054000081c4a004510a0251800300d0792043e25540314034080700d43c01c2401c01804604140e40c1040305800002c0d10045040100400d001c201d000304001950b440401c801c070303010038002c100960024801c26034040c01e201d01c1d00d039001d1000d081c100c24800304501c000400f0350003125200941c55022481c011400d00c10b117206a100c3c41c2120007045000302d002c00040e0a0b0044443e40c0b0300001000c441c560300740e15281c100100b40341c2c0300e001c14400c40c10729402c080d1654000b801040014415580c800c60441001c04441802c41d80080190101d0b13400c0400d201c00158140302c00c00c0c42c5200c0051800000303801002084991204d103041d040e103d09240649600f580c88e150f00031810090103020900c419550381040303a0304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 140159163 1250 140157913 140157937
    0xc0503060a2301050d0b040624030203010e0a0b0105070501090b010e0601020a05060f0a0902040612260a0f140d0b01020607020a0309050613051203041806030506070809010b0423010807050303 84
    0x26808a1905c0f9400740403040545078005040c014009490300d404090841c1c0c45000d90080341101407141d404408a000c244650300c07010701000c2c082000c0e54120303849020304600601d06185403d415480704d509481903004215908051000104600c014410045802031001d10140069100c0d50710f0309a9030b02006010b175022800c800d008111071058650018042e40c0d409001840001c2e42d840b010000b0300e184510566201e00f402a1328200166031088051904001080c8681807207040c40e07040b10840b540c44140010f0040085045580d00100e5015010401045002040440600f000203042940140c0362f20306650040003224002900003c0660030341d00705441c0552580c0c181d42c9030008588d034603840075400584100c03500c030540c2c00110085c015101c0f070b072401800c0f40c0038500c01c020407100300d440098159007206000c12001807240d02a1900442c0c407200114203240e1600c0010201e80541060300320804020701c20b01090aaa08001e80c010700d034000180404914110200e43c07640300f03035404401d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 140160413 1250 140159163 140159167
    0x60309100c0905030a050a05010507030b030706080705070b01080a060609021c0b0d0f050601091107030905010c03090302090106050408061521030408060a020a300905030903010c0503060a230105 85
    0x1049403080005500070f080003001c5604007040350410581303034410220300340e699500741400243e0b01c0c0c0c020701032803281c29000750043c449036107030807002c481e00c000160060b01080810030800011980d4021007501030403940b030190827201c1440c40c0c1401110b605501015815006100503002c011104070034500c0c02035040008901c0f0010384000410f0402c4e0078070700624482004c002181441400240d0605951031882c0130441424500c084002c24080d11000500240c070507142070099512559545241d0b6110342084540507840f9800140c03080f500340c21a0000820214003082811000c0080541005a0781400c2050721800340c041002a0300c0350801c0f0402003443c040c40c103c800000c0084400074005101074039064104030310544041c1d44510503203030015186880000d034008d040c4401c0811119400024544020364040020142c1700100e41940c3c0c902040c82401c809480038024000900107c0c1d0380c466172440c083d403c00120b0a200d0f0080740a101021020302d0b00e04800011140341e060090078026 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 140161663 1250 140160413 140160431
    0xb150409150e070306050307080a080a0509010309020406080c04060b04081b060f07052409152e091401030b040b2706040606060509090c07050c101d06030910 69
    0x1d0040325503540180d4401d9800020800c2007981640a8400d0398021400e8407107655884500f0b13591041880d00241c04075108100300e00c01c0c1030060008000f10380d010f05010401d6400c80e000541258001d5028041d1038001003c0900203241500c00c010244c010005020b05050900c2c1c8c946070754241072514204c14105040c10f5107400ea5030001a14181c50140e040d169440e1103030708d00141c580e620320318802c1140d03506014425007809850189071140552900500d1001480385140245140251a2145440c550354204581c07038820203891381c03400018982c0a0206141c03984c1481110742e80950443d11404130f1005100217217008a510b0382080c0c200700f01c1041038480351412240f84e66602400701d00d1000100c840c080c01d40c0003082140c0318a002e0710003000b0740da6a918007500e041c442d04841a5002c0c0c0303580b000a4424100c040581030403802141110342030381b00d91000c500307402490f0103010007050124201400c08140c4241102c1850010303950303542076003440b0f44469900e00d1030716145054203440314508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 140162913 1250 140161663 140161691
    0x129030703091403090310020a05031b04080a03020102131a03040803040206090405090d0f020c0f0603040503040b030c0403050d0203160b0603010e1009020117010501020a0209071806120b150409 85
    0x5142e01c83e080728102e4903400d80c1d84203440e0703203a10511002d0700070f01810040d000e002d80d192080d0752060445480d1f051031039580c208054002d4104001426014805103c0416000000c102615405129800050b51450003004904102450391700c4000030002c2080010760313079409801500d401c1035020001c40c3e2252143e1000800900511108941281c0741c0300c1000020b0a002070303400c02d01b0b10181c50790548801410000c0340c492030003002c1c90f6004144415480b01904109000f10b03130150145013902d09140d00d40c00c0101007503006403042c40416401140c1403091210900c4840c40c8038205000070741c501804903c9042001c25403160203892703000040005086910290001c14100f030b0391a080d03619021940401d00e0042400800590006130702030f0801500112168585050318816001400185500e901704101e08000810030401c04c030307000901500600c481240a0060001c903103c014100100400090440e1a0400c0e111700c124580000e0214104079a01100c094440309031022540301a01141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 140164163 1250 140162913 140162921
    0xf040c03083015040b0303041505090d210305040b070f0c0b240f0a0e090319090509090d0c060209061e0c06060d12030507110a03170129030703 63
    0x1424500002d5035001d204032005054818881d840c0010b444040c1500d18040c4411158820302103605980104024008280014144e03801c000640c43d1882c0742103140303400700e18000048481250b8002c60081c0c0301941860b8420200070901c507038641046186402d84400110f0400070f8148014003045010110800d41304040380086607401400c14a00d900700b5055541c1038a852010556868407615841141841d00540c0710f004890001c2140400b9130070f0000c03040401030003400381d925912041003105541414152100024080b80d2034940080d0318100c2802500030005080d1411070700400b210100254002c44c0b8000c1403034000030010303202e40042000c241640b040c51812800c0d9036070035046400300c5805400501000c01d03ca4199a010340351081841501c00f81c3c50801880d07651040c00c1d030300c52a4880e030700181c2d01c20721901e001041080e101c0036240c20640113003003e6000a2200d45109000c096000700c050040c0001484000e004032070700e16504d0105248160000151400004982c0301446600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 140165413 1250 140164163 140164207
    0x50402060904090506010f0f0e0c13080f0f01180f03080601031d0c1507020d0f02040605121b0a080c01030f020c060c040f0602150a0213030b130204050f040c0308 71
    0x1000f0095805141401542c03800240f14907444168491000720760f000070140c1c07000841e20356141341c101c40d84650840b0320356a00070100078051604001e00001c1c0314802008100b2000382c0c0c5d04050664554010710741800d5800415507000f0640300f20062900242201070f5004042c1c0c1c0518201c0007603103821004801030541420798028024510804458110000c0307010b0620710811240c607080c1e48810802c80140c1d0250f664080e42c400d0890302c0340e0740800c660344a00040f5510040000642c56110300006940c50707010b82188229901c0000c0c60400510b01c1810410036800850721994038038a0264000ea55514101042d410141c658072203018154a0741c041e14a100c160109a540914100b20749018de90010711604a00a03081000004c0b030301e0000c03d503401114000c9088910b943d81b0010048040d60082e05480a1000c00700c00000225049540c0c09000708440d444160b01805140100001e494018001080f032804183c14072000841304241c4a0440f03500c099580d84405003d200032200000500d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 140166663 1250 140165413 140165419
    0x40e0c03010c032703090e090a080301060305010e060d080a030902040204032a0e0106020705120a0f0818040b0f120a1406040309060507050d11071d090d0807080402040504020609 78
    0x8810307402001e4164021080792119001404505281044c00300ea201061078000f50114150110512560040c1c0036000d901c415204215070046d21155a15406030340241d0107000000d07502d8005015200d2140101030b00200c08a403042c1e8001d043d6207403000e542c41041840000e1681d11107a200440d11940c06413002140c00244e07443e030b1404424200781030420001c1036020048090707074000c188029105a114140c0306c442d8000c0072982e040405010089c8071586503d02e081c400e01c0c0741031001a100090000089204610013a210490b5900ca10001859203490034810f43c10508000a0b984407090079948007001114841c0ba00c0b40e20702c4040d030400d44041c4011b0514946d65412800e0500c00180590042d0303c256900c06145941c1c1804489078041c3e41d1008256800c91100d2004891180102c1d80103032030000199111555034a151107488200501034640c0c10728002d0820620300800d20120b21880114107140d110f40ca00028000c0c0340c2e00004100070b20a982d140c0c00301c5d040d174840c82c0c03e9030703400107000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 140167913 1250 140166663 140166671
    0x60703021f111206090601021504080a030e01020a090311010201140a0b060c0609010506030723120102130929150f0f07150e120f0d02220f091505040e0c0301 69
    0x5680c1c1c00c00c0307203c822100781e4052800f580200d1101d5100054004210342c01649075421a15a541c5805042d44500032250030140c9842c003448250000b80f0040950f8601526802c0740316180d842c0840400c19042c40c0a415645440411110104642080c075841003660794002038444541000455a010b01c080e148503d208100c2002406d240542c2f2030382c0203803401c1701204e10b42a074450346501c0c01c1e582036411701010810f0036403110309410100700202c00045900000f60500040000c41105452680d001820f40341d2115884076010000c030340010b03c046202c020307840303002980d500440d2041c1c1e40c03080300e00350280000072885240301306da0382a100c3c103d4294104c0360f901c59060426441180c0c1a560b0300c40100c3c030317000900049000c0001c5036024242c950801cbc0703080c600d030008000d00ba034200d0008441d0032502048651420410403101019482d404207035075209506111028090b010070350080f03082103282152105402c070511008200b120000c440228485881764134860902e41509150b982641c28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 140169163 1250 140167913 140167927
    0x6141614031804110702040506011e0207031a0c0712030b030102121e01031e050c060d1d01050903090f010e19080120040e0c1605150105060703021f11 66
    0x1011000b0110700c66018100c81e8400e02000c02c12048500c803206041090030100840d100500b084d40026500650504000640c079415150028410f801c4600040040c0c002c508244104100115101d1080c0a860840f100390b14200642849030320840d940607040000c0702c40a800b040303100b40c002d54505e0b00080c0080d0340320811003c5514102c901910344108040f0b089402c00344525030011014102d0760030988046c09088007151084048a100310142c0305800354001c410004e03102d2500402c1c5c075035800c0f08001140e1442c1d0a0000c0d90651100030394541e0b13410201031100340300001013954541c802c00c59040c0071803442400103a500b100801c0c2115002030305541480740e0740c0c4061003241c04940c21a4000d20180c102c046000031002e5104041c0303618141d05000c04e00c03180d840e2050030790784912141c1c255460b00007028803081c1d801090100888042d8081101041990a02c0e0405801030a0544a050a1410b02d55010791034191114a0305981450b403003011203060400d4000741000640403052517503400c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 140170413 1250 140169163 140169203
    0xe0d05070f1b030503181503060102150603010e0a0818010903150f0b1c02010318231906020c011409150601091503140708010806040b13080a02010b030601060504061416 74
    0x2c1e00e507e204501000c100e05160120b40c0441744036050503805850400568000e52007100b0010300b400381c142d965050205c1c400c03001001030700040f038098441d850300c98000740d52041c8000e0740c1030529410400e80c071b081000000c82904844a00c401d4142021683ca0500c07040c00c40204888540194042280c228100e03401d04403401201515000ba43c0a100280c0000d805002c201000c00c4002c0003107503061071002a21005600c0c00914284030010340f0f0121000048183e00410070000c10340700705a0014950405240c00d109400501000d05da003540c0394600981c51545072a000180c180d015a011400100c20b80e10466555024003a65002e031001e00302c01c1d11004000b8018442110141303103030000480c03811402a007110341221007010040042d43c0d1150fa0307089101c00090003600c85001c0304031840000604460160503036400350b900000756034a810080515110042c2d210b60280b110800c02804000d0b404420008010400340700e1276501c200f03141e28110851000d00c2c3c003402c914111000c4440c100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 140171663 1250 140170413 140170447
    0x118230402011101050106020a0f0203071208040e0a0902011d040b030d02010c020c030a0c03120e040203040602070201080a090803060f030307080301030c0e1f15031404060e0d05070f1b030503 84
    0x29000b0f0762010400c03003804299070b00304c60081c020322015911146524000401d071103541e900e40c40c030140640f0b544954903502040b0004e4140c0044070100c4001c5003d0016464403225642d0101400005110099168002070b0002d2140310748145610940500420382d83c03915008241610400390440c1d01025882e01300031300a01c040410b1000500843c01100c80c0e510b8002a18940c03550043c0120362180c0c03541d079a046405d0348000e1240103200413240e4542099450740b02544c130603801824090390b19403092000412482c0028528420310f0f103410300740004035104100343e1ba80b001c03041c0c5800301e4140c070f8180020b03c2c1d4040d0031002025060f0010000c8208048030050004449820000351525103e0001050126443d14480001c034001440c0800c40960047c4426910240d1410002440c0030f07080392800074004100c6003503440a440d440300003a503d104000c0c0494181a030f03c0e101c0d0800c2803a03602d548100800350406401070320f020240c030000510301c00182000391390000490765035a810b900200425 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 140172913 1250 140171663 140171671
    0x6020c030d020705090106050a09080d09150c150507110a05010b10080903070602090f031c0807030605030c090a11040806070807030203010605220801020d0b1e0108011823 75
    0xa000d5041c03a18810340c0001441d0050707420081908a0aa0174214102d480d508051107031001c210f1210383c0041c48c2c000521010982804a80d507585005080001c0d01803000800c0070756400b001003104012002c10308103145149040208a0041042d45844d442102c20310f6156205a006008a4254004200341540002e10810040e20b0803076054908442c2603844a000311103600554008101c090001380c00750b8010310f507004004044000e10f40140c00405c0ca000b00900114480300c2d503244c40c0c000320541104805603c0701061400780116818030340800e032142c44800d0500d004031180d8000c04e00c014410b4000310300085080088a448a0303070f9100485e9613180070b070340c80c0c00416004400b1502045c842d0003124142d460588070f86181c82c80100310540c0040b8600c4903884129141800814440d0081c00146070340c0180354030100d1a00d26000400c08404845401614420450340c00d40007541d03046040c56044810000e018a60380b1080b40790301020300b0740d00b0701100c1c00380c07010300140e0800f8401005040c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 140174163 1250 140172913 140172919
    0x60b1804050105040509030315010215070807090506041a0304110603090604030305070c0b220507080309030c030109020d03080c04030f0606061e09150504030b0a1d0307020a052806020c 81
    0x110b980c0e0f002030108541d010b8580404540041001800210a154020f05410810300c102c2d45503445030310030105420310a9486200081503101840245c680c05181000940360442d46246041d2414800e590080e0b021140c0300080c450100008084c041404040c01c00b80c08d0240940b079680c90b1440300c054440301c0c102c3c0e084011070f25103c0440c6449201d1034107120015440840701003192610aa091640401c4c09100c18500f411310000300b000800034003642c030040c03118200842d02d03014080101f504110382d05180d1130003613142031070080140e40d546143c1500306805040074125512482d011208600c07858101500703e00d084e0940318100071443d030110040301c0040c0e548051001028000203242c3c0c0f030441c119000039041020500c403d4005d103010307000e010032505040b071520303a883d40c845040e1078003219205401c0b0b6807110001901c1d418402c07007011041d83d0380c1c042c40c50410f140e800110120038500445000e20401c1000d034900080807010314545c1400c5035190001c459649000030369400ca002032840c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 140175413 1250 140174163 140174171
    0x2040f1e090305251a10090f020d11040920070b0c07050109050d14090f01050d090b0109140105030a03020601060c0606030b160e1c02060703021c0207030c0f05060307030b04060b1804 80
    0x5140c10300710b041180034940450303090a005103840258006080c0c0480b40d15082ca03800c020b445c102b442541304000b03603100b13081042c640301e80c0740000c50b100306c6120308002c09400d405042208007803800001242c0b94150f008a0340c0f1003a444080701c40d201e60050420017805517203070007004818800f001030340d017405803040d944e0010b0300e03054507040203024010054071942280448200c0505c56018a015142c000302c030305800950440103403600b5000d070a0a03400449200d0751090700c2500800002d03070076805000300b500207107500012075030700a41d01c00d81446a18100064032022030100407042d000b680c019a04103480a0050034990104414800c5600a80002c2401c0300540c030303924240405c00150115030f0210350b200d0000e51740c090018a0348200803c84c11801405050a800c0c268645c0410003602598004c0c80000d041d80b8110042c4022074000542c43d11001408000d6a07842000700c036407011072440c020590a00007400303d0050515504160011038001c504050060701c81044041c40d43e208803004e00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 140176663 1250 140175413 140175443
    0x12080103050c22092d12050901020637020c0c011103070f020402040b16050c0603040215070f050106080d03060e270a05010204060c02040f1e09030525 66
    0x88402c0600010401001e22079074141401840da10152000d40a080c00018100502c0400c40c3d201081c0d00c0010045007903403245c0014002040c0c5940502c40c07040c10424900304d54400081e5076000700a09011891014164403880c4a0303206503002d990090a0001c282c1201200b0303a204003a4119000180f401e02c030b04020311100798843c0d081d0072100c5920301c010b5480d0041603200c024885c3c100ca1420380e04944c0070040021360b143c40c0304c010140849071034000e0100b0304140c40d103a07003095102a282c2d881010140b0034800903a9030071443e00e512184030b42c911603032030086103008040700c4030b45c18001d001c2c1d51800320001504807000c80e6043c0081241c1e40c0420a0720340340d030000c1d240c0a00603140d0516914200000002d110480301c802c080c1548600110b4424911f155159400c1e030b03219410441c001000c1707a40030303c1181800e01400301c103104464014041a075003c4140c040041001d80003e00d42900c8072003080078140a90100e50030394900c00814900307201c22100700c0d907030700c1031840d4200c4054103600205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 140177913 1250 140176663 140176669
    0x7021c11030307121d01050417011b030b270610020c04061e0f081203060315010b0409051311090c0c0a050f062505090f101d010903051005040c0312080103050c 70
    0xa192402c2d17050716982d0a00e42401203080300f00c441100704014a40d643c0322812060070890700c00386c0c010b01450741c1c0810500750300d806010000100f005600c161300030a2040c0010112401c41081d4450020b44002103801e8500303004a00d400d01840859070064907114010403214a0048802098807a5800550100e60b46007060345102034240304007006ca4009148a2031f460014200950f0009001070449480140302903030a101202c00303174094001208002010480040c0c03d01402d54429142c03491000000d045460701c800628490720300c0b80c82a00c10a0000f0700e001d5041003660008a013141c2110320704031140c64501d031f454495444c0c0c800c06114640004060150340714002004180140d61081103401401d816111600014402a4048060741c41c4100365258602c180303942c102c1c290740364281f08007580d40c1940c20103821201c150401952034014800f041c1c00044c1c00031084911100080c456940d82800708104000360402000d0a4620020381c254a601980d002d042c1c034000e40c16107040740400020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 140179163 1250 140177913 140177957
    0x6100c0302061b04030c08010506150f161e05151305151306180c060315030213060f0e0709090501062f0f0106030c080307021c1103030712 61
    0x10040040e0701800000e440b107180030651149030851415001e0030645c40e42d0700c1803611307003941d0401e0025030364607000c101c501d240500307010710840e03100c0303420a18100808569070540c1c400c1c034184030b2111465580c401c0402a110382c0c20551241c0000b0f019100701e10b20315241e61100d000c07004c00d61404911001103400d24114002c14080680d00100411340040301030019541c242d80204085405144046010082140c40c0962022620441ca940070804418034008500341040c0e0002c9040500c1d00806054100321440d820040e40d8040b54840c0106c022112948081c1c00d4030741000d80c840d6030042002658000039030110f405100c094a80390712090311070381002c040324800d1190400191412540c1d50440c4411072800700030a20300440c2c0750a1788a41c6004030318140c003c0f515654140e5603001d040042c0301082241101408072140914908020f0340c00042c544803007400fa8084103440c400d00d103000c002c0020604000c040003e8260b9440780e401e800c2990440c80601a8140402d44e8a00601d595100c1d030b40e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 140180413 1250 140179163 140179187
    0x50901032004120f020301051521030f0705010213030507030b0c0909061003020c070303020c1002150402040c0c060f0209090601110a14160f0812250c050402120610 72
    0x280d01d030304061074050140c0e550792595070261440d019004180c1c0251710207000c0c0300d110f02340b03101c0a0000e88003000244480c01000084a2a425204c02c1700c01700c1440000c000c4991694030700c801da6442d00c09a0a18138024404d100400303d0b01d41ca42000003041250102e0542e013264010800c040042c1c0c2e03240c00da501e20b8801c200b5095031010160000030703414a00f82d039601003131590300e123401400c02c4c008104813450104650400c2d4007507884418001428a40880c40300e40d5440544050001d0381009403000c62030b400090b100904c100d860301c400525040c4141c2d5208545034101e1001e101d5004c150204200035804900c01c01c0c0622000c000040980d4040c5502c03805c01d00240d0000c00c4040c4040e02c8000b070900980c5070b10b01c1140210034036002c6852250344106c000e08091031041d8812403800c2542440c041407801c0800d800c070410f0010120208051025880b244a00c84200d80031941501d404002101e054000a6001c7c0c80842d400c10300800034180b107031280c081516030510421804100380c86101c1c40070303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 140181663 1250 140180413 140180471
    0xa060501051612140310030b0a1415030a120c060f0903020c1e0a03140d14040b0d110c0d080c03011a090f040207030807080c0306130b030f0d05090103 66
    0xa4165400a030b07680d103040c4448580c13854000780030340d54075210b100c1c036030310680781c1e0010a04600c130180305002d6001550768215502e8441003000310301142c2c600d080c0d40d10040c5100c5500c08510794481c02070b01c040c450b82d000e442c0d006845180b0018075410117031001110040a5440d02e1034140001e05d202030f113200d03a40d41c05405400a0a001c0448400c21001c2c44011200701920a040312611200362100d140060145208405040c29041c3e40c0840e580340c002e0080c0c0d200104110000004c0703e03041e000c0b0858094442c0c10fa001075035445001c2c0c1640c064a011040003a60000006011a0142004c140409085059a20046070b42c4848010f1302d100e010038003a060131341c0100d441064092101c41c004006106020f0010460700d0b855000143c00c03070f00011001e6000c11000004c01c0701065000f04c55540c0868440c0019040d400d140022481040f54400c840507126501d680d001e00300e641c10407004511140039011641242d01c4610000c0c442d40141d0070352070200f07043c0340202c5800054134400d015500605 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 140182913 1250 140181663 140181697
    0x1b08011a0a0e0d03090306050c07142107060e06010e0a0c02010c0503070f0905030106060905120307050a030302161515050102030301230d080301120b011e061d0d0b0a06050105 77
    0x440400050f81d803100790880601011036400000608540940d0b8419000a0f81240e241d01080c04d010300c5059040c40703d0101d94001d989840c4d90300d00501d5900c1841c0085030003071521041d161800c48010486400400c285124110000502c5140304804901c03922880000b4401c20041d01c0041e800d944000d804030020400610005484510401540c4261310603450034075140d540c4c52000c642100c0864018400003901c0a00500c040d061400c8212010200340c4c000390300d00310480c0c45054580c030f20031900800309a00018403c000000d082071002c00260080c034460013600c41d008004005114055400a1000780c0c90b200003215800402601c1c12034100e050b800c030703114039441150818003144600c0903502c00741480c01c441c0400d99500246028190f0007103a08004502d07820f0080e40d100b0140c4c0001e200030205690100c401e44859084411a511420309105981825000600c40d00034500c240b03400004012450050007101c1c01c06a020340418042040b116841d2401181d0500c84c240d150144c624607 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 140184163 1250 140182913 140182937
    0x3011409040b0f100306020c0a020f06030c03060d0c080d0f02010b01090503060c0304080f0403080901030501051c11030f0307030215150307060f02070b070305031006030b0d0305030a1b08011a0a 85
    0x1902e100709500002840395088003d46955440042360480020425a40d0080c2c50b00021070401003441b001c0e04400708e03030060951802c0b8805107042e01c0001c2013180101c2c1c0c0390840408100b40d0304cc801d006000c8a01c156442c4100b4040001d0110122031075490040d8204608c00c9825406602d44000f62003015000e046a0382d502e6030b4110103584083c1c411a800101046034403052988040540f0185208038440740d035402100000400303035681078000b2441402010504801c0c0d071091001c000c0c0f1207030b20200100448a02d54002420003082d120710b28032a010024a010400d580441c0350041103c000300e0100303458813001c0b004800410703401911780e011f900010003807040500840402280441c148100d40c4155150100a030058000c03600c220003007900402409070713120b03034001c001c40604160f01e4108008c4d64403c0c002182c4003111a005818084000007250030301e481c0da0400f080125459500c00301401d0710740d60041141109103d6105442c994840c40341c0c0e566084421610500e6140d5151680000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 140185413 1250 140184163 140184181
    0x5010506120405100c08040302060a11030402130e0102031e0a0507022508030a030f1b050a050f0d05011508130c0501030b0105090a08030306010e120703080912030d0203011409040b 79
    0x80c042c1090380c03984148032164000c0d4039940100300080c03e459a508160707003401d250292a014010f481105540d01304480b548060381901c2c140ea0303010350103c640c812010502c0413048010543c400c0800110b500010410048941d5060355800c01c08000010100550b1500c4840b0112501620100d00581007446071008510141164448142100705004107080e82c4140c640d03c0e55100c0040c003400309454482c1600002214454071003242c40c400f1100b8440c10485400500a109083d10002400f401041d0800802d44800607030344000341c55038003084156151541494028030b50340e011800901204009204141e21041030a22682d00a131285002c9007082c1c0150040e00000d084941041400e02a1845540d20b40003050700500c0c01101070f613564140f100c00105520301090304140200c00c029280c3c400700400003440400c50381c10080254880c401c2d88001b030659804d0340300060a0344804203c210301740800354011812602002c04600d072410300311041c07100d810170031200907081d201c100e030003c0ca20306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 140186663 1250 140185413 140185447
    0xf04050d0c080105280902150c01060801050a14091203011a070602030a0603060b06090a0e070203070f03180f0308090d110303070b04110102010204030b0112022b060f05010506 77
    0x162060703a04400954440040c0d80c02c6860413140120415140c5440c8180c070300d8245070f2039400348400d00c4240615003141e00859420003a202e89000300040004004c42104c1085d840307a80a0a9600002d010302c1c1004841c85025002c400c0740c1125040600c800310f44d140b10001022603024580011443c01c0d41e1910b000344a9400c0040e91000d0070000422900c00050060b100452080d0460000007803540d0650810204546c03215081d20b010f180f0410030200d05039240d820000859805542280f50340da81c0c004124114007541000502d141420b501c200205a0041e012900c1061900d001e0000c0c15a1182000c045841c0b03848040d145a10410480000f0b007050003400c042d40b80a1480d14500c0d034140c2c0007007071555110490a451107203841003400700708080b91001005181c824402941464290b0b181d090b8000f070103104e10342106804580007003c540b112401042c82001e800b0410701c1d110f501d40b82e4003407900080807040328854a019100d1601030018841c00f4181c0300064a0a070030104600540c032150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 140187913 1250 140186663 140186689
    0x8030a140d0209040207080c12031306050a090c0f150f05040320090c1b0c01051b0c131a010f090501030b04200403021801060c11120f030418020f0405 66
    0x81e5800300300c2120f50340c0341d500040c41864030402141c0d560b40000b904c220b00300250020880c80e0f1f10010014840000c003d040901100ca400404c00511600d501d0210402442c000000422007208803200003190094484040229400c400c12041c0c206842c090850740325200c0e10880c80892010f00c824004a10300b4074840c1302e4036110240c451a80400c0d00b0001d41a00411940310680320310005194031040c0949125455100ca040003c090340300e0002c1c00a081402007030038424840c444120f00581d0010100500940c42c840601a0109081c0d407000c110003501041810030311101c014107501030294070952160050b0580c95481007011410701004401401d10034001e140c0c01515030104811400c04050450301c01c1940d080b205c2ea840785075105003c22500084034820240c103240004000594000c0c0c00304840e9a030040d0086942c5210200003045080c00d10581c203aa886800b0b003115609600000400549406090b003150090105160304142c0c0303c0c1210761841d280051008208a080014403040d032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 140189163 1250 140187913 140187937
    0x90b16030e1e0d021209220c02070317120406020a1206090207030f05030112080a14070c06020c1203040905070201061a0a03060504060b090108040203010608010c080103060608030a14 80
    0x81c41045601d0705140040d00305214004004601c1d440c00014402c11a50001e9803450010b00b24180030320010900e41e004044080d0301a0b44c4481101440b580580004171030090030380030801a080c0d8441d00207644034190f00080707030050420b015070718035002448140c40780700c00c0708061310040d5a920743d612030194200c480302d00c050002d02c10140d80c40410780c1c0100c2c0c0140075208401a2038460900f0020003100d00300d4549000d0020400050090310044807800010a07081403090350383c0c80080d40210b580c1c403032241c0c42520b03040010400c1401c00a24a800750100d4049a080b54580d10100041085403800c072000d0f0b00641c1d00c10841048107004603080103a1040f001c0c000002d040c0d03554001040c803034011101c4000124000100c1140340d40c0c0510404002c0c01c400e80c2d0800c0070900f01240c1482c0c0f4030035170f50180c2c1400b85840015045640941103407010b001c51400a1181c98a41003019042034801e02003112224141000840c46042c00402d4540d00700c200d650703a240c8000c1c41100c5000651104012100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 140190413 1250 140189163 140189171
    0x110d021c0c050a0e09070e0403120b0604050603090d0909021306111006080d0f02010204050a0b0d06151d06071110180e16110303180307020904050102031603090b1603 73
    0x1a541d8520000c000240301300140c4141c0d602c1c02500060400b2115040410900a01004d203c04254088030700f07042c1440741c840008040c25450002800341c040d99000f00d40c04000001013010081001c19120481c24160312800340300c1d900c2d00340c810203078000c9011820003040041c000300b0007284229030b0003d51006840035160009001801c040565695800945c026800001d15000709584245100344111240c40210304180c100780000380c008004d4410b1040d0038801044840702e810441c5d01680c002c100020a100e05002400703400fa0080200746104114001c040f585410941400403c0307880b000c0e0312130182d0312010003280c1041130103210180c82108000700d10f40d402e918246100030a001034940d551100081740f0380440a07880c42c0c408182e044080100340300e4200718682001050345c0c1c02840c034005903440080c0f5065000c1c514010074101a5001c078220050106000044d401140034401c01c04680d80c80c201600c0c0c0c15015224861f40049c060418803002480d40c0f0700794848868400d001d858041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 140191663 1250 140190413 140190419
    0x3022404090c0504030308011706040605061201060603050a110319020a1e090f0501021c051b1914030a0507020402090d1a090607030b0307051003021c0504110d021c0c 73
    0x202c800c0b85070000c000c1031001800303000341030300159039130b0041c80446029000341004001c41c036110324020300000c00c12510b81011559030380e540001807903a550040003c00603c1d54400004018040070b031072000c3e8091408090f07039409a00707442203d2007414100c2080c1581011520340000030751103031095400b04205110303890481c0210700344840060389690f40c0c0710002424000141000c101a61020381076511a042250596a1a900800d80d202450a1041c0c4914104099000c0c0b1000448003000c07600508040b000d901035071202d02c241d214050b000350101802012021a43d901c114101003000c03440074082080145003e4004000803000070380f41111050260340e410040200000c07813950164040020001c03945001c0061a03072060051800b40000e004410100b510790303c060041500800b4401e0485411901a4040740d00040f1410400f0549a1625698900804080d901203a030810710700040d00e194905890211b007201d40040c5045a440c142500c550482c20b030300e0904450b8603518070000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 140192913 1250 140191663 140191679
    0x109031d0303162607030c0f02150a020303160f08040f0213021803012405060702041b12060e01051008040609081602040e0d0912030e0a090f0c030603022404 69
    0x1031070340584509500030032201e407948225611180c512400c1e1300301c0018802800030941c850380c0b07490300541200c2c3c482072803242c1d400070400c109841e070301b458103403c00024444400e90740003006602c120800403000c02c00d03118154040b00c6c240e849070600c50010ba00076010a010404050402c0c074034a01c001c0030b0503d01904c034040c00707003680c10281c80402e042807441001f080509083c02500007800b401940d0300c5070340208143c0e180310700b03525015450160101144450071900c42d54480203a0620040080150038102d0100a044800300075410005c0341c189500050400c02040d0264107896000700300071100c1e45040c45c00c0300c46600040c4241d03074140e02d900350f04020402800003404203041c1202224403406050050100b510031200316000d086e442256500701083d4007405501c107941d60100c01804119a505048070354015844403558041454a00015412441d50004021b00040c01c8280541d40301520268211090341c030000e50044280f04032000f8240c1030f12142060600c0340d442c80b83c2415154010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 140194163 1250 140192913 140192947
    0x3090e09190c03030e090f0112020d020603151504030305030105040e03070212030307031512021002150108030a121a06090a09050415110f160303060305030a02060114030109031d0303 80
    0x3064501d05080e82d014000d0651011101c0100302040c0c0d007032451414100310701404c11905100b004055058814038804540d10b081c581c0c2e24081d00103041e291241407181c41039140c02240c2c55903d101c5c1005d0092000204c0c00300e0260340480c2e82680718036096a10b01000d11000d88550324540a040c081001842c0059641c008a41181145240103584a00e803010000e41110501007000100b03400111080040311039101c00f40802c1541541c08400032540b10784140c2c03510802c40c810050a2071440000b00d1041c00c000302030002080b850703031402c40307445031440c89074104c42c482150305201c0d0312900c1300110182003007802056042001b90509103170985e035080e02c00032214161070407500c01d20400003410f009030003070258648601004501d2071401c03603a070610300e0f004e00c40d002100c40090140c501a03003c1c540668859001590804240d0395a82125003000752030b0700c0d0902600c161000e1004d484030700760805105203d9010f0381074854580071101000e80001c03250005140310360511040180e80c0200e904848 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 140195413 1250 140194163 140194213
    0x9050306101703040305031614030a050a0f080601170403050c0f01020324010c06050604020403080c300a050c030c1227090406020d20070302060c0703090e09 69
    0x700e14240c2070030080300c10760509116607040741e680d20a20040c00807500100c100e40e0f00f00300c05d99403240c241003689043c0c6140f82505945103000c2c0400711313100c844030b60840c3c0201242d54666842105011aa10003a01d5020043c0d407030740c3c0014200c0e0b12840b4007441c54200503030060300a0900505005242c2c03085071400c102c03c49200e40c0d070794000c014000c10111641660141445d2001c604c40c5846000c40000c1004600b030b40042d0106890b80089403e82d1943c2d81218003858002c0c000d82d603078540b00310640344e840400301c4200e0072a28100b19460041c04c00b441c09510310b00340b65101c4a1a040c3e0058049aa5410400d5604481e0004100d81c00b0352040801040b1540301204040301e444180045050300d50000ca0300a00c80c4a981600c01c1e580c0030382e0740001e11503019034030060058582c102e10503060002d0100b100c07034032101c00c2e6001040100c803c0c0038010380589807117507084500790b54a009141c1d841e4003507014000c0106000b59028031500b00c0d00404140c1c00704190b400c03a218286e10240700d40d06684c0c054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 140196663 1250 140195413 140195431
    0x7060b1002071e060f0c08041206020307120501060e04020a110d0804150209030601120f0f11040c09180b1f170a050709090e0a080417010e0a0f0b0709050306 69
    0xa4070803c0302406614980c41440000303169a50790b6841c080000e002c100c8008208020014090515001c20a40e034041e01c3c060b008114044110204615214000350710590b40c85c4042896903a8444108199000c1c480c1038409a6440200d0607103010180300203504807101e8401030184213202101c1c1d0000c1003001c1d49900c070300c1c2d98450900303040c58101442e9981d50702a10b010110700400002e405071b10001849811500c601101c00070809150525841d41904c1090007010b880c3c00b11500b005010070060402019441200c003044494090711080c1e5540419208090403042c40e221514080310302a80041805200907012240917201640c0111341101161211808900c80c035008144104003a882c003039114980380c0080115007030680018001105038800d0b82421a11000c02d581203000504c074903014150700c01c201d1034803a40c6070340040c1c04011540301d4028486d0301e4111064407440d400203109540503042091148030044d6526184005203006006800340184d9450004071a2401c000b0144580080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 140197913 1250 140196663 140196673
    0x1022e0207050c091003120f0504181509060e01030204150b160501050a0c02060622090309051302130b0c0a02150c0d0806031513080a0809010b01032007060b1002 71
    0x404001c008070002d0007106410000045c2800060703401c0a0b0310b104400c039800c03c2c6410704528181150144200d800c002410070460040003055000703071f00300e507240321003078520030040079201c074984003c071000f921500310408852401040541403942c082e1829041c05021141c0c180e444003000c090aa102c40d520380d0303084c000750b0409001d02c24203200e06604060307a98030500821508040080d59484050401d512480d03e02c05a10341c0c0814003d110242c41c20f1400080c00000740504001c0e00c001250b02c102405204641c8000300700103d01e10807650001c03848414070340b15500309280003030300380c00c01400c00d0618410840c01601581e00e04d01180e1042200a212990300c004070741f065410810b1007482c10062124400600a01d540d01143c1c1d802900561003c1c030660b6034402c0300600b1034943d184406012403100142c1e1205d0306170f100d03400c5481040c400b4000d204a00b07510004500321404810201124080c40f07540958220549000b40940d6000300d50214114082c20001078400d03507106a2440940c0c41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 140199163 1250 140197913 140197933
    0x50702060906040e1510050301030b100801060b04081509030f0703051e0702040c0908100b010e09010e1806060117040302010b1201050105120a080304060e15010b04091a01022e020705 80
    0x51304c0044a51402e05462000c451b1030342120140c89404180801446d1050743d100040300182c05c290301d5401071946000034000240e130381582c41a107900600407403c1a001d02c03502400760180303116a9500a4031558011490041170f0f668400c01c98118110480800c101045514400100c100c4100f450884a42041d5510031070340c41000200c0b00600350807030520012120801c40c0700c8010492072010540001c0c082000310742e50300100c0e403159100444541c048204000070038070160b1802c03568881c91a944059200c0101c00c0071413070340c030300048a0300c5002525048000400050401030181c106129000210b030828045000400605505645010980d501c0c3d00401003490080e1680300d101c250100544142c1342184c0394074041e0b1000030000f90402c1e842d00346424802804005180354156841d500740d070300303585036a1079800652051080c005200c0c10701c84040401072207143c0002c2c81202c16001007c0c1e508010384050b0390306080115108a54003034003e0300d05550114001043c00c01d1042010f4070201e44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 140200413 1250 140199163 140199181
    0xc0c0b090f01020d080705161403030619030809010309171c05330d1a010f06090509041520070209010b090a030305030c13080a020f0619050702060906040e 68
    0x4411a400c1d4119444201418001da03003000d8503540020641c42c2066070380034003c541c40004440301d400104901300740d1948405810020021310701504048800d0f04482c00312841c0f00d801020903000107492240c0400c40e07003850390b0282d8001220035200741c0c4040c038124075400c41c096494011154024140130742c0024081190058802d80e68007000100c2490002200b0030a000504c070043c200040200481022111080d510190010300082c1c0c01000242001031218624040010a00c40c82041c10515000424424016032040040e928013801d10304403903640762180f641081c11208030b42e120700d6035180000c2100d00901101414400b804403529078686032403060205402c0140d2002d64419400c1c002490240d81c0d030902c1804590b014a010740d22612280802c1c0c1051040710100358016140c600e001900c3c1101141c141001402147c0200c007203000c9205000292140001742002c4059503946000902e02603000340040728005881c09040585020210f01241c3c030a0b005200380e800305c2e20400c00110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 140201663 1250 140200413 140200429
    0x2060708070212071403040e071e03060605070224030a090309050a080309090702070902030a05091510060f0504050402030a141605090f18072006090601150c0c0b09 72
    0x1210702c1c4010498040305884450319400340f180c00810f0b043c400a00c0c1700645c2420000e55003d445000c0104c5110305201a0140000482c60345181c1200300c030b4100140a54040e00c81d000464032030791245843e108995003001000d03042c002c0c4490b404031001045104161140c001b0318801c030204000010b108000781000ba10824266015512032110340e0020710031310f040407096480e80c200640e50040d071500c400301c0a81c18450315802c80649944040108140c160090b0086400380e10004161011050b1545101500c002c08460f52001c1818420040040b9445032041001d8254585429410300b80c6a20006061744e0050350f100b141d103074484203000312140c0e00c08185500502440c18220101d284418003401600840611900ca18207c00001041d0344960f407a00780070103c0258040d045141040c1c01a0001a12131107049130040451a0f075082c5580000741c00c0e008a94203801800301e40c1c41c00320704140d81d8400802d004104280c2840d2440010880003060004e01800003c09031904d5072308060000c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 140202913 1250 140201663 140201671
    0x201060801060803040e09070b0c0703030807052109010b0904110108060a1a180409050f07050607050c0d050109050a050c09060409030e01110f030406020c040b04150605160b0702060708 81
    0x96450b00c00308003c0c006001085400b150b0031031180c42d0140d9181c600890030000d040e171016496140005040f903181c4008210b50b03041c1c0e4425110b02496407280d000031903040c000c1c0880c0e5184441c0c0341c445a02d81d1640c003005030b0350003501000040307401c0a80314085511b880c01a01d00700c92540d90042e6101d07c941c0c00c120816440340701504d450725442e203031198407004240404070030039001d40c000402101d0000d030040a44107028001d84144200304d901d2034115070301c507000354201910f80290b59020070186050070841e408281c000000f0b1a6900c0e130241082007401c401801103c0a40d80d5052440c0000e006125441d00d030703401080900b00f96041881802044440101034602c902e01e00f24010000942000c00000e250b0070030702c2d11001464103c00040c2c82e122010702c07600c03002d10010400281c1984d001850000142055070240040000c43e0148425103110640b060390381403c0e0282441251f1091014084407112601a2040c1d00311a8417400150f100c01d03101e60700142c10600c204282a80c0010303059401c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 140204163 1250 140202913 140202929
    0xd0905070b0304150906060f0305030304050d0203040503030d240305030301061d100309050c03011505040b120a350a020c1e0d0804170601061d030304121506090c020106 74
    0x2d946020766450310301414414409081c15621a040ca0600000398003000103885446001041d050303e905000786c1c2d0350000ca03800c6070a8454204008240362021080e40e048400140081d03040420740c100301400b604100c01d00d04200c0302148202143c14240c031007a1001140504045e6a0365414480000e02c0b071442c0b0010301690071000400500951660a6498149025481c001910a4a61070030a0810020b50b001680c95801d0140c620104000403440d042203410480c0c0c00c0101c000744000740070310400c2100d0354402a4100400d00780c0821000c1c40040703480038150030324804210701010134500b280a01d0724100c5681e900804c09130326064041003814080281110b1140d0402e9032207c07550307100d40300884850302454030f00321104208000700c03041d580a000c54a8045003a0300d00145d4480d0748031001d224040010b000e042e600c03644071441e01c00d8018540c0002d009140792508100c5000354201c00c1181c02c40c2c944d040e035004031001e00e04c20310640018107a2200701081d0019100030080c04e42d180c40d004845 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 140205413 1250 140204163 140204167
    0xc1709010606080408070f0b16020f06160e03100903090e010b1303080901020a0b0a05091e0303011401090504140a060b04051e0301060312090f0b030906071d03030d0905070b 76
    0x1101d10f4000c030740103901981c0015100d6540e03820b441e02c8002d01c49106802404a03200c0380a000418100d481c1110540e9010350845049500c2c83d100e280c2d031400d054a007128420245003050702424403401c1d54003601c02d00070b411910328440c01c61801c030449440c11401d030f001513034000041c00f40210028003a4014500003880d42c0c240700f19840040106400d510004001d0345002071400303030f264000c2c03104103038481c0c10290034001403602e47e0b11000503000840e00903010f40a11000b011361904c403d062010045503000c001e5065a081c00a0f4641c5280a01c20417410f10441c0c80340020340782c1d1240581c0c00380040c40b11a9000600384245100c0035200c8540210403424010f00007070000d91503030302500250101000d559081c0c416201c000c00e004058a41000d0003100c4600103013841d040d044640181103403005002500da0aa45002001043c00107032030b000c1c03868001d0350200e4500e0f84112085200140c8024107980e61610102c0000d14551200c110003e56a80740c500382030501805008400081c460181064 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 140206663 1250 140205413 140205419
    0x10312030b031f060f090209180c030109230405010e121608160b01061706101e03140a060303030b031b01081803030403030e1006050f040f0f0c17090106 67
    0x2516041d4201c100208280101c0f029a203040594120350002e1144001d00320030b841d110f011100c003a6102e014a580242c1c50103030120442d1410004103032154803130302103240c2940d0801b248103010b455003d040101018448040c0c00c5d0740908182e43c2c501941c4904000503100482184650402001c40d00416020006200c030a0b24101d620340c1d003a04541d03116140c2917031748a200309500f10200599601500c0d220751000081500758000b003252070845042486158180e0b03521042046001e203460304480007500036850b0681c801c80d1101218a04442810701040c040411102230540c10000c030b0715020b02c662251810000c4c190503215507450202c090f00a405080888000f240312070190000d0349040185400010301c0c40c0b51404800300c41c0362080c50039255641880e0500030090204074405030b4541c024654003481c81003a52090b041102c002505e002403660300c20b81000018441000030a114076194088403840400e40d103d4032074580c03600d8a41c03e201661003000c2080c581001051403801c0c1c2e150031014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 140207913 1250 140206663 140206669
    0x3020102120a02120705030c15090a1502070203010f0c09090203010b1603090b04060804030e030a0b04060c0509090108070e07050a08060f13021b010c0314060f180f010312030b 77
    0x30350301840c510300c48070b940c800d0040000c03441c1a04000c0703501070440d00814098100708000c4003c05108240398225500d100038a018404070900075501e00000e03911920034180051520080c5c0390054071082001801c2c144540c0119095804129540c01102e544492044190b50000d01100152014080031410341d030400d01c1d055a18031410f03a84070040d2254104d803504042c842c07410000601002d01c0c10a490726902c18003e0500700c0c0070781b82140400c200308402500c42c00c0025200325025000000c025441c3c81c0c548031000140203814611017001810031440440381c07541801c0034028941d0790000c0444500d00302050320300e81d2020388440c0410004000c5810080d0b4003412f450303005601141d845002c205000002403492408042c081030380f03030000c6045540c44801e0940c3d0024120082e00a1111040740c00c0d048003103c10840104101003411004100c59050241400c103030020094000080a074003150b5900b5159000c0b1102016034010400506c200800b04809200c041c40d2810140000f408078000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 140209163 1250 140207913 140207923
    0x30e01180209040807020a0608060420180a1520010603020904080c01021309090302010b01020c0a0e06040f050c1c0c0903060e070b0309010218060703090e13050d08061903020102 78
    0x1019100d10340c107030b0100d0f041c8080700c000c84020030f44c01005054400c4e6243c2c00948289411500288140c0c68140c800e119140d91290808176500c850080a05d41503159080103840089146a160040321340403001c078104c4000801d200d0900340b00d0f01c3d41c034817041c2801540c0010088502d1030011a90401c8820401038a801107c542c0140d03104510903201c190242c192402409801201e2401403500c080000709100b139540581000c501a6009000c0311a0720001660788000d10b1603c140c101c4443d0b84104000180c50074041e410000007800840c007441030786403249c199442560340d140c0031500000d00b2502000e0b42c42005c010080415410720508002c800080c00300b0141d8823001d801507840b60109034164009000201c0501400a0225220304020700c0343e87c004d405c14140800f906a0003070394241540360400545093356030558840100c5402c10000038041c0320080e0524503430403400c03181040021400d201d1200b00340340560754141540f078040304101d0080c900e240c40d6680c01d80c20031b03810700160b640414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 140210413 1250 140209163 140209211
    0x20c1002070206090d0602070218090d09030b0c070807020a0b0a180e0106080601030b180105040e03030f04080a0504030519060c110c040b0a18021b0609150402041d0105010303030e01 80
    0x510541c1040075070030410301030308ca04440250700001c1d01e00784880c01e914002c1c806020700c014400300c403121090603005660403040741c040079000e61480000122148801d02c010700c0880e02c9481804c0c1000d20741c0c0d001c035403040c443d03810491002d0400320b504550594443c800c01e04001c241c4482e20161442c1965541080006004803003c20200c2000110340364040d4020340446000a0503034000802e070300b4034180000501380107091040d4244004400105000401e60b401052200b6030094643c8481da070f40300c1c182c4e20404175a0107000040c030002011a0042c0080e05101844101070b4800c143c403440e0007030440701c100035034100b0700807015001c800640002076001c101402c203540005000c80340c50001980040c46601540c0940f038640d11202101110350050010340c0d004d499000c0d0b003c0141d05081c0d031100000c6488a070542e00c101c1c9144e48c48440303804041c0c1c000b4006003001800d4084040300d07141d1107520b219130f03180d541e4403200100105945807180e54840d50008008100300750798080ca0b26100d0123010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 140211663 1250 140210413 140210419
    0x406090e071707090501080901020c070b03072001090c0f060203030406110c0709022503080a020315090702030717180609030f0f061807030305030712060906060201020c100207020609 80
    0x100000396018001e080b4100ca002c190300400b1882d1030322500040c081c1c019030148500141c17020b00840d04002d014001c0d500c40401410140c041d041c1000401481c5410080c0303001c00b00030f41a690552040018012030303039204015000860001c03101d0600f14111062036218118444246404000c12640441502e030460360105010400e000b841c0036011560055175106401b034000c1d11400280507240c1e500400001c940b040045483c90040714507030302040c070401c4026001c2040d000003d10700900d9540155400108904245414120000420318040301181d044001da840044d114007400065001d004440041c80800d52900706803080300324803110488003c2c0d00480340885e04413020307902400403540e41181842215001420304459030350302c035407e503070910780540307220140040c2000202e0120152074140d01c8040c9152103901d01110008031059080031104d5480d000030440b10070710300404c4000c20081d4005601c5048144016080161903000805d00313038410481d940058070342c2c030140c5c1c24500d011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 140212913 1250 140211663 140211689
    0x2030a09230306070903020108060402030106050306010f111608160f090e2107140c011b020f10020708010b01390b010f0e0106110601030215160c0504050606040609 72
    0x84070020700c840190501e80c03640340c05410100441c969015480343c080300e00076071701d065641e224031301404100d100078011000000c904000080c403550050044030442d400c103107000301c98400104402410710094900700030882d052100204003400c420070440540424062030203081610780641c1e982c0d41012880f401c0003050b12241d560800c51024070030543c0503800b96540c2810590840c9003414030b68000d41c002c481058146030482159900028024140101a102d04104000e501841e13074908620003002ca86c40b151b003603440704007500d880d0602c0081c00307245d800034913031181014003003803d45000c07103006810050034100d05400c421002c516402441680d0000c00040c0241070701c100c0c00041040000303001c0318880e0000082e1480001c164904507200c0a506c1145030b40c86420480740304000c840103400c190701c41d8005001500e0b280e00b41d1001006003040c858906485030340d5420340305020310015941000c1c2020300304580e0915010b5554000f8080343d060746460b040902c068500d03641401088420700b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 140214163 1250 140212913 140212949
    0xf03030a08180109050105090a050d09060801030303092d0c05030a0f200604120c1413050907170106050a0e0402100f090506070f0c0e010b040b07020613030c0e0702030a09 75
    0xc20b41c04206295085402813025203003460b100c40d80c8040c2d41c0401c9505c0d00ca00704001c1805880cd80301802561002d540b6800f1076483e50320704070017808503207405032015503c05e81905101c101c0c840f003003c883d031200b0400e2824103d9a0820312024540340e8081d5000342c101c00c000100003030b6007800c40f0060980c0b2005a07810b503542d401c500320264040048445c0c000c4400107001c41e000b8142054071051500c500049901ba5841c1c201c2c0f118a2508c1d1644203410200e0100414a030002c1904011b0b40240b00c802100d0300181d40f0a452409a4801c0400b94400d035900c01040c03080381032000502c405800f90541c070082504140d400b04d02070040c1d407000d11040041c02c1074030905491240f034820b00103000042401e030b241d114504041420300b0784408226581207800d01c0c0000c250b8038810100d8100d40304c0c002c0b9103041900e00261808552710002081382c0c01401002200b030700040c0084800007079801040d131748940380d040058408140710081e00040640d401484959101588005500142c0d4080d050b4003c80f191 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 140215413 1250 140214163 140214211
    0x307200c0622050a0803120a0b060a0c14061e0a05040206070b070309170316020606130b0d2109080309101409150306040c1e030c140403110f03030a08 66
    0xb8990801c035402850700c1c40002e0310003800000360220f50348240c0c52940607211802c05004031011010a590410343c140400c103a50b42c040c403e070307005140c01894140c40c01003070b0302c001e5030a06800700c4403801d12082d404002c3c8000c40c1d000c1500ca50080c4080c000300003a060640000e45a8050018005e0241507003000051000e4801c0d00003c0c186680000f05140c5506d090b00042c425400441d080c20b0744001900043d24554400100b160180c1d07000742030003480c60341c44112134000e00902010a030300442803050400000d0050405500100d40c1d503225072030240d901c0e800007418270300c4e243e0140410758010701c68071540c0d581d101c031502a22003560030000d01c06024425061703d1400b841119651040c0c0c010840140115050015486024103d80800401c051100280c0c2c14848001404600d4640303611049402d902a0f4407440840d0100c1c2003802d6a940751040010140e032103900200c88001000031802514100784950b500351120440245042544034480109203540c020840c0c940105048030300701c4450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 140216663 1250 140215413 140215477
    0x6110a05030702240409050406051e04061a03030705071403210d110c010509070617040b0702031e0705060615120402060d0204061106010f0f14060f0307200c06 70
    0x13a40b403101e102d07100d80e03440f540c03000140070880b4141c507410f00706800109003c510703000c1120000000c0138580040e07112611004d00400c0c0d1490406481c41e54541c200405990400203060181d1040300103000403400d04001401c42444d104001d0f010b80c0c8400d03848400741650200340c042d14164038074550348031000c402040c4050407030503c082d803000400007070450b074449041d080b00d4400d006103422620426503c92040f0781d106211098002101480404117002500ca0707082c07a40c121503644101d908258041100110016a0a003080d10103000015900d0400c5403c0c000b880d07003d03c04582d0082c054603c24620716403441841540341e1b0280050000401310351340c41042d210314211409013152210f4840e40007618010b001c1225000f9440ba410000602003113a11242040d507041c0c640c0600030710700d04840241107000b0025015401003043c03154003a40e01848c805188180c0040d580d200c1e03078819042d1150652442c1040c100391980000144000c070f41c80b800101c030030200c1382004550240401400c2c1c98004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 140217913 1250 140216663 140216719
    0x2030904020409090b09035502070918060506041103090c010306050f0d141c0905040b1206070507110d051e06090d110a060f0606110a05030702 63
    0x510208001c120043d4650121401c544070301c00015158036200e808655901490800300606d0ba8411070740c5c03603001d5a04001003c6006880300c242c00324248186540103800221800c10005010443d4803502c6690410034003005000031041084500103105400c0b0000442c0c24018060a0301c0d4004200c85031201d0303220f0f00c0c40c00d50624070700361241024100c0c281c80d058a140e040340024100500030445190001c464241d290000708840c5082c0e903e651015170030303180d03001c641d8418000c0007601b076590045002c01c414001000d9550010040c102000c120440300760240580c055844a0391480c100400016a8ae402c90b5482c200300f6100c0240c0d213060740200004506040d04051201d090030200074000880c3c0308400c040c000034034081d10142c3c400f1a40c80008a405021039840745809640c184c2c0218813240c030284110042c1c51695055403694400e441c84422032100d01c3c0d40d5000c0c00c010385075000094504410502019040307891098449a90728060320b64080d100d2000f10b0001980751005000d41604 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 140219163 1250 140217913 140217919
    0xc1a030c0a2705120c0a140109080615040612020102060f180a080c0d17270d0216080a0804090b040e120418060803030f090705121f020306010f0f020309 67
    0xd120341200d0301042d0100e0030b126650256445101c02d1507044c0b0b012600400040e0090302412003075107001d200c1d0146400106003141400340300e11006c81c082c0c10034403820b4824848644d8208980d0075240a110483c3c50950110703010003013008032000140e03400304d140b5401c6190142000c25949a0074608441b80064541104052151050120402107070344003070464040c44134180c44441881c01020f5031300203082800360100718101030005030740702104001d40c1c0074000c01c060219a8507800c9170889103010307130814030140036910140781c03c030396022502140b034042c0003c01d000e880203111568642c200744c050783c000c0c2542c1c40e8541602003210781381c80d0f000a51403c0403400700c4200d00c1c082d10034811130340d1281c000d000c082a0140765140010342540101c00403110603070000c3d440c41c2d5444403185118003001d400746003d4010310500180316070f44d10301d45000f5034006c1400f801041000c8840e01300c400144030380381d03a0140d00500400020341c0c1c101c1c0d1306120345140c90420200b0100d109404a00354403505c0310340e030341c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 140220413 1250 140219163 140219207
    0x21e0303040608090705060c0a0f060f091407061107030605041a16020c030102040303050702100905060a02070815010303140c030c01050708060f0108041e08040509070203070c1a030c0a 81
    0x100294015001c50213006003200b40c4a095444206211662145510b5003445034004441d800003e0710300744428080030b0051a001038005111251030303003075550300c607025a44d04032654410744401c0030511483c0024201428400382654200100c0d41d250070452001400141e555000501400341c45003a11803030552080384200b140c034001c0590036041786080b25507001441401d0310b2900c5402d05208035000e994050300c48a00f032002a80c02c00c4150100d50840104019040300000796540f103070340250038500c1d559005480114100180b01c0c0c43d20f0320058401012880040c01080807075000101070b41100709400702e61766242450b400c1180fa51240e80d90800b030940c0380408001c03040f90701c0741200c0c0c044d6070304603285882610a08011199042c0a450150a1081000c5802c010180700c0e9540024544140807045c00d05550310000344840c6030454019001d43c20024902007001103414101001c0e11411100d04941d00c00d0a00d00903203800001c11801c205040042c900d0005401f41140d00703204000201104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 140221663 1250 140220413 140220419
    0x140403120e010e12030403080c1c0506040b150301152c010513123f091205060f010e0c040308030606070f0f2105180105040b0406170c0c0604021e030304 67
    0x513075500455054000034034400102e0007810840341100e0310740e284200d298900381c140c0d200000c01800041d00b0303154860341d520800f26061721199a03101c0c14065075441941c0300d43c581419030070701d0315480002904110111112461200e040e048080a0541190620f520080c0100040e50310703100c0c5038401d05102a003074500090071042071b401030305200e11480180c0920321007850011405000b0410403041c1411685140f0140e045c0801000b00780c11851400303c3d4150b6488290300440c80351890241c1d0950815020403100100903a061401001c044050554a14001d2400d0301c080c00347c3c2c040103100f2180000480c400340d4441d0309841000340c119090340b00c2c04110340f400c191890404001101d03a041c101c21042d07050301211001c03240d410416242c151030000c10141c025940c0030002d1483d414020203020105044c3d0030740026101400c541d4841c60400f00b80040740c440402c40007012402c0c201810032410030700c404041509900250705882404080c9522148440c284904100c501e4261002080c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 140222913 1250 140221663 140221693
    0x603080c0d091202011d0105131d01050d08030c0307090510020a050d08070905010c0c0306020a020618070f050f03011118010e030a031719090305090103140403120e010e 74
    0x2688098a952515426583c2d50650820b09030030740280a030100b40903d031070190b0484c046040e41a8581c0c1403402600d040441c0a83ca45036000e0303504146214503408002c41518046011118050b281c05c072103034010308203661746007600391000900b2603515960210101d10010702a01c6040064040106a1003d0380075150b0006d588543d4503805035258403c0c0f4100701022030255242c01e0003050103654000a01d418540152030b40c90010340b003150004080400000480c507a44040c001164240e8042c1885003801d1030135242a00440140600c160000e850420851441161001c1290804d4961552050090b4002401448103050031980040300051040c2d041e4420b84890010000c2621961002c036542014156900600040100403a0404000000702c0110403000c075446240c05882c101d107010050841401e0b9620240204c0200d0b00c00f003071000c12580c260080b4500c0c000801901013861410340c80050448250022200b403180d600e5288050140c42074000e8880722905208480002c0d240d9181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 140224163 1250 140222913 140222923
    0xe190608100b010314090616020f1c080702030406050409090516030501060f0e060901090504022403041a060a090c05040503070f08070f030308072604060f0c020118060f0603080c 78
    0x10b1140040e1070040c0030b403601115900d0440c00b443c801002481e130b03691406201140c0e481c40b600d15400b54410980d043e10b00301b10400c45140c034021150041e8884a0040d0006440c80340301520007811341d0801d000510000c2c2d40941a01e045480c5144040381105403400d0a03810056500c40040b8032544005000c400c3c40700540100080700c903040341d1480c0c51684c8180180e43c0482c00d81d82c2c951300c815024010441004142c110303603003140c0020f144c150030304240ba00a40d5128600304c1d120091354004020802804414003620400b80800d00c55450709180c5000000d410b480c6a000b100d06032556803105000b813a100d401034502404002c0d040f0b40285171200c900c035002c0c4140c0e01c5284014421000c000c01c40d882511460000c50380d16440e415202d0300c4110742599041c204110710460300102d401110664007414807024041c40c041c0e1740004218903a0b10440c1c095030205030f416419a070412100d40c1d08408180450602d0030382107400012a0100f000c6141c02500340d50780007401156000c01c00407480346001c15 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 140225413 1250 140224163 140224181
    0x90302060d1e0c08060d0303110304050616050a021c050c010212010302040c02070b070312020f0a08040b07090b0904150509070210060509010308070b071e03150f0e19060810 76
    0xc00c0807040e0b84410041055801c0700b240700d400102000c01140e410308101d0900c03442e203842402c2c04500d41b4101a9041303604e400881d4180d406600c8103040c0102c2070300d4030f410240d0f00c01c1589003052a009140c00040c1d80c800b17840d055040031040000180841d2413041d82078442c42c021101c025980d846581c402a20b07070342001c0c0030503032013540380148600f681c1e030000940170b04403a401c4201c0c505012241d1010349007040003080e80e181d00e9408101203100d18240c0c000504081038141c80c0d1000a04150034030a42452000741910180304070100d003800385501e107070f060b6190820700b00e40106d02031510703804d5001820419444a6000b512280c284280c064001c1803450010810f020304204c0d0550b51000c0004c9407400384800740070392400700011008141c94024040e8003c0c518186038882222151514168482c4204d10303c00203940c0329041c0d4005100a0215401050041e5213040120300304107919007020400392050f40111945d002640c821040750b0400d10090148005039141c04101e844550302804000f1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 140226663 1250 140225413 140225441
    0x50d020316090b011128050a020a060c030810060e060a09080f06070f030c0507030c05010e100e070504050903032212091508070c0209070c02061602040b031906050403090302060d 78
    0x44c2c034181e4840c0000c06506c42d0404a94101410022159403600d110396040c054503d03004004038070000d070726050080e03001052540d03180764121000d070400410968014150140442404508100c07155000008524000c0c04990785a0340381003a041c00e0b901d00740c2950000c2c0050243d444142480840442d900307200b0000317501c45500d11480366a01f00c007107851210360b071004030b8000d01c034103800300c0c0c401d01e50080014812070000441d000c072980e0844c030740800080d2007181103031503441d1030842c00c0062000d1401000c3c191414000c905281c00510380b2400001c150310004154032101c05004144400b01803101d6401c5910f1070010300c16040f005200c0362260040b202001403015100842d0340c0703d621158407420745540c0e100c8142905a0030801162406410002000141c1c0c0552015030b403000e005141e14980000400c102c2013a500c14041a0741e100001548681c000360300b0000d40011103109804440d42c031035800521a6900d140c2603a80d47c002340c001039017114003c1907404250a40354400318070310f0590 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 140227913 1250 140226663 140226677
    0x5090d0501062303030c06040f0c0816090609180f0203070b070308040b06010f1b1401020a0201091a04020d0f05120f030402010905090c04090b040608031201090501090501030b01050d020316090b01 86
    0x3c05240d900d110b04080089158421400200490740c01c0c425440750074424280c9104090769031028a281007001d96110b41034076240941000101c0f52840b42200070b01c16110180f000c00d451039441c03010041c40010251024003941d1680f01155410f009200c007919404580c42e440380d0407818010440d0100303c40c200e8412103c0004155158012107000340c00c103d080c1c5d2005100800d801000d84100700300c030700c00c13288280f0350003480f000c0b11800e001074070040c0712079400002c0f00381940c1040e642d114000f45001052100042c180805a218001d01014054100010360190716452500500d4600107407111400704401203910046c010b82c3c900211700607030007640c0e415201038030383c0108052003c05461000004004110402c10000d65170002c50512000a10005600b940c601c0502d040d98005d0034402603040740840107122400e65446001d000d046011800c0100750306664500090350418000d0b079228902c940030180031541c003000050b030030700030328087e41c80e031913a844019901800c9031000186c0130a042c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 140229163 1250 140227913 140227979
    0x3010f1103040326010b070f2004061424071a090129040e12030408030106140910030f0b1203030702010c030e0309010c030212070305090a0902071205090d050106 71
    0x210120700c0b6822610090044960b446c0420f07044c2241c0c02910b04450009600e900d200100341c01404503920b4400800e20380c40b0016040c000c0104403003064200b070400707048804d41400c1940310002030200c02d0b40c4110065400003004034802c4c44030700440900501d1080c1e001503401000340094162401001200b00a118028890086c0202e801c10300846074400800c901610b0b02d140b91a03088070120710600d00607034042c003425822404003503000b00d0342030f0ac081d0b8000004100c040d40c0600b8020a403039a00c104981040c0c400340014000d1100007000000305500c0e41e4a10310460a903a03c0a40030301002001c0d0361840f071703202400c181c5070b8108850360030165203040804607189009008918880e207150015500d411090720040d501050604815001c40c0304200e03104010500200007014281d01030303100c4548507240340c4100800103c09400c041c8801d40180040c80025118150105040d48141000c0c0d0701c1d4030242c800315407084480d01003c0c00719801c06000155855903500002c54407005200c04041400c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 140230413 1250 140229163 140229197
    0x20d0c060e1005030f0604020f0d1406010e0306150103050a1d010902132f0c0607050301050a060c03170a020c0a060609050c030606030406020906090a140907020d1d03010f11030403 79
    0x2255817a0b58850600e0001d07a0034070701742c1d008100c03054400c040103040c621034100090480b50031004904400e07a144041c4041c070341c0c00242c142c914400840040200d80303404101c0d2a03100c11800080c43c1031603198400f00f20b030310050350070440e4104095021540c054140380c3c00540a00b001080603400b40c40c1d0058031051800003030107580d08d543c02120009214054940d007800c03041c461461782c298640d005102c030050650080c07106034040c416942c0c5464907541804100008002160301c458240441c4641e8030002942004000303c40d0b050400031411079545401000000c1d219810150300b86004805030842081500c0d071103003044e91012031042010303a584002c0442644800e03149564000028000280014600d40041c0741055010b844141003503c41400300718000c1d11504000c42c8211405800c9a0758104032801640c052100d100412818580843c003901c054030a00c019110101e420321044603d407400d412503590000090410801038040c5504c40c0100c0d001624200c002403400a06500340780 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 140231663 1250 140230413 140230417
    0x60207050d021c0c061d0f13020a0e060c0d080c0711122107060506032a061c0209031204030b0a05071701090e0124050d020d0c060e1005 60
    0x1100070304949551403168007082003e040d0704651002c100550740e00b4074000382c2c1030401d03240104081d03120801408204100fa100162000590782d000e54110304404442d50b9a42c0e0014000084070a80183d0b1804242c000f01c031502c41002c44950889000200f010100c14002607030003021480e50345002d0251a4002900024815440040c0100d44000664101460720f442e2080c1000b6008040700e0a2441c80704a5924581c80035071041251100070400c2d405010440c010264007080c05c40103015a4005100e1030b284820840c44c040ac5042c541e00180c01064480c08100d622052500e4400704000c114545100065401054030a010340140307407008440c20b164100752800c0d60f60054508509645490082c0c5c0108801803c907010001c0c080c04d106e11300714030707000018041c001d030003004241c818646a070603085d6460204a48040fa03c1d42034500403012001d00294103441003241d0321803810790309000250142c8899100a0412001080001500c54000c4c0100254072000d4034541c02a0404c40c80c00d480c58 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 140232913 1250 140231663 140231669
    0x190501050f10021c0f12021606020d020903010f020304060c110d050d090f051b0a0506070f1106030f01030c0906030b15060409060f090b03010b01051b0705120d09060207 74
    0x101c0c0c2184100601458101941c1d1100d00592048075110100102d800c1d4400350031070088800300c0c61160b0f1800f519540910541200f48606c02c0541c41d00c514092440c00f40300c0d1030791000c0d100305c5d400304803514800043c2c2c0445194100060080c08040d400d40b0501c0000e40c400c0d1411501241b500e070f4070480190041002c640081d003294080e208480804101f56010f80c007444400026a44d03a10003131000410f40141c044e00c4ca4003a00c02408103960500381d4951a142c1d500c180d40c0725140305482000035990700011541e100d41d00018400001303040f45041240403500c1100076600540c00300800c00ea1458605003581280e01503541c410b441c0b03540d0a0f2041c01c0b5045400b0150001d422a4001080d115140e180c12040c410003818140ca0503944d0b00801040f41c3c415040b100042e000c2ca402008182090300422429902c101c0003004203504102c0043c04e14483c041d141e0022003030142828000100034880c09000b4103000d032070488821780d05502e00361034806a58840c030201c0c2c9240c401060403880080c1100507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 140234163 1250 140232913 140232919
    0x40e0901091e050c06040b0c06010501090b0d0b060d18111f18030210020133030201180b0a090305060a20090a030c0602030304120807020c0105030a090203010504050619050105 77
    0x91a105500c0360b0740d900c80442019a0340b40320712404943c894072600c000b0402444030b030300003544840315464102d050a8040e0b1203141084020380c003d01c944030b0004219107000c84c0510b8000740d64001035002c501140200140400c0c11847c00d6101e4102e440c40c0f140b00003020b0321070b03400170b001d0f4190082041100d0401054524208840e1103880350818003803509400b0090004075003154860350303640002d00342c91101082c180140d44840c1c0c0c0348010b03070003514400030240c10f9005d069401c048903655102000101d201c0a070403c02c00556a0f240644540d070705074003911140058981e50040d200d00901155002d100841e40f5101c5c4000055030003c4a1145010302402c03807254003a5107130f5000e258260ba40299031000d80c800d101d0040040050040b00c3d00400402c500c1d0041d5443c0e250a0600ea5500100c0016090034080e420041141a41e40818803016940f82400c0042d200e80b90f003130701000240040d0000a41540c07074403090009101e800500715101c3c00b0103861400c0840c52440022068440a10a55130 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 140235413 1250 140234163 140234183
    0x915020f0c070f030b22050a05010609060506030103020d03200304031a2208090f0a08060108120c0c04090309030605040f06060503010c02030405060901030e06010b0307081509071d04020a0302040e090109 89
    0xc4030560028581511076a141b020b01c901d03040c0f51144d03818201030a404580c660340d200c600708000045800b800300200803c403034450540d850758021a4584042507401402c100040b4004802004c1d001e02c0313501e840da1418116600c0d50384a280500d42203440400980c181c209a40005001d40a20b140c0b100c90640083d480992001c099a00d442c229000400c1d00d40e4086202280400940c541001c0744000700b50b558014400ea51410496a050401c0c401d0200c03a0402c0801c0341900c059800905100c030307230b00c0c1520000703038542e00d0382002c80300c01c1011f801c028038a030b040500344800c0c09018a0640030482c01070f841003002a64903001c25080311110311403500541c106200801103460320f400a044c00700010704010501c0f040c503580c52418908260444e12038080c0100500190590040d401da034440c101180c54030304011141d0000b0031003c0300604903020800d82d0745c80c1018031074498250000100d070107402551200240d00000e8041c0d00f25010385404a0036590014611620501402c0031990700100c1d880 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 140236663 1250 140235413 140235421
    0xe030301060c1a011d090309040908040e0f0709170a021e01031a030c0603130203010504051011030402150706060e0c09040f022b0623120703030207090915020f0c070f030b 75
    0x1c5c01c8910004c100400c54081030011004a884034000d6803200c0303201d200f1103903540381040301185402c100640828402614030080003055900054104151195490111508045426820300c4e100b40c0501c02900a00442e00f00780070008800c0981c501000b0988051100d042d5440320130504071200003200ea4183e21130551420207082c00c000840e00b10a00c1024204400017030303000f09007514400e0703404851582c041440026004814410410b41c02d182d21031a07803850800e07400041703c80c070b03854181e01c016074000240c40f0700f00000369102e203009200d210300b491010700d081c07400c9003c1a008510024022824074501c016070920030701c00c94032046078156015806d4140d4441c1000005810b8200c05890740d951080820f58109203044016101500c95401456141c04401d00001000c5841d9686095102d1001800000e03004200801602d001010009043c84981401088412244024062944001485d280b40007400300141905051002220202c030343e04d025843c508452440094502180b18000c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 140237913 1250 140236663 140236709
    0x1602030d0f02281406061305161202130f08070506030103080f0a11010501090933020903070e34020604080901030609020a0e09070f050f0903010e030301060c1a01 71
    0x300c0f001220032503000140c510707503112100e0600c89110322480d5448030341000344e689410800a0401d0074051030a01190601c4007506480c1e003044490403050060740c5540d40c01c078005c82d50541e10031080c0c10034825a0b1941c1c3d40c00c010019400e900601d40140512000070409041c00001c59041b2680025082d03c1c001c00341d40c0c006c9040d080141990100001e07414031442130388007402624080e00548000080b800142d260840300d03080e034943c0350107222003154200c0400724023900c0c009104c1c99400e000503030380e0b443c17a0001a041c08170f00e410601da22076034541031080319000340210802c111080c50000701c240c0000c6104203880c20041c2e170782e800140c0c440c50024000945c0c65014020a01d01818081030b480d44640192051b40c00c00c11440e0001036004545440300d142c0604241d030011038038140101034100038000206a48103415000e0f55403000000d60440c07944095000081d01100300d41501c0d22540c40b0350700203006442c0213401b5100d00c0c6104050000000e00c0c54075841c121600c042004a4485024440b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 140239163 1250 140237913 140237953
    0x30903020f0315070921051f020d09080904052214010204030816021306180b0f120a20060301060804052d120304030509150409021602030d0f02 63
    0x4015014000d800c1042203041040c0f00f414064411529403003030036800d000001618840320313481d03a19905040c1800e000807640110348201c03144500b1071130b0a0064000444000a031060143c10148030349000ca054050281d81409002c08030f000720b0342400309442d00c0e0412008040e03403020581d5414014114000051404500c84003861000c030000740c2403030350b40d894903541c9030480d5405a40900b540103a4004601d0510050100e4043d0f01c6000c1102d142042c0b034800c1e500c0d20929200d10070700d50303039001300d552655030304100c1091000040c070450110182503036454507840c1d04001101c028003d1410212803200c82d1a94004545000d0039003410740e07107071400450310444090002c0d40d1a010b181110060100b210300803500300902119030400d03007440080c40707a00d07140120070701c00b208800c140306100020341e12100311441844100ca40c50500e00c0c00d103000381e4003840355520865039948001212021180c1c40840c0d00c40c612300880030b64903c0034900205482c000b2f1502100b40043c1c1100c00d0b81d0f0191400404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 140240413 1250 140239163 140239189
    0xf18090c021b0f0603040f02030d082535101a12040209070c0b0403020d181404021c0204030b060f0405150907020f0601030c08060919080a0e06030a0b0108011203090302 74
    0x1580c02e000c9101f54010034105800501c1e03000000b0000010000c40d01d0000d94842c454410050500c0c0e100caa0000009090b82c83c4a0100380020810f800c41544902d0088108003070000c02d98184245c1d402c14690302080c81c42f40b0711030315015814007e000c04142030580142c41842d80d044040300d5241d0303550303030800c03400a00080074001440b061400d1000030889008100748600d1007a0010f0541403050f10000d04a800c071070400c5880d210901c0818404401c1c9840c0e11050030a041c0d0740036869040120f4802d4001222410240116101040c00018800c40c1c6070100c1c0550010f0b10501d5900b03c0180030301003035642c100d8808950703a041403050204c1c0e0030000c01d8a40d01c18071030b206446502c1c001c182800d06011003a1300035142c001e00040103114030728081c09880d4000b120903000340004a40c00d04422041281000094140000425156500c0b8010107814802c0d150040010b0350320328042007084000c00c4601c1c1890300040300b010021801c54040810311003144d0301030320f51444c014a103908000781507032150f07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 140241663 1250 140240413 140240423
    0x60d0c060c0303111809090c0a03080c01021e030103031d0105030721060801050603010501050a15050a090509070309110411120a0f14090105070e0109060f18090c021b0f060304 77
    0xc0790040a0540510240c0034141446007100c03000c9071145c1c100450304001901d0390259422500728000c40d0b94490b2843c1c2d048070b0b4090f0344252201e9034400b1041c024001d0100d02d4104001d00e20b2058016400035004505803486074460150096484812000868804403081c2c0030401c1000803404040c0146140071600c09400d1022015a8030702144906803401a4440d0103280e4460082c00343c0c6107000c1c080c06024002c03d0302c1c103410240c07800b44001c030780d00c000d00140400c0c488000b480c0c10880d4401c10004024041c041e020720114104820024000d0102100c19507010344200341c00a014601070040500c86000d081c0400e0400e421030340d1000784000003402d042c0440f036498500480700300840c02010030b5403002510408030f51030610071040c03e450004255500b00214070107080d0b80d50b82c0040c2d02c0d2064503007a05e4a6402c00e01111001e403924480d0521590f000f014020b00000c075a49507800003040300182c1d900762040a281d43d01b418100303070103044400742d006030707288180700442c2020005103602a01403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 140242913 1250 140241663 140241671
    0xc0304060e01020c0d03060b0703050703050711191e0803040501030c020a02090c030405060a050610030e0a0b0a0c110705060409020f1b0a0b0c0702100e130f02040e060d0c060c0303 79
    0x1401003402c913480764003481405d400c0300d1750000c3c1aa405214a200a100221040b440c003100b50750000c211b031064040c028140300000c00d0140510420300caa400b240f4030050005a0301c04e04601c1c04071817040c0350f4480d04041d1030895450030050000215440c0849030b83d040114100707814680150040c0091000100441c400c080c098809652001112801a0441030145680e0708003030810505002d0700074901842d2074104824042541c03582401061442000d00d00010440d03040d0090f103050500c40000601343e10784510500c95507010a40c0410028241c0703440740100000750301c84564030741d02c113072198990041d130500041100d00b42980042498080b1381782d07054603041e01c0d1001e20f032000d815450048100c2d4002c42000c400c00c0000c006268100d0420510f05007428010750010300c800d002680000100220031007665625120250f110070070105601c2c0600015103138901020003500988070b41640c04001d0070100d0003c0c2881250030008a030806844000942091070644133032030080c500b2410143e403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 140244163 1250 140242913 140242931
    0xe0c0108190f0c0f1110050c07050a030e0415080312090708030409061a0301120212071a1e0a0804060519020703031a06030108070909050c03011503050f01050f0c030406 74
    0x34411201110030781400001c0b8180034180091151400941110174400d03503010b1070714844c500203400c90004c0c24014020440c4e9680014401b071740e0050000041c603501c1781e101104101038004890524080c42980d003000b00c07203a92902c00300303208410310646c4801e0b00208081a2848588270705035038030060f101c1c222a00c85584200c1c0524560243d8820700b40c0c80d54400003400402004078400c40740207841280e050a550504180300744030003a801000b0b11074501c140b15411000c0e07090214030001c140c47c0611036a00c1c0d1000300c962859a0040b007a0342803c804030b01c2132454900c1040e0a5030a051000c0d62590b419603981da6030310300107100c050706403074520300000758a66800041d40001c0400c548070f41c0d400301c1c0c414441100007149015860000b84960414801404444000a400c504403032061001082c900c0346414554242801c00001c681c042d420036402030648000d440c5a202180d1140d411a41000c10f1141a2400c81d0f00959240c081035000201044506d07503030708003039604140030f10000282800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 140245413 1250 140244163 140244211
    0x31305070605030a0f06051c2406170a1101052104080711090411060a050d020d050108060708040c05010c02030f0a05100b0a03050c012607050714010e0c0108 69
    0x103590761180c00040c00000402c51000b0b15070040c403890040060051000c1c03820301001441000c48a0182403890a400385144180442a03440f601d10210311010085021400741441c0090095809020301c0092a10034101280f040056100013158201a0b030300344000c4103a004507000d500101c1c5440d8840121042c201c5002111416980514402c20000741d546880e80340c86040914490403451003801741e0400c01001c120032105c40c1c1d41a00046603034550361110700342c06851034054627011400051001c40e00900350740003076101c90b05883c4500110f94407a174801e44220351035030003164000c01c408171152007048554000c040c180c250610080581e1300300b8080b800c0982c90501c9031342040e58540e001d05480c0040c81c41c2441141e86d0000280c64184210b811034540503581c0340f40c19641c41c104000210203403040f182d0300b40da502c2c14000000030440f160034012402403882e0032030013094401403001002ea0ba00000c0501c0b0b0f044507a84002c0140001800300b60065851080051420039010315002100348014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 140246663 1250 140245413 140245423
    0x7050f06010e0402040c0e130c12050c0901030b0a12020f0d12090608090a030801031b030807080c010b040b1c02060c0d1d0307080729030a051515040308031305 70
    0x200001c1e18800d20b62400e401040141c038503590700c8900384155030301c0d4118151074000760fa806059170203002027616000280222a05008030603a01c242c2480c000034015083d5101e40200540c1000360b03000d00110b8400b104214200c000c86c0b080070030948020150100504003500c203064440001802c0f51601c992136203d5503203540304450514006200403100740403058100306101e40110103080144000c019a40e800b4108410600016066881390800e1081051180c56040003450b4866549601d825076490106003d42001c0074912140d402c00c10040001c0c10148a60300b1340c82d00003040b0f1041e1101070920411035020030368043c0d030070400030001d01c00c041d2400c00940b482c003d0255030b81c1400c101d000c81d22041412440000034840c0d00050b808101400c0002a00d03010f4448800d002010303514907402c08081d8170600e4540d0800b00c40007100f00204502c1c0382c7d000c1341c46166582c4404011a031198200110740c20b28005480c041ca005100078130200d41d042c4003030b551140b0941d0884070790402580f1071900d05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140247913 1250 140246663 140246669
    0x411180403051c0c021e01060f06020d090e06010e090a0902041d1c02030307110724030f0903050307230304050c0102300f07140c10080411040207050f0601 68
    0xb081001402480c5000041920030805205080401c8079009020000391220319403070080c00c00141c0306e640c488040000f1b50002d8010030280c10712060040e51000065200c030390f58a4a81d020407481000083c030300b8651100b1502c1464140c2d180307001007640307408110780d4640181000840c00e039107081c0c07880161600d1180c0440100000031a0454505c08440d50345481c1d02c5500311000d00e0402041c4105041c0c000040e80e8210b070141c10550303031020040c1c000601c2c002c52948550350014006259001b80303400c014001810b040555020300100158412140c02d4809240000780082d008000003000288030b030065580e5504420107200541010031642041c582040d142600e242e0441140d40d0721a6070100450440004401c010024948010f0320400c0c0c1c1c40500240109699000691120600300c10300032541c002d940028101450550024031664410388410320500070b410b040240f20881e800351051500c41c2d0341c480c4007460a100783d001404045e4010800450b080c0c4070707108034084100024405507000e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 140249163 1250 140247913 140247917
    0x110105060108071d0a27090b040209062d04050c03090a030e03010b0604031110090311040207030302070b090109140313050f040e0316060f0e03031302031c05041d010e0411180403 78
    0x1c007900240707200ea00022003e820300c0624001f040d2000900c0c0c40ba0346648030382c044900209540d6040c0100b1311100c00500ea1040403d03801041d80d43d2448904690584100141c13000c0181e95606480c000359848245c684241079801203101d40000381c410741c1e0701010030201500100c1c1060182002c16800d40160b001210004000341e03401c11541003000c0401540206854548607840c03540e10342120b03c2052190290040b90001098004d060083d0102c5400c0f0b40c0c1705000c100145003c06181e8000d210751201100c01c020307080d2405049a40001c181d0340400e40140150b10294544030800c21100250b8010640007034503000d01f0460501d00740081c0006a0100a9204190141c0c1c0790800c1200d9959518080d1585449003c004111780041543c0e401402d1403500500c551840c000a4500440520301e40300c0307640950340082050b0b90000c00780044500031001c0e00488402110b1400c0c03110001d0040e01148052800040d0104068504524000001401015030200c580c1c0c1ea8a18101e400c907003c0e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 140250413 1250 140249163 140249189
    0x4020f180a0b0102011e020a02030f03040b06030601060311160c05150a09050402040308030106030f090209310209070c0606081e0f06010e07050c01020c07060f110105060108071d0a 79
    0x10203441502809810b004248000c005c000c0b442009032a10b1014900c0031030b40c0703683c040b44510005008000f00d13600e103001c00c18400c1e2245020301c0d00342c10b18042202c2280c0603026480001a850307000303014840e003c61070902c0721401d10010804005030041012000d0f00c001d0b15800d40003c041e1114801d07013004e1070300302d141d291f07803400f280b02c1c0038144840c01d034441c070f01a40c81004200046281401030300e055906501c2c0c0480c1d00880d2170b00344805441c100101950110a540a00c1180d0050300c2d40e00022540800c10b100b62941d0940c854618000c203500040c0d0402d190800041c0c08910070741b096510303903104000020319103031296400c40c60b01460800e1000c0c07034100b030b80e42a03040700d01c100558550280054020720b05981800e0750081300000c05880c034801c0c000081540c6503100c000b901621900c116500440700c90031b54502008028901d06403000d0003090f00c503a200c080c9107106008080c8215010b131520b80d403503155000104c0350343c08103c03010034605e803240004c0041c907980c45c0350030801000e203215150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 140251663 1250 140250413 140250421
    0x1a0702041d1b090c0c01200a1b05060a2003070309030905040c121d03030420060c0705011209050105070e0307060f21180819090602030d0504020f18 65
    0x545081d914201c2c6082150300700a5081c02d03551160201588040d00800140d201d4400c511104d01604055503010f0a4400d02820000d1031841100500f000c1201c07652038900b0600c08005015200e5645400a00140c0250f0f0000309840e51940268a2400c5149146103074500c075090110f200f43c0096a01c01c0000b51980e0155051540c02545180500400c4400300015030300d850001d042007051801d40c0031400e0b1102200c0724042c10160f040a050052007096075620300d802d01c4c1c843c0300740742c811032121414030000e110f082d52401c249058072aa40014001010918100340066851480e004081c00500380c950303000500085080c0103070350142610380c0701c848164000400f01414640c990304581304000c2c1c0010084a2a5030003c9012200550940e415007040c4511142901424122090b52400103410500600700b1072603800505485e0380166405899010b15041141c0d60302052007001e005074000d200e91f04104455922583c0c01604c0140020643d02c2d1031000706158524241303e91308070190313900401c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 140252913 1250 140251663 140251721
    0x90322030b06040b060a08060a0b070515070c08070605060d02220b0303090307050d02031c120b0a0f03060506120d0507030201152706120804050f09010f1a070204 71
    0x303140c020008070b070203004020102012a0546c000d946008042100070070110380d20f901c508420401402d20012599625810350901e55680c0d00070034050444080c0010004140a208801e89030007a0b600c16440ca14205441e140c00019080c09404c0d41d0340444100740010060740c0341d05c445810401c030000c07088079060340051040101ca0802c0d038030500903003041019851954021070b0107801d0300d204039001004c0c03070441c4c004241760240e003110024081c3c058101224609170410a0700a034107006103400c0c07205c60024010b0025246e9544906616182d01c1d070014000581240c0010741c3c401c1c405000741f0b111080c001d010341e00c2c1941030014600030510001d03664080c564203000302d14462000c1c501014149140c013108041d680007070400d44402c2031201c044181d04211542000d0000c1c0500c4c61126290042c03414003828642c002e104040c4200940d8145013036a04101c600c00d03040301c000c242240388452400e0224841450007040c40c0201c01001c110070707801030b6118402c001920101c0520698940025806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 140254163 1250 140252913 140252933
    0x503101d04231009060213140324011203020a020901030c050f06120c07030c0b160f020105090703020f01050c0618010e1504020d0c0e070f030c03020c031209032203 72
    0x1034540003a80b8400c054000400002c0c0086241c07400500041d22000c103040000c001c2c05001501c1d41c009049400020303089030317511220800064120140ca91640102c0203001072441207248a00110b415140100001c480c54821040d014ac000d0041d0340d02700409031700003001103000340c0040b68407171500c8200344694240903149110008064598615104540410000311200200307082e01051000410300101071040404110304c5520045003221340c24480000035800c0212108800000d591013440b0250074414040d40f4001c1d0700d140c010306116401d503000c0c800c0c0c202e41c0c48401030612500700210f10b19014200400f511815a044020040d1024900030710309643c48081101d803550702011600780a4007000d50000c0d00a54115140038030000c42c0d1824103003c1d000340d8440700d008240013003040105500050117502c0c000296604114041e108a0700b5801c9004920f01f40160382d10611082a90340003240540b0340161001d8210380c105460b0381c008120041178803080b881d41c0c500e0031508204120b00414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 140255413 1250 140254163 140254193
    0x3030d140702030a0c06020304021c030c0605060d02010c032304060302090a080d05030703021606020307020109050d0311090909100204120b0c0913051302030d03020a02060906010b0a0503101d04 85
    0x4061440c14084034001085d00014020141032140d00001003402c541d06c601508480c0114075030300d0354140e025030030060405a44050706840190419001500c0f0b4a000c1e00340910a550584a0202403141600e088071031b1140c5ea0482c1d200080b00707049000080f14040c016100410b020341d809a80c503c40070701072090049059010740c80301c0d0b004003031408620f078009084c2d942c03100d40361400584a1601542650881d000b0030006001e03644008140702d4031580c190081d80015004a0444e42498058034084044034080104140402400c3c01608002d103840011290040d0220040b0703620121001c00510403a40300b58060000d2000e0b0220680c10080d40c500c040b03074411503e10303907142483c54260108105910100c40111010b590380c0014008040c4151806002c41d009001c450f00b4003c0160003600a6014180210141c405d4000107a070a800000303d0340d041c1d0360040f1080d03003070030b07020032040d51a038001600002210a01d0640810070046143c00060500955100310f000c0c0d00342421b00f21601da0040c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 140256663 1250 140255413 140255417
    0x312020403050c060a05090406030c030605160f03020d0e0f06010302130203060603070c05011806021c0513020d02031e0607080606070f0b0705091203040501031103070801090b06040503030d1407 85
    0xc4820004201c001c188100700f1102941c3c2c0d6581c1daa8805412103061161b0a00294810f1502e0300100a001405010b0001c0e244582c10410040e103801c0440c403143ca40919400300082c5115462802840c07003078001d0003140401d60808a41c014410700068103104455a8442055103c1c1c03004000b5445e00030420030b1810041e420071840c5041c0f00b0080780080c03000402050a021802034100e0800009511038030080418802d022601c49480c034055001c0e40c0494080500301c2040003d4550301c101d00c0c4106030213004aa04003501c3c1d03083c7c6900340107a407160700500340c1e450b020302d0b6060b040306011000740c18842c40c610000fa003d9071421403000b030800040070f021107002d000140590400075a402c01c0346407072550407600658441c4e440d03900071245031280002e8a500180c0c001303001540c0013000000342c01550000d032424045e40144400e42c44490100700c40c0000090500300040181030b11580c003101d1140d1014006901c0c040e200e0003c00d00c2c6900902c1000f15080e0341d51a8254079055980c1210382007030f114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 140257913 1250 140256663 140256667
    0x11071101171302010c1403030a090201091401020a06050a060e07030504120e0f19091a180408030a090501290a0602030a0f11030d060b03041205190815030118031202 72
    0x84840007818102c200905004040d45036906010120080150034104c5908480c2c2e0b1349003100c00d500103410b000004902080e1141c00205484010450f44000179006038000c0030413041d60b8403000041d0901610303840855503144408500c0a4402180030710400490302c02003030500303061038000741e00b540800b6440200640c1c190f41c410b0a0399845a40d40e80d20001b02e0707405211b41c0c98050202030840380c543c040020705241c525040c00794403464140140e07051040368074850750100700b010f03000b000004540c000e000000420006010f07038030f907912030303401180a600002018202c904c440b4a45c4c02003a642180c203209044824640c40c6400c14003840600601d00c0510304001d17071581c028040c240c80c850000e0911007001e003520350008040069070083c0c3c406002c2030003036994800c0c0b801c0495000ba1000d5070f038880086c0150f000030740100d04940a0b1004a112118a085209030881d50141d026100e4500c040300740841440c0c90380d00b4000d0b88921034008480c0340c28815245006006088d84034484001c980c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 140259163 1250 140257913 140257921
    0x2109040510140d02100c0c050406080a030305010815060d0c090c08061201060b03060402220e010f120c0501050309031201170c010309081603020703080403030203040509010915181107110117 83
    0x1c2c00350b03203216168290505039002001c41c54210003d00da15000b88d85c00c140303806400955820006000003229000c0d0b14104810f9880b189419242e00c1c21ba1441e035940328194000c03613400d003402c008401c11203000e440500d10383c2d5201c800c83c1054030001091f00707000410803814040b0614241c035001034928401c0008010360307448c3c80c158840c2400001c14261203281d0110301c8411003038071624000c0ca001d0540c04031000c0e050300c411026002080a000e003009492810308081a182c1041060318045a0041444a0a40e00d81030044516510040c040b4880d80418403100402c101c00c000402d01030005e0001900159900840c010700d48001106014101403c000c0e40d2400303e05070750300300c41341c0820b00794419000030380f20309090786011896800203269000000e400018154007001620559a0031034490340b0599072214070030192484410740509100710032008100401940c03001c00040461448040b401a445c1e00d4111402d800c510b0741034810b5100040203501944c3e1101e600100010f43c84064409814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 140260413 1250 140259163 140259169
    0x6081006080c0d050f0a0b0118230616020f04060e1303110303090d020d0c0213050603010f09060204050a050105130b0f190e01020f0607022109040510140d02 69
    0x15051003104188032008000c5441c8440c10011502d4142002e4420b21040c00c11206a01e002c800481c0c07000c60b403a02e043c142001d02e42c0f080005007090b034101a914a00715040181411a081c420803003040503000c8803031542c1c035a4480300d01410000303203042010081414140140604030004640803485a885c2c00e13414040c99000045240e046a8071441001d031413202450140c910720244080b000703c40c840842089407025000518407120b55455007074801d5401c0c110030640d903c403099400250300002c44141c117510b41c0704992101d80d0001000b400030440012090700f101c100c6229140c1540c0c543c2e0002410300203030600c008241d008050a00e820391414200c0b44c0c1d070203000d24507070085482e0360380005968408440c504007038800b1292007090102c501c03882542d000e05003609040d051405405241e942d00407403200400d100d849040c09402411400240101d40d0900c0d80d001140090926814440700a95807034520440388500741400d0105840707814680082405122201d0321031050341d40d40740c4580161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 140261663 1250 140260413 140260441
    0x9010e101509091508070e01091118010516080c0d110703050a0b150402270108090705010c0f050a030809060a0204060c0204021c0e010c030e010b0d0206070f060509070603060608 78
    0x180e0341d148000f03442c1c0304400144100c01c3d0340344d028682d01c1c85a080007140005000d00d47d40d0407103450031400c02c15400044100d80c176a0044910201944440c50800c100c294000c1000344034924243c4680f07207000d04142d441c2020b503002025000502d510040040c0e5507180c1011b0030f00800740710980100b440740d248d5500e181c1d035402c0c1118004c0618010802065409150450042c11540001e01c1907444810520041c500107001c1c1511684100340c0110403915540038203601e900035101701c0040e08095041900640d52422f0740745049402d03005140010020070300138032540c2440c034841d0b55259464140b0781e10042c581000a0300120304184104001c00480b508282d800440945c140e80250b2902c1100d141803102401d1004000300f2103050003091ba50001066015190328601500c082210318407448005080351001c400150308604160958809460548060100c85100b00b03103001d9034003a190741d2081500d8080d1803e41c0107502100e018801c481d0036011b4400600641c0c43d120909260540e102c5c0f540c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 140262913 1250 140261663 140261669
    0x90604020f16050a0b0a0b150a050403020d06050703241406071202010509061b0f0c031c0c0206060d15110408160e060307060f080601050909010e101509 67
    0x2856000400810100a0105903500010003407590303a010122801d00540700d03c0d040000300d0781940050000b40300000700d8868680711501c0503148151010640c0c9444078290b003c00f86180900c041807100100681d05e084210040c3c52142e0b0000c10507051600c00a0103a40e000010b0702d0401c56691041c242c80040015504102d035124196070f00b01307001680214900d03125401021703082003510f03c18400725a1301508414000c4c1001012036113641e80da1864183e51611043c600c0114043c10844040c1918120003c1c1c105d40c186070b000d4910700620f18440005082c2e000700040115512180d4541d40650144110381d400342c0181c503070403110182591008400316003605080c1d212907407030607090410840702040c3c5024045400466123182002510380ca6025a01d00c9500c603407091f42e40018503181070119044086800b03079201c80101c150024400d41b40314034000c0846040117001e100d0751406070380e2a00b8050003090752040031105805c2018007031400300465004072038854802e00185c45419031042c580021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 140264163 1250 140262913 140262919
    0x216060b1203040e0c070f142401050d0209040c090e060703051e0f090a02030f0309130b010f081807090605040f2009030f030406030e190203101e0501240c020906 71
    0x16954440c5001801c4011f0814050541d200d00c50714602c0c82d07000050300e08880d80c0361101404004d050f002c4031400380d09090040076085540c00310391900504180404541192003540c480c80500e032034801e00300c1182c101c4a01e5103810303804401407200031074042c0705407500842c2c440c0401129040c80080800d0350480540b140c800c428070400000d504584c01d100e6404240d60040c1500c0503d8090b00f0346907520f80164004910804801d0840c0c2c429044030311a43c0801c48068440b0200040004015105250002d10762000c90035200500d680c5018103100043c00307001c3d5080000b40c4141000140030845e002060302c441c8507841e0042c498401c50100c01954481e449090007941c0c0c611185022a09041ca1a441c00b0154840460041060364150300b20100120451045807810115041c600d42c8200c212140070390560091600b250300307461541c00155142340300803850200c00c00b230741284900701e80c0264480301401e03090001e240c80c0c560502d9403880c600b10b014901b250324600c6d2500014100400a090184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 140265413 1250 140264163 140264167
    0x6020105100b0c0307150506040627020a09090f02041517011809080706050919030e09071b0309031b0302010503270a030f091a09040c030216060b1203040e0c 69
    0x101000f08200f201c1d035550340040343c41c1c0c141d1011071000002d8030050350346510890030035601050780c0464240c0c400c0d038100e890300c48d0890706041e17440c100b00950003034000c40c0800484090200d182881405080407040f14400016a81c42c035003403064042d10166480320302004100a420004583e07145c0c009415101c40d010a03c2281c03002d0300c40c5070001c08205c81c004000c0603011030301c0c00c05e0001c103a00c280d10032141c030001d40f2900c05101c8020ac0d460401194000d010458100e180000fa00301807400940c889aa400c10300410004034080608801107158120002000c1e50310078410003494803503412130080445403012081381140d00103080307130200414003100b142071306d43c01050000741503c08e07c1150340340c00240e40d038a507842c3c10010f00d4405801560008134540c0780c4001100b5140c084020000d1400452560400c4903079401c0101400c01c011441003003540911051050a10f005000016284159000142c0c030442805105082c104e00d0441104d03508103020030069038a1982c0c01a5100441d04101c40d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 140266663 1250 140265413 140265427
    0x7060b0f04090609050c10020601090903210c021614150d060b07031103030f0c16051617010605061b01020d02030c0304031206080304060302250c05090106020105100b 73
    0x5884200100d00441e0320a050195501c140034055100d19a030b640600305940801c46840b0911942c400340c01c060a00603442030004003c60340003a84080810340c840d151980c83c62055034105803403428150114904165540005495540c0401c199070f50300c41514503580025190101e54100b01c084250464042d50180c01900c1c07050075558200c45006400310420011181c0b00c41c0301070610307000070300c003213000c03e044c5944c2e0040500000300381c91140e40d0180813105160350355902500e03141c00c202910705004600911180000f0b9050118415409811520890492500c2c900405000c03032002d42c54120b0345001d109105580301c1d08101c460401507902ca01c503e40540030241d80c02485410a40d2201030b00c00301c2402014180c11340214060303030003030b030f0741e803500d50712981440013254141d12800003954000c0104003c4c1c00d00175006041c0f00b101940079061485444a14000d8a0099132030842c1c285c50101c0051146103040e80b50320307002d400c05200820007403800c10500c03840d0420600514001810103d096 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 140267913 1250 140266663 140266669
    0x20106030533060d020f01210e190b01170307050a0303050f010b03090615010e1203090111030c0a0312020919030b1308030a02130e0112120507020607060b 68
    0x150008640c444101e40b03980c0103901200d116256a0280041039455402401442012481119015002c010849898103000d0390030460070003070744442c403414800110108a4190101444003901e50900400070440c40d000c016160300382a4a00c0700220324800034140070010403a0007100398191002c58074048134980000141520314040c510000300383d803241038a514102b5a25400042c09035800c00e101014907622a681690640012514000c0584c8240005032004202890000e08041e0605108940500d8800031640107171602035a00c0c0b4a5100042041a55a2001c440c2e80243c0740751002c0c5081c2440210140e40313030303910424003508008080d4001c1c9840411581102d404034030040070b5111120502040124502045c40b0a580171001200003900b4030b401007629803200d0b070740002003515541da14800358000350080603030350f1030f000e8202201084c00e074081005280070301021208980280d107076141200581d900798102e0b50802030203008880058440f0801e507a51983c0c070030004281580c200c008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 140269163 1250 140267913 140267921
    0x181205041505090f010c0b1314011109090c16141006080607020d08010602122a03070606291b060c0408010e03040b09090a180b0f0601080601120c0201 66
    0x2140c4081c410700c40c0000d049070000010540c0d00c40a480d501001d0b5035000064407030608060b009442c107000c840000c1c180d941c2e21003c2040c82c0d031003086000c0324148055800c0307007120700001501003107100c0001d20314100d182c150300e002c0d4440c0c40500c08034504140d141e401d0341c6010319207500038a656400c46404010607c14032411001c480e04041c00c02c01950f46280b01c550720802541c10f6005401200d80f0548110b1150001c58103803511170b001890036455410400400740d00141c862480006480b04030110b51540c00d41030301d41120038400964403691a800d080085600951104504000c03046e0001030b03441040c006000c102c02101e44090321a0395960509103124007680c0112524041d83e010400f95001603006003003500d136203100820009403203248995880c800e030f0044d50041e502c00d201181d018a010600c841e4840000c22010030b40000c3c880c3e04281100381d2010448070364103038508001280500350716190b4443c00074078040c001c500349440042d020b054074000e030011664954490070701e480d0003500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 140270413 1250 140269163 140269169
    0x7090b180c0d050708061206010b041716030506010e13020a03020909100504031101150f2904030309090c0503190e070302120601140d1505151c0201020c0418120504 72
    0x2000b84070904d00400c00400f02c6a0858981d40703c0e0b80940e40940f080500068007034107031480c0910303091915040c40315043c074000e00c0c50051002c0b4031130304c0a60780145e0010306241d0700462190700140400e50502c4210700141100911821026140940314009a5544403d07070044940540d50071100d601d51403410707400c20010a80350b012182c200030a0208069104122020200c2840000c00c6014409940078110746582d10070042d802d41c44003424001100c03400009004101e44020a2515100034002e1440c41d800c039600c00d80100d100305508002a0450b80220070b01c1d02940e01c4d00f94550b1420002560341070314900e0034130044c1a03440200d102c030321038100200005183c00070900f220200310b05c0302150b07442c84240154440c80d404544042c0322401c1c01c1c000c06c4c1c2e2007a03104440410016060034070030300810004004e1701100120410600e03250300d0b0140700c8601142038080412a0030100d0001900d4480140c0c04035000303070324140c0c40b03412003d401514060304551000e40c1220307400e07928008940d2802030390 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 140271663 1250 140270413 140270437
    0x90c0e0402070507090f0614060d0212010b0304031412071d03030c030c0c031f090501110a0203190203090a091d010e1005011a1914040f03020307090b180c 68
    0x110700c003e1143c002180c0045520400d020f02c0003c080b86005026504203205491a40071005200403061409902071314925050701001414500300840d00e40103c04282e0101603a035078004140303c00d140e8800e01c95002141692000c62404c4032038405c11000c0ca01c010612020050318001a925110644980c94451100102203d888242c00e040064995125005004462082e49101c00310743c140481c1c00003010105034462851000b86461200c098201d41104031400d541c0c5403280d030858261800640406800c0d41d000799141c1003454003004c401e0981040000645d03100340b103580e105c1da03503542c002d900380e448007000450a8480740741120011701074049101619420708055003001f0b980045c205e00700d07004840c0c1c00d10041c1d03a90008061410718481c5040541c800401081e007000c3c0140c080501d001c5032034580f00441c9803c120303011500e900b140e00300b480060500c150400552504000c0030010b4429031500304001540f800015840e42c100040b03c0341048806400aa1080c00241c29180c92003004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 140272913 1250 140271663 140271667
    0x804020307051e0a081c0503090f0a030906080a1103070c02010306211b030b04060504031803060c0207083d050a020d060605070b0105040b0604030503070b0702070816090c0e0402 78
    0xc40e400c081400150f5601402640ca8510000f809070002030302c1c440d094440d404036644c0b01011a81200c0950004120302194400c1c049000c1588000308103566489020b9034980340c1c0c542c1000070003405d090028200300e02880c00c100501c0e06406403401169000103d5051060a4922510050b0060000d6901c113028a01e82c514001e4509030381141d8020005110b03900b8032201c4c82c102020710000d50752600000c0c290352041d50020300001d07099401950005d0081c01e01140606082da1882d510740c4031a08100d0308541c94161030800c0760b03010007414020f0300d512005441407170721100091614003203003520000c60038015904070110131040082d000c010480a041030040c0c4c546460543e000e580f0212400c29160b19088001070218841c1064606a65224a210603582d182c581000702500701c52444c40e41c020300821000000400801c0104129841410914510300d003440001c0d0a03d16140c0c0003d41030b8100c0030214481c0c802c0034200c0340a84950b400d00052011804000700c8603401000341054000d840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 140274163 1250 140272913 140272939
    0x608070908060f160503130803040602090306040f030305160c20030703060b0a060503041e050127020405060307030b010b0a020a0804080102070b01240804051513050c0102070b0901080402030705 85
    0xc003c030550312032107074424441c641915000c01181c40c0c0c84100c0c0e00c91204014090000300050000c0c0003160090b008103005802c1c981050f00082c2811401e0320111110581c4010060816401d801000d520402c45001d0f2080342c10b00100250001d040309100400f8225070b580c100c280054100701c442c144100141c201c83c082501c038070b0200700808200d040c1074883c001822002070400c2c0b1804c2100d10807940070034a00e02015100100880b20494000106c1e90f654a07202400341c60089091000070149003c9032210440300d85005000440e100500802e000340c022110500c00700b08001003117070441d078405840550703c50312290304900741090414003e0140b000060005140c0748150003800e4558001c80b076000300b0f45d0760749103903001c44801d201c181d60202882c0d25122103c40c0c001c0380600d034054001e60a4850798000368003446c00c20001141c0c1d080303206000c9a828004d01100b00411070b004503081c001429058201841c82245003d641080e40c10000383d44c00050840d2003e200340710007814082c4c040d14078410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 140275413 1250 140274163 140274181
    0xa05040b060d0501030b0711030a050f07030c050303150901090506090610090503030310240f0e01030204030b0109051b3a09060204050f0a1d06061612030c0302030f01060807090806 79
    0xb06c06e0b1a1400003801540c1c100c1c1d079009011045031500550368580c9860000985044007603500090800e9040c0b2140c1102180407840030310040d441099503e0901380010b400904001040308181c0000a1080c940000c01000b0744540e54101d0300f001c03040f42c291110395148101140c1d0b030034440d0001901800003006020030403110424107016120701e1207001c9010b01000601100c50010403030f000000402e080c840c031460501410f40c8115406e01854003525282d102e440306460303040e00ba07000100d2640d8403410000b2618103401211040114602c40614040c07403840d9208000d98030400c072100700c0030040b07651104280c2500085030041d1802909019502542c14100c00941291007020b004200c0154591850714203540f41c41e054070402c0c00b811249211000c80380519841c010032103074002c041040008490080b1006102805104040000a411451070014160313260030505030141401441844600c208004246040d5005884c8c5880c10395550b2000716040601e039884a5002d004600602100740703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 140276663 1250 140275413 140275433
    0x1508040605130203100e030d05010305100b010203040f0b0906040e0a0603050d09061218080d05010306180506041103030f070b1608040305040e041b08010c0e040b0a05040b060d050103 80
    0xd01451041116a4890994405040c8002c0000f03606070020b160b070400c4100310354001703154959400c040ba401c10902c0e40d91001203800a8000340c0c0c80764844582c1c0028102c1d280600d22180ae0300388013071402d1901e807202c00c0b0300d102d6072401100b2480300080381c0c6030101d49480c816600213101c184a841d156043c245c054038003c2c40d50380010794042c0180d5444008160280b01e0f003000f141c101e82e40d200040c1c80c50207004001040d0116808146551b44020400800d072404042d200c406164400082c0c1c5514601d0b12070b04443c0442903914106450b401c034000031070004034006a002e070304000ca61169050400c006070641c420107c02c80c2d444880464030a040c01003c14001e8803860780114040d09102d0300c10816a5140421100100001d40401050080642c080c060540091190080040d1007a40042523410032245811041e45a07644402038100c40d81d12145207216080c09071020800c514181c00440c208403443e0040d2800b03643c403009200c8564560034101c0384c640d1b1030708500f00000d50312072926050351 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 140277913 1250 140276663 140276671
    0x3050705070608091b030f030703020d030e0105060109031401111602010207080109080a110c03010507050307020c01090320130e030c1c1704020d0611090315010803040303030b0a1508 80
    0x58030a40768041240b0780100c0926000384010f40081001c440400c0c84200a41595035a0356014020b064007140c804c0d4017040944815803280d0058003500d07024800007001c80300541780b01c0322541c0c1000b05200003660400603507002c0d130340c1064054071019010550b01e805840b4880240e00c6070135000031220b0164049030140391034207100b60300750380b07010342c2d900c2c4164269100d00d44d01078040d20013000b00c001400d010b189000c110320420800d880d44902d03e500000c0c06c640d02141e00b803001c41d100004200c40150f040c000c0c00c04809007400d243c00740c503003181c8584000d070071852000100c240c68840107081c55030300c220420a850345907110a10103540d031403203040e40f0790300314684030402031260001d43c6010302e03400203580c40008503540d200205c0503044a10748440c2d1101900aa0b0002c542c0d12004c004941c4c540580b0b00380102a000d030b607030f80f46844400d043c03424054558845660080c480184103181d004401ca8040729014500400c480c4036801c0021079103a016481a11007180320186c0300e100581082a21b442 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 140279163 1250 140277913 140277923
    0xc020d090e0711151f0504020f03060f1302030708010f080609100c0309080c0a170403050606010507021201050a0501030c060c0b010b09061912060506092409041d070816091e0504030507 81
    0x5031946e908180006e030300543e10380820704481880000e04c1d50600104907465000c000f01540407201400c6888000c90748141c4814001980d51001031000402c100030403c010400c120050035580303461015640c40d1040c80c6107041105440e40802006144260002a00140c011090641d10302400c60983ea88500124003101c1d40d109806615644005000a44007225005030180c88540e5647c001120a0707842490100c1e031202c1161110895a102440b41a04c00c082d40e1030000f0303442d41541841c041c038030507c0d84080e0410001036141400207410a0030a41110500d507681a201c8000000103280f03800f410b0903043e000e4280b0010301c0b001c03940c404e04000441c0f2007100108161906c40d000e0010602c1040c503046e4101e40c40e4070f584407060052001105840003c0c000b0541402074000006080c1c2d104171034584030080c2c03610000305030f0a400b80720314401420280000c0c000500c450f004040c4a090380e20400d1417041e41c404144920302980174842002c407904010411003032800d442c01811941000c141524 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 140280413 1250 140279163 140279221
    0x207030b0c03130611040e0901020c0c030610030303090c0302180712060b070b060a09060b180906090f0910140a0c09050a1205010b0d060c020d090e071115 68
    0x50359900240442c0e026090036000d900841d0320588a1101910007030100d115001c0c020400003562141990006000c0d901c140009a074071a0140d01562520000a20540c4a80c10030302c2480301d1954503510100c11644d15040120781c4020390305020941842c61360001e50403030b0008050b0031103c204404d1702440784815444400c04103001c0c1607881c00711507040c01201601ca808001ca44085000103540c180c0c080c40c02405600303416128030b11042500e04590041c2d015100c00b0071a4003c80030460300440a03440103440c00109443c1410006140400c0644a82c01a80725000420b4038000280800c00610f80a61024489101000c250012092088406642e07880c9424820401540305007020350486000801032602c080c2444e6582c84042c004140844031903580c0e00030100c3c00d8a501c001800e41c0c41c00b9a400040c032141c44880070b414500906400010002c95080c1803114a140344402c5811104518000125452120100385840d00070a21122001c40c110100138058820800c0b069040d00f800088078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 140281663 1250 140280413 140280421
    0x91a010b0408060f090a23071d130515130309050102010c0807030c12050c070605181f0b0405090709060f1202040e0c1009141c060902040605100207030b 67
    0x1219900550207424038a0700f01e1408151114499072909030002111030556803c11525a10166a807102805c941a443c1c2001c0c1644100ca005005402c010514007030100d80c800c1f881d145050113a02c0090503103542e01648002076051050801c21007142c0b001d40594140e041c14040d103410380b00e03c61000708400007041e6410200700e952040c003074200c040d40152100c91540d1126030007034000c1d1000c0320102040107008550901c10b44c10368000e45010354104031030b440d60781526003045419550024012001c62082086035121b9000000340c416160001210b43d8001d0510011420040c0000000e0b440c2d201d030401013480300c20200410080100d0b58014001c2010340d59640540001036018810350341c40d4503c4554000240c1031070780104914a01c9071080d50010880d800014500d8407038032080100061040009120000f003450103410581811107500100100304408001500c817101c00c010881034440040c40119100c40d0800e00c05410300428100c3c21411180b4001d5445065202c2a01c10541506c081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 140282913 1250 140281663 140281679
    0x5010b07050309091504060b0c100c020712030c14010b1009060e060d060f0e04050c0f0609061620090609010303200c060d06060305070e210c0301091a01 67
    0x1640050303070000103181000105410071072000c070f0090400d007120900c000105c0e50b0743d0301c030f21442c400392070f064070010307120310500c051f0510b4034072009032000802c0d28004100c1d0900350000b4560f401c031074203400c107041c0111952404403040c46101c10010101b12442d100100501d1064024508031002a92003a161401d10001214007400c984240e00120340900b4680400d400c003800202a540110740c004620a9541d400480881341954041811451044240400c0003030502c00f0150b0040308071000440340b2175200000e506807090004203031258030000740c4003441503980f48242155682061810020018603e060030010800101503031048004000148251900145d09410780340c141d501c5c0380540b07c0340025010b540b013010345010f07110b04c10506c070040c85075a07440003080118244d00c4c0c0450307917625051000e0203840019028906201c00d11034100003c0d21030341d0034030148420058901c020546052030780c0e030400329000c01c1e494144d42446a440184200f208420f02c17540101d00c09007241c2d0b83d071051070b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 140284163 1250 140282913 140282917
    0x18100615032003010603020901020c130b010f031514120d0e04110403080306150d0603150501090218060a050d11040807120b0a0c0e060d1e09030c02120c09010803090405010b 76
    0x20502c0001400d00050200c03034441d0b80501000304c3d041c0111500d45044100003020354041c070310301c0c0c00c0064640110300b10950f40000f0342d400451003800d003400192508902e00300c0c0c44005018080f50308011a0130402c240c1d580d510604d20b0714009005480042c200c515008210420020119001310308228000f0742c45040a001c035000c41c2e4100c0005030458650b0020881500500d90407415000b5043c03081d6140c912880c0300d440001c502c6422a8642107082c0c80c2c0b000140d80059014210441c8140105509001c080110a0002401b2100c07240d07500600f1105640c00d020707858004109a10f042001134580110000402c01c0d9140d01c0212400301d03aa0705a0a8803001d0340400040090240b000400c4502c5010380003c11a00135504069003060840303000300c0d620341c02600320400711a07161400d07030303402103e01c5806031001e10702d80009120300d000c5602c01906022044500900500c0102441810b6071024414940031100040002c4c1455075175642195680d00401403052140d0301d4400006041c0c850340c42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 140285413 1250 140284163 140284211
    0x20d033e0705090f0402010314070302070209070c11090a15140a0f06050403030c1a33010905130204050a180b010c030c0602032806030611070b1810061503 68
    0x110050750360b401390407050f4180c01400880c181600e82e141c009840c40038165451254407a6a001612050036004010716614040d2020060050342861580458070506160301403520030340341c1d2207079621440c102500511141c07042007900366440310302003000c4620160300c07841010f00312a588052902e0701050558480d182c072550001c03505c2000b0810019001b0720346501114010001030100c120040141c034001e402c129201d00e412200302c2c1301c48000c890000c0c444c524510814104074090707140500040d041a0143c000c06124004098034518110080d404032406000d002c0c00300c19075140c1d40c03401181d030008070203120040c940c10880c10307000c194403030243e420b14150141d50301949a03206440d694000c0d400500100c4104004190401180f0036200c1d011080a1070040001641c034a5070400800b140d0020041075040c01040142001040302c82d840706401807454914042941070b801501450801c810030a82190f508003800001c503e9400000300308400f40a441c140100f0b1760108046201c190181c0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 140286663 1250 140285413 140285419
    0xa0902191d04030504050406090b011b0201020303072a050309030601090c0903020411070c03080301050a06020609030a2006070c060614100807051309060504060503120403020d033e0705 81
    0x5884445800012120075000b41c02801c201386070a0315180410290354844d001f00b034105803500c410b85419640319048a00c407041d909521140200c8690000f5261f10025046400308002c442c000c004c5410848006140000d441016940d00c180c94a401c03034a94001030b020314800c9c082d46c400003c0c1e9207000d00400000d40403030358806201505647c02c01004002a00d10a00c0c070401c00d0000b80c00154182c2c840b0b8006d140200d049035220340c507007820400286841d42161003150401810300040d80e000105583c8075070750038102454144400605114822100414100d2521840c07081c2300501c0c1d000075032141c2c100d01a66042c0607081c1c44200d01d45004480f640c0765500011a01001d02a80f4490561560006454a061444c0289549541c8840800c83d00401c000654400042119207040d1040380020181680900001e40400c61100c1160207030384400b0703001d14802c0d4412000c06202d401e0407901c08608070805070481c4200b241c0300a4070705480b841c0c0300c60000c084101c0040028005040400c0b03034002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 140287769 1106 140286663 140286689
    0xa0e011d0f0a020108060904080f07060c0201050105010314070c0c05030a2a0e011403100212060102061005100e0a0f060203030f0714090f0d020303030a090219 70
    0x22440701c070841c0e031090140c800140d0304401340d268001d1040b120b15043d81c2d11414000e003240b140b12904032450354002000c03420405aa402160307454031a6008006a07a2900010f5088602d03501c2060944550100043c0c8076622806134040900d10540c1c101030440c0c0d840c0301081c6070010b01d404c1280c5084207032904000d43d41108131800aa0501050b00c1031b50070b498018400403d07941805200c180c100c1544098105480c10805c020340c0e12000403045550b5400120318030703040030b801d981c01401401035802248500018481080641b44014142e04100d41c0e23403a01a02c5d1000c502c8245a0405030001d40081e03059082a038400003010145c0103159079103000307458403e81190041c000f0b130501c001407170042c044441200c02d0700c0007c403059600440142041c0001424940600da00135032510001080242101141d04500c0b0704910a507450800c3e2040c20040e220600da403401810291281 = true := by decide +kernel

theorem cover : BRFrame.Cov 140107913 140287769 := by
  have h0 := BRFrame.cov_init 140107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 140107913 ≤ n) (h2 : n < 140287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
